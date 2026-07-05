/*
 * Copyright (c) 2026 Michal Pleban.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in the
 *    documentation and/or other materials provided with the distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE AUTHOR ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED WARRANTIES
 * OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE DISCLAIMED.
 * IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL DAMAGES (INCLUDING, BUT
 * NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES; LOSS OF USE,
 * DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED AND ON ANY
 * THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY, OR TORT
 * (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT OF THE USE OF
 * THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * pass2 local routines for the Zilog Z8001 / Coherent target.
 *
 * Frame layout (matches the reference Coherent compiler).
 *
 * Node offsets are computed relative to the ENTRY SP (the SP before the frame
 * is allocated): args positive, autos negative.  But r13 (the frame pointer)
 * is set to the frame BOTTOM, and every frame slot is addressed in the stack
 * segment via a per-function equate "L<n> = SS|total":
 *
 *          address form            effective address
 *   arg:   L<n>+off(r13)   -> SS:(total + off + r13),  off = +4,+6,...
 *   auto:  L<n>+off(r13)   -> SS:(total + off + r13),  off = -2,-4,...
 * with r13 = entry_SP - total, so EA = SS:(entry_SP + off) = the slot.  The
 * equate also supplies the SS segment, needed when the address is taken (lda).
 *
 *   high address
 *   [caller args]   entry_SP+4, +6, ...    (ARGINIT=32 bits = 4 bytes)
 *   [return addr]   entry_SP+0 .. +3        (4-byte segmented return addr)
 *   -------------- entry SP
 *   [locals]        entry_SP-2, -4, ...     (AUTOINIT=0)
 *   [callee saves]  bottom .. bottom+2*nsave-1
 *   -------------- r13 = r15 = current SP = frame bottom
 *   low address
 *
 * Prologue sequence:
 *   L<n> = SS|total              (total = fsize + 2*nsave; framelab)
 *   dec/sub r15, $total
 *   [ld (rr14), r13             (for nsave == 1)]
 *   [ldm (rr14), rX, $nsave     (for nsave > 1, saves rX..r13)]
 *   ld r13, r15                  (r13 = frame bottom)
 *
 * Note: neither the ld/ldm store nor load forms change r15; the frame is
 *       allocated solely by "dec/sub r15,$total" and reclaimed in the
 *       epilogue by "inc/add r15,$total".
 */

#include "pass2.h"
#include <string.h>

int canaddr(NODE *);
void mygenregs(struct interpass *ip);

/*
 * Register names indexed by PCC register number.
 * r0-r15 are 16-bit word registers; rr0,rr2,...,rr10 are 32-bit pairs;
 * rq0,rq4,rq8 are 64-bit quads (doubles).
 * Indices: 0-15 = r0-r15, 16=rr0 .. 21=rr10, 22=rq0, 23=rq4, 24=rq8.
 */
char *rnames[] = {
	"r0",  "r1",  "r2",  "r3",  "r4",  "r5",
	"r6",  "r7",  "r8",  "r9",  "r10", "r11",
	"r12", "r13", "r14", "r15",
	"rr0", "rr2", "rr4", "rr6", "rr8", "rr10",
	"rq0", "rq4", "rq8"
};

/*
 * The component pieces of a quad register: qword(q) is the index of its
 * first (most significant) word register, qpair(q, lo) names its high
 * (lo=0) or low (lo=1) pair.  Big-endian: the high pair/word holds the
 * IEEE sign+exponent.
 */
static int
qword(int q)
{
	return (q - RQ0) * 4;
}

static char *
qpair(int q, int lo)
{
	return rnames[RR0 + (q - RQ0) * 2 + (lo ? 1 : 0)];
}

void
deflab(int label)
{
	printf(LABFMT ":\n", label);
}

/*
 * Per-function frame-base label.  Coherent addresses every frame slot in the
 * stack segment SS via a symbol "L<n> = SS|<framesize>" and references slots
 * as "L<n>+off(r13)" (see echo.s: L10001=SS|526, "lda rr0,L10001-512(r13)").
 * r13 is set to the frame bottom (the SP after allocation), and the equate's
 * SS|framesize value plus the (entry-SP-relative) node offset reconstructs the
 * absolute frame offset while carrying the SS segment.  Set in prologue().
 */
static int framelab;

/*
 * Emit the function prologue.
 *
 * Callee-saved word registers are R6-R12.  We always save R13 (the frame
 * pointer) because we change its value.  We find the lowest-numbered
 * callee-saved register that was actually used and save a contiguous run
 * from that register through R13 with a single ldm or ld instruction.
 */
/*
 * Determine the lowest-numbered callee-saved word register that must be
 * saved.  Callee-saved word registers are R6-R12; the pair registers
 * RR6-RR10 alias those same word registers.  R13 is always saved because
 * the prologue overwrites it with the frame pointer.
 */
static int
firstsavereg(void)
{
	int i, firstsave = R13;

	for (i = R6; i <= R12; i++) {
		if (TESTBIT(p2env.p_regs, i)) {
			firstsave = i;
			break;
		}
	}
	/* A used pair RRn implies its two component word registers are used */
	for (i = RR6; i <= RR10; i++) {
		if (TESTBIT(p2env.p_regs, i)) {
			int base = (i - RR0) * 2;	/* low word of the pair */
			if (base < firstsave)
				firstsave = base;
		}
	}
	/* A used quad clobbers its callee-saved words: rq4 = r6/r7,
	 * rq8 = r8-r11.  (rq0 is all scratch.) */
	if (TESTBIT(p2env.p_regs, RQ4) && R6 < firstsave)
		firstsave = R6;
	if (TESTBIT(p2env.p_regs, RQ8) && R8 < firstsave)
		firstsave = R8;
	return firstsave;
}

void
prologue(struct interpass_prolog *ipp)
{
	int firstsave, nsave, fsize, total;

	firstsave = firstsavereg();

	/* Save firstsave..R13 inclusive (always save R13 since we clobber it) */
	nsave = R13 - firstsave + 1;
	fsize = (p2maxautooff + 1) & ~1;  /* p2maxautooff is bytes; round to word */
	total = fsize + nsave * 2;

	/*
	 * Frame-base equate for stack-segment addressing (see framelab above).
	 * L<n> = 0|total; slots are then addressed "L<n>+off(r13)" with r13 at
	 * the frame bottom, so EA = seg0:(total + off + r13_bottom) recovers the
	 * absolute frame offset and supplies the stack segment.  total >= 2
	 * always (R13 is always saved).
	 *
	 * The native compiler wrote "L<n>=SS|total" with SS an external symbol
	 * (crts0.s pins it: "SS = 0x0000"), but that form is POISON with the
	 * shipped Coherent "as": a symbolic segment expression is E_SEG, and
	 * outsof()'s E_SEG long-form path (needed whenever total+off > 255,
	 * i.e. any frame bigger than ~250 bytes) drops the bit-15 long-form
	 * flag from the first address word (machine.c:1011 sets it on the
	 * caller's expr, then emits the zeroed copy).  The CPU then decodes
	 * the short form, eats one word too few, and executes the offset word
	 * as an instruction - echo.c crashed exactly this way, and even the
	 * native echo.s reassembled with the on-disk as loses its argv (MWC's
	 * factory binaries were built with an assembler that didn't have the
	 * bug).  A NUMERIC segment ("0|total") is E_ASEG instead, whose short
	 * AND long emissions are both correct, and the segment truly is 0 on
	 * this ABI.
	 */
	framelab = getlab2();
	printf(LABFMT "=0|%d\n", framelab, total);

	/* Step 1: allocate entire frame */
	if (total > 0) {
		if (total <= 16)
			printf("\tdec\tr15,$%d\n", total);
		else
			printf("\tsub\tr15,$%d\n", total);
	}

	/* Step 2: save callee-saved registers at current SP (no auto-decrement) */
	if (nsave == 1)
		printf("\tld\t(rr14),r13\n");
	else
		printf("\tldm\t(rr14),r%d,$%d\n", firstsave, nsave);

	/*
	 * Step 3: r13 = current SP = frame bottom.  (Native keeps the frame
	 * pointer at the bottom and reaches slots via the SS|total equate;
	 * node offsets remain entry-SP-relative and are corrected by the +total
	 * baked into the equate.)
	 */
	printf("\tld\tr13,r15\n");
}

/*
 * Emit the function epilogue.
 */
void
eoftn(struct interpass_prolog *ipp)
{
	int firstsave, nsave, fsize, total;

	if (ipp->ipp_ip.ip_lbl == 0)
		return;

	/* Recompute the same values as the prologue */
	firstsave = firstsavereg();
	nsave = R13 - firstsave + 1;
	fsize = (p2maxautooff + 1) & ~1;
	total = fsize + nsave * 2;

	/* Restore callee-saved registers (neither ld nor ldm changes r15) */
	if (nsave == 1)
		printf("\tld\tr13,(rr14)\n");
	else
		printf("\tldm\tr%d,(rr14),$%d\n", firstsave, nsave);

	/* Reclaim the whole frame */
	if (total > 0) {
		if (total <= 16)
			printf("\tinc\tr15,$%d\n", total);
		else
			printf("\tadd\tr15,$%d\n", total);
	}

	printf("\tret\tun\n");
}

/*
 * hopcode: emit the base opcode string for a simple ALU operation.
 * The 'f' suffix is unused on Z8001 (no condition codes in opcode).
 */
void
hopcode(int f, int o)
{
	char *str;

	switch (o) {
	case PLUS:  str = "add"; break;
	case MINUS: str = "sub"; break;
	case AND:   str = "and"; break;
	case OR:    str = "or";  break;
	case ER:    str = "xor"; break;
	default:
		comperr("hopcode: %d", o);
		str = "";
	}
	printf("%s", str);
}

/*
 * tlen: return the type size in bytes.
 */
int
tlen(NODE *p)
{
	switch (p->n_type) {
	case CHAR: case UCHAR:
		return SZCHAR / SZCHAR;
	case SHORT: case USHORT:
		return SZSHORT / SZCHAR;
	case INT: case UNSIGNED:
		return SZINT / SZCHAR;
	case LONG: case ULONG:
		return SZLONG / SZCHAR;
	case FLOAT:
		return SZFLOAT / SZCHAR;
	case DOUBLE: case LDOUBLE:
		return SZDOUBLE / SZCHAR;
	case LONGLONG: case ULONGLONG:
		return SZLONGLONG / SZCHAR;
	default:
		if (ISPTR(p->n_type))
			return SZPOINT(p->n_type) / SZCHAR;
		comperr("tlen: unknown type %d", p->n_type);
		return 0;
	}
}

/*
 * blput: print an operand for a BYTE instruction.
 *
 * The Z8001 only has byte registers for r0..r7: in a byte instruction the
 * register field 8+N names the LOW byte of word register rN ("rlN"), while
 * field N names the HIGH byte ("rhN").  A char value held in word register rN
 * lives in its low byte, so byte ops (ldb/andb/cpb/...) must name it "rlN" --
 * printing the plain word name "rN" would (mis)select the high byte rhN.
 * Non-register operands (memory, constants) print exactly as adrput.
 */
static void
blput(NODE *p)
{
	if (p->n_op == REG) {
		if (p->n_rval > R7)
			comperr("blput: byte value in non-byte-addressable "
			    "register r%d (needs r0-r7)", p->n_rval);
		printf("rl%d", p->n_rval);
	} else
		adrput(stdout, p);
}

/*
 * prword: print one 16-bit half of a 32-bit (pair) operand.
 *
 * The Z8001 has no 32-bit logical/negate/complement instructions, so long
 * AND/OR/XOR/COM/NEG are synthesised from two word operations acting on the
 * high and low halves of the pair.  This prints whichever half is requested.
 *
 * Big-endian layout: the high (most significant) word is at the lower
 * address / the even register Rn; the low word is at offset+2 / Rn+1.
 *   lo == 0 -> high word, lo == 1 -> low word.
 */
static void
prword(NODE *p, int lo)
{
	CONSZ val;

	switch (p->n_op) {
	case REG:
		printf("%s", rnames[(p->n_rval - RR0) * 2 + (lo ? 1 : 0)]);
		break;
	case OREG:
	case NAME:
		if (lo)
			setlval(p, getlval(p) + 2);
		adrput(stdout, p);
		if (lo)
			setlval(p, getlval(p) - 2);
		break;
	case ICON:
		val = getlval(p);
		printf("$" CONFMT, lo ? (val & 0xffffLL) : ((val >> 16) & 0xffffLL));
		break;
	default:
		comperr("prword: bad op %d", p->n_op);
	}
}

/*
 * prmem: print a memory operand displaced by "plus" bytes.
 * Used for the second halves of multi-word accesses; adrput picks the
 * right encoding (X for frame, DA for names, IR/BA for pair bases).
 */
static void
prmem(NODE *p, CONSZ plus)
{
	setlval(p, getlval(p) + plus);
	adrput(stdout, p);
	setlval(p, getlval(p) - plus);
}

/*
 * quadmem: move a quad register to/from memory (a 64-bit double).
 *
 * Memory forms and their instructions:
 *   NAME (DA) or frame OREG r13 (X):  single "ldm rN,mem,$4" - the form
 *     the native compiler uses (ldm's operand may be IR/DA/X, never BA).
 *   pair-base OREG: two ldl using IR/BA ("(rrN)" / "rrN(d)").  ldm is
 *     avoided here even at displacement 0: if the base pair lies inside
 *     the target quad, ldm would overwrite the base mid-transfer.  For
 *     the two-ldl load the half containing the base is loaded LAST; its
 *     own ldl is safe because the destination write follows the address
 *     read.  (The register allocator cannot exclude this aliasing: an
 *     OREG base has no regw node, so addedge_r never sees it.)
 */
static void
quadmem(NODE *mem, int q, int store)
{
	int base, hi;

	if (mem->n_op == OREG && mem->n_rval >= RR0) {
		base = mem->n_rval;
		/* which half's pair equals the base? -1 if none */
		hi = (RR0 + (q - RQ0) * 2 == base) ? 0 :
		     (RR0 + (q - RQ0) * 2 + 1 == base) ? 1 : -1;
		if (store && hi >= 0)
			comperr("quadmem: store base %s inside quad %s",
			    rnames[base], rnames[q]);
		if (store) {
			printf("\tldl\t");
			prmem(mem, 0);
			printf(",%s\n\tldl\t", qpair(q, 0));
			prmem(mem, 4);
			printf(",%s\n", qpair(q, 1));
		} else if (hi == 0) {
			/* base is the high pair: load low half first */
			printf("\tldl\t%s,", qpair(q, 1));
			prmem(mem, 4);
			printf("\n\tldl\t%s,", qpair(q, 0));
			prmem(mem, 0);
			printf("\n");
		} else {
			printf("\tldl\t%s,", qpair(q, 0));
			prmem(mem, 0);
			printf("\n\tldl\t%s,", qpair(q, 1));
			prmem(mem, 4);
			printf("\n");
		}
	} else if (mem->n_op == NAME || (mem->n_op == OREG &&
	    mem->n_rval == R13)) {
		printf("\tldm\t");
		if (store) {
			prmem(mem, 0);
			printf(",r%d,$4\n", qword(q));
		} else {
			printf("r%d,", qword(q));
			prmem(mem, 0);
			printf(",$4\n");
		}
	} else
		comperr("quadmem: bad mem op %d", mem->n_op);
}

/*
 * zzzcode: handle special escape sequences in instruction templates.
 *
 *   ZB  stack cleanup after call: add/inc r15, $n_qual
 *   ZL  long bitwise (AND/OR/ER): word op on high halves, then low halves
 *   ZC  long complement: com on each half
 *   ZN  long negate: complement both halves, then add 1 across the pair
 *   ZQ  clear a pair (reg or mem): clr on each half
 *   ZF  frame-address operand "off(reg)" for an lda
 *   ZM  high (segment) word of result pair, for the post-lda segment mask
 *   ZS  struct assignment: ldirb block copy
 *   ZT  struct argument: allocate stack slot + ldirb block copy
 *   ZD  double assignment: quad reg <-> quad reg/memory
 *   ZE  double load: memory/quad reg -> result quad A1
 *   ZP  double argument push: two pushl (low pair first)
 *   ZW  high (sign+exponent) word of the left operand's quad/pair
 */
void
zzzcode(NODE *p, int c)
{
	int n;
	char *op;

	switch (c) {
	case 'H':	/* byte-register form of the result operand (A1) */
		blput(getlr(p, '1'));
		break;
	case 'G':	/* byte-register form of the left operand (AL) */
		blput(getlr(p, 'L'));
		break;
	case 'J':	/* byte-register form of the right operand (AR) */
		blput(getlr(p, 'R'));
		break;

	case 'L':	/* long bitwise: two word ops on the pair halves */
		switch (p->n_op) {
		case AND: op = "and"; break;
		case OR:  op = "or";  break;
		case ER:  op = "xor"; break;
		default:  comperr("zzzcode ZL: bad op %d", p->n_op); op = "";
		}
		printf("\t%s\t", op);
		prword(p->n_left, 0);
		printf(",");
		prword(p->n_right, 0);
		printf("\n\t%s\t", op);
		prword(p->n_left, 1);
		printf(",");
		prword(p->n_right, 1);
		printf("\n");
		break;

	case 'M':	/* high (segment) word of result pair A1, for the
			 * post-lda segment-normalising "and rN,$0x7F00" */
		prword(getlr(p, '1'), 0);
		break;

	case 'F':	/* &local: segmented pointer to a frame object, exactly
			 * as native does it -- "lda A1,L<n>+off(r13)" using the
			 * per-function frame-base equate L<n>=SS|framesize, then
			 * "and A1hi,$32512" to normalise the segment word (see
			 * echo.s: "lda rr0,L10001-512(r13); and r0,$32512").
			 * off is the PLUS/MINUS constant (entry-SP-relative),
			 * matching the OREG offsets in adrput. */
	    {
		NODE *res = getlr(p, '1');
		CONSZ off = getlval(p->n_right);
		if (p->n_op == MINUS)
			off = -off;
		printf("\tlda\t%s," LABFMT,
		    rnames[res->n_rval], framelab);
		if (off > 0)
			printf("+");
		if (off != 0)
			printf(CONFMT, off);
		printf("(%s)\n", rnames[p->n_left->n_rval]);
		printf("\tand\t");
		prword(res, 0);			/* segment (high) word */
		printf(",$32512\n");
	    }
		break;

	case 'Q':	/* clear a pair (reg or mem): clr both halves */
		printf("\tclr\t");
		prword(p->n_left, 0);
		printf("\n\tclr\t");
		prword(p->n_left, 1);
		printf("\n");
		break;

	case 'C':	/* long complement: com both halves */
		printf("\tcom\t");
		prword(p->n_left, 0);
		printf("\n\tcom\t");
		prword(p->n_left, 1);
		printf("\n");
		break;

	case 'N':	/* long negate: ~x then +1 across the full pair */
		printf("\tcom\t");
		prword(p->n_left, 0);
		printf("\n\tcom\t");
		prword(p->n_left, 1);
		printf("\n\taddl\t");
		adrput(stdout, p->n_left);
		printf(",$1\n");
		break;

	case 'B':
		/* Stack cleanup after call: n_qual bytes were pushed as args */
		n = p->n_qual;
		if (n == 0)
			break;
		if (n <= 16)
			printf("\tinc\tr15,$%d\n", n);
		else
			printf("\tadd\tr15,$%d\n", n);
		break;

	case 'S':	/* struct assignment: ldirb (dest),(src),count */
	    {
		struct attr *ap = attr_find(p->n_ap, ATTR_P2STRUCT);
		NODE *l = p->n_left;
		int sz = ap->iarg(0);

		/* Resources are ordered by class: A1 = word (count),
		 * A2 = pair (dest address).  AR = source pointer (pair).
		 * The lda-formed dest address needs its segment word
		 * normalised before use as an ldir base.
		 *
		 * lda has no IR mode, so a pair-based dest OREG cannot go
		 * through "lda A2,(rrN)": at displacement 0 just copy the
		 * pair (segment already clean); otherwise use the BA form
		 * rrN(disp), which lda does accept. */
		if (l->n_op == OREG && l->n_rval >= RR0) {
			if (getlval(l) == 0) {
				expand(p, FOREFF, "\tldl\tA2,");
				printf("%s\n", rnames[l->n_rval]);
			} else {
				expand(p, FOREFF, "\tlda\tA2,");
				printf("%s(" CONFMT ")\n",
				    rnames[l->n_rval], getlval(l));
				printf("\tand\t");
				prword(getlr(p, '2'), 0);
				printf(",$32512\n");
			}
		} else {
			expand(p, FOREFF, "\tlda\tA2,AL\n");
			printf("\tand\t");
			prword(getlr(p, '2'), 0);
			printf(",$32512\n");
		}
		printf("\tld\t");
		expand(p, FOREFF, "A1");
		printf(",$%d\n", sz);
		expand(p, FOREFF, "\tldirb\t(A2),(AR),A1\n");
	    }
		break;

	case 'R':	/* struct-return call setup: push the address of this
			 * call's own frame buffer (assigned by myreader(),
			 * carried in ATTR_P2_STBUF) as the hidden argument.
			 * rr0 is free here: it is caller-saved and anything
			 * live across the call already excludes it. */
	    {
		struct attr *ap = attr_find(p->n_ap, ATTR_P2_STBUF);

		if (ap == NULL)
			comperr("ZR: struct call without buffer attribute");
		printf("\tlda\trr0," LABFMT "-%d(r13)\n", framelab, ap->iarg(0));
		printf("\tand\tr0,$32512\n");
		printf("\tpushl\t(rr14),rr0\n");
	    }
		break;

	case 'D':	/* double assignment: left <- right, one side a quad */
	    {
		NODE *l = p->n_left, *r = p->n_right;

		if (l->n_op == REG && r->n_op == REG) {
			printf("\tldl\t%s,%s\n",
			    qpair(l->n_rval, 0), qpair(r->n_rval, 0));
			printf("\tldl\t%s,%s\n",
			    qpair(l->n_rval, 1), qpair(r->n_rval, 1));
		} else if (l->n_op == REG)
			quadmem(r, l->n_rval, 0);
		else if (r->n_op == REG)
			quadmem(l, r->n_rval, 1);
		else
			comperr("ZD: no quad register operand");
	    }
		break;

	case 'E':	/* double load: AL (leaf or quad reg) -> quad A1 */
	    {
		NODE *l = getlr(p, 'L');
		int q = getlr(p, '1')->n_rval;

		if (l->n_op == REG) {
			printf("\tldl\t%s,%s\n",
			    qpair(q, 0), qpair(l->n_rval, 0));
			printf("\tldl\t%s,%s\n",
			    qpair(q, 1), qpair(l->n_rval, 1));
		} else
			quadmem(l, q, 0);
	    }
		break;

	case 'P':	/* push a double argument: low pair first, so the
			 * high (sign+exponent) pair lands at the lower
			 * address (native: "pushl rr2; pushl rr0").
			 * Memory sources push directly; pushl accepts
			 * DA/X sources (proven: "pushl (rr14),L+4(r13)"
			 * in factor.s) but not BA, so pair-based OREGs
			 * are excluded by the rule shapes. */
	    {
		NODE *l = getlr(p, 'L');

		if (l->n_op == REG) {
			printf("\tpushl\t(rr14),%s\n", qpair(l->n_rval, 1));
			printf("\tpushl\t(rr14),%s\n", qpair(l->n_rval, 0));
		} else {
			printf("\tpushl\t(rr14),");
			prmem(l, 4);
			printf("\n\tpushl\t(rr14),");
			prmem(l, 0);
			printf("\n");
		}
	    }
		break;

	case 'W':	/* high (sign+exponent) word of the left operand's
			 * register, for the sign-flip UMINUS "xor ,$-32768"
			 * (native negates doubles this way: modf.s
			 * "xor r0,$-32768") */
	    {
		NODE *l = getlr(p, 'L');

		if (l->n_op != REG)
			comperr("ZW: not a register");
		if (l->n_rval >= RQ0)
			printf("r%d", qword(l->n_rval));
		else
			prword(l, 0);
	    }
		break;

	case 'T':	/* struct argument passed by value.
			 *
			 * Reserve the argument slot at the top of stack with
			 * "sub r15,$slot" (PCC's own post-call cleanup reclaims
			 * exactly this, so it is NOT double-counted), then copy
			 * the struct into it with ldirb.
			 *
			 * The ldirb dest needs a valid segmented pointer to the
			 * slot.  We do NOT copy rr14: the SP's segment word is
			 * not a plain data-segment value usable as an indirect
			 * base.  Instead build A2 = (segment of the source AL) :
			 * r15 -- AL is a valid pointer to the struct (for a
			 * stack/local struct it carries the stack segment) and
			 * r15 is the reserved slot's offset.  A1 = byte count. */
	    {
		struct attr *ap = attr_find(p->n_ap, ATTR_P2STRUCT);
		int bytes = ap->iarg(0);		/* exact struct size */
		int slot = (bytes + 1) & ~1;		/* word-rounded slot */

		printf("\tsub\tr15,$%d\n", slot);
		/* A2.hi = AL.hi (segment); A2.lo = r15 (slot offset) */
		printf("\tld\t");
		prword(getlr(p, '2'), 0);
		printf(",");
		prword(getlr(p, 'L'), 0);
		printf("\n\tld\t");
		prword(getlr(p, '2'), 1);
		printf(",r15\n");
		printf("\tld\t");
		expand(p, FOREFF, "A1");
		printf(",$%d\n", bytes);
		expand(p, FOREFF, "\tldirb\t(A2),(AL),A1\n");
	    }
		break;

	default:
		comperr("zzzcode: unknown code '%c'", c);
	}
}

int
rewfld(NODE *p)
{
	return 1;
}

int
canaddr(NODE *p)
{
	int o = p->n_op;

	if (o == NAME || o == REG || o == ICON || o == OREG ||
	    (o == UMUL && shumul(p->n_left, STARNM|SOREG)))
		return 1;
	return 0;
}

int
flshape(NODE *p)
{
	int o = p->n_op;

	if (o == OREG || o == REG || o == NAME)
		return SRDIR;
	if (o == UMUL && shumul(p->n_left, SOREG))
		return SROREG;
	return SRREG;
}

int
shtemp(NODE *p)
{
	return 0;
}

void
adrcon(CONSZ val)
{
	printf("$" CONFMT, val);
}

void
conput(FILE *fp, NODE *p)
{
	CONSZ val = getlval(p);

	switch (p->n_op) {
	case ICON:
		if (p->n_name[0] != '\0') {
			fprintf(fp, "%s", p->n_name);
			if (val != 0)
				fprintf(fp, "+" CONFMT, val);
		} else {
			fprintf(fp, CONFMT, val);
		}
		return;
	default:
		comperr("conput: bad op %d", p->n_op);
	}
}

/*ARGSUSED*/
void
insput(NODE *p)
{
	comperr("insput");
}

/*
 * upput: print the low (offset) word of a 32-bit value.
 *
 * For big-endian Z8001 pairs:
 *   rr0 = r0(high/segment) : r1(low/offset) → upput gives r1
 *   rr2 = r2(high) : r3(low)                → upput gives r3
 *   etc.
 *
 * For memory: the second word (at offset+2) is the low word.
 * For ICON: the low 16 bits.
 */
void
upput(NODE *p, int size)
{
	CONSZ val;

	switch (p->n_op) {
	case NAME:
	case OREG:
		/* Low word is at the higher address (offset+2) */
		setlval(p, getlval(p) + 2);
		adrput(stdout, p);
		setlval(p, getlval(p) - 2);
		break;
	case REG:
		/* Low word register of a pair: base+1 */
		/* rr0(16): base=(16-16)*2=0, low=1=r1 */
		printf("%s", rnames[(p->n_rval - RR0) * 2 + 1]);
		break;
	case ICON:
		val = getlval(p);
		if (p->n_name[0] != '\0') {
			/* Symbol address - not split */
			printf("%s", p->n_name);
			if (val)
				printf("+" CONFMT, val);
		} else {
			printf("$" CONFMT, val & 0xffffLL);
		}
		break;
	default:
		comperr("upput: bad op %d size %d", p->n_op, size);
	}
}

/*
 * adrput: print an address operand.
 *
 * REG:  print register name (r0..r12, rr0..rr10)
 * OREG: print offset(reg)  — r13 used for frame-relative, pairs for pointer-based
 * NAME: print symbol name  (with optional +offset)
 * ICON: print $value       (or symbol name for labels)
 */
void
adrput(FILE *io, NODE *p)
{
	CONSZ val;

	if (p->n_op == FLD)
		p = p->n_left;

	switch (p->n_op) {
	case NAME:
		if (p->n_name[0] != '\0') {
			fputs(p->n_name, io);
			val = getlval(p);
			if (val != 0)
				fprintf(io, "+" CONFMT, val);
		} else {
			fprintf(io, CONFMT, getlval(p));
		}
		return;

	case OREG:
		val = getlval(p);
		if (p->n_rval == R13) {
			/*
			 * Frame slot: address in the stack segment via the
			 * per-function equate, "L<n>+off(r13)".  r13 is a WORD
			 * register, so this is Indexed (X) addressing: the
			 * address (L<n>+off) is indexed by the word r13.  (off
			 * is the entry-SP-relative node offset; CONFMT prints
			 * the sign for negatives, positives need an explicit
			 * '+'.)
			 */
			fprintf(io, LABFMT, framelab);
			if (val > 0)
				fputc('+', io);
			if (val != 0)
				fprintf(io, CONFMT, val);
			fprintf(io, "(%s)", rnames[R13]);
		} else if (val != 0) {
			/*
			 * Pair-register base + displacement: BASED (BA)
			 * addressing, written "rrN(disp)" -- the base pair
			 * comes FIRST, the displacement in parens (cf. native
			 * "lda rr4, rr10(4)").  Writing "disp(rrN)" would be
			 * parsed as Indexed mode, using the pair as a 16-bit
			 * word index (its segment half) -> wrong address.
			 */
			fprintf(io, "%s(", rnames[p->n_rval]);
			fprintf(io, CONFMT, val);
			fputc(')', io);
		} else {
			/* Pair-register base, zero displacement: indirect. */
			fprintf(io, "(%s)", rnames[p->n_rval]);
		}
		return;

	case ICON:
		/*
		 * Addressable value of a constant: immediate mode, "$" prefix.
		 * Works for both numeric constants ($5) and symbol addresses
		 * ($L259, $printf_).  Call targets bypass this by using the
		 * "CL" template code (conput), which prints the bare name.
		 */
		fputc('$', io);
		conput(io, p);
		return;

	case REG:
		fprintf(io, "%s", rnames[p->n_rval]);
		return;

	default:
		comperr("adrput: bad op %d", p->n_op);
		return;
	}
}

/*
 * cbgen: emit a conditional branch.
 */
static char *ccnames[] = {
	"eq",	/* EQ  */
	"ne",	/* NE  */
	"le",	/* LE  */
	"lt",	/* LT  */
	"ge",	/* GE  */
	"gt",	/* GT  */
	"ule",	/* ULE */
	"ult",	/* ULT */
	"uge",	/* UGE */
	"ugt",	/* UGT */
};

void
cbgen(int o, int lab)
{
	if (o < EQ || o > UGT)
		comperr("cbgen: bad op %d", o);
	printf("\tjr\t%s," LABFMT "\n", ccnames[o - EQ], lab);
}

/*
 * rmove: emit a register-to-register move.
 */
void
rmove(int s, int d, TWORD t)
{
	if (s == d)
		return;
	if (szty(t) == 4) {
		/* 64-bit quad move: two pair moves (quads never overlap) */
		printf("\tldl\t%s,%s\n", qpair(d, 0), qpair(s, 0));
		printf("\tldl\t%s,%s\n", qpair(d, 1), qpair(s, 1));
	} else if (szty(t) == 2) {
		/* 32-bit pair move */
		printf("\tldl\t%s,%s\n", rnames[d], rnames[s]);
	} else {
		/* 16-bit word move */
		printf("\tld\t%s,%s\n", rnames[d], rnames[s]);
	}
}

/*
 * COLORMAP: can we add one more register of class c to the allocation set r[]?
 * r[i] is non-zero if register i is already in use.
 */
/*
 * COLORMAP: can a node of class c be colored, given r[], the count of
 * already-colored interfering neighbours in each register class?
 * r is indexed by class (r[CLASSA], r[CLASSB]) - NOT by register number.
 *
 * Class A holds 13 word registers (r0-r12).  Class B holds 6 register
 * pairs (each overlapping two words; rr0 is reserved, so 5 selectable).
 * Class C holds 3 quads (rq0,rq4,rq8), each overlapping 4 words / 2
 * pairs.  Worst-case (conservative) blocking counts.
 */
int
COLORMAP(int c, int *r)
{
	int num;

	switch (c) {
	case CLASSA:
		/* a pair blocks 2 words, a quad blocks 4 */
		num = r[CLASSA] + 2 * r[CLASSB] + 4 * r[CLASSC];
		return num < 13;
	case CLASSB:
		/* 5 allocatable pairs (rr2..rr10; rr0 reserved);
		 * a word or pair neighbour blocks 1 pair, a quad blocks 2 */
		num = r[CLASSB] + r[CLASSA] + 2 * r[CLASSC];
		return num < 5;
	case CLASSC:
		/* any neighbour blocks at most 1 of the 3 quads */
		num = r[CLASSA] + r[CLASSB] + r[CLASSC];
		return num < 3;
	}
	return 0;
}

/*
 * Return the register class suitable for a value of type t.
 * Consistent with PCLASS in macdefs.h: 64-bit values (double) use class
 * C (quads), 32-bit values (long/ptr/float) class B (pairs), everything
 * else class A (words).
 */
int
gclass(TWORD t)
{
	return szty(t) == 4 ? CLASSC : szty(t) == 2 ? CLASSB : CLASSA;
}

/*
 * Return the number of bytes an argument of this type occupies on the stack.
 */
static int
argsiz(NODE *p)
{
	TWORD t = p->n_type;

	if (t == LONG || t == ULONG || t == FLOAT || ISPTR(t))
		return 4;
	if (t == DOUBLE || t == LDOUBLE || t == LONGLONG || t == ULONGLONG)
		return 8;
	if (t == STRTY || t == UNIONTY)
		/* word-rounded to keep the stack aligned (matches ZT) */
		return (attr_find(p->n_ap, ATTR_P2STRUCT)->iarg(0) + 1) & ~1;
	return 2;	/* char/short/int promoted to word */
}

/*
 * Compute the total size of arguments to a call, stored in n_qual so the
 * 'ZB' zzzcode escape can emit the post-call stack adjustment.
 */
void
lastcall(NODE *p)
{
	NODE *op = p;
	int size = 0;

	p->n_qual = 0;
	if (p->n_op != CALL && p->n_op != FORTCALL && p->n_op != STCALL &&
	    p->n_op != UCALL && p->n_op != USTCALL)
		return;
	/* the ZR escape pushes the hidden struct-return pointer */
	if (p->n_op == STCALL || p->n_op == USTCALL)
		size = 4;
	if (p->n_right != NIL) {
		for (p = p->n_right; p->n_op == CM; p = p->n_left)
			size += argsiz(p->n_right);
		size += argsiz(p);
	}
	op->n_qual = size;
}

/*
 * Special shape matching.  See SNBA/SFRAME in macdefs.h: the based address
 * mode rrN(disp) exists only for the ld-family, so non-load rules use these
 * shapes to accept just the OREG flavours every instruction can encode.
 * Frame OREGs (base r13) print as L<n>+off(r13) = X mode; pair-base OREGs
 * with zero displacement print as (rrN) = IR mode.
 */
int
special(NODE *p, int shape)
{
	switch (shape) {
	case SNBA:
		if (p->n_op != OREG)
			return SRNOPE;
		if (p->n_rval == FPREG)
			return SRDIR;
		if (p->n_rval >= RR0 && getlval(p) == 0)
			return SRDIR;
		return SRNOPE;
	case SFRAME:
		if (p->n_op == OREG && p->n_rval == FPREG)
			return SRDIR;
		return SRNOPE;
	case SR13:
		if (p->n_op == REG && p->n_rval == FPREG)
			return SRDIR;
		return SRNOPE;
	}
	return SRNOPE;
}

/*
 * Bitfield expansion - not used (no FIELDOPS).
 */
int
fldexpand(NODE *p, int cookie, char **cp)
{
	return 0;
}

/*
 * Target-dependent command-line option handling.
 */
void
mflags(char *str)
{
}

/*
 * Target-dependent handling of inline-asm operands.
 */
int
myxasm(struct interpass *ip, NODE *p)
{
	return 0;
}

/* No target-specific pass2 optimisation. */
void
myoptim(struct interpass *ip)
{
}

/*
 * Software floating point.
 *
 * The Z8001 in the Commodore 900 has no FPU; the native Coherent
 * compiler lowers all floating-point operations to calls into the libc
 * runtime (libc/crt/{dadd,dcmp,dmul,ddiv,dtoi,itod,dtof,ftod}.s).  We
 * follow the exact same convention (ground truth: the compiler-emitted
 * call sites in factor.s/modf.s and the helper sources themselves):
 *
 *   value/arg convention: a double travels in rq0 (r0=sign+exponent),
 *     and is pushed "pushl rr2; pushl rr0" (8 bytes, caller pops);
 *   dradd/drsub/drmul/drdiv(da, db): both by value, result in rq0
 *     (the dl* variants taking &db are just a size optimization);
 *   drcmp(da, db): three-way result in r1 (1/0/-1), compared against 0;
 *   diflt/duflt/dlflt/dvflt(i): int/unsigned/long/ulong -> double, rq0;
 *   ifix/ufix(d) -> r1, lfix/vfix(d) -> rr0: double -> integer;
 *   dfpack: float rr0 -> double rq0, fdpack: double rq0 -> float rr0
 *     (register-based, no stack args; handled as table SCONV rules);
 *   negation is inline: "xor <hiword>,$-32768" (table UMINUS rules).
 *
 * Float arithmetic is computed in double (K&R style - the runtime has
 * no float helpers), converting operands in and the result back out.
 *
 * The rewrite runs from myreader(), before canon/sucomp, so the created
 * CALL nodes get the full standard treatment (argument FUNARG pushes,
 * n_qual cleanup via lastcall, pre-evaluation into temps when several
 * calls appear in one tree).
 */

#define	ISFPT(t)	((t) == FLOAT || (t) == DOUBLE || (t) == LDOUBLE)

/* rewrite a unary node into a one-argument helper call */
static void
mkcall(NODE *p, char *name)
{
	p->n_op = CALL;
	p->n_right = mkunode(FUNARG, p->n_left, 0, p->n_left->n_type);
	p->n_left = mklnode(ICON, 0, 0, FTN|p->n_type);
	p->n_left->n_name = name;
}

/* rewrite a binary node into a two-argument helper call; the CM chain
 * is evaluated rightmost-first (gencode), so the left operand is pushed
 * last and lands in the first-argument slot */
static void
mkcall2(NODE *p, char *name)
{
	p->n_op = CALL;
	p->n_right = mkunode(FUNARG, p->n_right, 0, p->n_right->n_type);
	p->n_left = mkunode(FUNARG, p->n_left, 0, p->n_left->n_type);
	p->n_right = mkbinode(CM, p->n_left, p->n_right, INT);
	p->n_left = mklnode(ICON, 0, 0, FTN|p->n_type);
	p->n_left->n_name = name;
}

/* wrap p's current contents in a new child node and make p an SCONV
 * to type t */
static void
wrapsconv(NODE *p, TWORD t)
{
	NODE *q = talloc();

	*q = *p;
	p->n_op = SCONV;
	p->n_left = q;
	p->n_type = t;
}

static NODE *
mksconv(NODE *p, TWORD t)
{
	return mkunode(SCONV, p, 0, t);
}

static void
fixfloatops(NODE *p, void *arg)
{
	NODE *l, *r;
	TWORD t = p->n_type, lt;
	char *fn;

	switch (p->n_op) {
	case PLUS:
	case MINUS:
	case MUL:
	case DIV:
		if (!ISFPT(t))
			return;
		fn = p->n_op == PLUS ? "dradd" : p->n_op == MINUS ? "drsub" :
		    p->n_op == MUL ? "drmul" : "drdiv";
		if (t == FLOAT) {
			/* compute in double, round the result back */
			p->n_left = mksconv(p->n_left, DOUBLE);
			p->n_right = mksconv(p->n_right, DOUBLE);
			p->n_type = DOUBLE;
			mkcall2(p, fn);
			wrapsconv(p, FLOAT);
		} else
			mkcall2(p, fn);
		break;

	case EQ:
	case NE:
	case LE:
	case LT:
	case GE:
	case GT:
		lt = p->n_left->n_type;
		if (!ISFPT(lt))
			return;
		l = p->n_left;
		r = p->n_right;
		if (lt == FLOAT) {
			l = mksconv(l, DOUBLE);
			r = mksconv(r, DOUBLE);
		}
		/* r1 = drcmp(a, b) = 1/0/-1; keep the relational op and
		 * compare that against 0 (native: "calr drcmp; test r1;
		 * jr cc" - our SZERO rule emits cp, same flags) */
		l = mkunode(FUNARG, l, 0, DOUBLE);
		r = mkunode(FUNARG, r, 0, DOUBLE);
		r = mkbinode(CM, l, r, INT);
		l = mklnode(ICON, 0, 0, FTN|INT);
		l->n_name = "drcmp";
		p->n_left = mkbinode(CALL, l, r, INT);
		p->n_right = mklnode(ICON, 0, 0, INT);
		break;

	case SCONV:
		l = p->n_left;
		lt = l->n_type;
		if (ISFPT(t) && ISFPT(lt))
			return;		/* dfpack/fdpack table rules */
		if (ISFPT(t)) {
			/* integer -> fp; helpers take int/unsigned/long/
			 * ulong, so widen narrow types first */
			switch (lt) {
			case CHAR: case SHORT: case BOOL:
				p->n_left = mksconv(l, INT);
				lt = INT;
				break;
			case UCHAR: case USHORT:
				p->n_left = mksconv(l, UNSIGNED);
				lt = UNSIGNED;
				break;
			}
			if (lt == INT)
				fn = "diflt";
			else if (lt == UNSIGNED)
				fn = "duflt";
			else if (lt == LONG)
				fn = "dlflt";
			else
				fn = "dvflt";	/* ulong, pointers */
			if (t == FLOAT) {
				p->n_type = DOUBLE;
				mkcall(p, fn);
				wrapsconv(p, FLOAT);
			} else
				mkcall(p, fn);
		} else if (ISFPT(lt)) {
			/* fp -> integer; helpers take a double and return
			 * int in r1 / long in rr0, narrow types truncate
			 * from the int result afterwards */
			TWORD rt;

			if (lt == FLOAT)
				p->n_left = mksconv(p->n_left, DOUBLE);
			switch (t) {
			case CHAR: case SHORT: case BOOL: case INT:
				rt = INT; fn = "ifix"; break;
			case UCHAR: case USHORT: case UNSIGNED:
				rt = UNSIGNED; fn = "ufix"; break;
			case LONG:
				rt = LONG; fn = "lfix"; break;
			default:
				rt = ULONG; fn = "vfix"; break;
			}
			if (rt != t) {
				p->n_type = rt;
				mkcall(p, fn);
				wrapsconv(p, t);
			} else
				mkcall(p, fn);
		}
		break;
	}
}

/*
 * Struct-return support: every STCALL/USTCALL gets its OWN buffer in
 * the caller's frame for the returned value (its address is pushed as
 * the hidden argument by the ZR escape).  The offset is attached to the
 * call node as ATTR_P2_STBUF.  Buffers must be distinct per call, not
 * shared: pass 2 pre-evaluates call-containing arguments into pointer
 * temps before pushing any argument, so f(g(), h()) has both results
 * live at once.  Reserved below the pass-1 autos; bumping p2autooff
 * here (myreader runs before code generation) keeps later spill temps
 * below them.
 */
static void
findstcall(NODE *p, void *arg)
{
	int *offp = arg;
	struct attr *ap;
	int sz;

	if (p->n_op != STCALL && p->n_op != USTCALL)
		return;
	if ((ap = attr_find(p->n_ap, ATTR_P2STRUCT)) == NULL)
		comperr("findstcall: struct call without size attribute");
	sz = (ap->iarg(0) + 1) & ~1;
	*offp += sz;
	ap = attr_new(ATTR_P2_STBUF, 1);
	ap->iarg(0) = *offp;
	p->n_ap = attr_add(p->n_ap, ap);
}

void
myreader(struct interpass *ip)
{
	struct interpass *ip2;
	int off = p2autooff;

	DLIST_FOREACH(ip2, ip, qelem) {
		if (ip2->type != IP_NODE)
			continue;
		walkf(ip2->ip_node, fixfloatops, 0);
		walkf(ip2->ip_node, findstcall, &off);
	}
	if (off > p2autooff) {
		p2autooff = off;
		if (p2autooff > p2maxautooff)
			p2maxautooff = p2autooff;
	}
}

void
mycanon(NODE *p)
{
}

void
mygenregs(struct interpass *ip)
{
}
