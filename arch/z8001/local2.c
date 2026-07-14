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
 * Descriptor carried by a SWDISP node (in n_name) from swcpir() to the ZZ
 * zzzcode: case count, default-target label, and the value/target table
 * label.  See mygenswitch() in code.c for the dispatch shape.
 */
struct swdesc {
	int n;			/* number of cases */
	int deflab;		/* default (no-match) label */
	int ltab;		/* .word value/offset table label */
};

/*
 * Register names indexed by PCC register number.
 * r0-r15 are 16-bit word registers; rr0,rr2,...,rr10 are 32-bit pairs;
 * rq0,rq4,rq8 are 64-bit quads (doubles); rl0-rl7 are the 8-bit byte
 * registers (low halves of r0-r7, register class D for char values).
 * Indices: 0-15 = r0-r15, 16=rr0 .. 21=rr10, 22=rq0 .. 24=rq8,
 * 25=rl0 .. 32=rl7.
 */
char *rnames[] = {
	"r0",  "r1",  "r2",  "r3",  "r4",  "r5",
	"r6",  "r7",  "r8",  "r9",  "r10", "r11",
	"r12", "r13", "r14", "r15",
	"rr0", "rr2", "rr4", "rr6", "rr8", "rr10",
	"rq0", "rq4", "rq8",
	"rl0", "rl1", "rl2", "rl3", "rl4", "rl5", "rl6", "rl7"
};

/*
 * dword: the word register containing byte register b.  Byte values are
 * operated on with WORD instructions (extsb, and, neg, push, ld) whenever
 * the byte-register field encoding would not do: word ops work on any
 * register and only the low byte carries the value.
 */
static int
dword(int b)
{
	return b - RL0;
}

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

/*
 * Labels already emitted in the current function, newest first.  cbfuse()
 * consults this to tell a backward branch (target already seen) from a
 * forward one: djnz is only a win backward - forward it would relax in the
 * assembler to the larger "dec;jp" form.  Allocated from the per-function
 * tmpalloc arena and reset at each prologue.
 */
struct seenlab {
	struct seenlab *next;
	int lab;
};
static struct seenlab *seenlabs;

static int
labseen(int lab)
{
	struct seenlab *s;

	for (s = seenlabs; s != NULL; s = s->next)
		if (s->lab == lab)
			return 1;
	return 0;
}

void
deflab(int label)
{
	struct seenlab *s;

	s = tmpalloc(sizeof(struct seenlab));
	s->lab = label;
	s->next = seenlabs;
	seenlabs = s;

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
 * Set by prologue() and consulted by eoftn(): this function needs no
 * frame-pointer setup at all (no r13 save, no "ld r13,r15", no frame
 * allocation), so both prologue and epilogue collapse to nothing but the
 * body and a bare "ret un".  See usesfp() and prologue() for the criteria.
 */
static int curframeless;

/*
 * Prologue's register-save plan, recomputed-invariant parts stashed here for
 * eoftn() (which cannot re-run usesfp() - it only sees the epilog end of the
 * list).  curneedfp: r13 is set up as a frame pointer (has autos/spills or the
 * body addresses a frame slot).  cursavetop: highest register in the saved
 * contiguous run (R13 when curneedfp, else the top used callee-saved r6..r12).
 */
static int curneedfp;
static int cursavetop;

/*
 * walkf callback: flag any reference to r13 (FPREG) used as a frame base.
 * By emit time canon() has lowered stack args and autos to OREG(FPREG) and
 * &local to ADDROF(OREG(FPREG)) or PLUS(REG FPREG, ICON); all of these carry
 * FPREG in n_rval, so a single test on OREG/REG suffices.  r13 is a dedicated
 * frame pointer, never allocated, so a hit is always a genuine frame use.
 */
static void
fpuse(NODE *p, void *arg)
{
	if ((p->n_op == OREG || p->n_op == REG) && p->n_rval == FPREG)
		*(int *)arg = 1;
}

/*
 * Does the function body reference the frame pointer r13 at all?  The whole
 * interpass list (IP_PROLOG .. IP_EPILOG) is still linked when prologue() runs
 * during the emit walk, so we scan the body forward from the prolog node.  A
 * function that touches no frame slot needs no frame pointer; combined with a
 * zero autosize (which also rules out spill slots, since any spill bumps
 * p2maxautooff) this is the frameless criterion.
 */
static int
usesfp(struct interpass_prolog *ipp)
{
	struct interpass *ip;
	int found = 0;

	for (ip = DLIST_NEXT(&ipp->ipp_ip, qelem); ip->type != IP_EPILOG;
	    ip = DLIST_NEXT(ip, qelem)) {
		if (ip->type == IP_NODE)
			walkf(ip->ip_node, fpuse, &found);
	}
	return found;
}

/*
 * Emit the function prologue.
 *
 * Callee-saved word registers are R6-R12; R13 is the frame pointer.  We save a
 * contiguous run of the callee-saved registers the body actually used.  R13 is
 * included in that run (and set to the frame bottom) ONLY when the function
 * needs a frame pointer - it has autos/spills or addresses a frame slot / stack
 * argument through r13 (see curneedfp).  A function that uses neither r13 nor
 * any callee-saved register emits no prologue at all.
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
	/* A used byte register rl6/rl7 lives inside callee-saved r6/r7 */
	if (TESTBIT(p2env.p_regs, RL6) && R6 < firstsave)
		firstsave = R6;
	if (TESTBIT(p2env.p_regs, RL7) && R7 < firstsave)
		firstsave = R7;
	return firstsave;
}

/*
 * Highest-numbered callee-saved word register (R6-R12) actually used, or -1 if
 * none.  Used when r13 is NOT a frame pointer (see prologue): the save run then
 * ends at the topmost used callee-saved register instead of always at R13.
 */
static int
lastsavereg(void)
{
	int i, last = -1;

	for (i = R6; i <= R12; i++)
		if (TESTBIT(p2env.p_regs, i))
			last = i;
	/* pair RRn's high word is (n-RR0)*2+1: rr6->r7, rr8->r9, rr10->r11 */
	for (i = RR6; i <= RR10; i++)
		if (TESTBIT(p2env.p_regs, i)) {
			int hi = (i - RR0) * 2 + 1;
			if (hi > last)
				last = hi;
		}
	/* quads: rq4 = r4-r7 (high saved word r7), rq8 = r8-r11 (high r11) */
	if (TESTBIT(p2env.p_regs, RQ4) && R7 > last)
		last = R7;
	if (TESTBIT(p2env.p_regs, RQ8) && R11 > last)
		last = R11;
	if (TESTBIT(p2env.p_regs, RL6) && R6 > last)
		last = R6;
	if (TESTBIT(p2env.p_regs, RL7) && R7 > last)
		last = R7;
	return last;
}

void
prologue(struct interpass_prolog *ipp)
{
	int firstsave, nsave, fsize, total;

	seenlabs = NULL;	/* start a fresh emitted-label set (see cbfuse) */

	firstsave = firstsavereg();
	fsize = (p2maxautooff + 1) & ~1;  /* p2maxautooff is bytes; round to word */

	/*
	 * r13 is set up as a frame pointer ONLY when the body needs one: either
	 * there are autos/spills (fsize>0) or the body addresses a frame slot /
	 * stack argument through r13 (usesfp()).  When it isn't needed we neither
	 * save nor load r13 - the caller's r13 is preserved simply by our never
	 * touching it - and the register-save run stops at the topmost callee-saved
	 * register the body actually used instead of running through r13.
	 */
	curneedfp = (fsize > 0 || usesfp(ipp));
	if (curneedfp) {
		cursavetop = R13;		/* always save AND set up r13 */
	} else {
		cursavetop = lastsavereg();	/* top used callee-saved, or -1 */
		if (cursavetop < 0) {
			/*
			 * Frameless: no autos, no r13 use, no callee-saved
			 * register touched.  Emit nothing; eoftn() emits only
			 * "ret un".  Typical of leaf/no-arg helpers.
			 */
			curframeless = 1;
			return;
		}
	}
	curframeless = 0;

	nsave = cursavetop - firstsave + 1;
	total = fsize + nsave * 2;

	/*
	 * Frame-base equate for stack-segment addressing (see framelab above),
	 * emitted only when r13 is a frame pointer.  L<n> = SS|total; slots are
	 * addressed "L<n>+off(r13)" with r13 at the frame bottom, so EA =
	 * SS:(total + off + r13_bottom) recovers the absolute frame offset AND
	 * supplies the stack segment.
	 *
	 * SS is an external symbol pinned per-ABI by the startup: crts0.s sets
	 * "SS = 0x0000" for user programs (a single flat segment), while the
	 * kernel's md.s sets "SS = 0x3F3F" (system stack in segment 0x3F).  Using
	 * the symbol makes frame/arg addressing correct in BOTH worlds; hardcoding
	 * a numeric "0|total" only works when SS==0 and silently reads segment 0
	 * for anything running segmented (the kernel), where every callee read its
	 * stack arguments out of ROM.  The symbolic segment is E_SEG; this relies
	 * on the assembler's E_SEG long-form emission being correct (it now is -
	 * the earlier outsof() bit-15 drop that motivated the "0|" workaround has
	 * been fixed in the Coherent "as").
	 */
	if (curneedfp)
		printf(LABFMT "=SS|%d\n", framelab, total);

	/*
	 * Allocate-and-save.  With no autos (fsize==0, so total==nsave*2) a single
	 * stack instruction does the SP decrement AND the store:
	 *   nsave==1               -> push  (2 bytes vs dec + ld  = 4)
	 *   nsave==2, aligned pair -> pushl (2 bytes vs dec + ldm = 6)
	 * The pair case is gated to rr6/rr8/rr10 (firstsave even, <= R10); rr12
	 * would include r13 and only arises on the frame-pointer path anyway.
	 * Otherwise allocate the frame with dec/sub, then ldm the run at the SP.
	 */
	if (fsize == 0 && nsave == 1) {
		printf("\tpush\t(rr14),r%d\n", firstsave);
	} else if (fsize == 0 && nsave == 2 &&
	    (firstsave & 1) == 0 && firstsave <= R10) {
		printf("\tpushl\t(rr14),rr%d\n", firstsave);
	} else {
		if (total > 0)
			printf("\t%s\tr15,$%d\n", total <= 16 ? "dec" : "sub",
			    total);
		if (nsave == 1)
			printf("\tld\t(rr14),r%d\n", firstsave);
		else
			printf("\tldm\t(rr14),r%d,$%d\n", firstsave, nsave);
	}

	/* r13 = current SP = frame bottom (only when it is the frame pointer). */
	if (curneedfp)
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

	/* Frameless (see prologue()): nothing to tear down but the return. */
	if (curframeless) {
		printf("\tret\tun\n");
		return;
	}

	/*
	 * Recompute the plan.  firstsave/fsize are deterministic from p2env, and
	 * cursavetop was stashed by prologue() (eoftn cannot re-run usesfp - it
	 * only sees the epilog end of the interpass list).
	 */
	firstsave = firstsavereg();
	fsize = (p2maxautooff + 1) & ~1;
	nsave = cursavetop - firstsave + 1;
	total = fsize + nsave * 2;

	/*
	 * Mirror of the prologue allocate-and-save combine: pop / popl restore the
	 * register(s) AND reclaim the frame in one instruction.
	 */
	if (fsize == 0 && nsave == 1) {
		printf("\tpop\tr%d,(rr14)\n", firstsave);
		printf("\tret\tun\n");
		return;
	}
	if (fsize == 0 && nsave == 2 && (firstsave & 1) == 0 &&
	    firstsave <= R10) {
		printf("\tpopl\trr%d,(rr14)\n", firstsave);
		printf("\tret\tun\n");
		return;
	}

	/* Restore the saved run (neither ld nor ldm changes r15) */
	if (nsave == 1)
		printf("\tld\tr%d,(rr14)\n", firstsave);
	else
		printf("\tldm\tr%d,(rr14),$%d\n", firstsave, nsave);

	/* Reclaim the whole frame */
	if (total > 0)
		printf("\t%s\tr15,$%d\n", total <= 16 ? "inc" : "add", total);

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
 * bwput: print the WORD register containing a class-D byte-register
 * operand, for the word instructions that implement char conversions
 * and arithmetic (extsb/and/neg/push/ld work on any word register and
 * the char value lives in its low byte).
 */
static void
bwput(NODE *p)
{
	if (p->n_op != REG || p->n_rval < RL0)
		comperr("bwput: not a byte register (op %d)", p->n_op);
	printf("%s", rnames[dword(p->n_rval)]);
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
 * Cost, in bytes, of loading a single 16-bit constant word: clr and ldk
 * are 2 bytes, a full "ld rN,#imm16" is 4.  Used by the Z0 escape to decide
 * whether splitting a long constant beats the 6-byte "ldl rrN,#imm32".
 */
static int
wordloadcost(CONSZ w)
{
	return (w == 0 || (w >= 1 && w <= 15)) ? 2 : 4;
}

/*
 * Emit the cheapest single-word load of constant w into half "lo" of the
 * pair operand p: clr (zero), ldk (1..15), or ld (anything else).
 */
static void
prwordload(NODE *p, int lo, CONSZ w)
{
	if (w == 0) {
		printf("\tclr\t");
		prword(p, lo);
	} else if (w >= 1 && w <= 15) {
		printf("\tldk\t");
		prword(p, lo);
		printf(",$" CONFMT, w);
	} else {
		printf("\tld\t");
		prword(p, lo);
		printf(",$" CONFMT, w);
	}
	printf("\n");
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
 *   ZG  word register containing the class-D (byte) LEFT operand
 *   ZH  word register containing the class-D (byte) result A1
 *   ZK  byte -> word conversion move: "ld A1,<word of left>", omitted
 *       when A1 already is that word (NSL sharing)
 *   ZU  uchar zero-extend of A1's low byte in place: "subb rhN,rhN"
 *       for r0-r7, "and A1,$0xff" for the high-byte-less r8-r15
 *   ZI  word -> byte conversion move: "ld <word of A1>,AL", omitted
 *       when AL already is A1's word (NSL sharing)
 *   ZS  struct assignment: ldirb block copy
 *   ZT  struct argument: allocate stack slot + ldirb block copy
 *   ZD  double assignment: quad reg <-> quad reg/memory
 *   ZE  double load: memory/quad reg -> result quad A1
 *   ZP  double argument push: two pushl (low pair first)
 *   ZW  high (sign+exponent) word of the left operand's quad/pair
 *   ZO  the compare just emitted is a sign-Only flag setter (test/testl:
 *       S and Z valid, P/V left as parity/stale): the LT/GE branch that
 *       cbgen emits next must read S alone, i.e. jr mi/pl
 *   ZV  condition-code name of this relop, non-negated, for the
 *       value-context "tcc cc,A1" (the truth value itself is wanted)
 *   ZY  bit number of the single CLEAR bit in the right ICON (an
 *       SNPOW2 shape), for res: "x &= ~0x40" prints as "$6"
 *   ZX  address constant + word index: "lda A1,sym(AR)" when the
 *       index register is not r0 and the address is named, else the
 *       "ldl A1,$sym ; add <low word of A1>,AR" fallback
 */

/* set by ZO, consumed by the cbgen call that follows the compare */
static int signonlycc;

/* condition-code names, indexed by relop - EQ (used by cbgen and ZV) */
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
zzzcode(NODE *p, int c)
{
	NODE *l;
	int n;
	char *op;

	switch (c) {
	case 'G':	/* word register containing the byte left operand */
		bwput(getlr(p, 'L'));
		break;
	case 'H':	/* word register containing the byte result A1 */
		bwput(getlr(p, '1'));
		break;

	case 'K':	/* byte -> word: copy the byte's containing word
			 * into the class-A result A1, whose low byte the
			 * following extsb/and then extends in place.  With
			 * NSL sharing A1 often IS that word: emit nothing. */
		l = getlr(p, 'L');
		if (l->n_op != REG || l->n_rval < RL0)
			comperr("ZK: left not a byte register");
		n = getlr(p, '1')->n_rval;
		if (n != dword(l->n_rval))
			printf("\tld\t%s,%s\n",
			    rnames[n], rnames[dword(l->n_rval)]);
		break;

	case 'U':	/* zero-extend the low byte of the class-A result A1
			 * in place (ZK put the uchar's word there): high-byte
			 * self-subtract when the word has an addressable high
			 * byte (r0-r7; the 2-byte native idiom), else the
			 * equivalent 4-byte word and. */
		n = getlr(p, '1')->n_rval;
		if (n < 0 || n > 15)
			comperr("ZU: result not a word register");
		if (n <= 7)
			printf("\tsubb\trh%d,rh%d\n", n, n);
		else
			printf("\tand\t%s,$0xff\n", rnames[n]);
		break;

	case 'A':	/* block memory clear via overlapping ldirb.  AL is the
			 * buffer's first byte (frame OREG); the node's n_lval is
			 * the byte count.  Clear byte 0, then copy it forward:
			 * ldirb propagates the zero through the whole block.
			 * The node result pair is the dst (used and discarded -
			 * DECRA packs only 3 regs, so the result slot doubles as
			 * a scratch); A2 = src pair, A1 = byte count. */
	    {
		int dst = getlr(p, 'D')->n_rval;	/* result pair, used as dst */
		int src = getlr(p, '2')->n_rval;	/* B scratch pair (src) */
		int cnt = getlr(p, '1')->n_rval;	/* A count register */

		printf("\tlda\t%s,", rnames[dst]);	/* dst = &buf[0] */
		expand(p, FOREFF, "AL");
		printf("\n\tand\t");
		prword(getlr(p, 'D'), 0);		/* normalise segment word */
		printf(",$32512\n");
		printf("\tclrb\t(%s)\n", rnames[dst]);	/* buf[0] = 0 */
		printf("\tldl\t%s,%s\n", rnames[src], rnames[dst]); /* src = &buf[0] */
		printf("\tinc\t");
		prword(getlr(p, 'D'), 1);		/* dst = &buf[1] */
		printf(",$1\n");
		printf("\tld\t%s,$%d\n", rnames[cnt], p->n_rval - 1);
		printf("\tldirb\t(%s),(%s),%s\n",
		    rnames[dst], rnames[src], rnames[cnt]);
	    }
		break;

	case 'Z':	/* sparse-switch cpir dispatch.  Search the .word
			 * case-value table (label d->ltab) for the switch
			 * value AL; on no match branch to the default; else
			 * load the matched case's 16-bit TARGET OFFSET from the
			 * parallel .word offset table into the search pair's LOW
			 * word, leaving its high (segment) word - which cpir did
			 * not touch - pointing at this (the code) segment; the
			 * outer GOTO(SWDISP) then jumps through the pair.  All
			 * case bodies share the dispatch's segment, so a 16-bit
			 * offset suffices (half the size of a .long address).
			 * A2 = search pair, A1 = count.  Displacement 2N-2:
			 * after cpir the low word is 2*(idx+1) past the table
			 * base; the .word target table starts 2N bytes in, so
			 * target idx sits at base + 2N + 2*idx =
			 * (base + 2N-2) + 2*(idx+1). */
	    {
		struct swdesc *d = (struct swdesc *)p->n_name;
		int cnt = getlr(p, '1')->n_rval;	/* A1 = A count word */
		int pair = getlr(p, '2')->n_rval;	/* A2 = B search pair */
		int lo = (pair - RR0) * 2 + 1;		/* pair's low word */

		printf("\tld\t%s,$%d\n", rnames[cnt], d->n);
		printf("\tldl\t%s,$" LABFMT "\n", rnames[pair], d->ltab);
		printf("\tcpir\t");
		expand(p, FOREFF, "AL");
		printf(",(%s),%s,eq\n", rnames[pair], rnames[cnt]);
		printf("\tjr\tne," LABFMT "\n", d->deflab);
		printf("\tsub\t%s,$" LABFMT "\n", rnames[lo], d->ltab);
		printf("\tld\t%s," LABFMT "+%d(%s)\n",
		    rnames[lo], d->ltab, 2 * d->n - 2, rnames[lo]);
	    }
		break;

	case 'O':	/* the test/testl this template printed sets S and Z
			 * but leaves P/V alone, so the signed conditions
			 * lt/ge (S xor V) would read a stale V: make the
			 * following cbgen branch on the sign flag alone. */
		signonlycc = 1;
		break;

	case 'V':	/* value-context relational: the cc name of this
			 * OPLOG itself, non-negated (the compare is already
			 * printed; tcc sets bit 0 of A1 when cc holds). */
		if (p->n_op < EQ || p->n_op > UGT)
			comperr("ZV: op %d not a relop", p->n_op);
		printf("%s", ccnames[p->n_op - EQ]);
		break;

	case 'J':	/* bit number of the single-bit mask in the right
			 * ICON (an SPOW2 shape), for the bit/bitb test
			 * rules and set: "x & 0x40" prints as "$6". */
		{
			CONSZ v = getlval(p->n_right);

			if (p->n_right->n_op != ICON)
				comperr("ZJ: right not ICON");
			v &= (p->n_type == CHAR || p->n_type == UCHAR) ?
			    0xff : 0xffff;
			if (v == 0 || (v & (v - 1)) != 0)
				comperr("ZJ: not a single-bit mask");
			for (n = 0; (v & 1) == 0; v >>= 1)
				n++;
			printf("$%d", n);
		}
		break;

	case 'Y':	/* bit number of the single CLEAR bit in the right
			 * ICON (an SNPOW2 shape), for res:
			 * "x &= ~0x40" prints as "$6". */
		{
			CONSZ v = getlval(p->n_right);

			if (p->n_right->n_op != ICON)
				comperr("ZY: right not ICON");
			v = ~v & ((p->n_type == CHAR || p->n_type == UCHAR) ?
			    0xff : 0xffff);
			if (v == 0 || (v & (v - 1)) != 0)
				comperr("ZY: not a single-clear-bit mask");
			for (n = 0; (v & 1) == 0; v >>= 1)
				n++;
			printf("$%d", n);
		}
		break;

	case 'X':	/* address constant + word index: lda A1,sym(AR),
			 * unless the index sits in r0 (an X-mode index
			 * field of 0 decodes as DA) or the address is a
			 * nameless constant - those get the ldl+add
			 * fallback.  A1 never overlaps AR (plain NBREG,
			 * no sharing), so the fallback's ldl cannot
			 * clobber the index before the add reads it. */
	    {
		NODE *r = getlr(p, 'R');

		l = getlr(p, 'L');
		n = getlr(p, '1')->n_rval;
		if (r->n_op != REG || l->n_op != ICON)
			comperr("ZX: bad operands");
		if (r->n_rval != 0 && l->n_name[0] != '\0') {
			printf("\tlda\t%s,%s", rnames[n], l->n_name);
			if (getlval(l) != 0)
				printf("+" CONFMT, getlval(l));
			printf("(%s)\n", rnames[r->n_rval]);
		} else {
			printf("\tldl\t%s,$", rnames[n]);
			conput(stdout, l);
			printf("\n\tadd\t%s,%s\n",
			    rnames[(n - RR0) * 2 + 1], rnames[r->n_rval]);
		}
		/*
		 * Normalise the segment (high) word.  lda leaves the reserved
		 * high bit of the segment byte set; a raw &arr[i] pointer must
		 * have it clear so that pointer equality works (e.g. comparing
		 * &arr[i] against a differently-formed pointer to the same
		 * cell).  Mask with $0x7F00 exactly as &local (ZF) and the
		 * lda-of-name rule (ZM) do.
		 */
		printf("\tand\t");
		prword(getlr(p, '1'), 0);
		printf(",$32512\n");
	    }
		break;

	case 'I':	/* word -> byte: copy the word into the byte result
			 * A1's containing word; A1 (its low byte) then holds
			 * the truncated char.  The word's high byte is dead
			 * space - a live class-D value in rlN conflicts with
			 * any class-A value in rN via ROVERLAP.  With NSL
			 * sharing the words often coincide: emit nothing. */
		l = getlr(p, 'L');
		if (l->n_op != REG || l->n_rval >= RL0)
			comperr("ZI: left not a word register");
		n = getlr(p, '1')->n_rval;
		if (dword(n) != l->n_rval)
			printf("\tld\t%s,%s\n",
			    rnames[dword(n)], rnames[l->n_rval]);
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
		int sz = ap->iarg(0);

		l = p->n_left;

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
		NODE *r = p->n_right;

		l = p->n_left;
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
		int q = getlr(p, '1')->n_rval;

		l = getlr(p, 'L');
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
		l = getlr(p, 'L');
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
		break;

	case 'W':	/* high (sign+exponent) word of the left operand's
			 * register, for the sign-flip UMINUS "xor ,$-32768"
			 * (native negates doubles this way: modf.s
			 * "xor r0,$-32768") */
		l = getlr(p, 'L');
		if (l->n_op != REG)
			comperr("ZW: not a register");
		if (l->n_rval >= RQ0)
			printf("r%d", qword(l->n_rval));
		else
			prword(l, 0);
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

	case '0':	/* materialize a numeric long/ptr constant (SLCON) into
			 * a pair register.  Split into per-word clr/ldk/ld when
			 * that is no larger than the 6-byte "ldl rrN,#imm32",
			 * else emit the plain ldl.  The destination is the ASSIGN
			 * left (RDEST) or the OPLTYPE result (RESC1); the constant
			 * is the other operand. */
	    {
		NODE *dst, *con;
		CONSZ v, hi, lo;

		if (p->n_op == ASSIGN) {
			dst = getlr(p, 'L');
			con = getlr(p, 'R');
		} else {
			dst = getlr(p, '1');
			con = getlr(p, 'L');
		}
		v = getlval(con);
		hi = (v >> 16) & 0xffffLL;
		lo = v & 0xffffLL;
		if (v == 0) {
			/* whole pair zero: 2-byte subl, cf. the ASSIGN
			 * SBREG<-SZERO rule (OPLTYPE has no zero rule). */
			printf("\tsubl\t%s,%s\n",
			    rnames[dst->n_rval], rnames[dst->n_rval]);
		} else if (wordloadcost(hi) + wordloadcost(lo) >= 6) {
			/* splitting is no smaller than one ldl #imm32: emit the
			 * plain ldl, printing the immediate exactly as the
			 * generic rule's "AR"/"AL" would (adrput). */
			printf("\tldl\t%s,", rnames[dst->n_rval]);
			adrput(stdout, con);
			printf("\n");
		} else {
			prwordload(dst, 0, hi);		/* high word */
			prwordload(dst, 1, lo);		/* low word */
		}
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
 * cbfuse: fuse a decrement-and-test loop branch into a single djnz.
 *
 * After fusecmp()/rmwrename() a "while (--n)" countdown reads, at emit
 * time, as
 *	CBRANCH(NE(ASSIGN(REG n, PLUS(REG n, -1)), ICON 0), lab)
 * which the normal path emits as "dec n,$1 ; jr ne,lab".  The Z8000 djnz
 * does exactly that in one word - decrement a word register and jump while
 * the result is nonzero - so emit "djnz n,lab" instead, saving the word.
 *
 * Returns 0 (keep the default dec;jr) unless every djnz precondition holds:
 *   - branch sense NE: djnz jumps while the counter is nonzero;
 *   - counter in a WORD register: djnz is a 16-bit decrement, so byte
 *     counters (dbjnz, not handled here), pointer/long pairs and memory
 *     counters are excluded;
 *   - step exactly -1, on that same register;
 *   - target BACKWARD (already emitted this function).  djnz cannot branch
 *     forward, and letting the assembler relax a forward one to "dec;jp"
 *     would be larger than the "dec;jr" it replaces.
 *
 * Called from emit()'s CBRANCH path (via TARGET_CBRANCH_FUSE) before the
 * compare/branch are generated; returns 1 once it has emitted the branch.
 */
int
cbfuse(NODE *p)
{
	NODE *rel, *asg, *mod, *dst;

	rel = p->n_left;
	if (rel->n_op != NE)
		return 0;
	/*
	 * Only the elided-compare shape, where the compare itself produced
	 * no instruction and the RMW child's flags ARE the branch result
	 * (the same su==0 discriminator emit() uses to pick the child rule).
	 * Otherwise a separate compare instruction is in play and djnz would
	 * drop it.
	 */
	if (rel->n_su != 0)
		return 0;
	asg = rel->n_left;
	if (asg->n_op != ASSIGN)
		return 0;
	dst = asg->n_left;		/* the counter (template AL) */
	mod = asg->n_right;		/* the modifying expression */
	if (dst->n_op != REG)
		return 0;
	if (dst->n_type != INT && dst->n_type != UNSIGNED &&
	    dst->n_type != SHORT && dst->n_type != USHORT)
		return 0;
	/*
	 * step must be a decrement by exactly 1 on the same register:
	 * MINUS(r,1) or PLUS(r,-1) - both select the "dec r,$1" rule.
	 */
	if (mod->n_left->n_op != REG || regno(mod->n_left) != regno(dst))
		return 0;
	if (mod->n_right->n_op != ICON || mod->n_right->n_name[0] != '\0')
		return 0;
	if (!((mod->n_op == MINUS && getlval(mod->n_right) == 1) ||
	    (mod->n_op == PLUS && getlval(mod->n_right) == -1)))
		return 0;
	/* djnz is backward-only; a forward target is never a win */
	if (!labseen((int)getlval(p->n_right)))
		return 0;

	printf("\tdjnz\t%s," LABFMT "\n", rnames[regno(dst)],
	    (int)getlval(p->n_right));
	return 1;
}

/*
 * cbgen: emit a conditional branch.
 */
void
cbgen(int o, int lab)
{
	char *cc;

	if (o < EQ || o > UGT)
		comperr("cbgen: bad op %d", o);
	cc = ccnames[o - EQ];
	if (signonlycc) {
		/* the compare was a test/testl (ZO): S is valid but V is
		 * not, so LT/GE must branch on the sign flag alone */
		signonlycc = 0;
		if (o == LT)
			cc = "mi";
		else if (o == GE)
			cc = "pl";
		else
			comperr("cbgen: sign-only cc for op %d", o);
	}
	printf("\tjr\t%s," LABFMT "\n", cc, lab);
}

/*
 * rmove: emit a register-to-register move.
 */
void
rmove(int s, int d, TWORD t)
{
	if (s == d)
		return;
	if (s >= RL0 || d >= RL0) {
		/* byte (class D) move; both sides are byte registers */
		if (s < RL0 || d < RL0)
			comperr("rmove: mixed byte/word %d -> %d", s, d);
		printf("\tldb\t%s,%s\n", rnames[d], rnames[s]);
	} else if (szty(t) == 4) {
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
 * pairs.  Class D holds the 8 byte registers rl0-rl7, each overlapping
 * one word (and through it one pair / one quad).  Worst-case
 * (conservative) blocking counts.
 */
int
COLORMAP(int c, int *r)
{
	int num;

	switch (c) {
	case CLASSA:
		/* a pair blocks 2 words, a quad blocks 4, a byte 1 */
		num = r[CLASSA] + 2 * r[CLASSB] + 4 * r[CLASSC] + r[CLASSD];
		return num < 13;
	case CLASSB:
		/* 5 allocatable pairs (rr2..rr10; rr0 reserved); a word,
		 * pair or byte neighbour blocks 1 pair, a quad blocks 2 */
		num = r[CLASSB] + r[CLASSA] + 2 * r[CLASSC] + r[CLASSD];
		return num < 5;
	case CLASSC:
		/* any neighbour blocks at most 1 of the 3 quads */
		num = r[CLASSA] + r[CLASSB] + r[CLASSC] + r[CLASSD];
		return num < 3;
	case CLASSD:
		/* a word neighbour blocks (at most) its own byte register,
		 * a pair blocks 2 bytes, a quad blocks 4 */
		num = r[CLASSD] + r[CLASSA] + 2 * r[CLASSB] + 4 * r[CLASSC];
		return num < 8;
	}
	return 0;
}

/*
 * pickcolor: the PICKCOLOR hook consulted by AssignColors' fallback
 * (regs.c colfind) when no move-related recommendation exists.
 *
 * Caller-saved registers come first in their usual lowest-first order,
 * so allocations that fit in scratch registers are unchanged.  The
 * callee-saved registers are preferred TOP-DOWN (r12 before r6, rr10
 * before rr8 before rr6, rl7 before rl6): the prologue saves one
 * CONTIGUOUS block from the lowest used callee register through r13
 * (ldm), so its cost in stack words and cycles is set by that lowest
 * register alone.  Native cc shows the same bias (common prologue is
 * "ldm r8,$6", not "ldm r6,$8").
 *
 * The tables list COLOR indices (positions in the mkext-generated rmap
 * order), not register numbers: class A colors 0-12 are r0-r12, class
 * B colors 0-5 are rr0,rr2,rr4,rr6,rr8,rr10 (rr0 is cleared from
 * clregs and never appears in the mask), class C colors 0-2 are
 * rq0,rq4,rq8, class D colors 0-7 are rl0-rl7.
 */
int
pickcolor(int class, int mask)
{
	static const signed char aorder[] =
	    { 0, 1, 2, 3, 4, 5, 12, 11, 10, 9, 8, 7, 6, -1 };
	static const signed char border[] =	/* rr2 rr4 rr10 rr8 rr6 rr0 */
	    { 1, 2, 5, 4, 3, 0, -1 };
	static const signed char corder[] =	/* rq0 rq8 rq4(r6,r7) */
	    { 0, 2, 1, -1 };
	static const signed char dorder[] =	/* rl0-rl5, rl7 before rl6 */
	    { 0, 1, 2, 3, 4, 5, 7, 6, -1 };
	const signed char *o;
	int i;

	switch (class) {
	case CLASSA: o = aorder; break;
	case CLASSB: o = border; break;
	case CLASSC: o = corder; break;
	default:     o = dorder; break;
	}
	for (i = 0; o[i] >= 0; i++)
		if (mask & (1 << o[i]))
			return o[i];
	comperr("pickcolor: empty mask class %d", class);
	return 0;
}

/*
 * Return the register class suitable for a value of type t.
 * Consistent with PCLASS in macdefs.h: char uses class D (byte
 * registers), 64-bit values (double) class C (quads), 32-bit values
 * (long/ptr/float) class B (pairs), everything else class A (words).
 */
int
gclass(TWORD t)
{
	if (t == CHAR || t == UCHAR)
		return CLASSD;
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
		if (p->n_op == UMUL) {
			/*
			 * A dereference whose address is a bare pair
			 * register/temp will fold to a ZERO-displacement
			 * OREG (IR mode, "(rrN)") at emit time: offstar
			 * puts the address in a pair and gencode's canon
			 * turns UMUL(REG) into the OREG.  IR is legal in
			 * every SNBA consumer, so accept it as SROREG.
			 * PLUS/MINUS(base,con) addresses must NOT be
			 * accepted: they fold to a displaced pair base =
			 * BA mode, which these instructions cannot encode.
			 */
			NODE *q = p->n_left;
			if (q->n_op == TEMP && szty(q->n_type) == 2)
				return SROREG;
			if (q->n_op == REG && szty(q->n_type) == 2 &&
			    q->n_rval != FPREG)
				return SROREG;
			return SRNOPE;
		}
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
	case SLDK:
		if (p->n_op == ICON && p->n_name[0] == '\0' &&
		    getlval(p) >= 0 && getlval(p) <= 15)
			return SRDIR;
		return SRNOPE;
	case SP16:
		if (p->n_op == ICON && p->n_name[0] == '\0' &&
		    getlval(p) >= 1 && getlval(p) <= 16)
			return SRDIR;
		return SRNOPE;
	case SPCON:
		if (p->n_op == ICON && p->n_name[0] == '\0' &&
		    getlval(p) >= -32768 && getlval(p) <= 65535)
			return SRDIR;
		return SRNOPE;
	case SLCON:
		/* any numeric (non-symbolic) constant: the Z0 escape decides
		 * per-value whether the per-word split beats a plain ldl. */
		if (p->n_op == ICON && p->n_name[0] == '\0')
			return SRDIR;
		return SRNOPE;
	case SPOW2: {
		/*
		 * A nameless ICON that is a single-bit mask within its
		 * type's width, in either sign representation (bit 15 of
		 * a word may arrive as 32768 or -32768).  The ZJ escape
		 * prints it as the bit number for bit/bitb.
		 */
		CONSZ v = getlval(p), vv;
		int w;

		if (p->n_op != ICON || p->n_name[0] != '\0')
			return SRNOPE;
		w = (p->n_type == CHAR || p->n_type == UCHAR) ? 8 : 16;
		vv = v & ((((CONSZ)1) << w) - 1);
		if (vv == 0 || (vv & (vv - 1)) != 0)
			return SRNOPE;
		if (v != vv && v != vv - (((CONSZ)1) << w))
			return SRNOPE;
		return SRDIR;
	}
	case SNPOW2: {
		/*
		 * The complement of SPOW2: a nameless ICON with every bit
		 * of its type's width set except one ("x &= ~mask"; the
		 * res operand).  Same two sign representations: ~8 on a
		 * word arrives as -9 or 65527.  ZY prints the clear
		 * bit's number.
		 */
		CONSZ v = getlval(p), vv, m;
		int w;

		if (p->n_op != ICON || p->n_name[0] != '\0')
			return SRNOPE;
		w = (p->n_type == CHAR || p->n_type == UCHAR) ? 8 : 16;
		m = (((CONSZ)1) << w) - 1;
		vv = ~v & m;	/* the single bit that is CLEAR in v */
		if (vv == 0 || (vv & (vv - 1)) != 0)
			return SRNOPE;
		if (v != (v & m) && v != (v & m) - (m + 1))
			return SRNOPE;
		return SRDIR;
	}
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

/*
 * Fuse an assignment with the compare of the value it just stored:
 *
 *	ASSIGN(TEMP t, expr) ; CBRANCH(relop(TEMP t, 0))
 *
 * adjacent in the interpass list becomes
 *
 *	CBRANCH(relop(ASSIGN(TEMP t, expr), 0))
 *
 * An ASSIGN yields its stored value, so this is exactly the tree pass 1
 * builds for "if ((t = expr))" - a shape the whole pipeline already
 * handles.  When expr is a read-modify-write of t, the compare-vs-zero
 * elision in geninsn then branches on the operation's own flags
 * ("dec r5,$1 ; jr ne" instead of dec + test + jr, gated per-op by
 * CCOKFORCOMP); otherwise pass 2 generates exactly the unfused code.
 * Integer and pointer temps only: float compares are rewritten to
 * fcomp helper calls and must keep their canonical shape.
 *
 * Runs from myoptim, i.e. AFTER deljumps/SSA/DCE and just before
 * register allocation: SSA splits exactly this kind of tree back into
 * the two-statement form (pass1's own "if ((t = expr))" trees
 * included), so fusing any earlier is undone at -O1.
 *
 * The basic blocks built during optimize() are REUSED by the register
 * allocator's liveness analysis (Build/LivenessAnalysis walk each
 * block from bb->last back to bb->first in the circular interpass
 * list) - removing an interpass that a bb->first points at would make
 * that walk miss its terminator and loop forever (ar.c update(): the
 * fused ASSIGN was the first statement of the for-body block).  Patch
 * any block boundary that names the removed element.
 */
static void
fusecmp(struct interpass *ipole)
{
	struct interpass *ip, *inext;
	struct basicblock *bb;
	NODE *p, *q;

	for (ip = DLIST_NEXT(ipole, qelem); ip != ipole; ip = inext) {
		inext = DLIST_NEXT(ip, qelem);
		if (ip->type != IP_NODE || inext == ipole ||
		    inext->type != IP_NODE)
			continue;
		p = ip->ip_node;
		if (p->n_op != ASSIGN || p->n_left->n_op != TEMP)
			continue;
		if (!KEEPLOGOPVALUE_T(p->n_left->n_type))
			continue;
		q = inext->ip_node;
		if (q->n_op != CBRANCH)
			continue;
		q = q->n_left;
		if (q->n_op < EQ || q->n_op > UGT)
			continue;
		if (q->n_left->n_op != TEMP ||
		    regno(q->n_left) != regno(p->n_left))
			continue;
		if (q->n_right->n_op != ICON || getlval(q->n_right) != 0 ||
		    q->n_right->n_name[0] != '\0')
			continue;
		nfree(q->n_left);
		q->n_left = p;
		if (xtemps || xssa) {	/* blocks exist iff optimize built
					 * them - same condition it uses */
			DLIST_FOREACH(bb, &p2env.bblocks, bbelem) {
				if (bb->first == ip)
					bb->first = inext;
				if (bb->last == ip)
					bb->last = DLIST_PREV(ip, qelem);
			}
		}
		DLIST_REMOVE(ip, qelem);
	}
}

/*
 * Count definitions and uses of TEMP number num in a tree.  A TEMP
 * that is the direct target of an ASSIGN is a definition; every
 * other occurrence is a use.
 */
static void
tmpcount(NODE *p, int num, int *defs, int *uses)
{
	if (p->n_op == ASSIGN && p->n_left->n_op == TEMP) {
		if (regno(p->n_left) == num)
			(*defs)++;
		tmpcount(p->n_right, num, defs, uses);
		return;
	}
	switch (optype(p->n_op)) {
	case BITYPE:
		tmpcount(p->n_right, num, defs, uses);
		/* FALLTHROUGH */
	case UTYPE:
		tmpcount(p->n_left, num, defs, uses);
		return;
	default:
		if (p->n_op == TEMP && regno(p) == num)
			(*uses)++;
	}
}

/*
 * Recover the -O0 read-modify-write shape at -O1.
 *
 * SSA renames the two halves of pass 1's fused countdown tree, so
 * after removephi a "while (--n)" loop reads
 *
 *	ASSIGN(TEMP s, TEMP x)			entry copy
 *   L:	CBRANCH(rel(ASSIGN(TEMP d, op(TEMP s, e)), 0))
 *	... body uses TEMP d ...
 *	ASSIGN(TEMP s, TEMP d)			back-edge copy
 *	GOTO L
 *
 * and findmops' treecmp(d, s) can never match, so the compare-vs-zero
 * elision that works at -O0 ("dec r5,$1 ; jr ne") is lost; the
 * register allocator does coalesce d and s into one register, but by
 * then geninsn has already emitted the separate test.
 *
 * When the whole-function interpass list proves this exact structure
 * - d defined only by the RMW, s used only by the RMW, and s defined
 * by exactly two plain top-level temp-to-temp copies, one before the
 * RMW (from neither d nor s) and one after it reading d - renaming s
 * to d is a semantics-preserving coalesce: the entry copy then loads
 * d, the back-edge copy becomes a self-copy and is deleted, and the
 * RMW reads and writes one temp, so the elision fires again.  The
 * two-copy requirement is what makes the rename sound: it pins the
 * removephi phi-lowering shape where every path back to the RMW
 * passes one of the (consistently renamed) copies, and rejects
 * aliasing shapes like "while (n = m - 1)" where m stays live.
 * Gated on xssa: only SSA produces the split-temp shape, and the
 * soundness argument leans on removephi's every-edge-gets-a-copy
 * invariant.  Runs after fusecmp, which builds the fused tree for
 * the pairs SSA split completely apart.
 *
 * The same basic-block boundary rule as fusecmp applies to the
 * deleted copy: the register allocator reuses optimize()'s blocks.
 */
static void
rmwrename(struct interpass *ipole)
{
	struct interpass *ip, *ip2, *entrycp, *backcp;
	struct basicblock *bb;
	NODE *p, *q, *rmw, *r;
	int d, s, seen, bad, ddefs, duses, sdefs, suses, du, dd;

	if (!xssa)
		return;
	for (ip = DLIST_NEXT(ipole, qelem); ip != ipole;
	    ip = DLIST_NEXT(ip, qelem)) {
		if (ip->type != IP_NODE)
			continue;
		p = ip->ip_node;
		if (p->n_op != CBRANCH)
			continue;
		q = p->n_left;
		if (q->n_op < EQ || q->n_op > UGT)
			continue;
		rmw = q->n_left;
		if (rmw->n_op != ASSIGN || rmw->n_left->n_op != TEMP)
			continue;
		r = rmw->n_right;
		if (r->n_op != PLUS && r->n_op != MINUS && r->n_op != AND &&
		    r->n_op != OR && r->n_op != ER)
			continue;
		if (r->n_left->n_op != TEMP)
			continue;
		d = regno(rmw->n_left);
		s = regno(r->n_left);
		if (d == s || rmw->n_left->n_type != r->n_left->n_type)
			continue;
		/* the modifier expression may mention neither temp */
		dd = du = 0;
		tmpcount(r->n_right, d, &dd, &du);
		tmpcount(r->n_right, s, &dd, &du);
		if (dd || du)
			continue;

		ddefs = duses = sdefs = suses = 0;
		entrycp = backcp = NULL;
		seen = bad = 0;
		for (ip2 = DLIST_NEXT(ipole, qelem); ip2 != ipole;
		    ip2 = DLIST_NEXT(ip2, qelem)) {
			if (ip2->type != IP_NODE)
				continue;
			q = ip2->ip_node;
			if (ip2 == ip) {
				/* the candidate: 1 d-def + 1 s-use by
				 * shape; anything more counts below and
				 * fails the ddefs/suses/sdefs checks */
				seen = 1;
			} else if (q->n_op == ASSIGN &&
			    q->n_left->n_op == TEMP &&
			    regno(q->n_left) == s &&
			    q->n_right->n_op == TEMP) {
				if (seen == 0 && entrycp == NULL &&
				    regno(q->n_right) != d &&
				    regno(q->n_right) != s) {
					/* entry copy: 1 s-def, no other
					 * d/s references */
					entrycp = ip2;
					sdefs++;
					continue;
				}
				if (seen == 1 && backcp == NULL &&
				    regno(q->n_right) == d) {
					/* back-edge copy: 1 s-def, 1 d-use */
					backcp = ip2;
					sdefs++;
					duses++;
					continue;
				}
				bad = 1;	/* copy in the wrong place */
				break;
			}
			tmpcount(q, d, &ddefs, &duses);
			tmpcount(q, s, &sdefs, &suses);
		}
		if (bad || ddefs != 1 || suses != 1 || sdefs != 2 ||
		    entrycp == NULL || backcp == NULL)
			continue;

		/* rename s to d; the back-edge copy becomes dead */
		entrycp->ip_node->n_left->n_rval = d;
		r->n_left->n_rval = d;
		DLIST_FOREACH(bb, &p2env.bblocks, bbelem) {
			if (bb->first == backcp)
				bb->first = DLIST_NEXT(backcp, qelem);
			if (bb->last == backcp)
				bb->last = DLIST_PREV(backcp, qelem);
		}
		tfree(backcp->ip_node);
		DLIST_REMOVE(backcp, qelem);
	}
}

/*
 * Recover the read-modify-write shape for a NON-loop store-and-test.
 *
 * The loop case above needs removephi's two edge-copies for soundness.
 * A straight-line "if ((x -= y))" (or &=, |=, ^=, +=) leaves a simpler
 * residue: SSA numbers the stored and read halves apart but inserts NO
 * copies, because there is no control-flow merge feeding the read -
 *
 *	ASSIGN(TEMP s, expr)			single definition of s
 *	... (no other reference to s) ...
 *	CBRANCH(rel(ASSIGN(TEMP d, op(TEMP s, e)), 0))
 *	... body/afterwards uses TEMP d ...
 *
 * so findmops' treecmp(d, s) still fails and the compare is emitted as a
 * separate test.  Renaming s to d is sound here for a different reason
 * than the loop copies: in SSA a temp with a SINGLE definition (no phi,
 * hence sdefs==1 after removephi) has that definition dominating every
 * use, so the one s-def dominates the RMW; and because s is used ONLY by
 * the RMW (suses==1) nothing else observes it.  After the rename the s-def
 * writes d and the RMW reads/writes d in place, exactly the -O0 shape.
 * Nothing is deleted, so no basic-block boundary needs patching.
 *
 * Runs after rmwrename(); a site rmwrename() already collapsed now has
 * d==s and is skipped here by the d==s guard.  Gated on xssa: only SSA
 * splits the two halves apart, and the soundness rests on the SSA
 * single-def-dominates-use property.
 */
static void
rmwrenamesd(struct interpass *ipole)
{
	struct interpass *ip, *ip2, *sdef;
	NODE *p, *q, *rmw, *r;
	int d, s, seen, bad, ddefs, duses, sdefs, suses, du, dd;

	if (!xssa)
		return;
	for (ip = DLIST_NEXT(ipole, qelem); ip != ipole;
	    ip = DLIST_NEXT(ip, qelem)) {
		if (ip->type != IP_NODE)
			continue;
		p = ip->ip_node;
		if (p->n_op != CBRANCH)
			continue;
		q = p->n_left;
		/*
		 * EQ/NE only: those read the Z flag alone, which every one of
		 * the ops below sets to (result == 0).  An ordered relop would
		 * need S/V/C, and after the in-place op those differ from a
		 * "cp result,$0" - only harmlessly (signed overflow is UB) for
		 * signed, but genuinely wrong for unsigned wrap - so leave the
		 * separate compare in place for anything but EQ/NE.
		 */
		if (q->n_op != EQ && q->n_op != NE)
			continue;
		rmw = q->n_left;
		if (rmw->n_op != ASSIGN || rmw->n_left->n_op != TEMP)
			continue;
		r = rmw->n_right;
		if (r->n_op != PLUS && r->n_op != MINUS && r->n_op != AND &&
		    r->n_op != OR && r->n_op != ER)
			continue;
		if (r->n_left->n_op != TEMP)
			continue;
		d = regno(rmw->n_left);
		s = regno(r->n_left);
		if (d == s || rmw->n_left->n_type != r->n_left->n_type)
			continue;
		/* the modifier expression may mention neither temp */
		dd = du = 0;
		tmpcount(r->n_right, d, &dd, &du);
		tmpcount(r->n_right, s, &dd, &du);
		if (dd || du)
			continue;

		ddefs = duses = sdefs = suses = 0;
		sdef = NULL;
		seen = bad = 0;
		for (ip2 = DLIST_NEXT(ipole, qelem); ip2 != ipole;
		    ip2 = DLIST_NEXT(ip2, qelem)) {
			if (ip2->type != IP_NODE)
				continue;
			q = ip2->ip_node;
			if (ip2 == ip) {
				/* candidate: 1 d-def + 1 s-use by shape,
				 * counted through the fall-through below */
				seen = 1;
			} else if (q->n_op == ASSIGN &&
			    q->n_left->n_op == TEMP && regno(q->n_left) == s) {
				/* the definition of s: must be the only one,
				 * lie before the RMW, and source neither temp */
				if (seen != 0 || sdef != NULL) {
					bad = 1;
					break;
				}
				dd = du = 0;
				tmpcount(q->n_right, d, &dd, &du);
				tmpcount(q->n_right, s, &dd, &du);
				if (dd || du) {
					bad = 1;
					break;
				}
				sdef = ip2;
				sdefs++;
				continue;
			}
			tmpcount(q, d, &ddefs, &duses);
			tmpcount(q, s, &sdefs, &suses);
		}
		if (bad || ddefs != 1 || suses != 1 || sdefs != 1 ||
		    sdef == NULL)
			continue;

		/* rename s to d: the s-def now writes d, the RMW is in place */
		sdef->ip_node->n_left->n_rval = d;
		r->n_left->n_rval = d;
	}
}

/*
 * Recover the -O0 read-modify-write shape for a loop INDUCTION variable
 * whose value is LIVE across the body - the mirror of rmwrename().
 *
 * A "for (t = 0; t < N; t++) use(t)" loop, after SSA + removephi, reads
 *
 *	ASSIGN(TEMP s, init)			entry def of s
 *   L:	... body USES TEMP s (the compare, printf args, ...) ...
 *	ASSIGN(TEMP d, op(TEMP s, e))		the update, a bare statement
 *	ASSIGN(TEMP s, TEMP d)			back-edge copy (reads d)
 *	GOTO L
 *
 * Here s is read all over the body, so rmwrename()'s "s used only by the
 * RMW" (suses==1) never holds and the split shape survives; the register
 * allocator then fails to make the update in place and emits the classic
 * "ldl rr2,rr10 ; addl rr2,$1 ; ldl rr10,rr2".
 *
 * But d is single-use: defined only by the update and read only by the
 * immediately-following back-edge copy.  Renaming d to s - the OPPOSITE
 * direction from rmwrename() - makes the update write s in place and turns
 * the copy into the dead "s = s", which is deleted.  Soundness: d has
 * exactly one def (the update) and one use (the copy), so removing it
 * observes nothing else; and because the copy IMMEDIATELY follows the
 * update, no reader of the old s value lies between where s is now
 * overwritten and where the copy originally overwrote it.  Only a rename
 * and a delete, both safe on the allocator's reused blocks (see fusecmp).
 *
 * Gated on xssa; runs after rmwrename()/rmwrenamesd(), whose (compare-
 * wrapped) sites do not match the bare-statement shape required here.
 */
static void
rmwrenameloop(struct interpass *ipole)
{
	struct interpass *ip, *ip2, *backcp;
	struct basicblock *bb;
	NODE *p, *q, *r;
	int d, s, ddefs, duses, dd, du;

	if (!xssa)
		return;
	for (ip = DLIST_NEXT(ipole, qelem); ip != ipole;
	    ip = DLIST_NEXT(ip, qelem)) {
		if (ip->type != IP_NODE)
			continue;
		p = ip->ip_node;
		/* the update: a bare top-level "d = op(s, e)" statement */
		if (p->n_op != ASSIGN || p->n_left->n_op != TEMP)
			continue;
		r = p->n_right;
		if (r->n_op != PLUS && r->n_op != MINUS && r->n_op != AND &&
		    r->n_op != OR && r->n_op != ER)
			continue;
		if (r->n_left->n_op != TEMP)
			continue;
		d = regno(p->n_left);
		s = regno(r->n_left);
		if (d == s || p->n_left->n_type != r->n_left->n_type)
			continue;
		/* the modifier expression may mention neither temp */
		dd = du = 0;
		tmpcount(r->n_right, d, &dd, &du);
		tmpcount(r->n_right, s, &dd, &du);
		if (dd || du)
			continue;
		/* the LITERAL next element must be the back-edge copy "s = d":
		 * an intervening label would let control reach the copy without
		 * the update, and any statement between could read the old s. */
		backcp = DLIST_NEXT(ip, qelem);
		if (backcp == ipole || backcp->type != IP_NODE)
			continue;
		q = backcp->ip_node;
		if (q->n_op != ASSIGN || q->n_left->n_op != TEMP ||
		    regno(q->n_left) != s || q->n_right->n_op != TEMP ||
		    regno(q->n_right) != d)
			continue;
		/* d must be defined only by the update and used only by the
		 * back-edge copy: then eliminating it observes nothing else */
		ddefs = duses = 0;
		for (ip2 = DLIST_NEXT(ipole, qelem); ip2 != ipole;
		    ip2 = DLIST_NEXT(ip2, qelem)) {
			if (ip2->type != IP_NODE)
				continue;
			tmpcount(ip2->ip_node, d, &ddefs, &duses);
		}
		if (ddefs != 1 || duses != 1)
			continue;

		/* rename d to s: the update writes s in place, the back-edge
		 * copy becomes "s = s" and is removed */
		p->n_left->n_rval = s;
		DLIST_FOREACH(bb, &p2env.bblocks, bbelem) {
			if (bb->first == backcp)
				bb->first = DLIST_NEXT(backcp, qelem);
			if (bb->last == backcp)
				bb->last = DLIST_PREV(backcp, qelem);
		}
		tfree(backcp->ip_node);
		DLIST_REMOVE(backcp, qelem);
	}
}

/*
 * NOTE (attempted, reverted): a "rmwcopyfuse" that handled the LIVE-source
 * non-loop RMW-test (the majority of the corpus's residual redundant tests,
 * e.g. "if ((x = a op b))" with a used later) by INSERTING an explicit
 * copy "d = s" at myoptim and rewriting the op in place -
 *	ASSIGN(d, s) ; CBRANCH(rel(ASSIGN(d, op(d, e)), 0))
 * - was semantically correct but destabilised the -xssa register allocator:
 * inserting a fresh IP node here crashes insnwalk()'s interference build
 * (rmwrename/rmwrenamesd only rename or delete nodes, which is safe; adding
 * one is not).  A sound version needs the copy materialised where liveness
 * is rebuilt (or a post-regalloc peephole), not a mid-stream insert.  Left
 * for future work; the dead-source case is handled by rmwrenamesd() above.
 */

void
myoptim(struct interpass *ip)
{
	fusecmp(ip);
	rmwrename(ip);
	rmwrenamesd(ip);
	rmwrenameloop(ip);
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

/*
 * Rewrite the /SW... comment interpasses that mygenswitch() left around a
 * sparse switch into the cpir dispatch (see mygenswitch() in code.c).
 *
 * Runs from myreader() - before optimize() builds the CFG and before
 * register allocation - which is essential:
 *
 *  - the switch value TEMP still exists here and gains a real use (the
 *    SWDISP child), so it is not dead-eliminated;
 *  - the case + default labels are registered in epp->ip_labels.  The
 *    dispatch ends in GOTO(SWDISP(value)) - a computed goto - so cfg_build
 *    adds an edge from the dispatch to every label in ip_labels; that both
 *    makes the case bodies reachable (else DCE removes them) and is what
 *    inuse()/deljumps use to keep those labels alive;
 *  - the SWDISP node gets its NEEDS scratch pair + count from the allocator.
 *
 * The value/target tables are emitted as one opaque IP_ASM blob (the table
 * label is defined inside the text) so no collectable IP_DEFLAB is created
 * for a label that is only ever referenced textually.
 */
static void
swcpir(struct interpass *ipole)
{
	struct interpass *ip, *inext, *prev, *m, *end, *dip, *bip, *r, *rn;
	struct swdesc *d;
	NODE *val, *sw, *go;
	int num, n, deflab, ltab, i, k, on, last;
	unsigned type;
	int *vals, *labs, *ol, *nl, *tg;
	char *blob, *q;

	for (ip = DLIST_NEXT(ipole, qelem); ip != ipole; ip = inext) {
		inext = DLIST_NEXT(ip, qelem);
		if (ip->type != IP_ASM || strncmp(ip->ip_asm, "\t/SWH ", 6))
			continue;

		sscanf(ip->ip_asm, "%*s %d %u %d %d %d",
		    &num, &type, &n, &deflab, &ltab);
		vals = tmpalloc(n * sizeof(int));
		labs = tmpalloc(n * sizeof(int));
		prev = DLIST_PREV(ip, qelem);

		/* collect the /SWC case lines up to /SWE */
		i = 0;
		for (m = DLIST_NEXT(ip, qelem); m != ipole;
		    m = DLIST_NEXT(m, qelem)) {
			if (m->type == IP_ASM &&
			    strncmp(m->ip_asm, "\t/SWC ", 6) == 0) {
				if (i < n)
					sscanf(m->ip_asm, "%*s %d %d",
					    &vals[i], &labs[i]);
				i++;
				continue;
			}
			break;
		}
		end = m;			/* the /SWE interpass */
		inext = DLIST_NEXT(end, qelem);

		/* drop the markers (SWH .. SWE inclusive) */
		for (r = ip; ; r = rn) {
			rn = DLIST_NEXT(r, qelem);
			last = (r == end);
			DLIST_REMOVE(r, qelem);
			if (last)
				break;
		}

		/* GOTO(SWDISP(TEMP value)); SWDISP result is the target pair */
		d = tmpalloc(sizeof(struct swdesc));
		d->n = n;
		d->deflab = deflab;
		d->ltab = ltab;
		val = mklnode(TEMP, 0, num, (TWORD)type);
		sw = mkunode(SWDISP, val, 0, INCREF(VOID));
		sw->n_name = (char *)d;
		go = mkunode(GOTO, sw, 0, INT);
		/* This dispatch's own target list (case labels + default),
		 * null-terminated, on the GOTO node: cfg_build edges only to
		 * these, keeping the computed-goto CFG precise per switch. */
		tg = tmpalloc((n + 2) * sizeof(int));
		for (i = 0; i < n; i++)
			tg[i] = labs[i];
		tg[n] = deflab;
		tg[n + 1] = 0;
		go->n_name = (char *)tg;

		dip = tmpalloc(sizeof(struct interpass));
		dip->type = IP_NODE;
		dip->lineno = 0;
		dip->ip_node = go;
		DLIST_INSERT_AFTER(prev, dip, qelem);

		/* value/target tables as one opaque blob (label defined in it).
		 * Targets are 16-bit .word OFFSETS (all case bodies share this
		 * code segment), not .long addresses - half the size. */
		blob = tmpalloc(n * 32 + 32);
		q = blob;
		q += sprintf(q, LABFMT ":\n", ltab);
		for (k = 0; k < n; k++)
			q += sprintf(q, "\t.word\t%d\n", vals[k]);
		for (k = 0; k < n; k++)
			q += sprintf(q, "\t.word\t" LABFMT "\n", labs[k]);

		bip = tmpalloc(sizeof(struct interpass));
		bip->type = IP_ASM;
		bip->lineno = 0;
		bip->ip_asm = blob;
		DLIST_INSERT_AFTER(dip, bip, qelem);

		/* Also add them to the function's ip_labels.  cfg_build now
		 * takes this dispatch's edges from the GOTO's own list (above),
		 * so this is purely to mark the labels used-outside so deljumps'
		 * inuse() never deletes a case body reached only by the jp. */
		ol = p2env.epp->ip_labels;
		on = 0;
		if (ol)
			while (ol[on])
				on++;
		nl = tmpalloc((on + n + 2) * sizeof(int));
		for (k = 0; k < on; k++)
			nl[k] = ol[k];
		for (i = 0; i < n; i++)
			nl[on + i] = labs[i];
		nl[on + n] = deflab;
		nl[on + n + 1] = 0;
		p2env.epp->ip_labels = nl;
	}
}

/*
 * A single-byte zero store to a frame slot:
 *	ASSIGN(UMUL(MINUS(REG r13, ICON off)), ICON 0)   [char]
 * (pass1 endinit->clearbf->insbf emits one per byte of the ANSI zero-fill
 * tail of a partially-initialized auto aggregate).  Return 1 and the base
 * register + byte offset, else 0.
 */
static int
bytezero(NODE *p, int *base, CONSZ *off)
{
	NODE *l, *m;

	if (p->n_op != ASSIGN ||
	    (p->n_type != CHAR && p->n_type != UCHAR))
		return 0;
	if (p->n_right->n_op != ICON || getlval(p->n_right) != 0 ||
	    p->n_right->n_name[0] != '\0')
		return 0;
	l = p->n_left;
	if (l->n_op != UMUL)
		return 0;
	m = l->n_left;
	if (m->n_op != MINUS || m->n_left->n_op != REG ||
	    regno(m->n_left) != R13 ||
	    m->n_right->n_op != ICON || m->n_right->n_name[0] != '\0')
		return 0;
	*base = regno(m->n_left);
	*off = getlval(m->n_right);
	return 1;
}

/*
 * Compact the run of consecutive single-byte zero stores that pass1 emits for
 * an auto aggregate's zero-fill tail (one clrb each; login 123, tar 101).
 * The run is buf[0..len-1] at the SAME base register with offsets hi, hi-1,
 * ... (decreasing = increasing address; the first node is buf[0], the lowest
 * address / highest offset).
 *
 *  - len >= BCLR_THRESH: fold the whole run into one overlapping-ldirb block
 *    clear (BCLR): ~7 insns regardless of len (clear buf[0], propagate it
 *    forward).  Reuse the first node's address lvalue as the BCLR operand.
 *  - 2 <= len < BCLR_THRESH: merge each word-aligned byte pair into one word
 *    clear (r13 is even, so an even offset is a word-aligned frame address);
 *    the even-offset store is retyped to a word and its odd neighbour dropped.
 *
 * Runs from myreader(), before canon/regalloc.  BCLR reserves its scratch
 * pairs + count via NEEDS; the word clears need no scratch.
 *
 * Threshold: word-collapse costs ~ceil(len/2) instructions, BCLR a flat ~7,
 * so BCLR only wins once len exceeds ~14.
 */
#define	BCLR_THRESH	15

static void
clrfill(struct interpass *ipole)
{
	struct interpass *ip, *nx, *past, *d, *dn;
	NODE *p, *l;
	int base, nbase, len;
	CONSZ off, noff;

	ip = DLIST_NEXT(ipole, qelem);
	while (ip != ipole) {
		if (ip->type != IP_NODE || !bytezero(ip->ip_node, &base, &off)) {
			ip = DLIST_NEXT(ip, qelem);
			continue;
		}
		/* measure the run: consecutive same-base bytes, off = off-1... */
		len = 1;
		for (nx = DLIST_NEXT(ip, qelem);
		    nx != ipole && nx->type == IP_NODE &&
		    bytezero(nx->ip_node, &nbase, &noff) &&
		    nbase == base && noff == off - 1;
		    nx = DLIST_NEXT(nx, qelem)) {
			len++;
			off = noff;
		}
		past = nx;		/* first interpass past the run */

		if (len >= BCLR_THRESH) {
			/* fold into one overlapping-ldirb clear.  ip is buf[0];
			 * reuse its address lvalue (UMUL) as the BCLR operand. */
			p = ip->ip_node;
			l = p->n_left;
			nfree(p->n_right);		/* the ICON 0 */
			nfree(p);			/* the ASSIGN shell */
			/* INCREF type -> the node result slot is a B pair, used
			 * as the dst scratch by ZA.  The byte count rides in
			 * n_rval (n_lval would alias n_left, the child). */
			p = mkunode(BCLR, l, len, INCREF(CHAR));
			ip->ip_node = p;
			for (d = DLIST_NEXT(ip, qelem); d != past; d = dn) {
				dn = DLIST_NEXT(d, qelem);
				tfree(d->ip_node);
				DLIST_REMOVE(d, qelem);
			}
		} else {
			/* word-collapse aligned byte pairs within the run */
			for (d = ip; d != past; ) {
				bytezero(d->ip_node, &nbase, &noff);
				dn = DLIST_NEXT(d, qelem);
				if ((noff & 1) == 0 && dn != past) {
					p = d->ip_node;	/* even off: word clear */
					p->n_type = INT;
					p->n_left->n_type = INT;
					p->n_left->n_left->n_type = INCREF(INT);
					p->n_right->n_type = INT;
					tfree(dn->ip_node);
					DLIST_REMOVE(dn, qelem);
					d = DLIST_NEXT(d, qelem);
				} else
					d = dn;		/* odd/last: lone clrb */
			}
		}
		ip = past;
	}
}

/*
 * PROTOTYPE: common-argument CSE across consecutive calls.
 *
 * Two adjacent statements that call different functions with the SAME
 * fixed-address argument
 *
 *	time(&clock);
 *	tp = localtime(&clock);
 *
 * each rematerialise "&clock" (lda + segment-mask "and") before their
 * push.  There is no cross-statement CSE in the pipeline, so the address
 * is computed once per call.  When the argument is the address of a frame
 * object, a global, an address-taken auto, a symbolic address constant
 * (a global array / function address), or a wide numeric constant, its
 * value is a compile-time fixed quantity that no intervening call can
 * perturb - so
 * evaluating it once into a temp and reusing that temp is unconditionally
 * safe, regardless of what the calls themselves do.  Register allocation
 * then keeps the shared address in one (callee-saved, since it is live
 * across the first call) register:
 *
 *	lda   rr8,L0-4(r13) ; and r8,$32512   ; &clock, ONCE
 *	pushl (rr14),rr8 ; calr time_      ; inc r15,$4
 *	pushl (rr14),rr8 ; calr localtime_ ; inc r15,$4
 *
 * This removes the redundant recompute (the "why not cache it" half of
 * the observation).  The inter-call pop+repush (inc r15,$4 then pushl of
 * the same value) is left in place: collapsing it would rely on the
 * freed stack slot surviving across the call, which Coherent's
 * same-stack signal delivery does not guarantee.
 *
 * The shared address need not be the whole argument list: a call may take
 * several arguments and only one of them be the shared fixed address
 *
 *	fprintf(fp, "%s", &buf[0]);
 *	fputs(&buf[0], fp);
 *
 * so each call's arguments are scanned, and when one call passes several
 * hoistable addresses the one reused by the longest following run of calls
 * is chosen.  Runs may overlap (A and B share X; B and C share Y): the scan
 * advances one call at a time, and an address already rewritten to a temp
 * is no longer a hoist candidate, so each distinct address is hoisted once.
 *
 * Runs from myreader(), before ADDROF/TEMP lowering, canon and optimize,
 * so the fresh temp and the inserted assignment get the full standard
 * treatment (this is the only point at which inserting interpass nodes is
 * safe - doing it at myoptim, after the SSA allocator's CFG is built,
 * crashes insnwalk(); see the rmwcopyfuse note above).  Gated on xtemps:
 * without it deltemp spills every temp to the stack, turning the shared
 * address back into per-use reloads with no benefit.
 *
 * The run length at which the transform fires is a per-kind threshold,
 * because hoisting the address into a register live across a call forces a
 * callee-saved register (a prologue/epilogue save/restore, ~4-6 bytes when
 * it grows the ldm range, upgrades ld->ldm, or - worst case - spills and
 * pushes the frame past 16 so dec/inc become sub/add).  The hoist clears
 * that cost easily once (uses-1) * recompute_size is large:
 *   - ADDROF (&auto/&global): recompute is "lda + and" = 8 bytes, so two
 *     uses already win comfortably -> ARGCSE_MIN_ADDR = 2.
 *   - an ICON (symbolic address constant "ldl rrN,$sym" = 4 bytes, or a
 *     wide numeric constant "ldl rrN,$imm32" = 6 bytes): the 4-byte case at
 *     two uses is a coin-flip (win when a callee-saved reg is free, small
 *     loss when it forces a save/spill) that cannot be called before
 *     register allocation; the 6-byte numeric case is at least as profitable.
 * Measured over the 106-program corpus, ICON at 2 nets about -120 bytes
 * beyond ICON at 3 (~14 programs shrink, ~4-8 bytes each) at the cost of 7
 * programs growing by +2..+14.  We take the larger net reduction and accept
 * those small regressions (project decision); set ARGCSE_MIN_ICON = 3 to
 * trade -120 bytes of wins for guaranteed no-regression instead.
 */
#define	ARGCSE_MIN_ADDR	2
#define	ARGCSE_MIN_ICON	2

/*
 * The call node carried by an expression-statement: the bare call of a
 * void/discarded call, or the right-hand side of "lhs = f(...)".  Only
 * plain CALL (binary, has an argument list); UCALL has no args, and the
 * struct-return / Fortran variants carry hidden operands best left alone.
 */
static NODE *
argcse_call(NODE *p)
{
	if (p->n_op == ASSIGN)
		p = p->n_right;
	return p->n_op == CALL ? p : NULL;
}

/* Structural equality of two argument trees (same op, type, and leaf
 * value); enough to prove two "&x" designators name the same object. */
static int
argcse_same(NODE *a, NODE *b)
{
	if (a->n_op != b->n_op || a->n_type != b->n_type)
		return 0;
	switch (optype(a->n_op)) {
	case BITYPE:
		if (!argcse_same(a->n_right, b->n_right))
			return 0;
		/* FALLTHROUGH */
	case UTYPE:
		return argcse_same(a->n_left, b->n_left);
	default:
		if (a->n_rval != b->n_rval || getlval(a) != getlval(b))
			return 0;
		return strcmp(a->n_name ? a->n_name : "",
		    b->n_name ? b->n_name : "") == 0;
	}
}

/*
 * An argument-list node (a FUNARG) whose value is a call-invariant quantity
 * that is expensive enough to rematerialise to be worth caching in a
 * register across the calls that share it.  Every accepted form is fixed at
 * compile/link time, so hoisting it past any call is unconditionally safe:
 *   - ADDROF(NAME|TEMP|OREG(FPREG)): the address of a global/static, an
 *     address-taken auto (temp before lowering, frame OREG after) - "lda +
 *     segment-mask", 8 bytes;
 *   - a nameful ICON: a symbolic address constant (a global array or
 *     function address, which pass 1 hands us as ICON not ADDROF) - a long
 *     "ldl rrN,$sym", 4 bytes;
 *   - a nameless ICON of long/ulong/pointer type: a wide numeric constant,
 *     which is pushed through a register ("ldl rrN,$imm32; pushl"), 6 bytes.
 * Returns that node, else NULL.  Deliberately rejected: word/byte numeric
 * constants (pushed as a direct immediate, nothing to cache), struct-by-value
 * STARG, and any value load - a register/temp value is already its own cached
 * form, and a memory load is not call-invariant (the callee may write it).
 */
static NODE *
argcse_addr(NODE *arg)
{
	NODE *a, *l;
	TWORD t;

	if (arg->n_op != FUNARG)
		return NULL;
	a = arg->n_left;
	if (a->n_op == ICON) {
		if (a->n_name != NULL && a->n_name[0] != '\0')
			return a;		/* &global_array / func address */
		t = a->n_type;			/* wide numeric constant only */
		if (t == LONG || t == ULONG || ISPTR(t))
			return a;
		return NULL;			/* word/byte const: push $N */
	}
	if (a->n_op != ADDROF)
		return NULL;
	l = a->n_left;
	if (l->n_op == NAME)			/* &global / &static */
		return a;
	if (l->n_op == TEMP)			/* &auto (pre-lowering) */
		return a;
	if (l->n_op == OREG && l->n_rval == FPREG)  /* &auto (lowered) */
		return a;
	return NULL;
}

/*
 * The argument list of a call is the left-leaning CM chain hanging off
 * n_right: each CM's n_right is one argument and the terminal (non-CM)
 * node is the first argument, all FUNARG-wrapped (see lastcall()).  The
 * three helpers below walk that list without materialising it.
 */

/* The k-th hoistable (fixed-address) argument of call, or NULL. */
static NODE *
argcse_nth(NODE *call, int k)
{
	NODE **pp, *a;
	int i = 0;

	if (call->n_right == NIL)
		return NULL;
	for (pp = &call->n_right; (*pp)->n_op == CM; pp = &(*pp)->n_left)
		if ((a = argcse_addr((*pp)->n_right)) != NULL && i++ == k)
			return a;
	if ((a = argcse_addr(*pp)) != NULL && i == k)
		return a;
	return NULL;
}

/* True if some argument of call is structurally the fixed address x. */
static int
argcse_has(NODE *call, NODE *x)
{
	NODE *p;

	if (call->n_right == NIL)
		return 0;
	for (p = call->n_right; p->n_op == CM; p = p->n_left)
		if (p->n_right->n_op == FUNARG &&
		    argcse_same(p->n_right->n_left, x))
			return 1;
	return p->n_op == FUNARG && argcse_same(p->n_left, x);
}

/*
 * Replace every argument of call that equals x with a fresh TEMP(num).
 * When keep is set, the first replaced subtree is detached and returned
 * (to become the single hoisted "tnew = x" evaluation) and any further
 * matches are freed; otherwise every match is freed and NULL returned.
 */
static NODE *
argcse_subst(NODE *call, NODE *x, int num, TWORD at, int keep)
{
	NODE **pp, *slot, *child, *first = NULL;

	for (pp = &call->n_right; ; pp = &(*pp)->n_left) {
		int cm = (*pp)->n_op == CM;
		slot = cm ? (*pp)->n_right : *pp;
		if (slot->n_op == FUNARG && argcse_same(slot->n_left, x)) {
			child = slot->n_left;
			slot->n_left = mklnode(TEMP, 0, num, at);
			if (keep && first == NULL)
				first = child;
			else
				tfree(child);
		}
		if (!cm)
			break;
	}
	return first;
}

static void
argcse(struct interpass *ipole)
{
	struct interpass *ip, *inext, *run, *newip;
	NODE *c1, *ck, *cand, *best, *arg1;
	TWORD at;
	int num, i, k, n, bestn, need;

	if (!xtemps)
		return;
	for (ip = DLIST_NEXT(ipole, qelem); ip != ipole; ip = inext) {
		inext = DLIST_NEXT(ip, qelem);
		if (ip->type != IP_NODE)
			continue;
		c1 = argcse_call(ip->ip_node);
		if (c1 == NULL)
			continue;

		/*
		 * Among c1's hoistable arguments pick the one shared by the
		 * longest run of immediately following calls (a call may pass
		 * several fixed addresses, each shared by a different reach;
		 * the longest run yields the most reuse for one temp).  Each
		 * candidate must clear its own kind's threshold (ICON address
		 * constants need a longer run than ADDROF, being cheaper to
		 * recompute) before it is eligible.
		 */
		best = NULL;
		bestn = 0;
		for (k = 0; (cand = argcse_nth(c1, k)) != NULL; k++) {
			need = cand->n_op == ICON ? ARGCSE_MIN_ICON
			    : ARGCSE_MIN_ADDR;
			n = 1;
			for (run = inext; run != ipole &&
			    run->type == IP_NODE; run = DLIST_NEXT(run, qelem)) {
				ck = argcse_call(run->ip_node);
				if (ck == NULL || !argcse_has(ck, cand))
					break;
				n++;
			}
			if (n >= need && n > bestn) {
				bestn = n;
				best = cand;
			}
		}
		if (best == NULL)
			continue;

		/* hoist: "tnew = &x" once, immediately before c1, reusing
		 * c1's own occurrence of the address as the evaluation */
		at = best->n_type;
		num = p2env.epp->ip_tmpnum++;
		arg1 = argcse_subst(c1, best, num, at, 1);
		newip = ipnode(mkbinode(ASSIGN,
		    mklnode(TEMP, 0, num, at), arg1, at));
		DLIST_INSERT_BEFORE(ip, newip, qelem);

		/* rewrite the shared argument to read tnew in the rest of
		 * the run (arg1 keeps best's structure, so the compares hold) */
		run = inext;
		for (i = 1; i < bestn; i++) {
			ck = argcse_call(run->ip_node);
			argcse_subst(ck, best, num, at, 0);
			run = DLIST_NEXT(run, qelem);
		}
	}
}

void
myreader(struct interpass *ip)
{
	struct interpass *ip2;
	int off = p2autooff;

	swcpir(ip);
	clrfill(ip);
	argcse(ip);
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
