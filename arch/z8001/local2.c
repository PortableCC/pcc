/*
 * Copyright (c) 2025 Michal Pleban.
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
 * Frame layout (our PCC-compatible model, different from reference compiler):
 *
 *   high address
 *   [caller args]   at r13+4, r13+6, ...   (ARGINIT=32 bits = 4 bytes)
 *   [return addr]   at r13+0 .. r13+3       (4-byte segmented return addr)
 *   -------------- r13 = entry SP = frame pointer
 *   [locals]        at r13-2, r13-4, ...    (AUTOINIT=0)
 *   [callee saves]  at r13-fsize-2*nsave .. r13-fsize-2
 *   -------------- r15 = current SP
 *   low address
 *
 * Prologue sequence:
 *   dec/sub r15, $total          (total = fsize + 2*nsave)
 *   [ld (rr14), r13             (for nsave == 1)]
 *   [ldm (rr14), rX, $nsave     (for nsave > 1, saves rX..r13)]
 *   ld r13, r15
 *   inc/add r13, $total          (r13 = entry SP)
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
 * r0-r15 are 16-bit word registers; rr0,rr2,...,rr10 are 32-bit pairs.
 * Indices: 0-15 = r0-r15, 16=rr0, 17=rr2, 18=rr4, 19=rr6, 20=rr8, 21=rr10.
 */
char *rnames[] = {
	"r0",  "r1",  "r2",  "r3",  "r4",  "r5",
	"r6",  "r7",  "r8",  "r9",  "r10", "r11",
	"r12", "r13", "r14", "r15",
	"rr0", "rr2", "rr4", "rr6", "rr8", "rr10"
};

void
deflab(int label)
{
	printf(LABFMT ":\n", label);
}

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

	/* Step 3: r13 = current SP */
	printf("\tld\tr13,r15\n");

	/* Step 4: r13 = entry SP (frame pointer for PCC convention) */
	if (total > 0) {
		if (total <= 16)
			printf("\tinc\tr13,$%d\n", total);
		else
			printf("\tadd\tr13,$%d\n", total);
	}
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
 * zzzcode: handle special escape sequences in instruction templates.
 *
 *   ZB  stack cleanup after call: add/inc r15, $n_qual
 *   ZT  struct argument (not yet implemented)
 */
void
zzzcode(NODE *p, int c)
{
	int n;

	switch (c) {
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

	case 'T':
		/* Struct argument by value: copy struct onto stack */
		/* TODO: implement struct-by-value argument passing */
		comperr("zzzcode ZT: struct arg not supported");
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
		if (val != 0)
			fprintf(io, CONFMT, val);
		fprintf(io, "(%s)", rnames[p->n_rval]);
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
	if (szty(t) == 2) {
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
 * pairs (rr0,rr2,rr4,rr6,rr8,rr10); each pair overlaps two word registers.
 */
int
COLORMAP(int c, int *r)
{
	int num;

	switch (c) {
	case CLASSA:
		/* each interfering pair blocks two word registers */
		num = r[CLASSA] + 2 * r[CLASSB];
		return num < 13;
	case CLASSB:
		/* each interfering word can block at most one pair */
		num = r[CLASSB] + r[CLASSA];
		return num < 6;
	}
	return 0;
}

/*
 * Return the register class suitable for a value of type t.
 * Consistent with PCLASS in macdefs.h: 32-bit values (long/ptr/float)
 * use class B (pairs), everything else uses class A (words).
 */
int
gclass(TWORD t)
{
	return szty(t) == 2 ? CLASSB : CLASSA;
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
		return attr_find(p->n_ap, ATTR_P2STRUCT)->iarg(0);
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
	if (p->n_right == NIL)
		return;		/* no arguments */
	for (p = p->n_right; p->n_op == CM; p = p->n_left)
		size += argsiz(p->n_right);
	size += argsiz(p);
	op->n_qual = size;
}

/*
 * Special shape matching.  Z8001 has no special address modes that need
 * this, so always decline.
 */
int
special(NODE *p, int shape)
{
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

void
myreader(struct interpass *ip)
{
}

void
mycanon(NODE *p)
{
}

void
mygenregs(struct interpass *ip)
{
}
