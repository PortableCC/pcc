/*	$Id$	*/
/*
 * Copyright (c) 2006 Anders Magnusson (ragge@ludd.luth.se).
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
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission
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


# include "pass2.h"
# include <ctype.h>
# include <string.h>
#include <stdlib.h>

void acon(NODE *p);
int argsize(NODE *p);

static int maxargsz;

void
deflab(int label)
{
	printf(LABFMT ":\n", label);
}

void
prologue(struct interpass_prolog *ipp)
{

#ifdef os_none
	if (ipp->ipp_flags & IF_VISIBLE)
		printf("	.ENT %s\n", ipp->ipp_name);
	printf("	.ZREL\n");
	printf("%s:	.%s\n", ipp->ipp_name, ipp->ipp_name);
	printf("	.NREL\n");
	printf("	0%o\n", p2maxautooff);
	printf(".%s:\n", ipp->ipp_name);
	printf("	sta 3,@csp\n");	/* put ret pc on stack */
	printf("	jsr @prolog\n");	/* jump to prolog */
#else
	printf("#BEGFTN\n");
	if (ipp->ipp_flags & IF_VISIBLE)
		printf("	.globl %s\n", ipp->ipp_name);
	printf("%s:\n", ipp->ipp_name);
	printf("	sta 3,@spref\n");	/* put ret pc on stack */
	printf("	jsr @csav\n");		/* jump to prolog */
	printf("	.word 0%o\n", p2maxautooff);
#endif
}

void
eoftn(struct interpass_prolog *ipp)
{
	if (ipp->ipp_ip.ip_lbl == 0)
		return; /* no code needs to be generated */
	printf("	jmp @cret\n");
	printf("#ENDFTN\n");
}

/*
 * add/sub/...
 *
 * Param given:
 */
void
hopcode(int f, int o)
{
	char *str = 0;

	switch (o) {
	case PLUS:
		str = "add";
		break;
	case MINUS:
		str = "sub";
		break;
	case AND:
		str = "and";
		break;
	case OR:
		cerror("hopcode OR");
		break;
	case ER:
		cerror("hopcode xor");
		str = "xor";
		break;
	default:
		comperr("hopcode2: %d", o);
		str = 0; /* XXX gcc */
	}
	printf("%s%c", str, f);
}

#if 0
/*
 * Return type size in bytes.  Used by R2REGS, arg 2 to offset().
 */
int
tlen(p) NODE *p;
{
	switch(p->n_type) {
		case CHAR:
		case UCHAR:
			return(1);

		case SHORT:
		case USHORT:
			return(SZSHORT/SZCHAR);

		case DOUBLE:
			return(SZDOUBLE/SZCHAR);

		case INT:
		case UNSIGNED:
		case LONG:
		case ULONG:
			return(SZINT/SZCHAR);

		case LONGLONG:
		case ULONGLONG:
			return SZLONGLONG/SZCHAR;

		default:
			if (!ISPTR(p->n_type))
				comperr("tlen type %d not pointer");
			return SZPOINT(p->n_type)/SZCHAR;
		}
}
#endif

int
fldexpand(NODE *p, int cookie, char **cp)
{
	return 0;
}

#if 0
/*
 * Assign to a bitfield.
 * Clumsy at least, but what to do?
 */
static void
bfasg(NODE *p)
{
	NODE *fn = p->n_left;
	int shift = UPKFOFF(fn->n_rval);
	int fsz = UPKFSZ(fn->n_rval);
	int andval, tch = 0;

	/* get instruction size */
	switch (p->n_type) {
	case CHAR: case UCHAR: tch = 'b'; break;
	case SHORT: case USHORT: tch = 'w'; break;
	case INT: case UNSIGNED: tch = 'l'; break;
	default: comperr("bfasg");
	}

	/* put src into a temporary reg */
	printf("	mov%c ", tch);
	adrput(stdout, getlr(p, 'R'));
	printf(",");
	adrput(stdout, getlr(p, '1'));
	printf("\n");

	/* AND away the bits from dest */
	andval = ~(((1 << fsz) - 1) << shift);
	printf("	and%c $%d,", tch, andval);
	adrput(stdout, fn->n_left);
	printf("\n");

	/* AND away unwanted bits from src */
	andval = ((1 << fsz) - 1);
	printf("	and%c $%d,", tch, andval);
	adrput(stdout, getlr(p, '1'));
	printf("\n");

	/* SHIFT left src number of bits */
	if (shift) {
		printf("	sal%c $%d,", tch, shift);
		adrput(stdout, getlr(p, '1'));
		printf("\n");
	}

	/* OR in src to dest */
	printf("	or%c ", tch);
	adrput(stdout, getlr(p, '1'));
	printf(",");
	adrput(stdout, fn->n_left);
	printf("\n");
}
#endif

#if 0
/*
 * Push a structure on stack as argument.
 * the scratch registers are already free here
 */
static void
starg(NODE *p)
{
	int sz = attr_find(p->n_ap, ATTR_P2STRUCT)->iarg(0);
	printf("	subl $%d,%%esp\n", sz);
	printf("	pushl $%d\n", sz);
	expand(p, 0, "	pushl AL\n");
	expand(p, 0, "	leal 8(%esp),A1\n");
	expand(p, 0, "	pushl A1\n");
	printf("	call memcpy\n");
	printf("	addl $12,%%esp\n");
}
#endif

/*
 * Compare long against 0.
 * Value is in AC0/AC1.
 */
static void
lzero(NODE *p)
{
	int l = 0;

	switch (p->n_op) {
	case EQ:
		expand(p, 0, "	add# 0,1,snr\n");
		break;
	case NE:
		expand(p, 0, "	add# 0,1,szr\n");
		break;
	case GE:
		expand(p, 0, "	movl# 0,0,snc\n");
		break;
	case LT:
		expand(p, 0, "	movl# 0,0,szc\n");
		break;
	case GT:
		l = getlab2();
		expand(p, 0, "	movl# 0,0,szc\n"); /* high word */
		printf("	jmp " LABFMT "\n", l);
		expand(p, 0, "	add# 0,1,szr\n");
		break;
	case LE:
		expand(p, 0, "	movl# 0,0,szc\n	jmp LC\n"); /* high word */
		expand(p, 0, "	add# 0,1,snr\n");
		break;
	default:
		comperr("lzero %d", p->n_op);
	}
	expand(p, 0, "	jmp LC\n");
	if (l)
		printf(LABFMT ":\n", l);
}

/*
 * Compare two long values.
 * Left value is in AC0/AC1, right in memory.
 * AC2 is available for use.
 */
static void
lcmp(NODE *p)
{

	expand(p, 0, "	lda 2,AR\n");
	expand(p, 0, "	sta 2,@sp\n");
	expand(p, 0, "	lda 2,UR\n");
	expand(p, 0, "	sta 2,@sp\n");

	switch (p->n_op) {
	case LE:
		expand(p, 0, "	jsr __pcc_lle\n");
		expand(p, 0, "	jmp LC\n");
		break;

	default:
		comperr("lcmp %d", p->n_op);
	}
}

void
zzzcode(NODE *p, int c)
{
	struct attr *ap;
	NODE *l;

	switch (c) {
	case 'N': /* compare two long */
		lcmp(p);
		break;

	case 'Q': /* struct assign */
		/* right is in ac2, left is name or oreg */
		l = getlr(p, 'L');
		if (l->n_op == NAME) {
			l->n_op = ICON;
			expand(p, 0, "	lda 0,AL\n");
			l->n_op = NAME;
		} else { /* in OREG */
			printf("	lda 0,[.word %d]\n", (int)getlval(l));
			printf("	add 3,0\n");
		}
		ap = attr_find(p->n_ap, ATTR_P2STRUCT);
		printf("	lda 1,[.word %d]\n", -(ap->iarg(0) >> 1));
		printf("	jsr __stcpy\n");
		break;

	case 'Z': /* compare long against 0 */
		lzero(p);
		break;


	default:
		comperr("zzzcode %c", c);
	}
}

/*ARGSUSED*/
int
rewfld(NODE *p)
{
	return(1);
}

int canaddr(NODE *);
int
canaddr(NODE *p)
{
	int o = p->n_op;

	if (o==NAME || o==REG || o==ICON || o==OREG ||
	    (o==UMUL && shumul(p->n_left, SOREG)))
		return(1);
	return(0);
}

/*
 * Does the bitfield shape match?
 */
int
flshape(NODE *p)
{
	int o = p->n_op;

cerror("flshape");
	if (o == OREG || o == REG || o == NAME)
		return SRDIR; /* Direct match */
	if (o == UMUL && shumul(p->n_left, SOREG))
		return SROREG; /* Convert into oreg */
	return SRREG; /* put it into a register */
}

/* INTEMP shapes must not contain any temporary registers */
/* XXX should this go away now? */
int
shtemp(NODE *p)
{
	return 0;
#if 0
	int r;

	if (p->n_op == STARG )
		p = p->n_left;

	switch (p->n_op) {
	case REG:
		return (!istreg(p->n_rval));

	case OREG:
		r = p->n_rval;
		if (R2TEST(r)) {
			if (istreg(R2UPK1(r)))
				return(0);
			r = R2UPK2(r);
		}
		return (!istreg(r));

	case UMUL:
		p = p->n_left;
		return (p->n_op != UMUL && shtemp(p));
	}

	if (optype(p->n_op) != LTYPE)
		return(0);
	return(1);
#endif
}

void
adrcon(CONSZ val)
{
	printf("[" CONFMT "]", val);
}

/*
 * Conput prints out a constant.
 */
void
conput(FILE *fp, NODE *p)
{
	int val = getlval(p);

	switch (p->n_op) {
	case NAME:
	case ICON:
		if (p->n_name[0] != '\0') {
			fprintf(fp, "%s", p->n_name);
			if (val)
				fprintf(fp, "+0%o", val & 0177777);
		} else
			fprintf(fp, "0%o", val & 0177777);
		return;

	default:
		comperr("illegal conput, p %p", p);
	}
}

/*ARGSUSED*/
void
insput(NODE *p)
{
	comperr("insput");
}

/*
 * Write out the upper address, like the upper register of a 2-register
 * reference, or the next memory location.
 */
void
upput(NODE *p, int size)
{
//printf("upput\n");
//fwalk(p, e2print, 0);
	switch (p->n_op) {
	case REG:
		printf("1"); /* ac1 is always upper */
		break;

	case NAME:
	case OREG:
		setlval(p, getlval(p) + 1);
		adrput(stdout, p);
		setlval(p, getlval(p) - 1);
		break;
	case ICON:
		printf("[.word " CONFMT "]", getlval(p) & 0177777);
		break;
	default:
		comperr("upput bad op %d size %d", p->n_op, size);
	}
}

void
adrput(FILE *io, NODE *p)
{
	int i;
	/* output an address, with offsets, from p */

static int looping = 7;
if (looping == 0) {
	looping = 1;
	printf("adrput %p\n", p);
	fwalk(p, e2print, 0);
	looping = 0;
}
	if (p->n_op == FLD)
		p = p->n_left;

	switch (p->n_op) {
	case NAME:
		fputc('@', io);
		/* FALLTHROUGH */
	case ICON:
		fputc('[', io);
		if (p->n_type == INCREF(CHAR) || p->n_type == INCREF(UCHAR))
			fprintf(io, ".bptr ");
		else
			fprintf(io, ".word ");
		if (p->n_type == LONG || p->n_type == ULONG)
			printf(CONFMT, getlval(p) >> 16);
		else
			conput(io, p);
		fputc(']', io);
		break;

	case OREG:
		if (p->n_name[0])
			comperr("name in OREG");
		i = (int)getlval(p);
		if (i < 0) {
			putchar('-');
			i = -i;
		}
		if (regno(p) != AC2 && regno(p) != AC3)
			comperr("bad index reg %d", regno(p));
		printf("0%o,%s", i, rnames[regno(p)]);
		break;

	case REG:
		if (p->n_type == LONG || p->n_type == ULONG)
			fprintf(io, "0");
		else
			fprintf(io, "%s", rnames[p->n_rval]);
		break;

	default:
		comperr("illegal address, op %d, node %p", p->n_op, p);
		break;

	}
}

/*   printf conditional and unconditional branches */
void
cbgen(int o, int lab)
{
	comperr("cbgen");
}

void
myreader(struct interpass *ipole)
{
	if (x2debug)
		printip(ipole);
}

void
mycanon(NODE *p)
{
	int size = 0;

	p->n_qual = 0;
	if (p->n_op != CALL && p->n_op != FORTCALL && p->n_op != STCALL)
		return;
	for (p = p->n_right; p->n_op == CM; p = p->n_left) { 
		if (p->n_right->n_op != ASSIGN)
			size += szty(p->n_right->n_type);
	}
	if (p->n_op != ASSIGN)
		size += szty(p->n_type);

	if (maxargsz < size)
		maxargsz = size;
	
}

void
myoptim(struct interpass *ip)
{
}

void
rmove(int s, int d, TWORD t)
{
	printf("	mov %s,%s\n", rnames[s], rnames[d]);
	if (t > UNSIGNED && !ISPTR(t))
		comperr("rmove");
}

/*
 * For class c, find worst-case displacement of the number of
 * registers in the array r[] indexed by class.
 * Return true if we always can find a color.
 */
int
COLORMAP(int c, int *r)
{
	int num = 0;

	switch (c) {
	case CLASSA:
		/* must have at least one reg free to guarantee */
		if (r[CLASSB]*2+r[CLASSA] < 3)
			num = 1;
		break;
	case CLASSB:
		if (r[CLASSB] || r[CLASSA])
			num = 0;
		break;
	case CLASSC:
		num = r[CLASSC] < CREGCNT;
		break;
	}
	return num;
}

char *rnames[] = {
	"0", "1", "2", "3", "lc0", "fp0", "cfp", "csp",
};

/*
 * Return a class suitable for a specific type.
 */
int
gclass(TWORD t)
{
	return (t==LONG||t==ULONG) ? CLASSB : CLASSA;
}

/*
 * Calculate argument sizes.
 */
void
lastcall(NODE *p)
{
	NODE *op = p;
	int size = 0;

	p->n_qual = 0;
	if (p->n_op != CALL && p->n_op != FORTCALL && p->n_op != STCALL)
		return;
	for (p = p->n_right; p->n_op == CM; p = p->n_left) { 
		if (p->n_right->n_op != ASSIGN)
			size += szty(p->n_right->n_type);
	}
	if (p->n_op != ASSIGN)
		size += szty(p->n_type);

        op->n_qual = size; /* XXX */
	if (maxargsz < size)
		maxargsz = size;
}

/*
 * Special shapes.
 */
int
special(NODE *p, int shape)
{
	switch (shape) {
	case SLDFPSP:
		return regno(p) == FPREG || regno(p) == STKREG;
	}
	return SRNOPE;
}

/*
 * Target-dependent command-line options.
 */
void
mflags(char *str)
{
}
/*
 * Do something target-dependent for xasm arguments.
 * Supposed to find target-specific constraints and rewrite them.
 */
int
myxasm(struct interpass *ip, NODE *p)
{
	return 0;
}
