/*	$Id$	*/
/*
 * Copyright (c) 2003 Anders Magnusson (ragge@ludd.luth.se).
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

#if defined(PECOFFABI) || defined(MACHOABI) || defined(AOUTABI)
#define EXPREFIX	"_"
#else
#define EXPREFIX	""
#endif

int msettings = MI686;
static int stkpos;
static int flabwrtn, loadlab;

void
deflab(int label)
{
	printf(LABFMT ":\n", label);
}

static int regoff[7];
static TWORD ftype;

/*
 * Print out the prolog assembler.
 * addto and regoff are already calculated.
 */
static void
prtprolog(struct interpass_prolog *ipp, int addto)
{
	int i;

#if 1
#if defined(MACHOABI)
	addto += 8;
#endif
	if (addto == 0 || addto > 65535) {
		printf("	pushl %%ebp\n\tmovl %%esp,%%ebp\n");
		if (addto)
			printf("	subl $%d,%%esp\n", addto);
	} else
		printf("	enter $%d,$0\n", addto);
#endif
	for (i = 0; i < MAXREGS; i++)
		if (TESTBIT(p2env.p_regs, i))
			printf("	movl %s,-%d(%s)\n",
			    rnames[i], regoff[i], rnames[FPREG]);
}

/*
 * calculate stack size and offsets
 */
static int
offcalc(struct interpass_prolog *ipp)
{
	int i, addto;

	addto = p2maxautooff;
	if (addto >= AUTOINIT/SZCHAR)
		addto -= AUTOINIT/SZCHAR;
	for (i = 0; i < MAXREGS; i++)
		if (TESTBIT(p2env.p_regs, i)) {
			addto += SZINT/SZCHAR;
			regoff[i] = addto;
		}
	return addto;
}

void
prologue(struct interpass_prolog *ipp)
{
	int addto;

	ftype = ipp->ipp_type;

#ifdef LANG_F77
	if (ipp->ipp_flags & IF_VISIBLE)
		printf("	.globl %s\n", ipp->ipp_name);
	printf("	.align 4\n");
	printf("%s:\n", ipp->ipp_name);
#endif
	/*
	 * We here know what register to save and how much to 
	 * add to the stack.
	 */
	addto = offcalc(ipp);
#if defined(MACHOABI)
	addto = (addto + 15) & ~15;	/* stack alignment */
#endif
	prtprolog(ipp, addto);
	if (kflag) {
#if defined(MACHOABI)
		printf("	call L%s$pb\n", ipp->ipp_name);
		printf("L%s$pb:\n", ipp->ipp_name);
		printf("	popl %%ebx\n");
#else
		int l;
		printf("	call " LABFMT "\n", l = getlab());
		printf(LABFMT ":\n", l);
		printf("	popl %%ebx\n");
		printf("	addl $_GLOBAL_OFFSET_TABLE_+[.-" LABFMT 
		    "], %%ebx\n", l);
#endif

	}
}

void
eoftn(struct interpass_prolog *ipp)
{
	int i;

	if (ipp->ipp_ip.ip_lbl == 0)
		return; /* no code needs to be generated */

	/* return from function code */
	for (i = 0; i < MAXREGS; i++)
		if (TESTBIT(p2env.p_regs, i))
			printf("	movl -%d(%s),%s\n",
			    regoff[i], rnames[FPREG], rnames[i]);

	/* struct return needs special treatment */
	if (ftype == STRTY || ftype == UNIONTY) {
		printf("	movl 8(%%ebp),%%eax\n");
		printf("	leave\n");
		printf("	ret $%d\n", 4 + ipp->ipp_argstacksize);
	} else {
		printf("	leave\n");
		if (ipp->ipp_argstacksize)
			printf("	ret $%d\n", ipp->ipp_argstacksize);
		else
			printf("	ret\n");
	}

#if defined(ELFABI)
	printf("\t.size " EXPREFIX "%s,.-" EXPREFIX "%s\n", ipp->ipp_name,
	    ipp->ipp_name);
#endif
	if (flabwrtn == 0 && loadlab) {
		printf("	.data\n");
		printf(LABFMT ":	.long 0x5f800000\n", loadlab);
		printf("	.text\n");
		flabwrtn = 1;
	}
}

/*
 * add/sub/...
 *
 * Param given:
 */
void
hopcode(int f, int o)
{
	char *str;

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
		str = "or";
		break;
	case ER:
		str = "xor";
		break;
	default:
		comperr("hopcode2: %d", o);
		str = 0; /* XXX gcc */
	}
	printf("%s%c", str, f);
}

/*
 * Return type size in bytes.  Used by R2REGS, arg 2 to offset().
 */
int
tlen(NODE *p)
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

/*
 * Emit code to compare two longlong numbers.
 */
static void
twollcomp(NODE *p)
{
	int u;
	int s = getlab2();
	int e = p->n_label;
	int cb1, cb2;

	u = p->n_op;
	switch (p->n_op) {
	case NE:
		cb1 = 0;
		cb2 = NE;
		break;
	case EQ:
		cb1 = NE;
		cb2 = 0;
		break;
	case LE:
	case LT:
		u += (ULE-LE);
		/* FALLTHROUGH */
	case ULE:
	case ULT:
		cb1 = GT;
		cb2 = LT;
		break;
	case GE:
	case GT:
		u += (ULE-LE);
		/* FALLTHROUGH */
	case UGE:
	case UGT:
		cb1 = LT;
		cb2 = GT;
		break;
	
	default:
		cb1 = cb2 = 0; /* XXX gcc */
	}
	if (p->n_op >= ULE)
		cb1 += 4, cb2 += 4;
	expand(p, 0, "	cmpl UR,UL\n");
	if (cb1) cbgen(cb1, s);
	if (cb2) cbgen(cb2, e);
	expand(p, 0, "	cmpl AR,AL\n");
	cbgen(u, e);
	deflab(s);
}

int
fldexpand(NODE *p, int cookie, char **cp)
{
	comperr("fldexpand");
	return 0;
}

/*
 * Push a structure on stack as argument.
 * the scratch registers are already free here
 */
static void
starg(NODE *p)
{
	struct attr *ap;
	NODE *q = p->n_left;

	ap = attr_find(p->n_ap, ATTR_P2STRUCT);
	printf("	subl $%d,%%esp\n", (ap->iarg(0) + 3) & ~3);
	p->n_left = mklnode(OREG, 0, ESP, INT);
	zzzcode(p, 'Q');
	tfree(p->n_left);
	p->n_left = q;
}

/*
 * Compare two floating point numbers.
 */
static void
fcomp(NODE *p)	
{
	int swap = ((p->n_su & DORIGHT) != 0);
	int failjump = attr_find(p->n_ap, ATTR_FP_SWAPPED) != 0;

//printf("fcomp: DOR %d op %s\n", swap, opst[p->n_op]);
	if (p->n_op == GT || p->n_op == GE) {
		swap ^= 1;
		p->n_op = (p->n_op == GT ? LT : LE);
	}
//printf("fcomp2: DOR %d op %s\n", swap, opst[p->n_op]);
	if (swap)
		expand(p, 0, "\tfxch\n");

	if (msettings & MI686) {
		expand(p, 0, "\tfucomip %st(1),%st\n"); /* emit compare insn  */
		expand(p, 0, "\tfstp %st(0)\n");	/* pop fromstack */
	} else {
		expand(p, 0, "\tfucompp\n");
		expand(p, 0, "\tfnstsw %ax\n");
		expand(p, 0, "\tsahf\n");
	}
	switch (p->n_op) {
	case EQ: /* jump if: Z is set and P is clear */
		expand(p, 0, "\tjne 1f\n");
		expand(p, 0, "\tjnp LC\n");
		expand(p, 0, "\t1:\n");
		break;
	case NE: /* jump if: Z is clear or P is set */
		expand(p, 0, "\tjne LC\n");
		expand(p, 0, "\tjp LC\n");
		break;
	case LT:
		expand(p, 0, "\tja LC\n");
		if (failjump)
			expand(p, 0, "\tjp LC\n");
		break;
	case LE:
		expand(p, 0, "\tjae LC\n");
		if (failjump)
			expand(p, 0, "\tjp LC\n");
		break;
	}

}

/*
 * Convert an unsigned long long to floating point number.
 */
static void
ulltofp(NODE *p)
{
	int jmplab = getlab2();

	if (loadlab == 0)
		loadlab = getlab2();
	expand(p, 0, "	movl UL,4+A2\n	movl AL,A2\n");
	expand(p, 0, "	fildq A2\n");
	expand(p, 0, "	test UL,UL\n");
	printf("	jge " LABFMT "\n", jmplab);
	printf("	fadds " LABFMT "%s\n", loadlab, kflag ? "@GOTOFF" : "");
	printf(LABFMT ":\n", jmplab);
}

static void
fcast(NODE *p)
{
	TWORD t = p->n_type;
	int sz, c;

	if (t >= p->n_left->n_type)
		return; /* cast to more precision */
	if (t == FLOAT)
		sz = 4, c = 's';
	else
		sz = 8, c = 'l';

	printf("	sub $%d,%%esp\n", sz);
	printf("	fstp%c (%%esp)\n", c);
	printf("	fld%c (%%esp)\n", c);
	printf("	add $%d,%%esp\n", sz);
}

static void
llshft(NODE *p)
{
	char *d[3];

	if (p->n_op == LS) {
		d[0] = "l", d[1] = "%eax", d[2] = "%edx";
	} else
		d[0] = "r", d[1] = "%edx", d[2] = "%eax";

	printf("\tsh%sdl %s,%s\n",d[0], d[1], d[2]);
	printf("\ts%s%sl %%cl,%s\n", p->n_op == RS &&
	    p->n_left->n_type == ULONGLONG ? "h" : "a", d[0], d[1]);
	printf("\ttestb $32,%%cl\n");
	printf("\tje 1f\n");
	printf("\tmovl %s,%s\n", d[1], d[2]);
	if (p->n_op == RS && p->n_left->n_type == LONGLONG)
		printf("\tsarl $31,%%edx\n");
	else
		printf("\txorl %s,%s\n",d[1],d[1]);
	printf("1:\n");
}

void
zzzcode(NODE *p, int c)
{
	struct attr *ap;
	NODE *l;
	int pr, lr, i;
	char *ch;

	switch (c) {
	case 'A': /* swap st0 and st1 if right is evaluated second */
		if ((p->n_su & DORIGHT) == 0) {
			if (logop(p->n_op))
				printf("	fxch\n");
			else
				printf("r");
		}
		break;

	case 'C':  /* remove from stack after subroutine call */
#ifdef GCC_COMPAT
		if (attr_find(p->n_left->n_ap, GCC_ATYP_STDCALL))
			break;
#endif
		pr = 0;
		if ((ap = attr_find(p->n_ap, ATTR_STKADJ)))
			pr = ap->iarg(0);
		if (attr_find(p->n_ap, ATTR_I386_FPPOP))
			printf("	fstp	%%st(0)\n");
		if (pr)
			printf("	addl $%d, %s\n", pr, rnames[ESP]);
#if defined(os_openbsd)
		ap = attr_find(p->n_ap, ATTR_P2STRUCT);
		if (p->n_op == STCALL && (ap->iarg(0) == 1 ||
		    ap->iarg(0) == 2 || ap->iarg(0) == 4 || 
		    ap->iarg(0) == 8)) {
			/* save on stack */
			printf("\tmovl %%eax,-%d(%%ebp)\n", stkpos);
			printf("\tmovl %%edx,-%d(%%ebp)\n", stkpos+4);
			printf("\tleal -%d(%%ebp),%%eax\n", stkpos);
		}
#endif
		break;

	case 'D': /* Long long comparision */
		twollcomp(p);
		break;

	case 'F': /* Structure argument */
		starg(p);
		break;

	case 'G': /* Floating point compare */
		fcomp(p);
		break;

	case 'H': /* assign of longlong between regs */
		rmove(DECRA(p->n_right->n_reg, 0),
		    DECRA(p->n_left->n_reg, 0), LONGLONG);
		break;

	case 'I': /* float casts */
		fcast(p);
		break;

	case 'J': /* convert unsigned long long to floating point */
		ulltofp(p);
		break;

	case 'K': /* Load longlong reg into another reg */
		rmove(regno(p), DECRA(p->n_reg, 0), LONGLONG);
		break;

#ifndef NOBREGS
	case 'M': /* Output sconv move, if needed */
		l = getlr(p, 'L');
		/* XXX fixneed: regnum */
		pr = DECRA(p->n_reg, 0);
		lr = DECRA(l->n_reg, 0);
		if ((pr == AL && lr == EAX) || (pr == BL && lr == EBX) ||
		    (pr == CL && lr == ECX) || (pr == DL && lr == EDX))
			;
		else
			printf("	movb %%%cl,%s\n",
			    rnames[lr][2], rnames[pr]);
		l->n_rval = l->n_reg = p->n_reg; /* XXX - not pretty */
		break;
#endif

	case 'N': /* output extended reg name */
		printf("%s", rnames[getlr(p, '1')->n_rval]);
		break;

	case 'O': /* print out emulated ops */
		pr = 16;
		if (p->n_op == RS || p->n_op == LS) {
			llshft(p);
			break;
		} else if (p->n_op == MUL) {
			printf("\timull %%ecx, %%edx\n");
			printf("\timull %%eax, %%esi\n");
			printf("\taddl %%edx, %%esi\n");
			printf("\tmull %%ecx\n");
			printf("\taddl %%esi, %%edx\n");
			break;
		}
		expand(p, INCREG, "\tpushl UR\n\tpushl AR\n");
		expand(p, INCREG, "\tpushl UL\n\tpushl AL\n");
		if (p->n_op == DIV && p->n_type == ULONGLONG) ch = "udiv";
		else if (p->n_op == DIV) ch = "div";
		else if (p->n_op == MOD && p->n_type == ULONGLONG) ch = "umod";
		else if (p->n_op == MOD) ch = "mod";
		else ch = 0, comperr("ZO");
#ifdef ELFABI
		printf("\tcall " EXPREFIX "__%sdi3%s\n\taddl $%d,%s\n",
			ch, (kflag ? "@PLT" : ""), pr, rnames[ESP]);
#else
		printf("\tcall " EXPREFIX "__%sdi3\n\taddl $%d,%s\n",
			ch, pr, rnames[ESP]);
#endif
                break;

	case 'Q': /* emit struct assign (large structs) */
		/*
		 * Put out some combination of movs{b,w,l}
		 * esi/edi/ecx are available.
		 */
		expand(p, INAREG, "	leal AL,%edi\n");
		ap = attr_find(p->n_ap, ATTR_P2STRUCT);
		if (ap->iarg(0) < 32) {
			i = ap->iarg(0) >> 2;
			while (i) {
				expand(p, INAREG, "	movsl\n");
				i--;
			}
		} else {
			printf("\tmovl $%d,%%ecx\n", ap->iarg(0) >> 2);
			printf("	rep movsl\n");
		}
		if (ap->iarg(0) & 2)
			printf("	movsw\n");
		if (ap->iarg(0) & 1)
			printf("	movsb\n");
		break;

	case 'R': /* emit struct assign to NAME (small structs) */
		ap = attr_find(p->n_ap, ATTR_P2STRUCT);
		l = p->n_left;
		for (i = 0; i < ap->iarg(0); i += 4) {
			char buf[200];
			sprintf(buf, "\tmovl %d(%s),A1\n\tmovl A1,AL+%d\n", 
			    i, rnames[regno(p->n_right)],
			    (int)getlval(l)+i);
			expand(p, INAREG, buf);
		}
		break;

	case 'V': /* emit struct assign to OREG (small structs) */
		ap = attr_find(p->n_ap, ATTR_P2STRUCT);
		l = p->n_left;
		expand(p, INAREG, "	leal AL,A2\n");
		for (i = 0; i < ap->iarg(0); i += 4) {
			char buf[200];
			sprintf(buf, "\tmovl %d(%s),A1\n\tmovl A1,%d(%s)\n", 
			    i, rnames[regno(p->n_right)],
			    i, rnames[regno(&resc[2])]);
			expand(p, INAREG, buf);
		}
		break;

	case 'S': /* emit eventual move after cast from longlong */
		pr = DECRA(p->n_reg, 0);
		lr = p->n_left->n_rval;
		switch (p->n_type) {
#ifdef NOBREGS
		case CHAR:
		case UCHAR:
			/* Go via stack.  XXX - optimize */
			expand(p, INAREG, "\tmovl AL,A2\n");
			if (ISUNSIGNED(p->n_type))
				expand(p, INAREG, "\tmovzbl A2,A1\n");
			else
				expand(p, INAREG, "\tmovsbl A2,A1\n");
			break;
#else
		case CHAR:
		case UCHAR:
			if (rnames[pr][2] == 'l' && rnames[lr][2] == 'x' &&
			    rnames[pr][1] == rnames[lr][1])
				break;
			if (rnames[lr][2] == 'x') {
				printf("\tmovb %%%cl,%s\n",
				    rnames[lr][1], rnames[pr]);
				break;
			}
			/* Must go via stack */
			expand(p, INAREG, "\tmovl AL,A2\n");
			expand(p, INBREG, "\tmovb A2,A1\n");
#ifdef notdef
			/* cannot use freetemp() in instruction emission */
			s = freetemp(1);
			printf("\tmovl %%e%ci,%d(%%ebp)\n", rnames[lr][1], s);
			printf("\tmovb %d(%%ebp),%s\n", s, rnames[pr]);
#endif
			break;
#endif

		case SHORT:
		case USHORT:
			if (rnames[lr][1] == rnames[pr][2] &&
			    rnames[lr][2] == rnames[pr][3])
				break;
			printf("\tmovw %%%c%c,%%%s\n",
			    rnames[lr][1], rnames[lr][2], rnames[pr]+2);
			break;
		case INT:
		case UNSIGNED:
			if (rnames[lr][1] == rnames[pr][2] &&
			    rnames[lr][2] == rnames[pr][3])
				break;
			printf("\tmovl %%e%c%c,%s\n",
				    rnames[lr][1], rnames[lr][2], rnames[pr]);
			break;

		default:
			if (rnames[lr][1] == rnames[pr][2] &&
			    rnames[lr][2] == rnames[pr][3])
				break;
			comperr("SCONV2 %s->%s", rnames[lr], rnames[pr]);
			break;
		}
		break;

	case 'T': /* Print out 8-bit reg name for assign */
		switch (regno(getlr(p, 'R'))) {
		case EAX: ch = "%al"; break;
		case EBX: ch = "%bl"; break;
		case ECX: ch = "%cl"; break;
		case EDX: ch = "%dl"; break;
		default: ch = "ERROR"; break;
		}
		printf("%s", ch);
		break;

	case 'U': /* print a/h for right shift */
		printf("%c", ISUNSIGNED(p->n_type) ? 'h' : 'a');
		break;

	default:
		comperr("zzzcode %c", c);
	}
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
	comperr("flshape");
	return 0;
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
	printf("$" CONFMT, val);
}

void
conput(FILE *fp, NODE *p)
{
	int val = (int)getlval(p);

	switch (p->n_op) {
	case ICON:
		if (p->n_name[0] != '\0') {
			fprintf(fp, "%s", p->n_name);
			if (val)
				fprintf(fp, "+%d", val);
		} else
			fprintf(fp, "%d", val);
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

	size /= SZCHAR;
	switch (p->n_op) {
	case REG:
		printf("%%%s", &rnames[p->n_rval][3]);
		break;

	case NAME:
	case OREG:
		setlval(p, getlval(p) + size);
		adrput(stdout, p);
		setlval(p, getlval(p) - size);
		break;
	case ICON:
		printf("$" CONFMT, getlval(p) >> 32);
		break;
	default:
		comperr("upput bad op %d size %d", p->n_op, size);
	}
}

void
adrput(FILE *io, NODE *p)
{
	int r;
	/* output an address, with offsets, from p */

	switch (p->n_op) {

	case NAME:
		if (p->n_name[0] != '\0') {
			fputs(p->n_name, io);
			if (getlval(p) != 0)
				fprintf(io, "+" CONFMT, getlval(p));
		} else
			fprintf(io, CONFMT, getlval(p));
		return;

	case OREG:
		r = p->n_rval;
		if (p->n_name[0])
			printf("%s%s", p->n_name, getlval(p) ? "+" : "");
		if (getlval(p))
			fprintf(io, "%d", (int)getlval(p));
		if (R2TEST(r)) {
			fprintf(io, "(%s,%s,4)", rnames[R2UPK1(r)],
			    rnames[R2UPK2(r)]);
		} else
			fprintf(io, "(%s)", rnames[p->n_rval]);
		return;
	case ICON:
#ifdef PCC_DEBUG
		/* Sanitycheck for PIC, to catch adressable constants */
		if (kflag && p->n_name[0] && 0) {
			static int foo;

			if (foo++ == 0) {
				printf("\nfailing...\n");
				fwalk(p, e2print, 0);
				comperr("pass2 conput");
			}
		}
#endif
		/* addressable value of the constant */
		fputc('$', io);
		conput(io, p);
		return;

	case REG:
		switch (p->n_type) {
		case LONGLONG:
		case ULONGLONG:
			fprintf(io, "%%%c%c%c", rnames[p->n_rval][0],
			    rnames[p->n_rval][1], rnames[p->n_rval][2]);
			break;
		case SHORT:
		case USHORT:
			fprintf(io, "%%%s", &rnames[p->n_rval][2]);
			break;
		default:
			fprintf(io, "%s", rnames[p->n_rval]);
		}
		return;

	default:
		comperr("illegal address, op %d, node %p", p->n_op, p);
		return;

	}
}

static char *
ccbranches[] = {
	"je",		/* jumpe */
	"jne",		/* jumpn */
	"jle",		/* jumple */
	"jl",		/* jumpl */
	"jge",		/* jumpge */
	"jg",		/* jumpg */
	"jbe",		/* jumple (jlequ) */
	"jb",		/* jumpl (jlssu) */
	"jae",		/* jumpge (jgequ) */
	"ja",		/* jumpg (jgtru) */
};


/*   printf conditional and unconditional branches */
void
cbgen(int o, int lab)
{
	if (o < EQ || o > UGT)
		comperr("bad conditional branch: %s", opst[o]);
	printf("	%s " LABFMT "\n", ccbranches[o-EQ], lab);
}

static void
fixcalls(NODE *p, void *arg)
{

	/* Prepare for struct return by allocating bounce space on stack */
	switch (p->n_op) {
	case LS:
	case RS:
		if (p->n_type != LONGLONG && p->n_type != ULONGLONG)
			break;
		if (p->n_right->n_op == ICON) /* constants must be char */
			p->n_right->n_type = CHAR;
		break;
	}
}

/*
 * Must store floats in memory if there are two function calls involved.
 */
static int
storefloat(struct interpass *ip, NODE *p)
{
	int l, r;

	switch (optype(p->n_op)) {
	case BITYPE:
		l = storefloat(ip, p->n_left);
		r = storefloat(ip, p->n_right);
		if (p->n_op == CM)
			return 0; /* arguments, don't care */
		if (callop(p->n_op))
			return 1; /* found one */
#define ISF(p) ((p)->n_type == FLOAT || (p)->n_type == DOUBLE || \
	(p)->n_type == LDOUBLE)
		if (ISF(p->n_left) && ISF(p->n_right) && l && r) {
			/* must store one. store left */
			struct interpass *nip;
			TWORD t = p->n_left->n_type;
			NODE *ll;
			int off;

                	off = freetemp(szty(t));
                	ll = mklnode(OREG, off, FPREG, t);
			nip = ipnode(mkbinode(ASSIGN, ll, p->n_left, t));
			p->n_left = mklnode(OREG, off, FPREG, t);
                	DLIST_INSERT_BEFORE(ip, nip, qelem);
		}
		return l|r;

	case UTYPE:
		l = storefloat(ip, p->n_left);
		if (callop(p->n_op))
			l = 1;
		return l;
	default:
		return 0;
	}
}

static void
outfargs(struct interpass *ip, NODE **ary, int num, int *cwp, int c)
{
	struct interpass *ip2;
	NODE *q, *r;
	int i;

	for (i = 0; i < num; i++)
		if (XASMVAL(cwp[i]) == c && (cwp[i] & (XASMASG|XASMINOUT)))
			break;
	if (i == num)
		return;
	q = ary[i]->n_left;
	r = mklnode(REG, 0, c == 'u' ? 040 : 037, q->n_type);
	ary[i]->n_left = tcopy(r);
	ip2 = ipnode(mkbinode(ASSIGN, q, r, q->n_type));
	DLIST_INSERT_AFTER(ip, ip2, qelem);
}

static void
infargs(struct interpass *ip, NODE **ary, int num, int *cwp, int c)
{
	struct interpass *ip2;
	NODE *q, *r;
	int i;

	for (i = 0; i < num; i++)
		if (XASMVAL(cwp[i]) == c && (cwp[i] & XASMASG) == 0)
			break;
	if (i == num)
		return;
	q = ary[i]->n_left;
	q = (cwp[i] & XASMINOUT) ? tcopy(q) : q;
	r = mklnode(REG, 0, c == 'u' ? 040 : 037, q->n_type);
	if ((cwp[i] & XASMINOUT) == 0)
		ary[i]->n_left = tcopy(r);
	ip2 = ipnode(mkbinode(ASSIGN, r, q, q->n_type));
	DLIST_INSERT_BEFORE(ip, ip2, qelem);
}

/*
 * Extract float args to XASM and ensure that they are put on the stack
 * in correct order.
 * This should be done sow other way.
 */
static void
fixxfloat(struct interpass *ip, NODE *p)
{
	NODE *w, **ary;
	int nn, i, c, *cwp;

	nn = 1;
	w = p->n_left;
	if (w->n_op == ICON && w->n_type == STRTY)
		return;
	/* index all xasm args first */
	for (; w->n_op == CM; w = w->n_left)
		nn++;
	ary = tmpcalloc(nn * sizeof(NODE *));
	cwp = tmpcalloc(nn * sizeof(int));
	for (i = 0, w = p->n_left; w->n_op == CM; w = w->n_left) {
		ary[i] = w->n_right;
		cwp[i] = xasmcode(ary[i]->n_name);
		i++;
	}
	ary[i] = w;
	cwp[i] = xasmcode(ary[i]->n_name);
	for (i = 0; i < nn; i++)
		if (XASMVAL(cwp[i]) == 't' || XASMVAL(cwp[i]) == 'u')
			break;
	if (i == nn)
		return;

	for (i = 0; i < nn; i++) {
		c = XASMVAL(cwp[i]);
		if (c >= '0' && c <= '9')
			cwp[i] = (cwp[i] & ~0377) | XASMVAL(cwp[c-'0']);
	}
	infargs(ip, ary, nn, cwp, 'u');
	infargs(ip, ary, nn, cwp, 't');
	outfargs(ip, ary, nn, cwp, 't');
	outfargs(ip, ary, nn, cwp, 'u');
}

static NODE *
lptr(NODE *p)
{
	if (p->n_op == ASSIGN && p->n_right->n_op == REG &&
	    regno(p->n_right) == EBP)
		return p->n_right;
	if (p->n_op == FUNARG && p->n_left->n_op == REG &&
	    regno(p->n_left) == EBP)
		return p->n_left;
	return NIL;
}

/*
 * Find arg reg that should be struct reference instead.
 */
static void
updatereg(NODE *p, void *arg)
{
	NODE *q;

	if (p->n_op != STCALL)
		return;
#if defined(os_openbsd)
	struct attr *ap = attr_find(p->n_ap, ATTR_P2STRUCT);
	if (ap->iarg(0) == 1 || ap->iarg(0) == 2 || ap->iarg(0) == 4 || 
	    ap->iarg(0) == 8)
		return;
#endif
	if (attr_find(p->n_ap, ATTR_I386_FCMPLRET))
		return;

	if (p->n_right->n_op != CM)
		p = p->n_right;
	else for (p = p->n_right;
	    p->n_op == CM && p->n_left->n_op == CM; p = p->n_left)
		;
	if (p->n_op == CM) {
		if ((q = lptr(p->n_left)))
			;
		else
			q = lptr(p->n_right);
	} else
		q = lptr(p);
	if (q == NIL)
		comperr("bad STCALL hidden reg");

	/* q is now the hidden arg */
	q->n_op = MINUS;
	q->n_type = INCREF(CHAR);
	q->n_left = mklnode(REG, 0, EBP, INCREF(CHAR));
	q->n_right = mklnode(ICON, stkpos, 0, INT);
}

void
myreader(struct interpass *ipole)
{
	struct interpass *ip;

	stkpos = p2autooff;
	DLIST_FOREACH(ip, ipole, qelem) {
		if (ip->type != IP_NODE)
			continue;
		walkf(ip->ip_node, fixcalls, 0);
		storefloat(ip, ip->ip_node);
		if (ip->ip_node->n_op == XASM)
			fixxfloat(ip, ip->ip_node);
	}
	if (stkpos != p2autooff) {
		DLIST_FOREACH(ip, ipole, qelem) {
			if (ip->type != IP_NODE)
				continue;
			walkf(ip->ip_node, updatereg, 0);
		}
	}
	if (stkpos > p2autooff)
		p2autooff = stkpos;
	if (stkpos > p2maxautooff)
		p2maxautooff = stkpos;
	if (x2debug)
		printip(ipole);
}

/*
 * Remove some PCONVs after OREGs are created.
 */
static void
pconv2(NODE *p, void *arg)
{
	NODE *q;

	if (p->n_op == PLUS) {
		if (p->n_type == (PTR|SHORT) || p->n_type == (PTR|USHORT)) {
			if (p->n_right->n_op != ICON)
				return;
			if (p->n_left->n_op != PCONV)
				return;
			if (p->n_left->n_left->n_op != OREG)
				return;
			q = p->n_left->n_left;
			nfree(p->n_left);
			p->n_left = q;
			/*
			 * This will be converted to another OREG later.
			 */
		}
	}
}

void
mycanon(NODE *p)
{
	walkf(p, pconv2, 0);
}

void
myoptim(struct interpass *ip)
{
}

static char rl[] =
  { EAX, EAX, EAX, EAX, EAX, EDX, EDX, EDX, EDX, ECX, ECX, ECX, EBX, EBX, ESI };
static char rh[] =
  { EDX, ECX, EBX, ESI, EDI, ECX, EBX, ESI, EDI, EBX, ESI, EDI, ESI, EDI, EDI };

void
rmove(int s, int d, TWORD t)
{
	int sl, sh, dl, dh;

	switch (t) {
	case LONGLONG:
	case ULONGLONG:
#if 1
		sl = rl[s-EAXEDX];
		sh = rh[s-EAXEDX];
		dl = rl[d-EAXEDX];
		dh = rh[d-EAXEDX];

		/* sanity checks, remove when satisfied */
		if (memcmp(rnames[s], rnames[sl]+1, 3) != 0 ||
		    memcmp(rnames[s]+3, rnames[sh]+1, 3) != 0)
			comperr("rmove source error");
		if (memcmp(rnames[d], rnames[dl]+1, 3) != 0 ||
		    memcmp(rnames[d]+3, rnames[dh]+1, 3) != 0)
			comperr("rmove dest error");
#define	SW(x,y) { int i = x; x = y; y = i; }
		if (sh == dl) {
			/* Swap if overwriting */
			SW(sl, sh);
			SW(dl, dh);
		}
		if (sl != dl)
			printf("	movl %s,%s\n", rnames[sl], rnames[dl]);
		if (sh != dh)
			printf("	movl %s,%s\n", rnames[sh], rnames[dh]);
#else
		if (memcmp(rnames[s], rnames[d], 3) != 0)
			printf("	movl %%%c%c%c,%%%c%c%c\n",
			    rnames[s][0],rnames[s][1],rnames[s][2],
			    rnames[d][0],rnames[d][1],rnames[d][2]);
		if (memcmp(&rnames[s][3], &rnames[d][3], 3) != 0)
			printf("	movl %%%c%c%c,%%%c%c%c\n",
			    rnames[s][3],rnames[s][4],rnames[s][5],
			    rnames[d][3],rnames[d][4],rnames[d][5]);
#endif
		break;
#ifndef NOBREGS
	case CHAR:
	case UCHAR:
		printf("	movb %s,%s\n", rnames[s], rnames[d]);
		break;
#endif

	case FLOAT:
	case DOUBLE:
	case LDOUBLE:
#ifdef notdef
		/* a=b()*c(); will generate this */
		comperr("bad float rmove: %d %d", s, d);
#endif
		break;
	default:
		printf("	movl %s,%s\n", rnames[s], rnames[d]);
	}
}

/*
 * For class c, find worst-case displacement of the number of
 * registers in the array r[] indexed by class.
 */
int
COLORMAP(int c, int *r)
{
	int num;

	switch (c) {
	case CLASSA:
		num = r[CLASSB] > 4 ? 4 : r[CLASSB];
		num += 2*r[CLASSC];
		num += r[CLASSA];
		return num < 6;
#ifndef NOBREGS
	case CLASSB:
		num = r[CLASSA];
		num += 2*r[CLASSC];
		num += r[CLASSB];
		return num < 4;
#endif
	case CLASSC:
		num = r[CLASSA];
		num += r[CLASSB] > 4 ? 4 : r[CLASSB];
		num += 2*r[CLASSC];
		return num < 5;
	case CLASSD:
		return r[CLASSD] < DREGCNT;
	}
	return 0; /* XXX gcc */
}

char *rnames[] = {
	"%eax", "%edx", "%ecx", "%ebx", "%esi", "%edi", "%ebp", "%esp",
	"%al", "%ah", "%dl", "%dh", "%cl", "%ch", "%bl", "%bh",
	"eaxedx", "eaxecx", "eaxebx", "eaxesi", "eaxedi", "edxecx",
	"edxebx", "edxesi", "edxedi", "ecxebx", "ecxesi", "ecxedi",
	"ebxesi", "ebxedi", "esiedi",
	"%st0", "%st1", "%st2", "%st3", "%st4", "%st5", "%st6", "%st7",
};

/*
 * Return a class suitable for a specific type.
 */
int
gclass(TWORD t)
{
#ifndef NOBREGS
	if (t == CHAR || t == UCHAR)
		return CLASSB;
#endif
	if (t == LONGLONG || t == ULONGLONG)
		return CLASSC;
	if (t == FLOAT || t == DOUBLE || t == LDOUBLE)
		return CLASSD;
	return CLASSA;
}

/*
 */
void
lastcall(NODE *p)
{
}

/*
 * Special shapes.
 */
int
special(NODE *p, int shape)
{
	struct attr *ap;
	int o = p->n_op;

	switch (shape) {
	case SHSTR:
		ap = attr_find(p->n_ap, ATTR_P2STRUCT);
		if (ap->iarg(0) <= 16 && (ap->iarg(0) & 3) == 0)
			return o != REG ? SRREG : SRDIR;
		break;
	case SFUNCALL:
		if (o == STCALL || o == USTCALL)
			return SRREG;
		break;
	case SPCON:
		if (o != ICON || p->n_name[0] ||
		    getlval(p) < 0 || getlval(p) > 0x7fffffff)
			break;
		return SRDIR;
	case SMIXOR:
		return tshape(p, SZERO);
	case SMILWXOR:
		if (o != ICON || p->n_name[0] ||
		    getlval(p) == 0 || getlval(p) & 0xffffffff)
			break;
		return SRDIR;
	case SMIHWXOR:
		if (o != ICON || p->n_name[0] ||
		     getlval(p) == 0 || (getlval(p) >> 32) != 0)
			break;
		return SRDIR;
	}
	return SRNOPE;
}

/*
 * Target-dependent command-line options.
 */
void
mflags(char *str)
{
#define	MSET(s,a) if (strcmp(str, s) == 0) \
	msettings = (msettings & ~MCPUMSK) | a

	MSET("arch=i386",MI386);
	MSET("arch=i486",MI486);
	MSET("arch=i586",MI586);
	MSET("arch=i686",MI686);
}

/*
 * Do something target-dependent for xasm arguments.
 */
int
myxasm(struct interpass *ip, NODE *p)
{
	struct interpass *ip2;
	int Cmax[] = { 31, 63, 127, 0xffff, 3, 255 };
	NODE *in = 0, *ut = 0;
	TWORD t;
	char *w;
	int reg;
	int c, cw;
	CONSZ v;

	cw = xasmcode(p->n_name);
	if (cw & (XASMASG|XASMINOUT))
		ut = p->n_left;
	if ((cw & XASMASG) == 0)
		in = p->n_left;

	c = XASMVAL(cw);
	switch (c) {
	case 'D': reg = EDI; break;
	case 'S': reg = ESI; break;
	case 'a': reg = EAX; break;
	case 'b': reg = EBX; break;
	case 'c': reg = ECX; break;
	case 'd': reg = EDX; break;

	case 't':
	case 'u':
		p->n_name = tmpstrdup(p->n_name);
		w = strchr(p->n_name, XASMVAL(cw));
		*w = 'r'; /* now reg */
		return 1;

	case 'A': reg = EAXEDX; break;
	case 'q': {
		/* Set edges in MYSETXARG */
		if (p->n_left->n_op == REG || p->n_left->n_op == TEMP)
			return 1;
		t = p->n_left->n_type;
		if (in && ut)
			in = tcopy(in);
		p->n_left = mklnode(TEMP, 0, p2env.epp->ip_tmpnum++, t);
		if (ut) {
			ip2 = ipnode(mkbinode(ASSIGN, ut, tcopy(p->n_left), t));
			DLIST_INSERT_AFTER(ip, ip2, qelem);
		}
		if (in) {
			ip2 = ipnode(mkbinode(ASSIGN, tcopy(p->n_left), in, t));
			DLIST_INSERT_BEFORE(ip, ip2, qelem);
		}
		return 1;
	}

	case 'I':
	case 'J':
	case 'K':
	case 'L':
	case 'M':
	case 'N':
		if (p->n_left->n_op != ICON) {
			if ((c = XASMVAL1(cw)) != 0) {
				p->n_name++;
				return 0; /* Try again */
			}
			uerror("xasm arg not constant");
		}
		v = getlval(p->n_left);
		if ((c == 'K' && v < -128) ||
		    (c == 'L' && v != 0xff && v != 0xffff) ||
		    (c != 'K' && v < 0) ||
		    (v > Cmax[c-'I']))
			uerror("xasm val out of range");
		p->n_name = "i";
		return 1;

	default:
		return 0;
	}
	/* If there are requested either memory or register, delete memory */
	w = p->n_name = tmpstrdup(p->n_name);
	if (*w == '=')
		w++;
	*w++ = 'r';
	*w = 0;

	t = p->n_left->n_type;
	if (reg == EAXEDX) {
		;
	} else {
		if (t == CHAR || t == UCHAR) {
			reg = reg * 2 + 8;
		}
	}
	if (t == FLOAT || t == DOUBLE || t == LDOUBLE) {
		reg += 037;
	}

	if (in && ut)
		in = tcopy(in);
	p->n_left = mklnode(REG, 0, reg, t);
	if (ut) {
		ip2 = ipnode(mkbinode(ASSIGN, ut, tcopy(p->n_left), t));
		DLIST_INSERT_AFTER(ip, ip2, qelem);
	}
	if (in) {
		ip2 = ipnode(mkbinode(ASSIGN, tcopy(p->n_left), in, t));
		DLIST_INSERT_BEFORE(ip, ip2, qelem);
	}
	return 1;
}

void
targarg(char *w, void *arg)
{
	NODE **ary = arg;
	NODE *p, *q;

	if (ary[(int)w[1]-'0'] == 0)
		p = ary[(int)w[1]-'0'-1]->n_left; /* XXX */
	else
		p = ary[(int)w[1]-'0']->n_left;
	if (optype(p->n_op) != LTYPE)
		comperr("bad xarg op %d", p->n_op);
	q = tcopy(p);
	if (q->n_op == REG) {
		if (*w == 'k') {
			q->n_type = INT;
		} else if (*w != 'w') {
			if (q->n_type > UCHAR) {
				regno(q) = regno(q)*2+8;
				if (*w == 'h')
					regno(q)++;
			}
			q->n_type = INT;
		} else
			q->n_type = SHORT;
	}
	adrput(stdout, q);
	tfree(q);
}

/*
 * target-specific conversion of numeric arguments.
 */
int
numconv(void *ip, void *p1, void *q1)
{
	NODE *p = p1, *q = q1;
	int cw = xasmcode(q->n_name);

	switch (XASMVAL(cw)) {
	case 'a':
	case 'b':
	case 'c':
	case 'd':
		p->n_name = tmpcalloc(2);
		p->n_name[0] = (char)XASMVAL(cw);
		return 1;
	default:
		return 0;
	}
}

static struct {
	char *name; int num;
} xcr[] = {
	{ "eax", EAX },
	{ "ebx", EBX },
	{ "ecx", ECX },
	{ "edx", EDX },
	{ "esi", ESI },
	{ "edi", EDI },
	{ "ax", EAX },
	{ "bx", EBX },
	{ "cx", ECX },
	{ "dx", EDX },
	{ NULL, 0 },
};

/*
 * Check for other names of the xasm constraints registers.
 */

/*
 * Check for other names of the xasm constraints registers.
 */
int xasmconstregs(char *s)
{
	int i;

	if (strncmp(s, "st", 2) == 0) {
		int off =0;
		if (s[2] == '(' && s[4] == ')')
			off = s[3] - '0';
		return ESIEDI + 1 + off;
	}

	for (i = 0; xcr[i].name; i++)
		if (strcmp(xcr[i].name, s) == 0)
			return xcr[i].num;
	return -1;
}

