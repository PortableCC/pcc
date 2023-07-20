/*      $Id$    */

 /*
 * Copyright (c) 2020 Puresoftware Ltd.
 *
 * Permission to use, copy, modify, and distribute this software for any
 * purpose with or without fee is hereby granted, provided that the above
 * copyright notice and this permission notice appear in all copies.
 *
 * THE SOFTWARE IS PROVIDED "AS IS" AND THE AUTHOR DISCLAIMS ALL WARRANTIES
 * WITH REGARD TO THIS SOFTWARE INCLUDING ALL IMPLIED WARRANTIES OF
 * MERCHANTABILITY AND FITNESS. IN NO EVENT SHALL THE AUTHOR BE LIABLE FOR
 * ANY SPECIAL, DIRECT, INDIRECT, OR CONSEQUENTIAL DAMAGES OR ANY DAMAGES
 * WHATSOEVER RESULTING FROM LOSS OF USE, DATA OR PROFITS, WHETHER IN AN
 * ACTION OF CONTRACT, NEGLIGENCE OR OTHER TORTIOUS ACTION, ARISING OUT OF
 * OR IN CONNECTION WITH THE USE OR PERFORMANCE OF THIS SOFTWARE.
 */

#include <assert.h>
#include <ctype.h>
#include <string.h>
#include <stdlib.h>

#include "pass2.h"

extern void defalign(int);

int isConverstion=0;
int addStack=0;
#define	exname(x) x

/*
In a 32-bit context,registers are specified by using w0-w30 in A64 instruction set
*/
char *wnames[] = {
	"w0", "w1", "w2", "w3","w4","w5", "w6", "w7",
	"w8", "w9", "w10","w11","w12","w13","w14",
	"w15", "w16","w17","w18","w19","w20", "w21",
	"w22","w23","w24","w25","w26","w27","w28",
	"w29","w30",
};

/*
In a 64-bit context,registers are specified by using x0-x30 in A64 instruction set
*/
char *rnames[] = {
	"x0", "x1", "x2", "x3","x4","x5", "x6", "x7",
	"x8", "x9", "x10","x11","x12","x13","x14", 
	"x15", "x16","x17","x18","x19","x20", "x21",
	"x22","x23","x24","x25","x26","x27","x28",
	"x29","x30","sp",
};

/*
 * Handling of integer constants.  We have 8 bits + an even
 * number of rotates available as a simple immediate.
 * If a constant isn't trivially representable, use an ldr
 * and a subsequent sequence of orr operations.
 */

static int
trepresent(const unsigned int val)
{
	int i;
#define rotate_left(v, n) (v << n | v >> (32 - n))

	for (i = 0; i < 32; i += 2)
		if (rotate_left(val, i) <= 0xff)
			return 1;
	return 0;
}

/*
 * Return values are:
 * 0 - output constant as is (should be covered by trepresent() above)
 * 1 - 4 generate 1-4 instructions as needed.
 */
static int
encode_constant(int constant, int *values)
{
	int tmp = constant;
	int i = 0;
	int first_bit, value;

	while (tmp) {
		first_bit = ffs(tmp);
		first_bit -= 1; /* ffs indexes from 1, not 0 */
		first_bit &= ~1; /* must use even bit offsets */

		value = tmp & (0xff << first_bit);
		values[i++] = value;
		tmp &= ~value;
	}
	return i;
}

/*
 * Use W registers to load value in 32-bit context 
 */
static void
load_constant_into_reg(int reg, int v)
{
	printf("\tmov %s,#%d\n", wnames[reg], v);
}

/*
 * Use X registers to load value in 64-bit context
 */
static void
load_64constant_into_reg(int reg, long long v)
{
	printf("\tmov %s,#%lld\n", rnames[reg], v);
}

static TWORD ftype;

/*
 * calculate stack size and offsets
 */
static int
offcalc(struct interpass_prolog *ipp)
{
	int addto;

#ifdef PCC_DEBUG
	if (x2debug)
		printf("offcalc: p2maxautooff=%d\n", p2maxautooff);
#endif

	addto = p2maxautooff;

#ifdef PCC_DEBUG
	if (x2debug)
		printf("offcalc: addto=%d\n", addto);
#endif

	addto -= AUTOINIT / SZCHAR;

	return addto;
}

void
prologue(struct interpass_prolog *ipp)
{
        int addto;
        int vals[4], nc, i;

#ifdef PCC_DEBUG
	if (x2debug)
		printf("prologue: type=%d, lineno=%d, name=%s, vis=%d, ipptype=%d, autos=%d, tmpnum=%d, lblnum=%d\n",
			ipp->ipp_ip.type,
			ipp->ipp_ip.lineno,
			ipp->ipp_name,
			ipp->ipp_flags,
			ipp->ipp_type,
			ipp->ipp_autos,
			ipp->ip_tmpnum,
			ipp->ip_lblnum);
#endif

	ftype = ipp->ipp_type;
        printf("%s:\n", exname(ipp->ipp_name));
        addto = offcalc(ipp);
        if (addto < 64){
		addto = 64;       
        }
        if((addto % 16)){
                addto = addto + (16 - (addto % 16));
        }
        if (trepresent(addto)) {
                printf("\tsub %s,%s,#%d\n", rnames[SP], rnames[SP], addto);
        } else {
                nc = encode_constant(addto, vals);
                for (i = 0; i < nc; i++)
                        printf("\tsub %s,%s,#%d\n",
                            rnames[SP], rnames[SP], vals[i]);
        }
        printf("\tstp %s,%s,[%s]\n", rnames[FP],rnames[LR],rnames[SP]);
        printf("\tmov %s,%s\n", rnames[FP], rnames[SP]);
        addStack=addto;
}

void
eoftn(struct interpass_prolog *ipp)
{
	if (ipp->ipp_ip.ip_lbl == 0)
		return; /* no code needs to be generated */

	/* struct return needs special treatment */
	if (ftype == STRTY || ftype == UNIONTY) {
		assert(0);
	} else {
                if (addStack == 0){
                        printf("\tldp %s,%s,[%s],#%d \n", rnames[FP], rnames[LR],
                                rnames[SP], 64);
                        printf("\tadd %s,%s,#%d\n", rnames[SP], rnames[SP], 64);
                }
                else{
                        printf("\tldp %s,%s,[%s] \n", rnames[FP], rnames[LR],
                                rnames[SP]);
                        printf("\tadd %s,%s,%d\n", rnames[SP], rnames[SP], addStack);
                }
	}
	printf("\tret\n");
	printf("\t.size %s,.-%s\n", exname(ipp->ipp_name),
	    exname(ipp->ipp_name));
}


/*
 * these mnemonics match the order of the preprocessor decls
 * EQ, NE, LE, LT, GE, GT, ULE, ULT, UGE, UGT
 */

static char *
ccbranches[] = {
	"b.eq",		/* branch if equal */
	"b.ne",		/* branch if not-equal */
	"b.le",		/* branch if less-than-or-equal */
	"b.lt",		/* branch if less-than */
	"b.ge",		/* branch if greater-than-or-equal */
	"b.gt",		/* branch if greater-than */
	/* what should these be ? */
	"b.ls",		/* branch if lower-than-or-same */
	"b.lo",		/* branch if lower-than */
	"b.hs",		/* branch if higher-than-or-same */
	"b.hi",		/* branch if higher-than */
};

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
			str = "orr";
			break;
		case ER:
			str = "eor";
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
			return(SZINT/SZCHAR);

		case ULONG:
		case LONG:
		case LONGLONG:
		case ULONGLONG:
			return SZLONGLONG/SZCHAR;
		default:
			if (!ISPTR(p->n_type))
				comperr("tlen type %d not pointer");
			return SZPOINT(p->n_type)/SZCHAR;
	}
}

int
fldexpand(NODE *p, int cookie, char **cp)
{
	CONSZ val;
	int shft;

        if (p->n_op == ASSIGN)
                p = p->n_left;

	if (features(FEATURE_BIGENDIAN))
		shft = SZINT - UPKFSZ(p->n_rval) - UPKFOFF(p->n_rval);
	else
		shft = UPKFOFF(p->n_rval);

        switch (**cp) {
	        case 'S':
        	        printf("#%d", UPKFSZ(p->n_rval));
                	break;
	        case 'H':
        	        printf("#%d", shft);
                	break;
	        case 'M':
        	case 'N':
                	val = (CONSZ)1 << UPKFSZ(p->n_rval);
 	               --val;
        	        val <<= shft;
                	printf("%lld", (**cp == 'M' ? val : ~val)  & 0xffffffff);
 	               break;
       		default:
                	comperr("fldexpand");
        }
        return 1;
}


/*
 * Structure assignment.
 */
static void
stasg(NODE *p)
{
	NODE *l = p->n_left;
	int val = getlval(l);

	/* R0 = dest, R1 = src, R2 = len */
	load_constant_into_reg(R2, attr_find(p->n_ap, ATTR_P2STRUCT)->iarg(0));
	if (l->n_op == OREG) {
		if (R2TEST(regno(l))) {
			int r = regno(l);
			printf("\tadd %s,%s,lsl #%d\n",
			    rnames[R0], rnames[R2UPK2(r)], R2UPK3(r)+1);
			printf("\tadd %s,%s,%s\n", rnames[R0], rnames[R0],
			    rnames[R2UPK1(r)]);
		} else  {
			if (trepresent(val)) {
				printf("\tadd %s,%s,#%d\n",
				    rnames[R0], rnames[regno(l)], val);
			} else {
				load_constant_into_reg(R0, val);
				printf("\tadd %s,%s,%s\n", rnames[R0],
				    rnames[R0], rnames[regno(l)]);
			}
		}
	} else if (l->n_op == NAME) {
		cerror("not implemented");
	}

	printf("\tbl %s\n", exname("memcpy"));
}

/*
 * http://gcc.gnu.org/onlinedocs/gccint/Soft-float-library-routines.html#Soft-float-library-routines
 */
static void
fpemul(NODE *p)
{
	NODE *l = p->n_left;
	char *ch = NULL;

	if (p->n_op == PLUS && p->n_type == FLOAT) ch = "addsf3";
	else if (p->n_op == PLUS && p->n_type == DOUBLE) ch = "adddf3";
	else if (p->n_op == PLUS && p->n_type == LDOUBLE) ch = "adddf3";

	else if (p->n_op == MINUS && p->n_type == FLOAT) ch = "subsf3";
	else if (p->n_op == MINUS && p->n_type == DOUBLE) ch = "subdf3";
	else if (p->n_op == MINUS && p->n_type == LDOUBLE) ch = "subdf3";

	else if (p->n_op == MUL && p->n_type == FLOAT) ch = "mulsf3";
	else if (p->n_op == MUL && p->n_type == DOUBLE) ch = "muldf3";
	else if (p->n_op == MUL && p->n_type == LDOUBLE) ch = "muldf3";

	else if (p->n_op == DIV && p->n_type == FLOAT) ch = "divsf3";
	else if (p->n_op == DIV && p->n_type == DOUBLE) ch = "divdf3";
	else if (p->n_op == DIV && p->n_type == LDOUBLE) ch = "divdf3";

	else if (p->n_op == UMINUS && p->n_type == FLOAT) ch = "negsf2";
	else if (p->n_op == UMINUS && p->n_type == DOUBLE) ch = "negdf2";
	else if (p->n_op == UMINUS && p->n_type == LDOUBLE) ch = "negdf2";

	else if (p->n_op == EQ && l->n_type == FLOAT) ch = "eqsf2";
	else if (p->n_op == EQ && l->n_type == DOUBLE) ch = "eqdf2";
	else if (p->n_op == EQ && l->n_type == LDOUBLE) ch = "eqdf2";

	else if (p->n_op == NE && l->n_type == FLOAT) ch = "nesf2";
	else if (p->n_op == NE && l->n_type == DOUBLE) ch = "nedf2";
	else if (p->n_op == NE && l->n_type == LDOUBLE) ch = "nedf2";

	else if (p->n_op == GE && l->n_type == FLOAT) ch = "gesf2";
	else if (p->n_op == GE && l->n_type == DOUBLE) ch = "gedf2";
	else if (p->n_op == GE && l->n_type == LDOUBLE) ch = "gedf2";

	else if (p->n_op == LE && l->n_type == FLOAT) ch = "lesf2";
	else if (p->n_op == LE && l->n_type == DOUBLE) ch = "ledf2";
	else if (p->n_op == LE && l->n_type == LDOUBLE) ch = "ledf2";

	else if (p->n_op == GT && l->n_type == FLOAT) ch = "gtsf2";
	else if (p->n_op == GT && l->n_type == DOUBLE) ch = "gtdf2";
	else if (p->n_op == GT && l->n_type == LDOUBLE) ch = "gtdf2";

	else if (p->n_op == LT && l->n_type == FLOAT) ch = "ltsf2";
	else if (p->n_op == LT && l->n_type == DOUBLE) ch = "ltdf2";
	else if (p->n_op == LT && l->n_type == LDOUBLE) ch = "ltdf2";

	else if (p->n_op == SCONV && p->n_type == FLOAT) {
		if (l->n_type == DOUBLE) ch = "truncdfsf2";
		else if (l->n_type == LDOUBLE) ch = "truncdfsf2";
		else if (l->n_type == ULONGLONG) ch = "floatunsdisf";
		else if (l->n_type == LONGLONG) ch = "floatdisf";
		else if (l->n_type == LONG) ch = "floatsisf";
		else if (l->n_type == ULONG) ch = "floatunsisf";
		else if (l->n_type == INT) ch = "floatsisf";
		else if (l->n_type == UNSIGNED) ch = "floatunsisf";
	} else if (p->n_op == SCONV && p->n_type == DOUBLE) {
		if (l->n_type == FLOAT) ch = "extendsfdf2";
		else if (l->n_type == LDOUBLE) ch = "trunctfdf2";
		else if (l->n_type == ULONGLONG) ch = "floatunsdidf";
		else if (l->n_type == LONGLONG) ch = "floatdidf";
		else if (l->n_type == LONG) ch = "floatsidf";
		else if (l->n_type == ULONG) ch = "floatunsidf";
		else if (l->n_type == INT) ch = "floatsidf";
		else if (l->n_type == UNSIGNED) ch = "floatunsidf";
	} else if (p->n_op == SCONV && p->n_type == LDOUBLE) {
		if (l->n_type == FLOAT) ch = "extendsfdf2";
		else if (l->n_type == DOUBLE) ch = "extenddftd2";
		else if (l->n_type == ULONGLONG) ch = "floatunsdidf";
		else if (l->n_type == LONGLONG) ch = "floatdidf";
		else if (l->n_type == LONG) ch = "floatsidf";
		else if (l->n_type == ULONG) ch = "floatunsidf";
		else if (l->n_type == INT) ch = "floatsidf";
		else if (l->n_type == UNSIGNED) ch = "floatunsidf";
	} else if (p->n_op == SCONV && p->n_type == ULONGLONG) {
		if (l->n_type == FLOAT) ch = "fixunssfdi";
		else if (l->n_type == DOUBLE) ch = "fixunsdfdi";
		else if (l->n_type == LDOUBLE) ch = "fixunsdfdi";
	} else if (p->n_op == SCONV && p->n_type == LONGLONG) {
		if (l->n_type == FLOAT) ch = "fixsfdi";
		else if (l->n_type == DOUBLE) ch = "fixdfdi";
		else if (l->n_type == LDOUBLE) ch = "fixdfdi";
	} else if (p->n_op == SCONV && p->n_type == LONG) {
		if (l->n_type == FLOAT) ch = "fixsfsi";
		else if (l->n_type == DOUBLE) ch = "fixdfsi";
		else if (l->n_type == LDOUBLE) ch = "fixdfsi";
	} else if (p->n_op == SCONV && p->n_type == ULONG) {
		if (l->n_type == FLOAT) ch = "fixunssfdi";
		else if (l->n_type == DOUBLE) ch = "fixunsdfdi";
		else if (l->n_type == LDOUBLE) ch = "fixunsdfdi";
	} else if (p->n_op == SCONV && p->n_type == INT) {
		if (l->n_type == FLOAT) ch = "fixsfsi";
		else if (l->n_type == DOUBLE) ch = "fixdfsi";
		else if (l->n_type == LDOUBLE) ch = "fixdfsi";
	} else if (p->n_op == SCONV && p->n_type == UNSIGNED) {
		if (l->n_type == FLOAT) ch = "fixunssfsi";
		else if (l->n_type == DOUBLE) ch = "fixunsdfsi";
		else if (l->n_type == LDOUBLE) ch = "fixunsdfsi";
	}

	if (ch == NULL) comperr("ZF: op=0x%x (%d)\n", p->n_op, p->n_op);

	printf("\tbl __%s" COM "softfloat operation\n", exname(ch));

	if (p->n_op >= EQ && p->n_op <= GT)
		printf("\tcmp %s,#0\n", rnames[R0]);
}


/*
 * http://gcc.gnu.org/onlinedocs/gccint/Integer-library-routines.html#Integer-library-routines
 */

static void
emul(NODE *p)
{
	char *ch = NULL;

	if (p->n_op == LS && DEUNSIGN(p->n_type) == LONGLONG) ch = "ashldi3";
	else if (p->n_op == LS && DEUNSIGN(p->n_type) == LONG) ch = "ashlsi3";
	else if (p->n_op == LS && DEUNSIGN(p->n_type) == INT) ch = "ashlsi3";

	else if (p->n_op == RS && p->n_type == ULONGLONG) ch = "lshrdi3";
	else if (p->n_op == RS && p->n_type == ULONG) ch = "lshrsi3";
	else if (p->n_op == RS && p->n_type == UNSIGNED) ch = "lshrsi3";

	else if (p->n_op == RS && p->n_type == LONGLONG) ch = "ashrdi3";
	else if (p->n_op == RS && p->n_type == LONG) ch = "ashrsi3";
	else if (p->n_op == RS && p->n_type == INT) ch = "ashrsi3";
	
	else if (p->n_op == MUL && p->n_type == LONGLONG) ch = "muldi3";
	else if (p->n_op == MUL && p->n_type == LONG) ch = "mulsi3";
	else if (p->n_op == MUL && p->n_type == INT) ch = "mulsi3";

	else if (p->n_op == UMINUS && p->n_type == LONGLONG) ch = "negdi2";
	else if (p->n_op == UMINUS && p->n_type == LONG) ch = "negsi2";
	else if (p->n_op == UMINUS && p->n_type == INT) ch = "negsi2";

	else ch = 0, comperr("ZE");
	printf("\tbl __%s" COM "emulated operation\n", exname(ch));
}

static void
halfword(NODE *p)
{
	NODE *r = getlr(p, 'R');
	NODE *l = getlr(p, 'L');
	int idx0 = 0;
	CONSZ lval;

	if (features(FEATURE_BIGENDIAN)) {
		idx0 = 1;
	}

	if (p->n_op == ASSIGN && r->n_op == OREG) {
                /* load */
		lval = getlval(r);
		expand(p, 0, "\tldrh A1,");
		printf("[%s,#" CONFMT "]\n", rnames[r->n_rval], lval+idx0);
        } else if (p->n_op == ASSIGN && l->n_op == OREG) {
                /* store */
		lval = getlval(l);
		expand(p, 0, "\tstrh AR,");
		printf("[%s,#" CONFMT "]\n", rnames[l->n_rval], lval+idx0);
        } else if (p->n_op == SCONV || p->n_op == UMUL) {
                /* load */
		lval = getlval(l);
		expand(p, 0, "\tldrh A1,");
		printf("[%s,#" CONFMT "]\n", rnames[l->n_rval], lval+idx0);
        } else if (p->n_op == NAME || p->n_op == ICON || p->n_op == OREG) {
                /* load */
		lval = getlval(p);
		switch (p->n_type) {
			case SHORT:
				expand(p, 0, "\tldrsh A1,");
				break;
			default:
				expand(p, 0, "\tldrh A1,");
		}
		printf("[%s,#" CONFMT "]\n", rnames[p->n_rval], lval+idx0);
	} else {
		comperr("halfword");
	}
}

static void
bfext(NODE *p)
{
	int sz;
	if (ISUNSIGNED(p->n_right->n_type))
		return;
	sz = 32 - UPKFSZ(p->n_left->n_rval);
	expand(p, 0, "\tmov AD,AD,lsl ");
	printf("#%d\n", sz);
	expand(p, 0, "\tmov AD,AD,lsr ");
	printf("#%d\n", sz);
}

static int
argsiz(NODE *p)
{
	TWORD t = p->n_type;

	if (t < LONGLONG || t == FLOAT || t > BTMASK)
		return 4;
	if (t == LONGLONG || t == ULONGLONG || t == LONG || t == ULONG )
		return 8;
	if (t == DOUBLE || t == LDOUBLE)
		return 8;
	if (t == STRTY || t == UNIONTY)
		return attr_find(p->n_ap, ATTR_P2STRUCT)->iarg(0);
	comperr("argsiz");
	return 0;
}

void
zzzcode(NODE *p, int c)
{
	int pr;

	switch (c) {
		case 'B': /* bit-field sign extension */
			bfext(p);
			break;

		case 'C':  /* remove from stack after subroutine call */
			pr = p->n_qual;
			if (p->n_op == UCALL)
				return; /* XXX remove ZC from UCALL */
			if (pr > 0)
				printf("\tadd %s,%s,#%d\n", rnames[SP], rnames[SP], pr);
			break;
	        case 'D':
			isConverstion= 1;
                	break;
		case 'E': /* print out emulated ops */
			emul(p);
                	break;

		case 'F': /* print out emulated floating-point ops */
			fpemul(p);
			break;

		case 'H':		/* do halfword access */
			halfword(p);
			break;

		case 'I':		/* init constant */
			if (p->n_name[0] != '\0')
				comperr("named init");
			load_constant_into_reg(DECRA(p->n_reg, 1),
			    getlval(p) & 0xffffffff);
        		break;
		case 'J':		/* init longlong constant */
			load_64constant_into_reg(DECRA(p->n_reg, 1)-R16,
			    getlval(p) & 0xffffffffffffffff);
			break;

		case 'Q': /* emit struct assign */
			stasg(p);
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

/*
 * Does the bitfield shape match?
 */
int
flshape(NODE *p)
{
	int o = p->n_op;

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
}

void
adrcon(CONSZ val)
{
	printf("#" CONFMT, val);
}

void
conput(FILE *fp, NODE *p)
{
	char *s;
	int val = getlval(p);

	switch (p->n_op) {
		case ICON:
#ifdef notdef	/* ICON cannot ever use sp here */
		/* If it does, it's a giant bug */
			if (p->n_sp == NULL || (
			   (p->n_sp->sclass == STATIC && p->n_sp->slevel > 0)))
				s = p->n_name;
			else
				s = exname(p->n_name);
#else
			s = p->n_name;
#endif		
			if (*s != '\0') {
				fprintf(fp, "%s", s);
				if (val > 0)
					fprintf(fp, "+%d", val);
				else if (val < 0)
					fprintf(fp, "-%d", -val);
			} else
				fprintf(fp, "#" CONFMT, (CONSZ)val);
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
			printf("%s", rnames[p->n_rval-R16+1]);
			break;

		case NAME:
		case OREG:
			setlval(p, getlval(p) + size);
			adrput(stdout, p);
			setlval(p, getlval(p) - size);
			break;
		case ICON:
			printf("#" CONFMT, getlval(p) >> 32);
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

	if (p->n_op == FLD)
		p = p->n_left;
	switch (p->n_op) {
		case NAME:
			if (p->n_name[0] != '\0') {
				fputs(p->n_name, io);
				if (getlval(p) != 0)
					fprintf(io, "+%lld", getlval(p));
			} else
				fprintf(io, "#" CONFMT, getlval(p));
			return;

		case OREG:
			r = p->n_rval;
                	if (R2TEST(r))
				fprintf(io, "[%s, %s, lsl #%d]",rnames[R2UPK1(r)],rnames[R2UPK2(r)],R2UPK3(r));
			else
				fprintf(io, "[%s,#%d]", rnames[p->n_rval], (int)getlval(p));
			return;

		case ICON:
			/* addressable value of the constant */
			conput(io, p);
			return;
	
		case REG:
			switch (p->n_type) {
				case CHAR:
				case UCHAR:
				case INT:
				case SHORT:
				case USHORT:
				case BOOL:
				case UNSIGNED:
					if (!ISPTR(p->n_type)) {
						if (isConverstion) {
							fprintf(io, "%s", wnames[0]);
							isConverstion = 0;
						}
						else
							fprintf(io, "%s", wnames[p->n_rval]);
					}
					else
						fprintf(io, "%s", rnames[p->n_rval]);
					break;
				case DOUBLE:
				case LDOUBLE:
					if (features(FEATURE_HARDFLOAT)) {
						fprintf(io, "%s", rnames[p->n_rval]);
						break;
					}
					/* FALLTHROUGH */
				case LONGLONG:
				case ULONGLONG:
					fprintf(io, "%s", rnames[p->n_rval-R16]);
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

/*   printf conditional and unconditional branches */
void
cbgen(int o, int lab)
{
	if (o < EQ || o > UGT)
		comperr("bad conditional branch: %s", opst[o]);
	printf("\t%s " LABFMT COM "conditional branch\n",
	    ccbranches[o-EQ], lab);
}

/*
 * The arm can only address 4k to get a NAME, so there must be some
 * rewriting here.  Strategy:
 * For first 1000 nodes found, print out the word directly.
 * For the following 1000 nodes, group them together in asm statements
 * and create a jump over.
 * For the last <1000 statements, print out the words last.
 */
struct addrsymb {
	SLIST_ENTRY(addrsymb) link;
	char *name;	/* symbol name */
	int num;	/* symbol offset */
	char *str;	/* replace label */
};
SLIST_HEAD(, addrsymb) aslist;
static struct interpass *ipbase;
static int prtnumber, nodcnt, notfirst;
#define	PRTLAB	".LY%d"	/* special for here */

static struct interpass *
anode(char *p)
{
	extern int thisline;
	struct interpass *ip = tmpalloc(sizeof(struct interpass));

	ip->ip_asm = p;
	ip->type = IP_ASM;
	ip->lineno = thisline;
	return ip;
}

static void
flshlab(void)
{
	struct interpass *ip;
	struct addrsymb *el;
	int lab = prtnumber++;
	char *c;

	if (SLIST_FIRST(&aslist) == NULL)
		return;

	snprintf(c = tmpalloc(32), 32, "\tb " PRTLAB "\n", lab);
	ip = anode(c);
	DLIST_INSERT_BEFORE(ipbase, ip, qelem);

	SLIST_FOREACH(el, &aslist, link) {
		/* insert each node as asm */
		int l = 32+strlen(el->name);
		c = tmpalloc(l);
		if (el->num)
			snprintf(c, l, "%s:\n\t.dword %s+%d\n",
			    el->str, el->name, el->num);
		else
			snprintf(c, l, "%s:\n\t.dword %s\n", el->str, el->name);
		ip = anode(c);
		DLIST_INSERT_BEFORE(ipbase, ip, qelem);
	}
	/* generate asm label */
	snprintf(c = tmpalloc(32), 32, PRTLAB ":\n", lab);
	ip = anode(c);
	DLIST_INSERT_BEFORE(ipbase, ip, qelem);
}

static void
prtaddr(NODE *p, void *arg)
{
	NODE *l = p->n_left;
	struct addrsymb *el;
	int found = 0;
	int lab;

	nodcnt++;

	if (p->n_op == ASSIGN && p->n_right->n_op == ICON &&
	    p->n_right->n_name[0] != '\0') {
		/* named constant */
		p = p->n_right;

		/* Restore addrof */
		l = mklnode(NAME, getlval(p), 0, 0);
		l->n_name = p->n_name;
		p->n_left = l;
		p->n_op = ADDROF;
	}

	if (p->n_op != ADDROF || l->n_op != NAME)
		return;

	/* if we passed 1k nodes printout list */
	if (nodcnt > 1000) {
		if (notfirst)
			flshlab();
		SLIST_INIT(&aslist);
		notfirst = 1;
		nodcnt = 0;
	}

	/* write address to byte stream */

	SLIST_FOREACH(el, &aslist, link) {
		if (el->num == getlval(l) && el->name[0] == l->n_name[0] &&
		    strcmp(el->name, l->n_name) == 0) {
			found = 1;
			break;
		}
	}
	if (!found) {
		/* we know that this is text segment */
		lab = prtnumber++;
		if (nodcnt <= 1000 && notfirst == 0) {
			if (getlval(l))
				printf(PRTLAB ":\n\t.dword %s+%lld\n",
				    lab, l->n_name, getlval(l));
			 else
                                printf(PRTLAB ":\n\t.dword %s\n",
                                    lab, l->n_name);	
		}
		el = tmpalloc(sizeof(struct addrsymb));
		el->num = getlval(l);
		el->name = l->n_name;
		el->str = tmpalloc(32);
		snprintf(el->str, 32, PRTLAB, lab);
		SLIST_INSERT_LAST(&aslist, el, link);
	}

	nfree(l);
	p->n_op = NAME;
	setlval(p, 0);
	p->n_name = el->str;
}

void
myreader(struct interpass *ipole)
{
	struct interpass *ip;

	SLIST_INIT(&aslist);
	notfirst = nodcnt = 0;

	DLIST_FOREACH(ip, ipole, qelem) {
		switch (ip->type) {
			case IP_NODE:
				lineno = ip->lineno;
				ipbase = ip;
				walkf(ip->ip_node, prtaddr, 0);
				break;
			case IP_EPILOG:
				ipbase = ip;
				if (notfirst)
					flshlab();
				break;
			default:
				break;
		}
	}
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
		if (p->n_type == (PTR+SHORT) || p->n_type == (PTR+USHORT)) {
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
myoptim(struct interpass *ipp)
{
}

/*
 * Register move: move contents of register 's' to register 'r'.
 */
void
rmove(int s, int d, TWORD t)
{
        switch (t) {
		case DOUBLE:
		case LDOUBLE:
			if (features(FEATURE_HARDFLOAT)) {
				printf("\tfmr %s,%s" COM "rmove\n",rnames[d], rnames[s]);
				break;
			}
			/* FALLTHROUGH */
	        case LONGLONG:
        	case ULONGLONG:
		#define LONGREG(x, y) rnames[(x)-(R16-(y))]
			printf("\tmov %s,%s\n",LONGREG(d,0), LONGREG(s,0));
               		break;
		case FLOAT:
			if (features(FEATURE_HARDFLOAT)) {
				printf("\tmr %s,%s" COM "rmove\n",rnames[d], rnames[s]);
				break;
			}
			/* FALLTHROUGH */
        	default:
                	if (!ISPTR(t)){
                        	printf("\tmov %s,%s" COM "rmove\n", wnames[d], wnames[s]);
   	        	}
                	else{
                        	printf("\tmov %s,%s" COM "rmove\n", rnames[d], rnames[s]);
                	}
        }
}

/*
 * Can we assign a register from class 'c', given the set
 * of number of assigned registers in each class 'r'.
 *
 * On ARM, we have:
 *	11  CLASSA registers (32-bit hard registers)
 *	10  CLASSB registers (64-bit composite registers)
 *	8 or 32 CLASSC registers (floating-point)
 *
 *  There is a problem calculating the available composite registers
 *  (ie CLASSB).  The algorithm below assumes that given any two
 *  registers, we can make a composite register.  But this isn't true
 *  here (or with other targets), since the number of combinations
 *  of register pairs could become very large.  Additionally,
 *  having so many combinations really isn't so practical, since
 *  most register pairs cannot be used to pass function arguments.
 *  Consequently, when there is pressure composite registers,
 *  "beenhere" compilation failures are common.
 *
 *  [We need to know which registers are allocated, not simply
 *  the number in each class]
 */
int
COLORMAP(int c, int *r)
{
	int num = 0;	/* number of registers used */
	switch (c) {
		case CLASSA:
			num += r[CLASSA];
			num += 2*r[CLASSB];
			return num < 11;
		case CLASSB:
			num += 2*r[CLASSB];
			num += r[CLASSA];
			return num < 6;  /* XXX see comments above */
		case CLASSC:
	        	num += r[CLASSC];
   			return num < 8;
	}
	cerror("colormap 2");
	return 0; /* XXX gcc */
}

/*
 * Return a class suitable for a specific type.
 */
int
gclass(TWORD t)
{
	if (t == DOUBLE || t == LDOUBLE) {
		if (features(FEATURE_HARDFLOAT))
			return CLASSC;
		else
			return CLASSB;
	}
	if (t == FLOAT) {
		if (features(FEATURE_HARDFLOAT))
			return CLASSC;
		else
			return CLASSA;
	}
	if (DEUNSIGN(t) == LONGLONG || DEUNSIGN(t) == LONG || t == LONGLONG || t == LONG)
		return CLASSB;
	return CLASSA;
}

int
retreg(int t)
{
	int c = gclass(t);
	if (c == CLASSB)
		return R16;
	return R0;
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
	for (p = p->n_right; p->n_op == CM; p = p->n_left)
		size += argsiz(p->n_right);
	size += argsiz(p);
	op->n_qual = size - 16; /* XXX */
}

/*
 * Special shapes.
 */
int
special(NODE *p, int shape)
{
	return SRNOPE;
}

/*
 * default to ARMv2
 */
#ifdef TARGET_BIG_ENDIAN
#define DEFAULT_FEATURES	FEATURE_BIGENDIAN | FEATURE_MUL
#else
#define DEFAULT_FEATURES	FEATURE_MUL
#endif

static int fset = DEFAULT_FEATURES;

/*
 * Target-dependent command-line options.
 */
void
mflags(char *str)
{
	//Handling needs to be done for ARMv8
}
int
features(int mask)
{
	if (mask == FEATURE_HARDFLOAT)
		return ((fset & mask) != 0);
	return ((fset & mask) == mask);
}

/*
 * Define the current location as an internal label.
 */
void
deflab(int label)
{
	printf(LABFMT ":\n", label);
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
