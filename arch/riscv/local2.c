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

#include "pass1.h"	/* for cftnsp */
#include "pass2.h"
#include <ctype.h>
#include <string.h>
#include <stdlib.h>

#if defined(MACHOABI)
#define EXPREFIX	"_"
#else
#define EXPREFIX	""
#endif

#define TAB "\t"

#define CONFMT	"%lld"		/* format for printing constants */
#if (defined(ELFABI) || defined(AOUTABI))
#define LABFMT	".L%d"		/* format for printing labels */
#define REGPREFIX		/* format for printing registers */
#elif defined(MACHOABI)
#define LABFMT	"L%d"		/* format for printing labels */
#define REGPREFIX
#else
#error undefined ABI
#endif

#define LOWREG		0
#define HIREG		1

char *rnames[] = {

#ifdef SAVE_RA_FOR_LAST
	REGPREFIX "x0", REGPREFIX "t6", REGPREFIX "sp",  REGPREFIX "gp", REGPREFIX "tp",
#else
	REGPREFIX "x0", REGPREFIX "ra", REGPREFIX "sp",  REGPREFIX "gp", REGPREFIX "tp",
#endif

	/* temp registers */
	REGPREFIX "t0",REGPREFIX "t1",  REGPREFIX "t2",

	/* frame and stack pointers */
	REGPREFIX "fp", REGPREFIX "s1",

	/* argument registers */
	REGPREFIX "a0", REGPREFIX "a1", REGPREFIX "a2", REGPREFIX "a3",
	REGPREFIX "a4", REGPREFIX "a5", REGPREFIX "a6", REGPREFIX "a7",
	/* saved registers */
	REGPREFIX "s2", REGPREFIX "s3", REGPREFIX "s4", REGPREFIX "s5",
	REGPREFIX "s6", REGPREFIX "s7", REGPREFIX "s8", REGPREFIX "s9",
	REGPREFIX "s10", REGPREFIX "s11",
	
	/* temp registers */
	REGPREFIX "t3", REGPREFIX "t4", REGPREFIX "t5", 
#ifdef SAVE_RA_FOR_LAST
	REGPREFIX "ra", 
#else
	REGPREFIX "t6",
#endif

	/* floating point registers */
	/* temp registers */
	REGPREFIX "ft0", REGPREFIX "ft1", REGPREFIX "ft2", REGPREFIX "ft3",
	REGPREFIX "ft4", REGPREFIX "ft5", REGPREFIX "ft6", REGPREFIX "ft7",
	/* saved registers */
	REGPREFIX "fs0", REGPREFIX "fs1", 
	/* argument registers */
	REGPREFIX "fa0", REGPREFIX "fa1", REGPREFIX "fa2", REGPREFIX "fa3",
	REGPREFIX "fa4", REGPREFIX "fa5", REGPREFIX "fa6", REGPREFIX "fa7",
	/* saved registers */
	REGPREFIX "fs2", REGPREFIX "fs3", REGPREFIX "fs4", REGPREFIX "fs5",
	REGPREFIX "fs6", REGPREFIX "fs7", REGPREFIX "fs8",	REGPREFIX "fs9",
	REGPREFIX "fs10", REGPREFIX "fs11",
	/* temp registers */
	REGPREFIX "ft8", REGPREFIX "ft9", REGPREFIX "ft10", REGPREFIX "ft11",
	
	/* pseudo-registers for longlongs */
	/* saved registers */
	REGPREFIX "ds0", REGPREFIX "ds1", REGPREFIX "ds2",  REGPREFIX "ds3",
	REGPREFIX "ds5", 
	/* argument registers */
	REGPREFIX "da0", REGPREFIX "da1", REGPREFIX "da2", REGPREFIX "da3",
	/* temp registers */
#ifdef USE_T0_AS_TEMP
	REGPREFIX "dt0", REGPREFIX "dt1", REGPREFIX "dt2", 
#else
	REGPREFIX "xxx", REGPREFIX "dt1", REGPREFIX "dt2"
#endif
};

static int argsize(NODE *p);

static int p2calls;
static int p2temps;		/* TEMPs which aren't autos yet */
static int p2framesize;
static int p2maxstacksize;

extern int p2maxautooff;

void
deflab(int label)
{
	printf(LABFMT ":\n", label);
}

static TWORD ftype;

/*
 * Print out the prolog assembler.
 */
void
prologue(struct interpass_prolog *ipp)
{
	int i, r, sz = 0, idx = 1, addto = p2maxautooff;

#ifdef PCC_DEBUG
	if (x2debug)
		printf("prologue: type=%d, lineno=%d, name=%s, vis=%d, ipptype=%d, autos=%d, tmpnum=%d, lblnum=%d\n",
			ipp->ipp_ip.type,
			ipp->ipp_ip.lineno,
			ipp->ipp_name,
			ipp->ipp_vis,
			ipp->ipp_type,
			ipp->ipp_autos,
			ipp->ip_tmpnum,
			ipp->ip_lblnum);
#endif

	/* calculate the frame space */
	for (i = 0; i < MAXREGS; i++) {
		if (TESTBIT(p2env.p_regs, i)) {
				addto += SZLONG/SZCHAR;
		}
	}
	
	if ((addto == 0) && (p2calls == 0))
		return; /* no need to create a stack frame */
	printf(";" TAB "p2maxautooff: %d, addto: %d\n", p2maxautooff, addto);

	/* make space for fp */
	addto += SZLONG/SZCHAR;

	/* put current frame pointer into temp register */
	printf(TAB "mv %s, %s\n", rnames[T1], rnames[FP]);
	
	/* save the stack pointer to the frame pointer */
	printf(TAB "mv %s, %s\n", rnames[FP], rnames[SP]);

	/* make space for ra */
	if (p2calls > 0)
		addto += SZLONG/SZCHAR;
	
	/* create the new stack frame */
	addto = (addto+15) & ~15; /* 16-byte aligned */
	if (addto < 1<<20) {
		printf(TAB "subi %s, %s, %d\n", rnames[SP], rnames[SP], addto);	
	} else {
		printf(TAB "addi %s, %s, %d\n", rnames[T1], rnames[ZERO], (addto) >> 16);
		printf(TAB "sll %s,%s,%d\n", rnames[T1], rnames[T1], 16);
		printf(TAB "addi %s,%d\n", rnames[T1], rnames[ZERO], (addto) & 0xffff);
		printf(TAB "sub %s,%s,%s\n", rnames[SP], rnames[SP], rnames[T1]);
	}
	
	/* stack pointer can grow downward
	 * frame pointer points to top of the
	 * stack-based arguments 
	 */

	/* save the original frame pointer to the bottom of the stack */
	printf(TAB "sw %s, 0(%s)\n", rnames[T1], rnames[SP]);

	if (p2calls > 0) {
		printf(TAB "sw %s, 4(%s)\n", rnames[RA], rnames[SP]);
		sz += (SZLONG/SZCHAR);
	}
		
	/* save non-volatile registers from the bottom of stack up */
	for (i = 0; i < MAXREGS; i++) {
		if (TESTBIT(p2env.p_regs, i)) {
			sz += (SZLONG/SZCHAR);
			if (sz == addto)
				cerror("collision between stack and frame");
		
			printf(TAB "sw %s, %d(%s)\n", rnames[i], sz, rnames[SP]);
		}
	}

}


void
eoftn(struct interpass_prolog *ipp)
{

int i, sz, idx = 0, addto = p2maxautooff;

#ifdef PCC_DEBUG
	if (x2debug)
		printf("eoftn:\n");
#endif

	if (ipp->ipp_ip.ip_lbl == 0)
		return; /* no code needs to be generated */

	/* calculate the frame space */
	for (i = 0; i < MAXREGS; i++) {
		if (TESTBIT(p2env.p_regs, i)) {
				addto += SZLONG/SZCHAR;
		}
	}
	
	if ((addto == 0) && (p2calls == 0)) {
		printf(TAB "jr %s\n", rnames[RA]);   
		return; /* no stack frame was created */
	}

	/* struct return needs special treatment */
	if (ftype == STRTY || ftype == UNIONTY) 
		cerror("eoftn");
		
	for (i = 0; i < MAXREGS; i++) {
		if (TESTBIT(p2env.p_regs, i))
			idx++; 
	}
	
	if (p2calls > 0)
		idx++;
		
	/* unwind stack frame */
	for (i = (MAXREGS-1); i >= 0; --i) {
		if (TESTBIT(p2env.p_regs, i)) {
			sz = idx*(SZLONG/SZCHAR);
			if (sz == 0)
				cerror("collision unwinding stack");
		
			printf(TAB "lw %s, %d(%s)\n", rnames[i], sz, rnames[SP]);
			--idx; 
		}
	}

	if (p2calls > 0)
		/* restore ra */
		printf(TAB "lw %s, 4(%s)\n", rnames[RA], rnames[SP]);

	/* move the original frame pointer to a temp */
	printf(TAB "lw %s, 0(%s)\n", rnames[T1], rnames[SP]);
	
	/* restore the stack pointer */
	printf(TAB "mv %s, %s\n", rnames[SP], rnames[FP]);
	
	/* restore the frame pointer */
	printf(TAB "mv %s, %s\n", rnames[FP], rnames[T1]);

	printf(TAB "jr %s\n", rnames[RA]);  

}


void
zzzcode(NODE *p, int c)
{
	switch (c) {

	case 'C': /* floating-point conversions */
		fpconv(p);
		break;

	case 'D': /* long long comparision */
		twollcomp(p);
		break;
		
	case 'E': /* generate and error */
		comperr("zzzcode received ZE macro");
		break;
	
	case 'O': /* 64-bit left and right shift operators */
		shiftop(p);
		break;

	case 'P': /* special SCON OPSIMP */
		if (getlval(p->n_right) >= 1<<12) {
			expand(p, 0, "li A2, AR\n");
			printf("\t");
			hopcode('0', p->n_op);
			expand(p, 0, " A1, AL, A2");
		} else {
			hopcode('i', p->n_op);
			expand(p, 0, " A1, AL, AR");
		}
		break;
		
	case 'Q': /* emit struct assign */
		printf("%d", attr_find(p->n_ap, ATTR_P2STRUCT)->iarg(0));
		/* stasg(p); */
		break;

	case 'R':  /* remove from stack after subroutine call */
		//printf("zzzcode R %d, 0x%x\n", p->n_qual, p);
		//fwalk(p, e2print, 0);
		if (p->n_qual > 0)
			printf("\taddi sp, sp, %d\n", p->n_qual);
		break;

	case 'S': /* substitution */
		printf("substitution in zzzcode\n");
		break;

	default:
		comperr("zzzcode %c", c);
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
	char opcode[20][7] = {"add", "sub", "and", "or", "xor",
					  "addi", "subi", "andi", "ori", "xori",
					  "fadd.s", "fsub.s", "andi", "ori", "xori",
					  "fadd.d", "fsub.d", "andi", "ori", "xori"}; 
	int i = 5, j;
	switch (o) {
		case PLUS:
			j = 0;
			break;
		case MINUS:
			j = 1;
			break;	
		case AND:
			j = 2;
			break;
		case OR:
			j = 3;
			break;
		case ER:
			j = 4;
			break;
			
	default:
		comperr("hopcode2: %d", o);
	}

	if (f == 'i')
		j += i;
	else if (f == 'f')
		j+= 2*i;
	else if (f == 'd')
		j+= 3*i;
	printf("%s", opcode[j]);
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
 * these mnemonics match the order of the preprocessor decls
 * EQ, NE, LE, LT, GE, GT, ULE, ULT, UGE, UGT
 */

static char *
ccbranches[] = {
	"beq",		/* branch if equal */
	"bne",		/* branch if not-equal */
	"ble",		/* branch if less-than-or-equal */
	"blt",			/* branch if less-than */
	"bge",		/* branch if greater-than-or-equal */
	"bgt",		/* branch if greater-than */
	/* unsigned */
	"bleu",		/* branch if less-than-or-equal */
	"bltu",		/* branch if less-than */
	"bgeu",		/* branch if greater-than-or-equal */
	"bgtu",		/* branch if greater-than */

};


/*   printf conditional and unconditional branches */
void
cbgen(int o, int lab)
{
printf("hitting cbgen %d-%d=%d\n", o, EQ, o-EQ);
	if (o < EQ || o > UGT)
		comperr("bad conditional branch: %s", opst[o]);
	printf(TAB "%s  AL,AR, " LABFMT "\n", ccbranches[o-EQ], lab);
}

/*
 * Emit code to compare two longlong numbers.
 */
static void
twollcomp(NODE *p)
{
	int o, op;
	int s = getlab2();
	int e = p->n_label;
	int cb1, cb2;
	
	o = op = p->n_op;	
	if (o >= ULE)
		o -= (ULE-LE);
	switch (o) {
	case NE:
		cb1 = 0;
		cb2 = NE; /* if ne, branch to e */
		break;
	case EQ:
		cb1 = NE; /* if ne, branch to s */
		cb2 = 0;
		break;
	case LE:
	case LT:
		cb1 = GT; /* if gt, branch to s */
		cb2 = LT; /* if lt, branch to e */
		break;
	case GE:
	case GT:
		cb1 = LT; /* branch to s */
		cb2 = GT; /* branch to e */
		break;
	
	default:
		cb1 = cb2 = 0; /* XXX gcc */
	}
	printf(TAB "%s ", ccbranches[op-EQ]);
	expand(p, 0, "UL, UR,");
	if (cb1)
		printf(LABFMT, s);
	if (cb2)
		printf(LABFMT, e);
	printf(COM "compare 64-bit values (upper)\n");
	
	printf( TAB "%s ", ccbranches[op-EQ]);
	expand(p, 0, "AL, AR,");
	printf(LABFMT, e);
	printf(COM "(and lower)\n");
	
	deflab(s);
}

static void
shiftop(NODE *p)
{
	NODE *r = p->n_right;
	TWORD ty = p->n_type;

	if (p->n_op == LS && r->n_op == ICON && getlval(r) < 32) {
		/* left shift less than 32 bits */
		expand(p, INBREG, TAB "srli A1,AL,32-AR" COM "64-bit left-shift\n");
		expand(p, INBREG, TAB "slli U1,UL,AR\n");
		expand(p, INBREG, TAB "or U1,U1,A1\n");
		expand(p, INBREG, TAB "slli A1,AL,AR\n");
	} else if (p->n_op == LS && r->n_op == ICON && getlval(r) < 64) {
		/* left shift more than 31 bits but less than 64 */
		expand(p, INBREG, TAB "add A1,x0,x0" COM "64-bit left-shift\n");
		if (getlval(r) == 32)
			expand(p, INBREG, TAB "mv U1,AL\n");
		else
			expand(p, INBREG, TAB "slli U1,AL,AR-32\n");
	} else if (p->n_op == LS && r->n_op == ICON) {
		/* left shift 64 bits */
		expand(p, INBREG, TAB "add A1,x0,x0" COM "64-bit left-shift\n");
		expand(p, INBREG, TAB "add U1,x0,x0\n");
	} else if (p->n_op == RS && r->n_op == ICON && getlval(r) < 32) {
		/* right shift less than 32 bits */
		expand(p, INBREG, TAB "slli U1,UL,32-AR" COM "64-bit right-shift\n");
		expand(p, INBREG, TAB "srli A1,AL,AR\n");
		expand(p, INBREG, TAB "or A1,A1,U1\n");
		if (ty == LONGLONG)
			expand(p, INBREG, TAB "srai U1,UL,AR\n");
		else
			expand(p, INBREG, TAB "srli U1,UL,AR\n");
	} else if (p->n_op == RS && r->n_op == ICON && getlval(r) < 64) {
		/* right shift more than 31 bits but less than 64 */
		if (ty == LONGLONG)
			expand(p, INBREG, TAB "addi U1,x0,-1" COM "64-bit right-shift\n");
		else
			expand(p, INBREG, TAB "addi U1,x0, x0" COM "64-bit right-shift\n");
		if (getlval(r) == 32)
			expand(p, INBREG, TAB "mv A1,UL\n");
		else if (ty == LONGLONG)
			expand(p, INBREG, TAB "srai A1,UL,AR-32\n");
		else
			expand(p, INBREG, TAB "srli A1,UL,AR-32\n");
	} else if (p->n_op == RS && r->n_op == ICON) {
		/* right shift 64 bits */
		expand(p, INBREG, TAB "add A1,x0,x0" COM "64-bit right-shift\n");
		expand(p, INBREG, TAB "add U1,x0,x0\n");
	}
}

/*
 * Structure assignment.
 */
static void
stasg(NODE *p)
{
	NODE *l = p->n_left;
	int val = getlval(l);

printf(" ; stasg\n");

        /* A0 = dest, A1 = src, A2 = len */
        printf(TAB "addi %s, x0, %d\n", rnames[A2], attr_find(p->n_ap, ATTR_P2STRUCT)->iarg(0));
        if (l->n_op == OREG) {
                printf(TAB "addi %s, %s, %d\n", rnames[A0], rnames[regno(l)], val);
        } else if (l->n_op == NAME) {
#if defined(ELFABI) || defined(AOUTABI)
                printf(TAB "addi %s, x0,", rnames[A0]);
                adrput(stdout, l);
		printf("@ha\n");
                printf(TAB "addi %s, %s,", rnames[A0], rnames[A0]);
                adrput(stdout, l);
		printf("@l\n");
#elif defined(MACHOABI)
                printf(TAB "addi %s,x0,ha16(", rnames[A0]);
                adrput(stdout, l);
		printf(")\n");
                printf(TAB "addi %s,%s,lo16(", rnames[A0], rnames[A0]);
                adrput(stdout, l);
		printf(")\n");
#endif
        }
	if (kflag) {
#if defined(ELFABI) || defined(AOUTABI)
	        printf(TAB "jalr ra,%s@got(30)\n", EXPREFIX "memcpy");
#elif defined(MACHOABI)
	        printf(TAB "jalr ra,L%s$stub\n", EXPREFIX "memcpy");
		addstub(&stublist, EXPREFIX "memcpy");
#endif
	} else {
	        printf(TAB "jalr ra,%s\n", EXPREFIX "memcpy");
	}
}


/*
 *  Floating-point conversions (int -> float/double & float/double -> int)
 */

static void
ftoi(NODE *p)
{
	NODE *l = p->n_left;
	int n_type = l->n_type, n_op = l->n_op;

	printf(COM "start conversion float/(l)double to int\n");

	if (n_op != OREG) {
		/* comes in from a floating point register specified by AL */
		/* and will go out in integer register A1 */
		if (n_type == FLOAT) { /* single precision */
			expand(p, 0, TAB "fcvt.w.s A1, AL\n");
		}
		else { /* double precision */ 
			expand(p, 0, TAB "fcvt.l.d A1, AL\n");
		}	
	}	
	else if (n_op == NAME) {
		/* comes in as a memory address */
		/* move the memory address to register A1 */
		expand(p, 0, TAB "lla A1, AL\n");
		if (n_type == FLOAT) { /* single precision */
			/* move the value into register A2 */
			expand(p, 0, TAB "flw A2, 0(A1)\n");
			/* once in A2, operate */
			expand(p, 0, TAB "fcvt.w.s A1, A2\n");
		}
		else{ /* double precision */ 
			/* move the value into register A2 */
			expand(p, 0, TAB "fld A2, 0(A1)\n");
			/* once in A2, operate */
			expand(p, 0, TAB "fcvt.w.d A1, A2\n");
		}
	}	
	else if (n_op == OREG) {
		/* comes in as an offset from the GPR specified in AL */
		if (n_type == FLOAT) { /* single precision */
			/* move the value into register A2 */
			expand(p, 0, TAB "fmv.w.x A2, AL\n");
			/* once in A2, operate */
			expand(p, 0, TAB "fcvt.w.s A1, A2\n");
		}
		else{ /* double precision */ 
			/* move the value into register A2 */
			expand(p, 0, TAB "fmv.d.x A2, AL\n");
			/* once in A2, operate */
			expand(p, 0, TAB "fcvt.w.d A1, A2\n");
		}
	}
	else 
		cerror("unknown n_op in ftoi()\n");

	printf(COM "end conversion\n");
}

static void
ftou(NODE *p)
{
	static int lab = 0;
	NODE *l = p->n_left;
	int lab1 = getlab2();
	int lab2 = getlab2();

	printf(COM "start conversion of float/(l)double to unsigned\n");

	printf(COM "end conversion\n");
}

static void
itof(NODE *p)
{
	static int labu = 0;
	static int labi = 0;
	int lab;
	NODE *l = p->n_left;

	printf(COM "start conversion (u)int to float/(l)double\n");

	printf(COM "end conversion\n");
}


static void
fpconv(NODE *p)
{
	NODE *l = p->n_left;

#ifdef PCC_DEBUG
	if (p->n_op != SCONV)
		cerror("fpconv 1");
#endif

	if (DEUNSIGN(l->n_type) == INT)
		itof(p);
	else if (p->n_type == INT)
		ftoi(p);
	else if (p->n_type == UNSIGNED)
		ftou(p);
	else
		cerror("unhandled floating-point conversion");

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

	if (o == NAME || o == REG || o == ICON || o == OREG ||
	    (o == UMUL && shumul(p->n_left, SOREG)))
		return(1);
	return 0;
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
		printf("%d", UPKFSZ(p->n_rval));
		break;
	case 'H':
		printf("%d", shft);
		break;
	case 'M':
	case 'N':
		val = (CONSZ)1 << UPKFSZ(p->n_rval);
		--val;
		val <<= shft;
		printf(CONFMT, (**cp == 'M' ? val : ~val)  & 0xffffffff);
		break;
	default:
		comperr("fldexpand");
	}
	return 1;
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
	printf("; shtemp\n");
	return 0;
#if 0
	int r;

	if (p->n_op == STARG )
		p = p->n_left;

	switch (p->n_op) {
	case REG:
		return (!istreg(regno(p)));

	case OREG:
		r = regno(p);
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
	printf( CONFMT, val);
}

void
conput(FILE *fp, NODE *p)
{


	int val = getlval(p);

//printf("conput %d \n", val);
//fwalk(p, e2print, 0);

	switch (p->n_op) {
	case ICON:
		if (p->n_name[0] != '\0') {
			fprintf(fp, "%s", p->n_name);
			if (val)
				fprintf(fp, "+%d", val);
		} else {
			if (GCLASS(p->n_type) == CLASSC)
				fprintf(fp, CONFMT, getlval(p) >> 32);
			else
				fprintf(fp, "%d", val);
		}
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
 * Print lower or upper name of 64-bit register.
 */
static void
reg64name(int reg, int hi)
{
	int idx;
	int off = 0;

	if (hi == HIREG)
		off = 1;

	//printf("reg64name: %d %s ", reg, off == 1 ? "HIREG" : "LOREG");
	
	if (reg > MAXREGS) {
		cerror("maxregs exceeded in reg64name");
	}
	else if (reg >= DS1) {
		switch (reg) {
			default:
				idx = S2 + 2*(reg - DS1);
		}		
	}
	else if (reg >= DT0) {
		switch(reg) {
			case DT0:
				idx = T0;
				break;
			case DT1:
				idx = T2;
				if (off == 1)
					off = T3 - T2;
				break;
			default: 
				idx = T4;
		} 
	} else if (reg >= DA0) {
		idx = A0 + 2*(reg-DA0);
	} else if (off == 0) {
		idx = reg;
	} else {
		printf("bad reg64name: (%d) \n", reg);
		user_stacktrace();
		return;
	}
		
	printf("%s" , rnames[idx + off]);
}

/*
 * Write out the upper address, like the upper register of a 2-register
 * reference, or the next memory location.
 */
void
upput(NODE *p, int size)
{

	size /= SZCHAR;
//fwalk(p, e2print, 0);
//printf("upput p->n_op: 0x%x size %d", p->n_op, size);
//printf("X");
//return;


	switch (p->n_op) {
	case REG:
		reg64name(regno(p), HIREG);
		break;

	case NAME:
	case OREG:
		printf("%d", (int)(getlval(p) + 4));
		printf("(%s)", rnames[regno(p)]);
		break;

	case ICON:
		printf(CONFMT, getlval(p) >> 32);
		break;

	default:
		comperr("upput bad op %d size %d", p->n_op, size);
	}
}

void
adrput(FILE *io, NODE *p)
{
	/* output an address, with offsets, from p */

	if (p->n_op == FLD)
		p = p->n_left;

	switch (p->n_op) {

		case FUNARG:
			printf("%d", p->n_rval);
			break;

		case NAME:
			if (p->n_name[0] != '\0') {
				fputs(p->n_name, io);
				if (getlval(p) != 0)
					printf( "+" CONFMT, getlval(p));
			} else
				printf(CONFMT, getlval(p));
			return;
	
		case OREG:
			printf("%d", (int)getlval(p));
			printf("(%s)", rnames[regno(p)]);
			return;
	
		case FCON:
		case ICON:
	#ifdef PCC_DEBUG
			/* Sanitycheck for PIC, to catch adressable constants */
			if (kflag && p->n_name[0] && 0) {
				static int foo;
	
				if (foo++ == 0) {
					printf("\nfailing...\n");
					fwalk(p, e2print, 0);
					comperr("pass2 adrput");
				}
			}
	#endif
			/* addressable value of the constant */
			conput(io, p);
			return;
	
		case REG:
			switch (p->n_type) {
				case LONGLONG:
				case ULONGLONG:
					if (regno(p) == FT11)	printf("**yep** ");
					reg64name(regno(p), LOWREG);
					break;
				default:
					printf("%s", rnames[regno(p)]);
				}
			return;
	
		default:
			user_stacktrace();
			comperr("illegal address, op %d, node %p", p->n_op, p);
			return;

	}
}


static int
argsize(NODE *p)
{
	TWORD t = p->n_type;

	if (t < LONGLONG || t == FLOAT || t > BTMASK)
		return 4;
	if (t == LONGLONG || t == ULONGLONG)
		return 8;
	if (t == DOUBLE || t == LDOUBLE)
		return 8;
	if (t == STRTY || t == UNIONTY)
		return attr_find(p->n_ap, ATTR_P2STRUCT)->iarg(0);
	comperr("argsize");
	return 0;
}

static int
calc_args_size(NODE *p)
{
	int n = 0;
        
        if (p->n_op == CM) {
                n += calc_args_size(p->n_left);
                n += calc_args_size(p->n_right);
                return n;
        }

        n += argsize(p);

        return n;
}


static void
fixcalls(NODE *p, void *arg)
{
	int n = 0;

	switch (p->n_op) {
	case STCALL:
	case CALL:
		n = calc_args_size(p->n_right);
		if (n > p2maxstacksize)
			p2maxstacksize = n;
		/* FALLTHROUGH */
	case USTCALL:
	case UCALL:
		++p2calls;
		break;
	case TEMP:
		p2temps += argsize(p);
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

                	off = (freetemp(szty(t)));
                	ll = mklnode(OREG, off, SP, t);
			nip = ipnode(mkbinode(ASSIGN, ll, p->n_left, t));
			p->n_left = mklnode(OREG, off, SP, t);
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

void
myreader(struct interpass *ipole)
{
	struct interpass *ip;

	p2calls = 0;
	p2temps = 0;
	p2maxstacksize = 0;

	DLIST_FOREACH(ip, ipole, qelem) {
		if (ip->type != IP_NODE)
			continue;
		walkf(ip->ip_node, fixcalls, 0);
		storefloat(ip, ip->ip_node);
	}
#if 0
	if (p2maxstacksize < NARGREGS*SZINT/SZCHAR)
		p2maxstacksize = NARGREGS*SZINT/SZCHAR;

	p2framesize = ARGINIT/SZCHAR;		/* stack ptr / return addr */
	p2framesize += 8;			/* for R31 and R30 */
	p2framesize += p2maxautooff;		/* autos */
	p2framesize += p2temps;			/* TEMPs that aren't autos */
	if (p2calls != 0)
		p2framesize += p2maxstacksize;	/* arguments to functions */
	p2framesize += (ALSTACK/SZCHAR - 1);	/* round to 16-byte boundary */
	p2framesize &= ~(ALSTACK/SZCHAR - 1);
#endif

#ifdef PCC_DEBUG
	if (x2debug) {
		printf("!!! MYREADER\n");
		printf("!!! p2maxautooff = %d\n", p2maxautooff);
		printf("!!! p2autooff = %d\n", p2autooff);
		printf("!!! p2temps = %d\n", p2temps);
		printf("!!! p2calls = %d\n", p2calls);
		printf("!!! p2maxstacksize = %d\n", p2maxstacksize);
	}
#endif

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
#ifdef PCC_DEBUG
	if (x2debug) {
		printf("myoptim\n");
	}
#endif
}

/*
 * Move data between registers.  While basic registers aren't a problem,
 * we have to handle the special case of overlapping composite registers.
 * It might just be easier to modify the register allocator so that
 * moves between overlapping registers isn't possible.
 */
void
rmove(int s, int d, TWORD t)
{
	switch (t) {
	case LDOUBLE:
	case DOUBLE:
			printf(TAB "fmv.d %s,%s" COM "rmove\n",
			    rnames[d], rnames[s]);
			break;
	case LONGLONG:
	case ULONGLONG:
		if (s == d+1) {
			/* dh = sl, copy low word first */
			printf(TAB "mv ");
			reg64name(d, LOWREG);
			printf(",");
			reg64name(s, LOWREG);
			printf("\n");
			printf(TAB "mv ");
			reg64name(d, HIREG);
			printf(",");
			reg64name(s, HIREG);
			printf("\n");
		} else {
			/* copy high word first */
			printf(TAB "mv ");
			reg64name(d, HIREG);
			printf(",");
			reg64name(s, HIREG);
			printf("\n");
			printf(TAB "mv ");
			reg64name(d, LOWREG);
			printf(",");
			reg64name(s, LOWREG);
			printf("\n");
		}
		break;
	case FLOAT:
		if (features(FEATURE_HARDFLOAT)) {
			printf(TAB "fmv.s %s,%s" COM "rmove\n",
			    rnames[d], rnames[s]);
			break;
		}
		/* FALL-THROUGH */
	default:
		printf(TAB "mv %s, %s" COM "rmove (%d)\n", rnames[d], rnames[s], t);
	}
}

/*
 * For class c, find worst-case displacement of the number of
 * registers in the array r[] indexed by class.
 *
 * On RISC-V, we have:
 *
 * 32 32-bit registers (7 reserved)
 * 13 64-bit pseudo registers (1 reserved)
 * 32 floating-point registers (1 reserved)
 */
int
COLORMAP(int c, int *r)
{
	int num = 0;

	/* RISC-V32 has longlong in CLASSC */
	switch (c) {
        case CLASSA:
			num += r[CLASSA];
			num += 2*r[CLASSC];
			return num < 25;
        case CLASSB:
			num += r[CLASSB];
			return num < 31;
		case CLASSC:
			return num < 12;
        }

        return 0;
}

/*
 * Return a class suitable for a specific type.
 */
int
gclass(TWORD t)
{
	if (t == LONGLONG || t == ULONGLONG)
		return CLASSC;
	if (t == FLOAT || t == DOUBLE || t == LDOUBLE) {
		return CLASSB;
	}
	return CLASSA;
}

int p2arg_overflow(NODE* r) {

  NODE* q = r;
  int sz, off = 0, last = 0, n_regs = 0, n_fregs = 0;

	if (!r->n_left) 
		last = 1;
			
	while (1)  {
//printf("r: 0x%x, op: %d, n_left: 0x%x n_right: 0x%x last = %d\n", 
//				r, r->n_op, r->n_left, r->n_right, last);

		if (q->n_op == STARG) {
		//printf("STARG\n");
			sz = attr_find(q->n_ap, ATTR_P2STRUCT)->iarg(0);
			switch (sz) {
				case 1:
					n_regs += 1;
					break;
				case 2: 
					n_regs += 2;
					break;
				default:
					n_regs += 1;
			}
		} else if (DEUNSIGN(q->n_type) == LONGLONG) {
		//printf("LONGLONG\n");
						n_regs += 2;
		} else if (q->n_type == DOUBLE || q->n_type == LDOUBLE) {
		//printf("DOUBLE\n");
						n_fregs += 2;
		} else if (q->n_type == FLOAT) {
		//printf("FLOAT\n");
						n_fregs += 1;
		} else if (q->n_type > 0) {
		//printf(">0\n");
						n_regs += 1;
		}

		if (last)
			break;
		r = r->n_left;
		if (r->n_op == CM)
			q = r->n_right;
		else {
			q = r;
			last = 1;
		}

	} 
	
	if (n_fregs > NARGREGS) 
		n_regs  += n_fregs - NARGREGS;

	if (n_regs > NARGREGS) {
			off += (n_regs - NARGREGS)*(SZINT/SZCHAR);
	} 
	if (n_fregs > NARGREGS) {
			off += (n_fregs - NARGREGS)*(SZINT/SZCHAR);
	}	
	
//printf("n_regs: %d, off: %d\n", n_regs, off);

return off;

}


/*
 * Calculate argument sizes.
 */
void
lastcall(NODE *p)
{
	NODE *op = p;
	int off = 0;

#ifdef PCC_DEBUG
	if (x2debug)
		printf("lastcall:\n");
#endif

	if (p->n_right == 0)
		return;
		
	off  = p2arg_overflow(p->n_right->n_left);
	p->n_qual = (off+15) & ~15; 
	
//printf("lastcall %d, 0x%x\n", p->n_qual, p->n_right->n_left);
//fwalk(p, e2print, 0);

}

/*
 * Special shapes.
 */
int
special(NODE *p, int shape)
{
	int o = p->n_op;

	switch (shape) {
	case SFUNCALL:
		if (o == STCALL || o == USTCALL)
			return SRREG;
		break;
	case SPCON:
		if (o == ICON && p->n_name[0] == 0 && (getlval(p) & ~0x7fff) == 0)
			return SRDIR;
		break;
	}
	return SRNOPE;
}

static int fset = FEATURE_HARDFLOAT;

/*
 * Target-dependent command-line options.
 */
void
mflags(char *str)
{

	fprintf(stderr, "unknown m option '%s'\n", str);
}

int
features(int mask)
{
	return ((fset & mask) == mask);
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

/*
 * Check for other names of the xasm constraints registers.
 */
int xasmconstregs(char *s)
{

	return -1;
}
