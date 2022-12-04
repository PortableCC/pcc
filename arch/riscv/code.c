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

#include <assert.h>
#include <stdlib.h>

#include "pass1.h"
#include "pass2.h"

#ifdef LANG_CXX
#define p1listf listf
#define p1tfree tfree
#define p1nfree nfree
#define p1fwalk fwalk
#define p1walkf walkf
#define p1tcopy tcopy
#else
#define NODE P1ND
#define talloc p1alloc
#endif

static void genswitch_bintree(int num, TWORD ty, struct swents **p, int n);
static int p1arg_overflow(NODE* r);

#if 0
static void genswitch_table(int num, struct swents **p, int n);
static void genswitch_mrst(int num, struct swents **p, int n);
#endif

static int rvnr;

/*
 * Print out assembler segment name.
 */
void
setseg(int seg, char *name)
{
	switch (seg) {
	case PROG: name = ".text"; break;
	case DATA:
	case LDATA: name = ".data"; break;
	case UDATA: break;

	case PICLDATA: name = ".section .data.rel.local,\"aw\",@progbits";break;
	case PICDATA: name = ".section .data.rel.rw,\"aw\",@progbits"; break;
	case PICRDATA: name = ".section .data.rel.ro,\"aw\",@progbits"; break;
	case STRNG:
#ifdef AOUTABI
	case RDATA: name = ".data"; break;
#else
	case RDATA: name = ".section .rodata"; break;
#endif
	case TLSDATA: name = ".section .tdata,\"awT\",@progbits"; break;
	case TLSUDATA: name = ".section .tbss,\"awT\",@nobits"; break;
	case CTORS: name = ".section\t.ctors,\"aw\",@progbits"; break;
	case DTORS: name = ".section\t.dtors,\"aw\",@progbits"; break;
	case NMSEG: 
		printf("\t.section %s,\"a%c\",@progbits\n", name,
		    cftnsp ? 'x' : 'w');
		return;
	}
	printf("\t%s\n", name);
}



/*
 * Define everything needed to print out some data (or text).
 * This means segment, alignment, visibility, etc.
 */
void
defloc(struct symtab *sp)
{
	char *name;

	name = getexname(sp);
	if (sp->sclass == EXTDEF)
		printf("	.globl %s\n", name);
	if (sp->slevel == 0)
		printf("%s:\n", name);
	else
		printf(LABFMT ":\n", sp->soffset);
}

/* Put a symbol in a temporary
 * used by bfcode() and its helpers
 */
static void
putintemp(struct symtab *sym)
{
	NODE *p;
	//cerror("putintemps called, not supported");
	p = tempnode(0, sym->stype, sym->sdf, sym->sap);
	p = buildtree(ASSIGN, p, nametree(sym));
	sym->soffset = regno(p->n_left);
	sym->sflags |= STNODE;

	ecomp(p);
}

/* setup a 64-bit parameter (longlong)
 * used by bfcode() */
static void
param_64bit(struct symtab *sym, int *argofsp, int dotemps)
{
	int argofs = *argofsp;
	NODE *p, *q;
	int navail;

	printf("param_64bit argofs before %d\n", argofs);
#if ALLONGLONG == 64 && 0
	/* alignment */
	++argofs;
	argofs &= ~1;
	printf("param_64bit argofs after %d\n", argofs);
#endif

	navail = NARGREGS - argofs;

	if (navail < 2) {
		/* half in and half out of the registers */
		cerror("too many arguments, do something intelligent");
		return; /* Quiet llvm */
	} else {
		q = block(REG, NIL, NIL, sym->stype, sym->sdf, sym->sap);
		if ((DA0 + argofs) > MAXREGS)
			printf("%s:%d requesting register too far\n", __FILE__, __LINE__);
		regno(q) = DA0 + argofs; 	/*cregs count by 1 */
		printf("param_64bit regno(q) = %d\n", regno(q));
		if (dotemps) {
			p = tempnode(0, sym->stype, sym->sdf, sym->sap);
			sym->soffset = regno(p);
			sym->sflags |= STNODE;
		} else {
			p = nametree(sym);
		}
	}
	p = buildtree(ASSIGN, p, q);
	ecomp(p);
	*argofsp = argofs + 1;
}

/* setup a 32-bit param on the stack
 * used by bfcode() */
static void
param_32bit(struct symtab *sym, int *argofsp, int dotemps)
{
	NODE *p, *q;
	
	q = block(REG, NIL, NIL, sym->stype, sym->sdf, sym->sap);
	regno(q) = A0 + (*argofsp)++;
	if (dotemps) {
		p = tempnode(0, sym->stype, sym->sdf, sym->sap);
		sym->soffset = regno(p);
		sym->sflags |= STNODE;
	} else {
		//cerror("param32bit called without dotemps");
		p = nametree(sym);
	}
	p = buildtree(ASSIGN, p, q);
	ecomp(p);
}

/* setup a double param on the stack
 * used by bfcode() */
static void
param_double(struct symtab *sym, int *argofsp, int dotemps)
{
	NODE *p, *q;
	int tmpnr, r = *argofsp;;

		if (r < 8) {

		     q = block(REG, NIL, NIL, sym->stype, sym->sdf, sym->sap);
			regno(q) = FA0 + r;
			if (dotemps) {
				p = tempnode(0, sym->stype, sym->sdf, sym->sap);
				sym->soffset = regno(p);
				sym->sflags |= STNODE;
			} else {
				//cerror("param64bit called without dotemps");
				p = nametree(sym);
			}
			p = buildtree(ASSIGN, p, q);
			ecomp(p);

		}
		else {
			cerror("too many arguments, do something intelligent");
	}


	(*argofsp) += 1;
	if (0) {
	sym->soffset = tmpnr;
	sym->sflags |= STNODE;
	}
}

#if 0
/* setup a float param on the stack
 * used by bfcode() */
static void
param_float(struct symtab *sym, int *argofsp, int dotemps)
{
	NODE *p, *q;
	int tmpnr, r = *argofsp;

	/*
	 * we have to dump the float from the general register
	 * into a temp, since the register allocator doesn't like
	 * floats to be in CLASSA.  This may not work for -xtemps.
	 */

	if (r < 8) {
		 q = block(REG, NIL, NIL, sym->stype, sym->sdf, sym->sap);
		regno(q) = FA0 + r;
		if (dotemps) {
			p = tempnode(0, sym->stype, sym->sdf, sym->sap);
			sym->soffset = regno(p);
			sym->sflags |= STNODE;
		} else {
		cerror("param_float called without dotemps");
			p = nametree(sym);
		}
		p = buildtree(ASSIGN, p, q);
		ecomp(p);

	}
	else {
		cerror("too many arguments, do something intelligent");
	}

	(*argofsp)++;
	if (0) {
	sym->soffset = tmpnr;
	sym->sflags |= STNODE;
	}

}
#endif

/* setup the hidden pointer to struct return parameter
 * used by bfcode() */
static void
param_retstruct(void)
{
	NODE *p, *q;

	p = tempnode(0, INCREF(cftnsp->stype), 0, cftnsp->sap);
	rvnr = regno(p);
	q = block(REG, NIL, NIL, INCREF(cftnsp->stype),
	    cftnsp->sdf, cftnsp->sap);
	regno(q) = A0;
	p = buildtree(ASSIGN, p, q);
	ecomp(p);
}


/* setup struct parameter
 * push the registers out to memory
 * used by bfcode() */
static void
param_struct(struct symtab *sym, int *argofsp)
{
	int argofs = *argofsp;
	NODE *p, *q;
	int navail;
	int sz;
	int off;
	int num;
	int i;

	navail = NARGREGS - argofs;
	sz = tsize(sym->stype, sym->sdf, sym->sap) / SZINT;
	off = ARGINIT/SZINT + argofs;
	num = sz > navail ? navail : sz;
	if (sz > 2)
		printf("passed as reference (%d)\n", sz);
		
	for (i = 0; i < num; i++) {
		q = block(REG, NIL, NIL, INT, 0, 0);
		regno(q) = A0 + argofs++;
		p = block(REG, NIL, NIL, INT, 0, 0);
		regno(p) = SP;
		p = block(PLUS, p, bcon(4*off++), INT, 0, 0);
		p = block(UMUL, p, NIL, INT, 0, 0);
		p = buildtree(ASSIGN, p, q);
		ecomp(p);
	}

	*argofsp = argofs;
}

/*
 * code for the beginning of a function
 * sp is an array of indices in symtab for the arguments
 * cnt is the number of arguments
 */
void
bfcode(struct symtab **sp, int cnt)
{

	struct symtab *sp2;
	union arglist *usym;
	NODE *q, *p;
	TWORD t;
	int saveallargs = 0, off = 0;
	int i, argofs = 0, fargofs = 0, dotemps = (xtemps && !saveallargs);

	/*
	 * Detect if this function has ellipses and save those
	 * argument registers onto stack.
	 */
	if (cftnsp->sdf && cftnsp->sdf->dfun) {
		usym = cftnsp->sdf->dfun;
		for (; usym->type != TELLIPSIS; usym++) {
			t = usym->type;
			if (t == TNULL)
				break;
			if (ISSOU(BTYPE(t)))
				usym++;
			for (i = 0; t > BTMASK; t = DECREF(t)) 
				if (ISARY(t) || ISFTN(t))
					i++;
			if (i)
				usym++;
		}
		if (usym->type == TELLIPSIS)
			saveallargs = 1;
	}
	
	if (cftnsp->stype == STRTY+FTN || cftnsp->stype == UNIONTY+FTN) {
		param_retstruct();
		++argofs;
	}

	/* recalculate the arg offset and create TEMP moves */
	for (i = 0; i < cnt; i++) {

		if (sp[i] == NULL)
			continue;

		int stype = sp[i]->stype;

		if ((argofs >= NARGREGS) && !xtemps)
			break;

		if (argofs >= NARGREGS) {
			//cerror("too many arguments, do something intelligent");
				putintemp(sp[i]);
		} else if (stype == STRTY || stype == UNIONTY) {
				param_struct(sp[i], &argofs);
		} else if (DEUNSIGN(stype) == LONGLONG) {
				param_64bit(sp[i], &argofs, dotemps);
		} else if (stype == DOUBLE || stype == LDOUBLE ||  stype == FLOAT) {
				param_double(sp[i], &fargofs, dotemps);
//		} else if (stype == FLOAT) {
//				param_float(sp[i], &argofs, dotemps);
		} else {
				param_32bit(sp[i], &argofs, dotemps);
		}
		
	} /*  for (i = 0; i < cnt; i++) */

	/* if saveallargs, save the rest of the args onto the stack */
	if (saveallargs) {
		off = NARGREGS*ARGINIT/SZINT;
		off = (off+15) & ~15; /* 16-byte aligned */ 
		p = block(REG, NIL, NIL, INT, 0, 0);
		regno(p) = SP;
		p = buildtree(MINUSEQ, p, bcon(off));
		ecomp(p);
		
		while (argofs < NARGREGS ) {
			/* int off = (ARGINIT+FIXEDSTACKSIZE*SZCHAR)/SZINT + argofs; */
			off = ARGINIT/SZINT + argofs;
			q = block(REG, NIL, NIL, INT, 0, 0);
			regno(q) = A0 + argofs++;
			p = block(REG, NIL, NIL, INT, 0, 0);
			regno(p) = SP;
			p = block(PLUS, p, bcon(4*off), INT, 0, 0);
			p = block(UMUL, p, NIL, INT, 0, 0);
			p = buildtree(ASSIGN, p, q);
			ecomp(p);
		}

	}
	
/* profiling */
	if (pflag) {
#if defined(ELFABI) || defined(AOUTABI)
	
		sp2 = lookup("_mcount", 0);
		sp2->stype = EXTERN;
		p = nametree(sp2);
		p->n_sp->sclass = EXTERN;
		p = clocal(p);
		p = buildtree(ADDROF, p, NIL);
		p = block(UCALL, p, NIL, INT, 0, 0);
		ecomp(funcode(p));
	
#endif
	}
}

/*
 * code for the end of a function
 * deals with struct return here
 */
void
efcode(void)
{
	NODE *p, *q;
	int tempnr;
	int ty;

#ifdef USE_GOTNR
	extern int gotnr;
	gotnr = 0;
#endif

	if (cftnsp->stype != STRTY+FTN && cftnsp->stype != UNIONTY+FTN)
		return;

	ty = cftnsp->stype - FTN;

	q = block(REG, NIL, NIL, INCREF(ty), 0, cftnsp->sap);
	regno(q) = A0;
	p = tempnode(0, INCREF(ty), 0, cftnsp->sap);
	tempnr = regno(p);
	p = buildtree(ASSIGN, p, q);
	ecomp(p);

	q = tempnode(tempnr, INCREF(ty), 0, cftnsp->sap);
	q = buildtree(UMUL, q, NIL);

	p = tempnode(rvnr, INCREF(ty), 0, cftnsp->sap);
	p = buildtree(UMUL, p, NIL);

	p = buildtree(ASSIGN, p, q);
	ecomp(p);

	q = tempnode(rvnr, INCREF(ty), 0, cftnsp->sap);
	p = block(REG, NIL, NIL, INCREF(ty), 0, cftnsp->sap);
	regno(p) = A0;
	p = buildtree(ASSIGN, p, q);
	ecomp(p);
}

struct stub stublist;
struct stub nlplist;

/* called just before final exit */
/* flag is 1 if errors, 0 if none */
void
ejobcode(int flag)
{

	printf("\t.ident \"PCC: %s\"\n", VERSSTR);

}

void
bjobcode(void)
{
	DLIST_INIT(&stublist, link);
	DLIST_INIT(&nlplist, link);
	
	/* riscv names for some asm constant printouts */
	astypnames[INT] = astypnames[UNSIGNED] = "\t.long";

}	

#ifdef notdef
/*
 * Print character t at position i in one string, until t == -1.
 * Locctr & label is already defined.
 */
void
bycode(int t, int i)
{
	static	int	lastoctal = 0;

	/* put byte i+1 in a string */

	if (t < 0) {
		if (i != 0)
			puts("\"");
	} else {
		if (i == 0)
			printf("\t.ascii \"");
		if (t == '\\' || t == '"') {
			lastoctal = 0;
			putchar('\\');
			putchar(t);
		} else if (t < 040 || t >= 0177) {
			lastoctal++;
			printf("\\%o",t);
		} else if (lastoctal && '0' <= t && t <= '9') {
			lastoctal = 0;
			printf("\"\n\t.ascii \"%c", t);
		} else {	
			lastoctal = 0;
			putchar(t);
		}
	}
}
#endif

/* fix up type of field p */
void
fldty(struct symtab *p)
{
}

/*
 * XXX - fix genswitch.
 */
int
mygenswitch(int num, TWORD type, struct swents **p, int n)
{
	if (num < 0) {
		genswitch_bintree(num, type, p, n);
		return 1;
	}

	return 0;

#if 0
	if (0)
	genswitch_table(num, p, n);
	if (0)
	genswitch_bintree(num, p, n);
	genswitch_mrst(num, p, n);
#endif
}

static void bintree_rec(TWORD ty, int num,
	struct swents **p, int n, int s, int e);

static void
genswitch_bintree(int num, TWORD ty, struct swents **p, int n)
{
	int lab = getlab();

	if (p[0]->slab == 0)
		p[0]->slab = lab;

	bintree_rec(ty, num, p, n, 1, n);

	plabel(lab);
}

static void
bintree_rec(TWORD ty, int num, struct swents **p, int n, int s, int e)
{
	NODE *r;
	int rlabel;
	int h;

	if (s == e) {
		r = tempnode(num, ty, 0, 0);
		r = buildtree(NE, r, bcon(p[s]->sval));
		cbranch(buildtree(NOT, r, NIL), bcon(p[s]->slab));
		branch(p[0]->slab);
		return;
	}

	rlabel = getlab();

	h = s + (e - s) / 2;

	r = tempnode(num, ty, 0, 0);
	r = buildtree(GT, r, bcon(p[h]->sval));
	cbranch(r, bcon(rlabel));
	bintree_rec(ty, num, p, n, s, h);
	plabel(rlabel);
	bintree_rec(ty, num, p, n, h+1, e);
}


/*
 * Straighten a chain of CM ops so that the CM nodes
 * only appear on the left node.
 *
 *	  CM	       CM
 *	CM  CM	   CM  b
 *       x y  a b	CM  a
 *		      x  y
 *
 *	   CM	     CM
 *	CM    CM	CM c
 *      CM z  CM  c      CM b
 *     x y    a b      CM a
 *		   CM z
 *		  x y
 */
static NODE *
straighten(NODE *p)
{
	NODE *r = p->n_right;

	if (p->n_op != CM || r->n_op != CM)
		return p;

	p->n_right = r->n_left;
	r->n_left = straighten(p);

	return r;
}

#if 0
static NODE *
reverse1(NODE *p, NODE *a)
{
	NODE *l = p->n_left;
	NODE *r = p->n_right;

	a->n_right = r;
	p->n_left = a;

	if (l->n_op == CM) {
		return reverse1(l, p);
	} else {
		p->n_right = l;
		return p;
	}
}

/*
 * Reverse a chain of CM ops
 */
static NODE *
reverse(NODE *p)
{
	NODE *l = p->n_left;
	NODE *r = p->n_right;

	p->n_left = r;

	if (l->n_op == CM)
		return reverse1(l, p);

	p->n_right = l;

	return p;
}
#endif

/* push arg onto the stack */
/* called by moveargs() */
static NODE *
pusharg(NODE *p, int *regp)
{
  NODE *q;
  int sz, off = 0;

	/* convert to register size, if smaller */
	sz = tsize(p->n_type, p->n_df, p->n_ap);
	if (sz < SZINT)
		p = block(SCONV, p, NIL, INT, 0, 0);

	q = block(REG, NIL, NIL, INCREF(p->n_type), p->n_df, p->n_ap);
	regno(q) = SP;

	off = SZINT/SZCHAR * (*regp - (A7 + 1));
//printf("pusharg: off = %d, regp = %d\n", off, *regp);

	if (off > 0)
		q = block(PLUS, q, bcon(off), INT, 0, 0);
	q = block(UMUL, q, NIL, p->n_type, p->n_df, p->n_ap);
	(*regp) += szty(p->n_type);

	return buildtree(ASSIGN, q, p);
}

/* setup call stack with 32-bit argument */
/* called from moveargs() */
static NODE *
movearg_32bit(NODE *p, int *regp)
{
  int reg = *regp;
  NODE *q;

	q = block(REG, NIL, NIL, p->n_type, p->n_df, p->n_ap);
	regno(q) = reg++;
	q = buildtree(ASSIGN, q, p);

	*regp = reg;
  
  return q;

}

/* setup call stack with 64-bit argument */
/* called from moveargs() */
static NODE *
movearg_64bit(NODE *p, int *regp)
{
  int reg = *regp;
  NODE *q, *r;

#if ALLONGLONG == 64 && 0
	/* alignment */
	++reg;
	reg &= ~1;
#endif

//printf("movearg_64bit: reg 0%o\n", reg);

	if (reg > A7) {
		*regp = reg;
		q = pusharg(p, regp);
	} else if (reg == A7) {
		/* half in and half out of the registers */
		r = p1tcopy(p);
		q = block(SCONV, p, NIL, INT, 0, 0);
		q = movearg_32bit(q, regp);
		r = buildtree(RS, r, bcon(32));
		r = block(SCONV, r, NIL, INT, 0, 0);
		r = pusharg(r, regp);

		q = straighten(block(CM, q, r, p->n_type, p->n_df, p->n_ap));
	} else {
		q = block(REG, NIL, NIL, p->n_type, p->n_df, p->n_ap);
		regno(q) = DA0 + (reg - A0);	/* cregs come in pairs  */
		q = buildtree(ASSIGN, q, p);
		*regp = reg + 1;
     }

  return q;
}

/* setup call stack with float argument */
/* called from moveargs() */
static NODE *
movearg_float(NODE *p, int *fregp, int *regp)
{

	p = movearg_32bit(p, fregp);

  return p;
}

/* setup call stack with float/double argument */
/* called from moveargs() */
static NODE *
movearg_double(NODE *p, int *fregp, int *regp)
{

	/* this does the move to a single register for us */
	p = movearg_32bit(p, fregp);

  return p;
}

/* setup call stack with a structure */
/* called from moveargs() */
static NODE *
movearg_struct(NODE *p, int *regp)
{
	int off;
	NODE *l, *q, *t, *r;
	int sz;

#if 1

/* ABI calls for
 * 1) aggregates less than 2*XLEN to be passed in one register
 * 2) aggregates of 2*XLEN passed in two registers
 * 3) aggregates greater than two registers passed by reference
 */
 
	sz = tsize(p->n_type, p->n_df, p->n_ap) / SZINT;
	
	printf("walking \n");
	p1fwalk(p, eprint, 0); 

	/* remove STARG node */
	l = p->n_left;
	p1nfree(p);
			printf("2 walking \n");
			p1fwalk(l, eprint, 0); 

	switch (sz) {
		case 2:
			printf("case 2\n");		

			q = block(UMUL, l, NIL, INT, 0, 0);
			if ((*regp - A0) < NARGREGS)
				q = movearg_32bit(q, regp);
			else 
				q = pusharg(q, regp);
			
			/* set-up second field */
			r = block(REG, NIL, NIL, INT, 0, 0);
			regno(r) = FP;
			r = block(MINUS, r, bcon(4), INT, 0, 0);
			
			q = block(CM, q, r, INT, 0, 0);
			printf("walking again\n");
			p1fwalk(q, eprint, 0);

			l = r;
			
			/* fallthrough */
			
		case 1:
			printf("case 1 (%d)\n", (*regp - A0));
			l = block(UMUL, l, NIL, INT, 0, 0);
			if ((*regp - A0) < NARGREGS)
				l = movearg_32bit(l, regp);
			else
				l = pusharg(l, regp);
			if (sz == 2)
				q->n_right = l;
			else
				q = l;	
				
			printf("2 walking again\n");
			p1fwalk(l, eprint, 0);
			
			break;
			
		default:
			r = l;
			
			off = ((sz*(SZINT/SZCHAR))+15) & ~15; /* 16-byte aligned */
			l = block(REG, NIL, NIL, INT, 0, 0);
			regno(l) = SP;
			slval(l, 0);
			l = block(MINUS, l, bcon(off), INT, 0, 0);
			q = block(REG, NIL, NIL, INT, 0, 0);
			regno(q) = SP;
			q = buildtree(ASSIGN, q, l);

			printf("3 walking again\n");
			p1fwalk(q, eprint, 0);

			t = block(OREG, NIL, NIL, INT, 0, 0);
			regno(t) = SP;
			r = block(UMUL, r, NIL, INT, 0, 0);
			t = block(ASSIGN, t, r, INT, 0, 0);
			q = block(CM, t, q, INT, 0, 0);
			printf("4 walking again\n");
			p1fwalk(q, eprint, 0);

			break;
	}

#else
	int tmpnr, i, num, navail, reg = *regp;

	assert(p->n_op == STARG);

	navail = NARGREGS - (reg - A0);
	navail = navail < 0 ? 0 : navail;
	sz = tsize(p->n_type, p->n_df, p->n_ap) / SZINT;
	num = sz > navail ? navail : sz;

	/* remove STARG node */
	l = p->n_left;
	p1nfree(p);
	ty = l->n_type;

	/*
	 * put it into a TEMP, rather than tcopy(), since the tree
	 * in p may have side-effects
	 */
	t = tempnode(0, ty, l->n_df, l->n_ap);
	tmpnr = regno(t);
	q = buildtree(ASSIGN, t, l);

	/* copy structure into registers */
	for (i = 0; i < num; i++) {
		t = tempnode(tmpnr, ty, 0, 0);
		t = block(SCONV, t, NIL, PTR+INT, 0, 0);
		t = block(PLUS, t, bcon(4*i), PTR+INT, 0, 0);
		t = buildtree(UMUL, t, NIL);

		r = block(REG, NIL, NIL, INT, 0, 0);
		regno(r) = reg++;
		r = buildtree(ASSIGN, r, t);

		q = block(CM, q, r, INT, 0, 0);
	}

	/* put the rest of the structure on the stack */
	for (i = num; i < sz; i++) {
		t = tempnode(tmpnr, ty, 0, 0);
		t = block(SCONV, t, NIL, PTR+INT, 0, 0);
		t = block(PLUS, t, bcon(4*i), PTR+INT, 0, 0);
		t = buildtree(UMUL, t, NIL);
		r = pusharg(t, &reg);
		q = block(CM, q, r, INT, 0, 0);
	}

	q = reverse(q);
	
	*regp = reg;
	
#endif

	return q;
}

int recursion_level = 0;

static NODE *
moveargs(NODE *p, int *regp, int *fregp, int *llregp)
{
	NODE *r, **rp;
	int reg, freg, llreg, bottom = 0, top = 0;
	int numregs;
	
	if (p->n_op == CM) {
		recursion_level++;
		p->n_left = moveargs(p->n_left, regp, fregp, llregp);
		r = p->n_right;
		rp = &p->n_right;
		--recursion_level;
		if (recursion_level == 0) {
			bottom = 1;
		}
	} else {
		r = p;
		rp = &p;
	}

	reg = *regp;
	freg = *fregp;
	llreg = *llregp;
	numregs = (A7 - reg) + (DA0 - llreg)*2;
	
//printf("movargs: reg = %d, recursion_level = %d, top  = %d, bottom  = %d\n", reg, recursion_level, top, bottom);
printf("; movargs: reg = %d, numregs %d\n", reg, numregs);
	if (freg > FA7)
		cerror("max floating point args exceeded");
	else if (reg > A7 && r->n_op != STARG) {
		if (!bottom)
			*rp = pusharg(r, regp);
		else
			*rp = block(FUNARG, r, NIL, r->n_type, r->n_df, r->n_ap);
	} else if (r->n_op == STARG) {
	printf("; STARG\n");
		*rp = movearg_struct(r, regp);
	} else if (DEUNSIGN(r->n_type) == LONGLONG) {
		*rp = movearg_64bit(r, llregp);
	} else if (r->n_type == DOUBLE || r->n_type == LDOUBLE) {
		*rp = movearg_double(r, fregp, regp);
	} else if (r->n_type == FLOAT) {
		*rp = movearg_float(r, fregp, regp);
	} else {
		*rp = movearg_32bit(r, regp);
	}

	if (top) {
		// clear out stuff if needed
	}

  return straighten(p);
}

/*
 * Fixup arguments to pass pointer-to-struct as first argument.
 *
 * called from funcode().
 */
static NODE *
retstruct(NODE *p)
{
	struct symtab s;
	NODE *l, *r, *t, *q;
	TWORD ty;

	l = p->n_left;
	r = p->n_right;

	ty = DECREF(l->n_type) - FTN;

	s.sclass = AUTO;
	s.stype = ty;
	s.sdf = l->n_df;
	s.sap = l->n_ap;
	oalloc(&s, &autooff);
	q = block(REG, NIL, NIL, INCREF(ty), l->n_df, l->n_ap);
	regno(q) = FPREG;
	q = block(MINUS, q, bcon(autooff/SZCHAR), INCREF(ty),
	    l->n_df, l->n_ap);

	/* insert hidden assignment at beginning of list */
	if (r->n_op != CM) {
		p->n_right = block(CM, q, r, INCREF(ty), l->n_df, l->n_ap);
	} else {
		for (t = r; t->n_left->n_op == CM; t = t->n_left)
			;
		t->n_left = block(CM, q, t->n_left, INCREF(ty),
		    l->n_df, l->n_ap);
	}

	return p;
}

int
p1arg_overflow(NODE* r)
{

  NODE* q = r;
  int sz, off = 0, last = 0, n_regs = 0, n_fregs = 0;

	if (! r->n_left)
		last = 1;

printf("; r: %p, op: %d, n_left: %p n_right: %p last = %d\n", 
					r, r->n_op, r->n_left, r->n_right, last);
return 0;		
	while (1)  {
printf("; r: %p, op: %d, n_left: %p n_right: %p last = %d\n", 
					r, r->n_op, r->n_left, r->n_right, last);
		if (q->n_op == STARG) {
		//printf("STARG\n");
			sz = tsize(q->n_type, q->n_df, q->n_ap) / SZINT;
			switch (sz) {
				case 1:
					n_regs += 1;
					break;
				case 2: 
					n_regs += 2;
					break;
				default:
					/* struct of length >= 3 has been passed directly */
					n_regs += 1;
					off += sz * (SZINT/SZCHAR);
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
		
#if 1
		if (last)
			break;
		r = r->n_left;
		if (r->n_op == CM)
			q = r->n_right;
		else {
			q = r;
			last = 1;
		}
#endif
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
 * Called with a function call with arguments as argument.
 * This is done early in buildtree() and only done once.
 */
NODE *
funcode(NODE *p)
{
	int regnum = A0;
	int fregnum = FA0;
	int llregnum = DA0;
 	NODE *r, *q;
	int off = 0;
	
	if (DECREF(p->n_left->n_type) == STRTY+FTN ||
		DECREF(p->n_left->n_type) == UNIONTY+FTN)
			p = retstruct(p);

	r = p->n_right;
	off = p1arg_overflow(r);

	//p1fwalk(r, eprint, 0);
	if (off > 0) {
		off = (off+15) & ~15; /* 16-byte aligned */ 
		q = block(ICON, NIL, NIL, INT, 0, 0);
		slval(q, off);
		p->n_right = block(CM, p->n_right, q, INT, 0, 0);
		p->n_qual = off;
	}  else
		p->n_qual = 0;
	
//printf("funcode %d, 0x%x\n", off, p->n_right);	

	p->n_right = moveargs(p->n_right, &regnum, &fregnum, &llregnum);

	if (p->n_right == NULL)
		p->n_op += (UCALL - CALL);

	return p;

}
