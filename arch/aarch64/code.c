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

/*
 *  Stuff for pass1.
 */

#include <assert.h>
#include <limits.h>

#include "pass1.h"

#ifdef LANG_CXX
#define p1listf listf
#define p1tfree tfree
#else
#define NODE P1ND
#define talloc p1alloc
#define tcopy p1tcopy
#define nfree p1nfree
#define attr ssdesc
#undef n_type
#define n_type ptype
#undef n_qual
#define n_qual pqual
#undef n_df
#define n_df pdf
#define	sap sss
#define	n_ap pss
#endif

static int rvnr;
int p1maxstacksize = 0; /* XXX - remove, move calculation to pass2 */


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
#ifdef MACHOABI
		case PICLDATA:
		case PICDATA: name = ".section .data.rel.rw,\"aw\""; break;
		case PICRDATA: name = ".section .data.rel.ro,\"aw\""; break;
		case RDATA: name = ".const_data"; break;
		case STRNG: name = ".cstring"; break;
#else
		case RDATA: name = ".section .rodata"; break;
		case STRNG: name = ".section .rodata"; break;
		case PICLDATA: name = ".section .data.rel.local,\"aw\",@progbits";break;
		case PICDATA: name = ".section .data.rel.rw,\"aw\",@progbits"; break;
		case PICRDATA: name = ".section .data.rel.ro,\"aw\",@progbits"; break;
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
	char *n;

	n = getexname(sp);
#ifdef USE_GAS
	if (ISFTN(t))
		printf("\t.type %s,%%function\n", n);
#endif
	if (sp->sclass == EXTDEF)
		printf("\t.global %s\n", n);
	if (sp->slevel == 0 && !ISFTN(sp->stype))
		printf("%s:\n", n);
	else
		printf(LABFMT ":\n", sp->soffset);
}

/*
 * Create a node on stack storage.
 *
 * This is almost equivalent to cstknode(), with the
 * exception that this never creates TEMP nodes, only
 * stack nodes.
 *
 * XXX - I suggest this to be moved to ccom/trees.c
 * & cxxcom/trees.c as a generic routine.
 */
static NODE *
mkstknode(TWORD t, union dimfun *df, struct attr *ss)
{
	struct symtab s;
	NODE *n;

	s.stype = t;
	s.squal = 0;
	s.sdf = df;
	s.sap = ss;
	s.sclass = AUTO;
	s.soffset = NOOFFSET;
	s.sname = "mkstknode"; /* or else nametree() accesses invalid string */

	oalloc(&s, &autooff);
	n = nametree(&s);
	n->n_sp = 0;
	return n;
}

/* Put a symbol in a temporary
 * used by bfcode() and its helpers
 */
static void
putintemp(struct symtab *sym, NODE *q)
{
	NODE *p;

	p = tempnode(0, sym->stype, sym->sdf, sym->sap);
	p = buildtree(ASSIGN, p, q);
	sym->soffset = regno(p->n_left);
	sym->sflags |= STNODE;
	ecomp(p);
}

/* setup a 64-bit parameter (double/ldouble/longlong)
 * used by bfcode() */
static void
param_64bit(struct symtab *sym, int *regp, int *stackofsp, int dotemps)
{
	NODE *q;

	if (*regp >= NARGREGS) {
		sym->soffset = *stackofsp + ARGINIT;
		q = nametree(sym);
		*stackofsp += SZLONG;
		if (dotemps) {
		        putintemp(sym, q);
		}
	} else {
		q = block(REG, NIL, NIL, sym->stype, sym->sdf, sym->sap);
		regno(q) = R0 + (*regp)++;
		putintemp(sym, q);
	}
}

/* setup a 32-bit param
 * used by bfcode() */
static void
param_32bit(struct symtab *sym, int *regp, int *stackofsp, int dotemps)
{
	/* On aarch64, setup of 32-bit and 64-bit args
	   are equivalent.
	   Each argument either occupies one register,
	   or 8-byte aligned stack.
	*/
        param_64bit(sym, regp, stackofsp, dotemps);
}

/* setup a double param
 * used by bfcode() */
static void
param_double(struct symtab *sym, int *fregp, int *stackofsp, int dotemps)
{
	NODE *q;

	/* Only hard-float ABI reaches here.
	   soft-float ABI parameters are handled
	   by param_64bit.
	*/
	if (*fregp >= NARGREGS) {
		sym->soffset = *stackofsp + ARGINIT;
		q = nametree(sym);
		*stackofsp += SZLONG;
		if (dotemps) {
		        putintemp(sym, q);
		}
	} else {
		q = block(REG, NIL, NIL, sym->stype, sym->sdf, sym->sap);
		regno(q) = V0 + (*fregp)++;
		putintemp(sym, q);
	}
}

/* setup a float param
 * used by bfcode() */
static void
param_float(struct symtab *sym, int *fregp, int *stackofsp, int dotemps)
{
	/* Only hard-float ABI reaches here.
	   soft-float ABI parameters are handled
	   by param_32bit.

	   On aarch64, setup of 32-bit and 64-bit FP args
	   are equivalent.
	   Each argument either occupies one register,
	   or 8-byte aligned stack.
	*/
	param_double(sym, fregp, stackofsp, dotemps);
}

/* setup the hidden pointer to struct return parameter
 * used by bfcode() */
static void
param_retstruct(void)
{
	NODE *p, *q;

	p = tempnode(0, PTR-FTN+cftnsp->stype, 0, cftnsp->sap);
	rvnr = regno(p);
	q = block(REG, NIL, NIL, PTR+STRTY, 0, cftnsp->sap);
	regno(q) = R8;
	p = buildtree(ASSIGN, p, q);
	ecomp(p);
}


/* setup struct parameter
 * push the registers out to memory
 * used by bfcode() */
static void
param_struct(struct symtab *sym, int *regp, int *fregp, int *stackofsp)
{
	int reg = *regp;
	NODE *p, *q, *s;
	int navail;
	int sz, szb;
	int num;
	int i;

	navail = NARGREGS - reg;
	navail = navail < 0 ? 0 : navail;
	sz = tsize(sym->stype, sym->sdf, sym->sap);
	szb = sz / SZCHAR;
	num = (sz+SZLONGLONG-1) / SZLONGLONG; /* ceil(sz/8) */

	/* XXX - HFA structs are not handled yet */

	if (szb > 16) {
		/*
		 * the struct is larger than 16 bytes. it was copied by the caller
		 * and lives in their stack frame. obtain the pointer to it.
		 */
		/*
		 * XXX: Unnecessary copy.
		 * For ABI reasons, this C "struct by value" parameter is actually
		 * passed indirectly (hidden pointer). Our IR/symbol model cannot
		 * currently represent "indirect-by-ABI" params, so we materialize
		 * a local stack copy and treat it as the canonical object.
		 *
		 * Proper fix: represent indirect struct params explicitly (e.g. param
		 * becomes a PTR-to-struct with implicit deref at uses), or perform a
		 * dedicated IR lowering pass that rewrites references to use the hidden
		 * pointer instead of forcing a memcpy.
		 */
		s = cstknode(sym->stype, sym->sdf, sym->sap);
		sym->soffset = AUTOINIT - autooff;

		if (navail == 0) {
			/*
			 * we have no free argument register left, read pointer
			 * from stack.
			 */
			q = block(REG, NIL, NIL, INCREF(PTR+STRTY), 0, sym->sap);
			regno(q) = FPREG;
			q = block(PLUS, q, bcon(ARGINIT/SZCHAR + *stackofsp), INCREF(PTR+STRTY), 0, sym->sap);
			*stackofsp += SZLONGLONG;
			q = buildtree(UMUL, q, 0);

			/* XXX - perform unnecessary copy */
			q = buildtree(UMUL, q, 0);
			p = buildtree(ASSIGN, s, q);
			ecomp(p);
		} else {
			/*
			 * we have at least one free argument register, read the
			 * pointer from the available register.
			 */
			q = block(REG, NIL, NIL, PTR+STRTY, 0, sym->sap);
			regno(q) = R0 + reg++;

			/* XXX - perform unnecessary copy */
			q = buildtree(UMUL, q, 0);
			p = buildtree(ASSIGN, s, q);
			ecomp(p);
		}
	} else {
		/*
		 * the struct is <=16 bytes in size. it was packed by the caller.
		 */
		if (navail < num) {
			/*
			 * we are over available argument registers.
			 * the caller pushed the struct to the call stack.
			 */
			sym->soffset = ARGINIT + *stackofsp;
			*stackofsp += num * SZLONGLONG;
		} else {
			/*
			 * we have enough free argument registers.
			 * reconstruct the packed struct in the stack.
			 */
			for (i = 0; i < num; i++) {
				s = mkstknode(LONGLONG, 0, 0); /* 8-byte chunk */
				q = block(REG, NIL, NIL, LONGLONG, 0, 0);
				regno(q) = R0 + reg + num-i-1;
				p = buildtree(ASSIGN, s, q);
				ecomp(p);
				if (i == num - 1)
					sym->soffset = AUTOINIT - autooff;
			}
			reg += num;
		}
	}

	*regp = reg;
}


/*
 * Beginning-of-function code:
 *
 * 'sp' is an array of indices in symtab for the arguments
 * 'cnt' is the number of arguments
 */
void
bfcode(struct symtab **sp, int cnt)
{
	int saveallargs, i, reg, freg, stackofs;
	saveallargs = i = reg = freg = stackofs = 0;
	p1maxstacksize = 0;

#if defined(MACHOABI)
	/*
	 * On aarch64 Darwin ABI, varargs are already spilled
	 * to memory by caller. No need to spill from callee side.
	 */
	saveallargs = 0;
#else
	/*
	 * Detect if this function has ellipses and save all
	 * argument registers onto stack.
	 */
	if (cftnsp->sdf->dlst)
		saveallargs = pr_hasell(cftnsp->sdf->dlst);
#endif

	/* if returning a structure, move the hidden argument into a TEMP */
	if (cftnsp->stype == STRTY+FTN || cftnsp->stype == UNIONTY+FTN) {
		param_retstruct();
	}

	/* recalculate the arg offset and create TEMP moves */
	for (i = 0; i < cnt; i++) {

		if (sp[i] == NULL)
			continue;

	        if (sp[i]->stype == STRTY || sp[i]->stype == UNIONTY) {
			param_struct(sp[i], &reg, &freg, &stackofs);
		} else if (DEUNSIGN(sp[i]->stype) == LONGLONG  || DEUNSIGN(sp[i]->stype) == LONG) {
			param_64bit(sp[i], &reg, &stackofs, xtemps && !saveallargs);
		} else if (sp[i]->stype == DOUBLE || sp[i]->stype == LDOUBLE) {
			if (features(FEATURE_HARDFLOAT))
				param_double(sp[i], &freg, &stackofs, xtemps && !saveallargs);
			else
				param_64bit(sp[i], &reg, &stackofs, xtemps && !saveallargs);
		} else if (sp[i]->stype == FLOAT) {
			if (features(FEATURE_HARDFLOAT))
				param_float(sp[i], &freg, &stackofs, xtemps && !saveallargs);
			else
				param_32bit(sp[i], &reg, &stackofs, xtemps && !saveallargs);
		} else {
			param_32bit(sp[i], &reg, &stackofs, xtemps && !saveallargs);
		}
	}

	/* if saveallargs, save the rest of the args onto the stack */
	/* XXX - investigate, rewrite for FP regs */
	while (saveallargs && reg < NARGREGS) {
      		NODE *p, *q;
		int off = ARGINIT/SZINT + reg;
		q = block(REG, NIL, NIL, INT, 0, 0);
		regno(q) = R0 + reg++;
		p = block(REG, NIL, NIL, INT, 0, 0);
		regno(p) = SPREG;
		p = block(PLUS, p, bcon(4*off), INT, 0, 0);
		p = block(UMUL, p, NIL, INT, 0, 0);
		p = buildtree(ASSIGN, p, q);
		ecomp(p);
	}

}

/*
 * End-of-Function code:
 */
void
efcode(void)
{
	NODE *p, *q, *t;
	int tempnr, sz, szb, num, i;

	if (cftnsp->stype != STRTY+FTN && cftnsp->stype != UNIONTY+FTN)
		return;

	sz = tsize(DECREF(cftnsp->stype), cftnsp->sdf, cftnsp->sap);
	szb = sz / SZCHAR;
	num = (sz+SZLONGLONG-1) / SZLONGLONG;

	/*
	 * At this point, the address of the return structure on
	 * has been FORCEd to RETREG, which is R0.
	 */

	/* move the pointer out of R0 to a tempnode */
	q = block(REG, NIL, NIL, PTR+STRTY, 0, cftnsp->sap);
	q->n_rval = R0;
	p = tempnode(0, PTR+STRTY, 0, cftnsp->sap);
	tempnr = regno(p);
	p = buildtree(ASSIGN, p, q);
	ecomp(p);

	/* get the address from the tempnode */
	q = tempnode(tempnr, PTR+STRTY, 0, cftnsp->sap);
	
	if (szb > 16) {
		/*
		 * Struct exceeds 16 bytes in size.
		 * We want to copy the contents from there to the address
		 * we placed into the tempnode "rvnr".
		 */
		q = buildtree(UMUL, q, NIL);
		/* get the structure destination */
		p = tempnode(rvnr, PTR+STRTY, 0, cftnsp->sap);
		p = buildtree(UMUL, p, NIL);

		/* struct assignment */
		p = buildtree(ASSIGN, p, q);
		ecomp(p);
	} else {
		/*
		 * Struct is <= 16 bytes in size.
		 * We want to place the contents from there to
		 * R0, and if >8 bytes R1.
		 */
		for (i = 0; i < num; i++) {
			/* divide struct to 8-byte chunk */
			t = block(SCONV, tcopy(q), NIL, PTR+LONGLONG, 0, 0);
			t = block(PLUS, t, bcon(8*i), PTR+LONGLONG, 0, 0);
			t = buildtree(UMUL, t, NIL);

			/* get return register (R0 or R1) */
			p = block(REG, NIL, NIL, LONGLONG, 0, 0);
			regno(p) = R0 + num-i-1;

			/* register assignment */
			p = buildtree(ASSIGN, p, t);
			ecomp(p);
		}
	}
}

/*
 * End-of-job: called just before final exit.
 */
void
ejobcode(int flag)
{
	printf("\t.ident \"PCC: %s\"\n", VERSSTR);
}

/*
 * Beginning-of-job: called before compilation starts
 *
 * Initialise data structures specific for the local machine.
 */
void
bjobcode(void)
{
	/* aarch64 names for some asm constant printouts */
	astypnames[INT] = astypnames[UNSIGNED] = "\t.long";
	astypnames[LONG] = astypnames[ULONG] = "\t.quad";
}

/*
 * fix up type of field p
 */
void
fldty(struct symtab *p)
{
}

/*
 * Build target-dependent switch tree/table.
 *
 * Return 1 if successfull, otherwise return 0 and the
 * target-independent tree will be used.
 */
int
mygenswitch(int num, TWORD type, struct swents **p, int n)
{
	return 0;
}


/*
 * Straighten a chain of CM ops so that the CM nodes
 * only appear on the left node.
 *
 *	  CM	       CM
 *	CM  CM	   CM  b
 *       x y  a b	CM  a
 *		      x  y
 */
static NODE *
straighten(NODE *p)
{
	NODE *r = p->n_right;

	if (p->n_op != CM || r->n_op != CM)
		return p;

	p->n_right = r->n_left;
	r->n_left = p;

	return r;
}

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


/* push arg onto the stack */
/* called by moveargs() */
static NODE *
pusharg(NODE *p, int *stackofsp)
{
	NODE *q;
	int sz;

	/* convert to register size, if smaller */
	sz = tsize(p->n_type, p->n_df, p->n_ap);
	if (sz < SZINT)
		p = block(SCONV, p, NIL, INT, 0, 0);

	q = block(REG, NIL, NIL, INT, 0, 0);
	regno(q) = SP;

	q = block(PLUS, q, bcon(*stackofsp), INT, 0, 0);
	*stackofsp += SZLONG / 8;

	q = block(UMUL, q, NIL, p->n_type, p->n_df, p->n_ap);

	return buildtree(ASSIGN, q, p);
}


/* setup call stack with 64-bit argument */
/* called from moveargs() */
static NODE *
movearg_64bit(NODE *p, int *regp)
{
	int reg = *regp;
	NODE *q;

	q = block(REG, NIL, NIL, p->n_type, p->n_df, p->n_ap);
	regno(q) = R0 + reg++;
	q = buildtree(ASSIGN, q, p);

	*regp = reg;
	return q;
}

/* setup call stack with 32-bit argument */
/* called from moveargs() */
static NODE *
movearg_32bit(NODE *p, int *regp)
{
	/* On aarch64, passing of 32-bit and 64-bit args
	   are equivalent.
	   Each argument either occupies one register,
	   or 8-byte aligned stack.
	*/
	return movearg_64bit(p, regp);
}


/* setup call stack with float/double argument */
/* called from moveargs() */
static NODE *
movearg_double(NODE *p, int *regp)
{
	/* Only hard-float ABI reaches here.
	   soft-float ABI parameters are handled
	   by movearg_64bit.
	*/
	int reg = *regp;
	NODE *q;

	q = block(REG, NIL, NIL, p->n_type, p->n_df, p->n_ap);
	regno(q) = V0 + reg++;
	q = buildtree(ASSIGN, q, p);

	*regp = reg;
	return q;
}

/* setup call stack with float/double argument */
/* called from moveargs() */
static NODE *
movearg_float(NODE *p, int *regp)
{
	/* Only hard-float ABI reaches here.
	   soft-float ABI parameters are handled
	   by movearg_32bit.

	   On aarch64, passing of 32-bit and 64-bit FP args
	   are equivalent.
	   Each argument either occupies one register,
	   or 8-byte aligned stack.
	*/
        return movearg_double(p, regp);
}

/* setup call stack with a structure */
/* called from moveargs() */
static NODE *
movearg_struct(NODE *p, int *regp, int *fregp, int *stackofsp)
{
	int reg = *regp;
	NODE *l, *q, *t, *r, *s;
	int navail;
	int num;
	int sz, szb;
	int i;

	assert(p->n_op == STARG);

	navail = NARGREGS - reg;
	navail = navail < 0 ? 0 : navail;
	sz = tsize(p->n_type, p->n_df, p->n_ap);
	szb = sz / SZCHAR;
	num = (sz+SZLONGLONG-1) / SZLONGLONG; /* ceil(sz/8) */

	/* remove STARG node */
	l = p->n_left;
	nfree(p);

	/* XXX - HFA structs are not handled yet */

	if (szb > 16) {
		/*
		 * the struct is larger than 16 bytes. create a copy of it
		 * and obtain a pointer to it.
		 */
		t = buildtree(UMUL, l, NIL);
		s = cstknode(t->n_type, t->n_df, t->n_ap); /* free real estate */
		t = buildtree(ASSIGN, s, t);
		t = nfree(t);
		q = tcopy(s->n_left); /* pointer to copied struct */

		if (navail == 0) {
			/*
			 * we have no free argument register left, push the pointer
			 * to the stack.
			 */
		        q = pusharg(q, stackofsp);
		} else {
			/*
			 * we have at least one free argument register, move the
			 * pointer to the available register.
			 */
			r = block(REG, NIL, NIL, PTR+STRTY, 0, q->n_ap);
			regno(r) = R0 + reg++;
			q = buildtree(ASSIGN, r, q);
		}
		q = block(CM, q, t, INT, 0, 0);

	} else {
		q = NULL;
		if (navail < 2) {
			/*
			 * we have less than 2 free argument registers, and the struct
			 * is <=16 bytes in size. push the struct on the stack.
			 */
			for (i = 0; i < num; i++) {
				t = block(SCONV, tcopy(l), NIL, PTR+LONGLONG, 0, 0);
				t = block(PLUS, t, bcon(8*i), PTR+LONGLONG, 0, 0);
				t = buildtree(UMUL, t, NIL);
				r = pusharg(t, stackofsp);

				if (i == 0)
					q = r;
				else
					q = block(CM, q, r, INT, 0, 0);
			}
		} else {
			/*
			 * we have >=2 free argument registers, and the struct
			 * is <=16 bytes in size. pack the struct in registers.
			 */
			for (i = 0; i < num; i++) {
				t = block(SCONV, tcopy(l), NIL, PTR+LONGLONG, 0, 0);
				t = block(PLUS, t, bcon(8*i), PTR+LONGLONG, 0, 0);
				t = buildtree(UMUL, t, NIL);

				r = block(REG, NIL, NIL, LONGLONG, 0, 0);
				regno(r) = R0 + reg++;
				r = buildtree(ASSIGN, r, t);

				if (i == 0)
					q = r;
				else
					q = block(CM, q, r, INT, 0, 0);
			}
		}
		p1tfree(l);
	}

	*regp = reg;
	return q;
}

static NODE *
moveargs(NODE *p, int vararg, int *idxp, int *regp, int *fregp, int *stackofsp)
{
	NODE *r, **rp;

	if (p->n_op == CM) {
		p->n_left = moveargs(p->n_left, vararg, idxp, regp, fregp, stackofsp);
		r = p->n_right;
		rp = &p->n_right;
	} else {
		r = p;
		rp = &p;
	}

	int isfp = features(FEATURE_HARDFLOAT)
		&& (r->n_type == DOUBLE || r->n_type == LDOUBLE
		 || r->n_type == FLOAT);

        if (r->n_op == STARG) {
		*rp = movearg_struct(r, regp, fregp, stackofsp);
	} else if ((*idxp >= vararg)
		   || (isfp && *fregp >= NARGREGS)
		   || (!isfp && *regp >= NARGREGS)) {
		*rp = pusharg(r, stackofsp);
	} else if (DEUNSIGN(r->n_type) == LONGLONG) {
		*rp = movearg_64bit(r, regp);
	} else if (r->n_type == DOUBLE || r->n_type == LDOUBLE) {
		if (features(FEATURE_HARDFLOAT))
			*rp = movearg_double(r, fregp);
		else
			*rp = movearg_64bit(r, regp);
	} else if (r->n_type == FLOAT) {
		if (features(FEATURE_HARDFLOAT))
			*rp = movearg_float(r, fregp);
		else
			*rp = movearg_32bit(r, regp);
	} else {
		*rp = movearg_32bit(r, regp);
	}

	(*idxp)++;
	return straighten(p);
}

NODE *
builtin_frame_address(const struct bitable *bt, NODE *a)
{
	assert(0);
	return NULL;
}

NODE *
builtin_return_address(const struct bitable *bt, NODE *a)
{
	assert(0);
	return NULL;
}

NODE *
builtin_cfa(const struct bitable *bt, NODE *a)
{
	assert(0);
	return NULL;
}

/*
 * Sort arglist so that register assignments ends up last.
 * Copied over from amd64/code.c.
 *
 * XXX - This routine creates an absurd amount of read/write
 * instructions when -xtemps is disabled. It works, but it
 * is suboptimal.
 */
static int
argsort(NODE *p)
{
	NODE *q, *r;
	int rv = 0;

	if (p->n_op != CM) {
		if (p->n_op == ASSIGN && p->n_left->n_op == REG &&
		    coptype(p->n_right->n_op) != LTYPE) {
			q = tempnode(0, p->n_type, p->n_df, p->n_ap);
			r = tcopy(q);
			p->n_right = buildtree(COMOP,
			    buildtree(ASSIGN, q, p->n_right), r);
		}
		return rv;
	}
	if (p->n_right->n_op == CM) {
		/* fixup for small structs in regs */
		q = p->n_right->n_left;
		p->n_right->n_left = p->n_left;
		p->n_left = p->n_right;
		p->n_right = p->n_left->n_right;
		p->n_left->n_right = q;
	}
	if (p->n_right->n_op == ASSIGN && p->n_right->n_left->n_op == REG &&
	    coptype(p->n_right->n_right->n_op) != LTYPE) {
		/* move before everything to avoid reg trashing */
		q = tempnode(0, p->n_right->n_type,
			     p->n_right->n_df, p->n_right->n_ap);
		r = tcopy(q);
		p->n_right->n_right = buildtree(COMOP,
		    buildtree(ASSIGN, q, p->n_right->n_right), r);
	}
	if (p->n_right->n_op == ASSIGN && p->n_right->n_left->n_op == REG) {
		if (p->n_left->n_op == CM &&
		    p->n_left->n_right->n_op == STASG) {
			q = p->n_left->n_right;
			p->n_left->n_right = p->n_right;
			p->n_right = q;
			rv = 1;
		} else if (p->n_left->n_op == STASG) {
			q = p->n_left;
			p->n_left = p->n_right;
			p->n_right = q;
			rv = 1;
		}
	}
	return rv | argsort(p->n_left);
}

/*
 * Called with a function call with arguments as argument.
 * This is done early in buildtree() and only done once.
 */
NODE *
funcode(NODE *p)
{
	int reg, freg, stackofs, idx;
	reg = freg = stackofs = idx = 0;
	int vararg = INT_MAX;

#if defined(MACHOABI)
	if (p->n_left->n_df)
		vararg = pr_ellidx(p->n_left->n_df->dlst);
	if (vararg < 0)
		vararg = INT_MAX;
#endif

	p->n_right = moveargs(p->n_right, vararg, &idx, &reg, &freg, &stackofs);

	/* Must sort arglist so that STASG ends up first */
	/* This avoids registers being clobbered */
	while (argsort(p->n_right))
		;

	if (p->n_right == NULL)
		p->n_op += (UCALL - CALL);

	if (stackofs > p1maxstacksize)
		p1maxstacksize = stackofs;

	return p;
}
