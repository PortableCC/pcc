/*      $Id$     */
/*
 * Copyright (c) 2023 Anders Magnusson (ragge@ludd.ltu.se).
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

#include <inttypes.h>

#include "pass1.h"

#ifdef NEWPARAMS

static struct callspec *cftns;

static P1ND *
nmtree(int off, int type, union dimfun *df, struct attr *ap)
{
	struct symtab spp, *sp = &spp;

	sp->soffset = off;
	sp->sclass = PARAM;
	sp->slevel = 2; /* ??? */
	sp->sflags = 0;
	sp->sname = "foo";
	sp->stype = type;
	sp->squal = 0;
	sp->sdf = df;
	sp->sap = ap;
	return nametree(sp);
}

/*
 * Called to get correct initial argument assign for an entered function.
 */
void
fun_enter(struct symtab *sp, struct symtab **spp, int nargs)
{
	struct callspec *cs;
	struct rdef *rp;
	P1ND *p, *q;
	int i;

	cs = cftns = tmpcalloc(sizeof(struct callspec) +
	    nargs * sizeof(struct rdef));

	/* prepare return values */
	cs->rv.type = DECREF(sp->stype); /* remove FTN */
	cs->rv.df = sp->sdf;
	cs->rv.ap = sp->sap;

	/* prepare parameter values */
	for (i = 0; i < nargs; i++) {
		cs->av[i].type = spp[i]->stype;
		cs->av[i].df = spp[i]->sdf;
		cs->av[i].ap = spp[i]->sap;
	}
	cs->nargs = nargs;
	cs->rv.flags = RV_CALLEE;

	mycallspec(cs);

	if (cs->rv.flags & RV_STRET) {
		q = tempnode(0, INTPTR, 0, 0);
		i = regno(q);
		if (cs->rv.flags & RV_ARG0_REG) {
			p = block(REG, 0, 0, INTPTR, 0, 0);
			regno(p) = cs->rv.reg[0];
		} else
			p = nmtree(cs->rv.off, INTPTR, 0, 0);
		ecomp(buildtree(ASSIGN, q, p));
		cs->rv.off = i;		/* keep tempnr in off */
	}

	for (i = 0; i < cs->nargs; i++) {
		rp = &cs->av[i];
		sp = spp[i];
		//sz = (int)tsize(rp->type, rp->df, rp->ap);
		if (rp->flags & AV_STREG) {
			// st = (int)tsize(off, 0, 0);
			cerror("AV_STREG");
		} else if (rp->flags & AV_REG2) {
			cerror("AV_REG2");
		} else if (rp->flags & AV_REG) {
			/* arg in reg, always save in temp */
			p = block(REG, 0, 0, sp->stype, sp->sdf, sp->sap);
			regno(p) = rp->reg[0];
			q = tempnode(0, sp->stype, sp->sdf, sp->sap);
			sp->soffset = regno(q);
			sp->sflags |= STNODE;
			ecomp(buildtree(ASSIGN, q, p));
		} else if (rp->flags & AV_STK) {
			/* argument on stack, move to temp if optimizing */
			sp->soffset = rp->off;
			if (xtemps && !ISSOU(sp->stype) && cisreg(sp->stype) &&
			    ((cqual(sp->stype, sp->squal) & VOL) == 0)) {
				p = nametree(sp);
				q = tempnode(0, p->n_type, p->n_df, p->n_ap);
				sp->soffset = regno(q);
				sp->sflags |= STNODE;
				ecomp(buildtree(ASSIGN, q, p));
			}
		} else
			cerror("no arg");
	}
}

/*
 * Setup for return values from function just compiled.
 */
void
fun_leave(void)
{
	struct callspec *cs = cftns;
	extern P1ND *cftnod;
	P1ND *p, *q, *cn = cftnod;
	int sz;

	if (cn == NULL)
		return;
	if (cn->n_op != TEMP) {
		p1fwalk(cn, eprint, 0);
		cerror("cn->n_op != TEMP");
	}

	if (cs->rv.flags & RV_RETREG) {
		/* scalar/float return in registers */
		p = block(REG, 0, 0, cn->n_type, cn->n_df, cn->n_ap);
		regno(p) = cs->rv.reg[0];
		ecomp(buildtree(ASSIGN, p, p1tcopy(cn)));
	} else if (cs->rv.flags & RV_STREG) {
		/* struct return in regs,  struct ptr in cn */
		sz = (int)tsize(cs->rv.type, cs->rv.df, cs->rv.ap);
		cn->n_type = cs->rv.rtp+PTR;
		if (sz > (int)tsize(cs->rv.rtp, 0, 0)) {
			/* must move second word */
			q = buildtree(PLUS, p1tcopy(cn), bcon(1));
			q = buildtree(UMUL, q, 0);
			p = block(REG, NULL, NULL, cs->rv.rtp, 0, 0);
			regno(p) = cs->rv.reg[1];
			q = (buildtree(ASSIGN, p, q));
			ecomp(q);
		}
		q = buildtree(UMUL, p1tcopy(cn), 0);
		p = block(REG, NULL, NULL, cs->rv.rtp, 0, 0);
		regno(p) = cs->rv.reg[0];
		ecomp(buildtree(ASSIGN, p, q));
	} else if (cs->rv.flags & RV_STRET) {
		/* Create struct assignment */
		q = tempnode(cs->rv.off, PTR+cs->rv.type, cs->rv.df, cs->rv.ap);
		q = buildtree(UMUL, q, NULL);
		p = buildtree(UMUL, p1tcopy(cn), NULL);
		p = buildtree(ASSIGN, q, p);
		ecomp(p);

		if (cs->rv.flags & RV_RETADDR) {
			q = tempnode(cs->rv.off, INTPTR, 0, 0);
			p = block(REG, NULL, NULL, INTPTR, 0, 0);
			regno(p) = cs->rv.reg[1];
			ecomp(buildtree(ASSIGN, p, q));
		}
	}
}

#if 0
/*
 * Put arguments at the right place for a function call.
 */
fun_call()
{

}
#endif
#endif

static FILE *pr_file;
int arglistcnt;

static void pr_alprnt(int off, int in);

/*
 * Prototypes are saved on a temp file and are kept track of using the
 * offset in the temp file.  The layout in the temp file is (longword):
 *	first: argument type
 *	next:  (if type specifies) pointer to struct/union description.
 *	next:  (if type specifies) pointer into dimension array.
 * Last type may be TELLIPSIS.
 * Argument list ends with TNULL.
 */

static void
pr_err(char *e)
{
	fprintf(stderr, "prototype file: %s: ", e);
	perror(NULL);
	exit(1);
}

static void
pr_wr(int w)
{
if (pdebug > 2) printf("pr_wr: %#x\n", w);
	if (putw(w, pr_file))
		pr_err("pr_wr");
}

static int
pr_rd(void)
{
	int w;

	w = getw(pr_file);
if (pdebug > 2) printf("pr_rd: %#x\n", w);
	if (ferror(pr_file) || feof(pr_file))
		pr_err("pr_rd");
	return w;
}

static void
pr_wptr(uintptr_t w)
{
	pr_wr(w);
	w >>= 16;
	if (sizeof(uintptr_t) > sizeof(int))
		pr_wr(w >> 16);
}

static uintptr_t
pr_rptr(void)
{
	uintptr_t w, w2;

	w = w2 = pr_rd();
	if (sizeof(uintptr_t) > sizeof(int)) {
		w &= 0xffffffffL;
		w2 = pr_rd() << 16;
		w2 = (w2 << 16) | w;
	}
	return w2;
}

static void
pr_init(void)
{
	if ((pr_file = tmpfile()) == NULL)
		pr_err("pr_init");
	arglistcnt = sizeof(int);
}

static void
pr_seek(int off)
{
	if (fseek(pr_file, off, SEEK_SET))
		pr_err("pr_seek");
}

static int
pr_tell(void)
{
	int w;

	if ((w = ftell(pr_file)) < 0)
		pr_err("pr_tell");
	return w;
}

/*
 * Write (or compare) prototype info for one parameter.
 */
static void
argeval(P1ND *p)
{
	uintptr_t ptr1, ptr2;
	int type, tw;

	ptr1 = ptr2 = -1;
	/* convert arrays to pointers */
	if (ISARY(p->n_type)) {
		p->n_type += (PTR-ARY);
		p->n_df++;
	}
	/* convert function to function pointer */
	if (ISFTN(p->n_type))
		p->n_type = INCREF(p->n_type);

	if (p->n_op == ELLIPSIS) {
		type = TELLIPSIS;
		p->n_op = ICON; /* for tfree() */
	} else
		type = p->n_type;
#ifdef GCC_COMPAT
	if (type == UNIONTY &&
	    attr_find(p->n_ap, GCC_ATYP_TRANSP_UNION)){
		/* transparent unions must have compatible types
		 * shortcut here: if pointers, set void *,
		 * otherwise btype  */
		struct symtab *sp = strmemb(p->n_ap);
		type = ISPTR(sp->stype) ? PTR|VOID : sp->stype;
	}
#endif
	if (ISSOU(BTYPE(type)))
		ptr1 = (uintptr_t)p->n_ap;
	for (tw = type; ISPTR(tw); tw = DECREF(tw))
		;
	if (tw > BTMASK)
		ptr2 = (uintptr_t)p->n_df;

	pr_wr(type);
	if ((intptr_t)ptr1 != -1)
		pr_wptr(ptr1);
	if ((intptr_t)ptr2 != -1)
		pr_wptr(ptr2);

}

#define	SEEKRD(x,y) { pr_seek(x); y = pr_rd(); }
#define	SEEKRDP(x,y) { pr_seek(x); y = (void *)pr_rptr(); }
#define	SEEKWR(x,y) { pr_seek(x); pr_wr(y); }

/*
 * Check if function is a varargs function.
 * Used by inline code, which cannot handle varargs.
 */
int
pr_hasell(int dsym)
{
	int i, t;

if (pdebug) printf("pr_hasell: dsym %d\n", dsym);
	SEEKRD(dsym, t);
	while (t != TNULL) {
		if (t == TELLIPSIS)
			return 1;
		if (ISSOU(BTYPE(t)))
			(void)pr_rptr();
		for (i = 0; t > BTMASK; t = DECREF(t))
			if (ISFTN(t) || ISARY(t))
				(void)pr_rptr();
		t = pr_rd();
	}
	return 0;
}

/*
 * Extract the important parts of arguments and put away them for 
 * prototype checking.
 * Return index pointer for this prototype argument list.
 */
int
pr_arglst(P1ND *n)
{
	int rv;

	if (pr_file == NULL)
		pr_init();

	rv = arglistcnt;
	if (pdebug)
		printf("arglst: pos %d\n", arglistcnt/(int)sizeof(int));
	pr_seek(arglistcnt);
	p1listf(n, argeval);
	pr_wr(TNULL);
	arglistcnt = ftell(pr_file);
	if (pdebug)
		printf("arglst: pos %d totsz %d\n",
		    arglistcnt/(int)sizeof(int), (arglistcnt-rv)/(int)sizeof(int));
	if (pdebug > 1)
		pr_alprnt(rv, 0);

	return rv;
}

static int
pr_chk2(TWORD type, union dimfun *dsym, union dimfun *ddef, int old)
{

	if (pdebug)
		printf("pr_chk2: type %#x usym %p udef %p old %d\n",
		    type, dsym, ddef, old);

	while (type > BTMASK) {
		switch (type & TMASK) {
		case ARY:
			/* may be declared without dimension */
			if (dsym->ddim == NOOFFSET)
				; /* XXX writeback */
			if (dsym->ddim < 0 && ddef->ddim < 0)
				; /* dynamic arrays as arguments */
			else if (ddef->ddim > 0 && dsym->ddim != ddef->ddim)
				return 1;
			dsym++, ddef++;
			break;
		case FTN:
			/* old-style function headers with function pointers
			 * will most likely not have a prototype.
			 * This is not considered an error.  */
			if (ddef->dlst == 0) {
#ifdef notyet
				werror("declaration not a prototype");
#endif
			} else if (pr_ckproto(dsym->dlst, ddef->dlst, old))
				return 1;
			dsym++, ddef++;
			break;
		}
		type = DECREF(type);
	}
	return 0;

}

/*
 * Compare two prototypes to see if they match.
 * p1 and p2 are offset into the prototype file.
 */
int
pr_ckproto(int usym, int udef, int old)
{
	union dimfun *u1, *u2;
	int t1, t2, tt2, ty, tyn;

	if (pdebug)
		printf("pr_ckproto: usym %d udef %d old %d\n",
		    usym/(int)sizeof(int), udef/(int)sizeof(int), old);

	if (usym == 0)
		return 0; /* no prototype */
	SEEKRD(usym, t1); usym += sizeof(int);
	if (cftnsp != NULL && udef == 0 && t1 == VOID)
		return 0; /* foo() { function with foo(void); prototype */
	if (udef == 0 && t1 != TNULL)
		return 1;
	SEEKRD(udef, t2); udef += sizeof(int);
	while (t1 != TNULL) {
		if (pdebug)
			printf("pr_ckproto2: t1 %#x t2 %#x\n", t1, t2);
		if (t1 == t2)
			goto done;
		/*
		 * If an old-style declaration, then all types smaller than
		 * int are given as int parameters.
		 */
		if (old) {
			ty = BTYPE(t1);
			tyn = BTYPE(t2);
			if (ty == tyn || ty != INT)
				return 1;
			if (tyn == CHAR || tyn == UCHAR ||
			    tyn == SHORT || tyn == USHORT)
				goto done;
			return 1;
		} else
			return 1;

done:		ty = BTYPE(t1);
		tt2 = t1;
		if (ISSOU(ty)) {
			SEEKRDP(usym, u1);
			SEEKRDP(udef, u2);
			usym += sizeof(intptr_t), udef += sizeof(intptr_t);
			if (suemeq((struct attr *)u1, (struct attr *)u2) == 0)
				return 1;
		}

		while (!ISFTN(tt2) && !ISARY(tt2) && tt2 > BTMASK)
			tt2 = DECREF(tt2);
		if (tt2 > BTMASK) {
			SEEKRDP(usym, u1);
			SEEKRDP(udef, u2);
			usym += sizeof(intptr_t), udef += sizeof(intptr_t);
			if (pr_chk2(tt2, u1, u2, old))
                                return 1;
                }
		SEEKRD(usym, t1);
		SEEKRD(udef, t2);
		usym += sizeof(int), udef += sizeof(int);
        }
        if (t1 != t2)
                return 1;
        return 0;

}

/*
 * Prototype check of an old-style declared function.
 * Do so by faking a function argument list.
 */
void
pr_oldstyle(struct symtab **as, int nparams)
{
	int i, waspos = arglistcnt;

	pr_seek(arglistcnt);
	if (cftnsp->sdf == NULL || cftnsp->sdf->dlst == 0)
		return; /* no prototype given */

	for (i = 0; i < nparams; i++) {
		int t = as[i]->stype;
		pr_wr(t);
		if (ISSOU(BTYPE(t)))
			pr_wptr((uintptr_t)as[i]->sap);
		while (!ISFTN(t) && !ISARY(t) && t > BTMASK)
			t = DECREF(t);
		if (t > BTMASK)
			pr_wptr((uintptr_t)as[i]->sdf);
	}
	pr_wr(TNULL);
	if (pr_ckproto(cftnsp->sdf->dlst, waspos, 1))
		uerror("function doesn't match prototype");
	arglistcnt = waspos; /* clear use */
}

static void
oldarg(P1ND *p)
{
	if (p->n_op == TYPE)
		uerror("type is not an argument");
	if (p->n_type == FLOAT) {
		P1ND *q = p1alloc();
		*q = *p; q = cast(q, DOUBLE, q->n_qual); *p = *q;
		p1nfree(q);
	}
}

static int isell;

/*
 * Check each argument against the stored prototype, cast
 * if needed, complain if needed.
 */
static void
protoarg(P1ND *p)
{
	struct attr *ap;
	union dimfun *dp;
	P1ND *q;
	int tp, t;

	/* quick out if varargs */
	if (isell) {
		oldarg(p);
		return;
	}

	/* Get both types */
//	tn = p->n_type;
	tp = pr_rd();

	/* handle varargs */
	if (tp == TELLIPSIS) {
		isell++;
		oldarg(p);
		return;
	}

#if 0
	/* Taking addresses of arrays are meaningless in expressions */
	/* but people tend to do that and also use in prototypes */
	/* this is mostly a problem with typedefs */
	if (ISARY(tn)) {
		if (ISPTR(tp) && ISARY(DECREF(tp)))
			tn = INCREF(tn);
		else
			tn += (PTR-ARY);
	} else if (ISPTR(tn) && !ISARY(DECREF(tn)) &&
	    ISPTR(tp) && ISARY(DECREF(tp))) {
		tn += (ARY-PTR);
		tn = INCREF(tn);
	}

	/* Check structs (tn=type, tp=arrt) */
	an = p->n_ap;
#endif
	ap = ISSOU(BTYPE(tp)) ? (void *)pr_rptr() : NULL;
	for (t = tp; ISPTR(t); t = DECREF(t))
		;
	dp = t > BTMASK ? (void *)pr_rptr() : NULL;

	q = p1alloc();
	*q = *p;
	q = ccast(q, tp, 0, dp, ap);
	*p = *q;
	p1nfree(q);

}

/*
 * Check against prototype (and cast arguments) for a function call.
 * f is function, a is argument list.
 */
void
pr_callchk(struct symtab *sp, P1ND *f, P1ND *a)
{
	int alp, t;

	if (f->n_df == NULL || f->n_df[0].dlst == 0) {
		/*
		 * Handle non-prototype declarations.
		 */
		if (f->n_op == NAME && f->n_sp != NULL) {
			if (strncmp(f->n_sp->sname, "__builtin", 9) != 0 &&
			    (f->n_sp->sflags & SINSYS) == 0)
				warner(Wmissing_prototypes, f->n_sp->sname);
		} else
			warner(Wmissing_prototypes, "<pointer>");

		/* floats must be cast to double */
		if (a == NULL)
			return; /* no args */
		p1listf(a, oldarg);
		return;
	}
	alp = f->n_df[0].dlst;
	SEEKRD(alp, t);
	if (t == VOID) {
		if (a != NULL)
			uerror("function takes no arguments");
		return;
	}
	if (a == NULL) {
		uerror("function needs arguments");
		return;
	}
#ifdef PCC_DEBUG
	if (pdebug) {
		printf("arglist for %s\n",
		    f->n_sp != NULL ? f->n_sp->sname : "function pointer");
		pr_alprnt(alp, 0);
	}
#endif

	isell = 0;
	pr_seek(alp);
	p1listf(a, protoarg);


}

#ifdef PCC_DEBUG
/*
 * Print a prototype.
 */
static void
pr_alprnt(int off, int in)
{
	struct attr *ap;
	union dimfun *df;
	TWORD t;
	int i = 0, j;

	pr_seek(off);

	for (; (t = pr_rd()) != TNULL; ) {
		for (j = in; j > 0; j--)
			printf("  ");
		printf("arg %d: ", i++);
		tprint(t, 0);
		while (t > BTMASK) {
			if (ISARY(t)) {
				df = (union dimfun *)pr_rptr();
				printf(" dim %d ", df->ddim);
			} else if (ISFTN(t)) {
				df = (union dimfun *)pr_rptr();
				if (df->dlst) {
					int p = pr_tell();
					printf("\n");
					pr_alprnt(df->dlst, in+1);
					pr_seek(p);
				}
			}
			t = DECREF(t);
		}
		if (ISSOU(t)) {
			ap = (struct attr *)pr_rptr();
			printf(" (size %d align %d)", (int)tsize(t, 0, ap),
			    (int)talign(t, ap));
		}
		printf("\n");
	}
	if (in == 0)
		printf("end arglist\n");
}
#endif

