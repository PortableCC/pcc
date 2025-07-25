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
 * Copyright(C) Caldera International Inc. 2001-2002. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code and documentation must retain the above
 * copyright notice, this list of conditions and the following disclaimer.
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditionsand the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 * All advertising materials mentioning features or use of this software
 * must display the following acknowledgement:
 * 	This product includes software developed or owned by Caldera
 *	International, Inc.
 * Neither the name of Caldera International, Inc. nor the names of other
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * USE OF THE SOFTWARE PROVIDED FOR UNDER THIS LICENSE BY CALDERA
 * INTERNATIONAL, INC. AND CONTRIBUTORS ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED.  IN NO EVENT SHALL CALDERA INTERNATIONAL, INC. BE LIABLE
 * FOR ANY DIRECT, INDIRECT INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OFLIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE 
 * POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * Many changes from the 32V sources, among them:
 * - New symbol table manager (moved to another file).
 * - Prototype saving/checks.
 */

# include "pass1.h"
#include "unicode.h"

#include <stddef.h>
#include <stdlib.h>

#include "cgram.h"

#define	NODE P1ND
#define	tfree p1tfree
#define	nfree p1nfree
#define	ccopy p1tcopy
#define	flist p1flist
#define	fwalk p1fwalk
#undef n_type
#define n_type ptype
#undef n_qual
#define n_qual pqual
#undef n_df
#define n_df pdf


struct symtab *cftnsp;
int dimfuncnt;	/* statistics */
int symtabcnt, suedefcnt;	/* statistics */
int lcommsz, blkalloccnt;
int autooff,		/* the next unused automatic offset */
    maxautooff,		/* highest used automatic offset in function */
    argoff;		/* the next unused argument offset */
int retlab = NOLAB;	/* return label for subroutine */
int brklab;
int contlab;
int flostat;
int blevel;
int reached, prolab;

struct params;

#define MKTY(p, t, d, s) r = p1alloc(); *r = *p; \
	r = argcast(r, t, d, s); *p = *r; nfree(r);

/*
 * Linked list stack while reading in structs.
 */
struct rstack {
	struct	rstack *rnext;
	int	rsou;
	int	curpos;	/* position in struct */
	int	maxsz;	/* total size of struct */
	struct	symtab *rsym;
	struct	symtab *rb;
	struct	ssdesc *ss;
	struct	attr *ap;
	int	pack;
	int	flags;
#define	LASTELM	1
} *rpole;

/*
 * Array for parameter declarations.
 */
#define	ARGSZ	16
static int maxastore = ARGSZ;
static struct symtab *argstore[ARGSZ];
static struct symtab **argptr = argstore;

static int nparams;

/* defines used for getting things off of the initialization stack */

#define	MAXDF		12	/* 5.2.4.1 */
NODE *arrstk[10];
static int intcompare;
NODE *parlink;

void fixtype(NODE *p, int class);
int fixclass(int class, TWORD type);
static void dynalloc(struct symtab *p, int *poff);
int isdyn(struct symtab *p);
void inforce(OFFSZ n);
void vfdalign(int n);
static void lcommadd(struct symtab *sp);
extern int fun_inline;

void
defid(NODE *q, int class)
{
	defid2(q, class, 0);
}

static void
addsoname(struct symtab *sp, char *so)
{
	struct attr *ap = attr_new(ATTR_SONAME, 1);
	ap->sarg(0) = so;
	sp->sap = attr_add(sp->sap, ap);
}

/*
 * Declaration of an identifier.  Handles redeclarations, hiding,
 * incomplete types and forward declarations.
 *
 * q is a TYPE node setup after parsing with n_type, n_df and n_ap.
 * n_sp is a pointer to the not-yet initalized symbol table entry
 * unless it's a redeclaration or supposed to hide a variable.
 */

void
defid2(NODE *q, int class, char *astr)
{
	struct attr *ap;
	struct symtab *p;
	TWORD type, qual;
	TWORD stp, stq;
	int scl, i;
	union dimfun *dsym, *ddef;
	int slev, temp, changed;

	if (q == NIL)
		return;  /* an error was detected */

#ifdef GCC_COMPAT
	gcc_modefix(q);
#endif
	p = q->n_sp;

	if (p->sname == NULL)
		cerror("defining null identifier");

#ifdef PCC_DEBUG
	if (ddebug) {
		printf("defid(%s '%s'(%p), ", p->sname, "soname" , p);
		tprint(q->n_type, q->n_qual);
		printf(", %s, (%p)), level %d\n\t", scnames(class),
		    q->n_df, blevel);
		if (p->sss)
			printf("link %p size %d align %d\n",
			    p->sss->sp, p->sss->sz, p->sss->al);
#ifdef GCC_COMPAT
		dump_attr(q->n_ap);
#endif
	}
#endif

	fixtype(q, class);

	type = q->n_type;
	qual = q->n_qual;
	class = fixclass(class, type);

	stp = p->stype;
	stq = p->squal;
	slev = p->slevel;

#ifdef PCC_DEBUG
	if (ddebug) {
		printf("	modified to ");
		tprint(type, qual);
		printf(", %s\n", scnames(class));
		printf("	previous def'n: ");
		tprint(stp, stq);
		printf(", %s, (%p,%p)), level %d\n",
		    scnames(p->sclass), p->sdf, p->sap, slev);
	}
#endif

	if (blevel == 1) {
		switch (class) {
		default:
			if (!(class&FIELD) && !ISFTN(type))
				uerror("declared argument %s missing",
				    p->sname );
			break;
		case MOS:
		case MOU:
			cerror("field5");
		case TYPEDEF:
		case PARAM:
			break;
		}
	}

	if (stp == UNDEF)
		goto enter; /* New symbol */

	if (type != stp)
		goto mismatch;

	if (blevel > slev && (class == AUTO || class == REGISTER))
		/* new scope */
		goto mismatch;

	/*
	 * test (and possibly adjust) dimensions.
	 * also check that prototypes are correct.
	 */
	dsym = p->sdf;
	ddef = q->n_df;
	changed = 0;
	for (temp = type; temp & TMASK; temp = DECREF(temp)) {
		if (ISARY(temp)) {
			if (dsym->ddim == NOOFFSET) {
				dsym->ddim = ddef->ddim;
				changed = 1;
			} else if (ddef->ddim != NOOFFSET &&
			    dsym->ddim!=ddef->ddim) {
				goto mismatch;
			}
			++dsym;
			++ddef;
		} else if (ISFTN(temp)) {
			/* add a late-defined prototype here */
			if (!oldstyle && dsym->dlst == 0)
				dsym->dlst = ddef->dlst;
			if (!oldstyle && ddef->dlst != 0 &&
			    pr_ckproto(dsym->dlst, ddef->dlst, intcompare))
				uerror("declaration doesn't match prototype");
			dsym++, ddef++;
		}
	}
#ifdef STABS
	if (changed && gflag)
		stabs_chgsym(p); /* symbol changed */
#endif

	/* check that redeclarations are to the same structure */
	if (temp == STRTY || temp == UNIONTY) {
		if (suemeq(p->td->ss, q->n_td->ss) == 0)
			goto mismatch;
	}

	scl = p->sclass;

#ifdef PCC_DEBUG
	if (ddebug)
		printf("	previous class: %s\n", scnames(scl));
#endif

	/*
	 * Its allowed to add attributes to existing declarations.
	 * Be careful though not to trash existing attributes.
	 * XXX - code below is probably not correct.
	 */
	if (p->sap && p->sap->atype <= ATTR_MAX) {
		/* nothing special, just overwrite */
		p->sap = q->n_ap;
	} else {
		if (p->slevel == blevel) {
			for (ap = q->n_ap; ap; ap = ap->next) {
				if (ap->atype > ATTR_MAX)
					p->sap = attr_add(p->sap, attr_dup(ap));
			}
		} else
			p->sap = q->n_ap;
	}

	if (class & FIELD)
		cerror("field1");
	switch(class) {

	case EXTERN:
		if (astr)
			addsoname(p, astr);
		switch( scl ){
		case STATIC:
		case USTATIC:
			if( slev==0 )
				goto done;
			break;
		case EXTDEF:
		case EXTERN:
			goto done;
		case SNULL:
			if (p->sflags & SINLINE) {
				p->sclass = EXTDEF;
				inline_ref(p);
				goto done;
			}
			break;
		}
		break;

	case STATIC:
		if (astr)
			addsoname(p, astr);
		if (scl==USTATIC || (scl==EXTERN && blevel==0)) {
			p->sclass = STATIC;
			goto done;
		}
		if (changed || (scl == STATIC && blevel == slev))
			goto done; /* identical redeclaration */
		break;

	case USTATIC:
		if (scl==STATIC || scl==USTATIC)
			goto done;
		break;

	case TYPEDEF:
		if (scl == class)
			goto done;
		break;

	case MOU:
	case MOS:
		cerror("field6");

	case EXTDEF:
		switch (scl) {
		case EXTERN:
			p->sclass = EXTDEF;
			goto done;
		case USTATIC:
			p->sclass = STATIC;
			goto done;
		case SNULL:
#ifdef GCC_COMPAT
			/*
			 * Handle redeclarations of inlined functions.
			 * This is allowed if the previous declaration is of
			 * type gnu_inline.
			 */
			if (attr_find(p->sap, GCC_ATYP_GNU_INLINE))
				goto done;
#endif
			break;
		}
		break;

	case AUTO:
	case REGISTER:
		break;  /* mismatch.. */
	case SNULL:
		if (fun_inline && ISFTN(type)) {
			if (scl == EXTERN) {
				p->sclass = EXTDEF;
				inline_ref(p);
			}
			goto done;
		}
		break;
	}

	mismatch:

	/*
	 * Only allowed for automatic variables.
	 */
	if ((blevel == 2 && slev == 1) || blevel <= slev || class == EXTERN) {
		uerror("redeclaration of %s", p->sname);
		return;
	}
	if ((ISFTN(p->stype) && ISFTN(type)) ||
	    (!ISFTN(p->stype) && !ISFTN(type)))
		warner(Wshadow, p->sname, p->slevel ? "local" : "global");
	q->n_sp = p = hide(p);

	enter:  /* make a new entry */

	if (type == VOID && class != TYPEDEF)
		uerror("void not allowed for variables");

#ifdef PCC_DEBUG
	if(ddebug)
		printf("	new entry made\n");
#endif
	p->stype = type;
	p->squal = qual;
	p->sclass = (char)class;
	p->slevel = (char)blevel;
	p->soffset = NOOFFSET;
	p->sss = q->pss;
	if (q->n_ap)
		p->sap = attr_add(q->n_ap, p->sap);

	/* copy dimensions */
	p->sdf = q->n_df;
	/* Do not save param info for old-style functions */
	if (ISFTN(type) && oldstyle)
		p->sdf->dlst = 0;

	/* allocate offsets */
	if (class&FIELD) {
		cerror("field2");  /* new entry */
	} else switch (class) {

	case REGISTER:
		p->sclass = class = AUTO;
#ifndef PASS1
		if (astr != NULL) {
#ifdef GCC_COMPAT
			if (blevel == 0)
				werror("no register assignment (yet)");
			else if (astr != NULL) {
				for (i = 0; i < MAXREGS; i++) {
					extern char *rnames[]; /* XXX */
					if (strcmp(rnames[i], astr) == 0) {
						p->sflags |= SINREG;
						p->soffset = i;
						break;
					}
				}
				if (i != MAXREGS)
					break;
				werror("reg '%s' invalid", astr);
			}
#endif
		}
#endif
		/* FALLTHROUGH */
	case AUTO:
		if (isdyn(p)) {
			p->sflags |= SDYNARRAY;
			dynalloc(p, &autooff);
		} else if ((i = tnodenr(p)) != 0) {
			p->soffset = i;
			p->sflags |= STNODE;
		} else
			oalloc(p, &autooff);
		break;

	case PARAM:
		if (q->n_type != FARG)
			oalloc(p, &argoff);
		break;
		
	case STATIC:
	case EXTDEF:
	case EXTERN:
		p->soffset = getlab();
		/* FALLTHROUGH */
	case USTATIC:
		if (astr)
			addsoname(p, astr);
		break;

	case MOU:
	case MOS:
		cerror("field7");
	case SNULL:
#ifdef notdef
		if (fun_inline) {
			p->slevel = 1;
			p->soffset = getlab();
		}
#endif
		break;
	}

#ifdef STABS
	if (gflag && p->stype != FARG)
		stabs_newsym(p);
#endif

done:
	fixdef(p);	/* Leave last word to target */
#ifndef HAVE_WEAKREF
	{
		struct attr *at;

		/* Refer renamed function */
		if ((at = attr_find(p->sap, GCC_ATYP_WEAKREF)))
			addsoname(p, at->sarg(0));
	}
#endif
#ifdef PCC_DEBUG
	if (ddebug) {
		printf( "	sdf, offset: %p, %d\n\t",
		    p->sdf, p->soffset);
#ifdef GCC_COMPAT
		dump_attr(p->sap);
#endif
	}
#endif
}

/*
 * end of function
 */
void
ftnend(void)
{
#ifdef GCC_COMPAT
	struct attr *gc, *gd;
#endif
	extern int *mkclabs(void);
	extern NODE *cftnod;
	extern struct savbc *savbc;
	extern struct swdef *swpole;
	extern int tvaloff;
	int stack_usage;
	char *c;

	if (retlab != NOLAB && nerrors == 0) { /* inside a real function */
		plabel(retlab);
#ifndef NEWPARAMS
		if (cftnod)
			ecomp(buildtree(FORCE, p1tcopy(cftnod), NIL));
#endif
		efcode(); /* struct return handled here */
#ifdef NEWPARAMS
		fun_leave();
#endif
		c = getexname(cftnsp);
#ifndef STACK_TYPE
#define	STACK_TYPE	CHAR
#endif
		SETOFF(maxautooff, talign(STACK_TYPE, NULL));
		stack_usage = maxautooff / (int)tsize(STACK_TYPE, NULL, NULL);
		send_passt(IP_EPILOG, stack_usage, c,
		    cftnsp->stype, cftnsp->sclass == EXTDEF,
		    retlab, tvaloff, mkclabs());
	}

	cftnod = NIL;
	tcheck();
	brklab = contlab = retlab = NOLAB;
	flostat &= FP_CONTR_CBR;
	if (nerrors == 0) {
		if (savbc != NULL)
			cerror("bcsave error");
		if (swpole != NULL)
			cerror("switch error");
	}
#ifdef GCC_COMPAT
	if (cftnsp) {
		gc = attr_find(cftnsp->sap, GCC_ATYP_CONSTRUCTOR);
		gd = attr_find(cftnsp->sap, GCC_ATYP_DESTRUCTOR);
		if (gc || gd) {
			struct symtab sts = *cftnsp;
			NODE *p;
			sts.stype = INCREF(sts.stype);
			p = nametree(&sts);
			p->n_op = ICON;
			if (gc) {
				locctr(CTORS, NULL);
				inval(0, SZPOINT(0), p);
			}
			if (gd) {
				locctr(DTORS, NULL);
				inval(0, SZPOINT(0), p);
			}
			tfree(p);
		}
	}
#endif
	savbc = NULL;
	cftnsp = NULL;
	maxautooff = autooff = AUTOINIT;
	reached = 1;

	if (isinlining)
		inline_end();
	inline_prtout();

	tmpfree(); /* Release memory resources */
}

static struct symtab nulsym = {
	NULL, 0, 0, 0, 0, "null", {{ INT, 0, NULL, NULL }},
};

void
dclargs(void)
{
	struct symtab *p; /* XXX gcc */
	int i;

	/*
	 * Deal with fun(void) properly.
	 */
	if (nparams == 1 && argptr[0]->stype == VOID)
		goto done;

	/*
	 * Generate a list for bfcode().
	 * Parameters were pushed in reverse order.
	 */

	for (i = 0; i < nparams; i++) {
		p = argptr[i];
		if (p == NULL) {
			uerror("parameter %d name missing", i);
			p = &nulsym; /* empty symtab */
		}
		if (p->stype == FARG)
			p->stype = INT;
		if (ISARY(p->stype)) {
			p->stype += (PTR-ARY);
			p->sdf++;
		} else if (p->stype == FLOAT && oldstyle) {
			p->stype = DOUBLE;
		} else if (ISFTN(p->stype)) {
			werror("function declared as argument");
			p->stype = INCREF(p->stype);
		}
#ifdef STABS
		if (gflag)
			stabs_newsym(p);
#endif
	}

	if (oldstyle)
		pr_oldstyle(argptr, nparams);

	if (oldstyle && nparams) {
		/* Must recalculate offset for oldstyle args here */
		argoff = ARGINIT;
		for (i = 0; i < nparams; i++) {
			argptr[i]->soffset = NOOFFSET;
			oalloc(argptr[i], &argoff);
		}
	}

done:	autooff = AUTOINIT;

	plabel(prolab); /* after prolog, used in optimization */
	retlab = getlab();
	bfcode(argptr, nparams);
#ifdef NEWPARAMS
	fun_enter(cftnsp, argptr, nparams);
#endif
	if (fun_inline && (xinline
#ifdef GCC_COMPAT
 || attr_find(cftnsp->sap, GCC_ATYP_ALW_INL)
#endif
		))
		inline_args(argptr, nparams);
	plabel(getlab()); /* used when spilling */
	if (parlink)
		ecomp(parlink);
	parlink = NIL;
	nparams = 0;
	symclear(1);	/* In case of function pointer args */
}

#define	SEDESC()	memset(permalloc(sizeof(struct ssdesc)), \
	0, sizeof(struct ssdesc));

/*
 * Struct/union/enum symtab construction.
 */
static void
defstr(struct symtab *sp, int class)
{
	sp->sclass = (char)class;
	if (class == STNAME)
		sp->stype = STRTY;
	else if (class == UNAME)
		sp->stype = UNIONTY;
	else if (class == ENAME)
		sp->stype = ENUMTY;
}

/*
 * Declare a struct/union/enum tag.
 * If not found, create a new tag with UNDEF type.
 */
static struct symtab *
deftag(char *name, int class)
{
	struct symtab *sp;

	if ((sp = lookup(name, STAGNAME))->sss == NULL) {
		/* New tag */
		defstr(sp, class);
	} else if (sp->sclass != class)
		uerror("tag %s redeclared", name);
	if (sp->sss == NULL)
		sp->sss = SEDESC();
	return sp;
}

/*
 * reference to a structure or union, with no definition
 */
NODE *
rstruct(char *tag, int soru)
{
	struct symtab *sp;

	sp = deftag(tag, soru);
	return mkty(sp->stype, 0, sp->sss);
}

static int enumlow, enumhigh;
int enummer;

/*
 * Declare a member of enum.
 */
void
moedef(char *name, int num)
{
	struct symtab *sp;

	sp = lookup(name, SNORMAL);
	if (sp->stype == UNDEF || (sp->slevel < blevel)) {
		if (sp->stype != UNDEF)
			sp = hide(sp);
		sp->stype = INT; /* always */
		sp->sclass = CCONST;
		sp->soffset = num;
	} else
		uerror("%s redeclared", name);
	if (num < enumlow)
		enumlow = num;
	if (num > enumhigh)
		enumhigh = num;
}

/*
 * Declare an enum tag.  Complain if already defined.
 */
struct symtab *
enumhd(char *name)
{
	struct symtab *sp;

	enummer = enumlow = enumhigh = 0;
	if (name == NULL)
		return NULL;

	sp = deftag(name, ENAME);
	if (sp->stype != ENUMTY) {
		if (sp->slevel == blevel)
			uerror("%s redeclared", name);
		sp = hide(sp);
		defstr(sp, ENAME);
	}
	sp->sss->sp = sp;
	return sp;
}

/*
 * finish declaration of an enum
 */
NODE *
enumdcl(struct symtab *sp)
{
	NODE *p;
	TWORD t;

#ifdef ENUMSIZE
	t = ENUMSIZE(enumhigh, enumlow);
#else
	t = ctype(enumlow < 0 ? INT : UNSIGNED);
#ifdef notdef
	if (enumhigh <= MAX_CHAR && enumlow >= MIN_CHAR)
		t = ctype(CHAR);
	else if (enumhigh <= MAX_SHORT && enumlow >= MIN_SHORT)
		t = ctype(SHORT);
	else
		t = ctype(INT);
#endif
#endif
	
	if (sp)
		sp->stype = t;
	p = mkty(t, 0, 0);
	p->n_sp = sp;
	return p;
}

/*
 * Handle reference to an enum
 */
NODE *
enumref(char *name)
{
	struct symtab *sp;
	NODE *p;

	sp = lookup(name, STAGNAME);

#ifdef notdef
	/*
	 * 6.7.2.3 Clause 2:
	 * "A type specifier of the form 'enum identifier' without an
	 *  enumerator list shall only appear after the type it specifies
	 *  is complete."
	 */
	if (sp->sclass != ENAME)
		uerror("enum %s undeclared", name);
#endif
	if (sp->sclass == SNULL) {
		/* declare existence of enum */
		sp = enumhd(name);
		sp->stype = ENUMTY;
	}

	p = mkty(sp->stype, 0, sp->sss);
	p->n_sp = sp;
	return p;
}

/*
 * begining of structure or union declaration
 * It's an error if this routine is called twice with the same struct.
 */
struct rstack *
bstruct(char *name, int soru, NODE *gp)
{
	struct ssdesc *ss;
	struct rstack *r;
	struct symtab *sp;
	struct attr *gap = NULL;
	int pack = 0;

#ifdef GCC_COMPAT
	if (gp) {
		struct attr *ap;
		gap = gcc_attr_parse(gp);
		if ((ap = attr_find(gap, GCC_ATYP_PACKED)))
			pack = ap->iarg(0);
	}
#endif

	if (name != NULL) {
		sp = deftag(name, soru);
		if (sp->sss->al != 0) {
			if (sp->slevel < blevel) {
				sp = hide(sp);
				defstr(sp, soru);
				sp->sss = SEDESC();
			} else
				uerror("%s redeclared", name);
		}
		ss = sp->sss;
	} else {
		ss = SEDESC();
		sp = NULL;
	}
	ss->al = ALCHAR;

	r = tmpcalloc(sizeof(struct rstack));
	r->rsou = soru;
	r->rsym = sp;
	r->rb = NULL;
	r->ss = ss;
	r->ap = gap;
	r->pack = pack;
	r->rnext = rpole;
	rpole = r;

	return r;
}

/*
 * Called after a struct is declared to restore the environment.
 * - If ALSTRUCT is defined, this will be the struct alignment and the
 *   struct size will be a multiple of ALSTRUCT, otherwise it will use
 *   the alignment of the largest struct member.
 */
NODE *
dclstruct(struct rstack *r)
{
	NODE *n;
	struct ssdesc *ss;
	struct symtab *sp;

	ss = r->ss;
	ss->sp = r->rb;
	ss->sz = r->maxsz;

	SETOFF(ss->sz, ss->al);

#ifdef PCC_DEBUG
	if (ddebug) {
		printf("dclstruct(%s): size=%d, align=%d\n",
		    r->rsym ? r->rsym->sname : "??", ss->sz, ss->al);
	}
	if (ddebug>1) {
		printf("\tsize %d align %d link %p\n", ss->sz, ss->al, ss->sp);
		for (sp = ss->sp; sp != NULL; sp = sp->snext) {
			printf("\tmember %s(%p)\n", sp->sname, sp);
		}
	}
#endif

#ifdef STABS
	if (gflag)
		stabs_struct(r->rsym);
#endif

	rpole = r->rnext;
	n = mkty(r->rsou == STNAME ? STRTY : UNIONTY, 0, r->ss);
	n->n_sp = r->rsym;

	n->n_qual |= 1; /* definition place XXX used by attributes */
	return n;
}

/*
 * Add a new member to the current struct or union being declared.
 */
void
soumemb(NODE *n, char *name, int class)
{
	struct symtab *sp, *lsp;
	int incomp, tsz, al;
	TWORD t;
 
	if (rpole == NULL)
		cerror("soumemb");
 
#ifdef PCC_DEBUG
        if (ddebug) {
		printf("soumemb %s\n", name);
	}
#endif
	/* check if tag name exists */
	lsp = NULL;
	for (sp = rpole->rb; sp != NULL; lsp = sp, sp = sp->snext)
		if (*name != '*' && sp->sname == name)
			uerror("redeclaration of %s", name);

	sp = getsymtab(name, SMOSNAME);
	if (rpole->rb == NULL)
		rpole->rb = sp;
	else
		lsp->snext = sp;

	n->n_sp = sp;
	*sp->td = *n->n_td;

	sp->slevel = blevel;
	sp->sap = n->n_ap;

	if (rpole->rsou == UNAME)
		rpole->curpos = 0;
	if (class & FIELD) {
		sp->sclass = (char)class;
		falloc(sp, class&FLDSIZ, NIL);
		al = talign(sp->stype, sp->sss);
		tsz = sp->sclass&FLDSIZ;
	} else if (rpole->rsou == STNAME || rpole->rsou == UNAME) {
		sp->sclass = rpole->rsou == STNAME ? MOS : MOU;

		al = talign(sp->stype, sp->sss);
		tsz = (int)tsize(sp->stype, sp->sdf, sp->sss);

		if (rpole->pack && al > rpole->pack)
			al = rpole->pack;
		if (al < SZCHAR)
			al = SZCHAR;

		SETOFF(rpole->curpos, al);
		sp->soffset = rpole->curpos;
		rpole->curpos += tsz;

	} else {
		/* assume no alignment for the rest */
		al = 0;
	}
	if (rpole->rsou == UNAME) {
		if (tsz > rpole->maxsz)
			rpole->maxsz = tsz;
	} else {
		rpole->maxsz = rpole->curpos;
	}
	if (al > rpole->ss->al)
		rpole->ss->al = al;

	/*
	 * 6.7.2.1 clause 16:
	 * "...the last member of a structure with more than one
	 *  named member may have incomplete array type;"
	 */
	if (ISARY(sp->stype) && sp->sdf->ddim == NOOFFSET)
		incomp = 1;
	else
		incomp = 0;
	if ((rpole->flags & LASTELM) || (rpole->rb == sp && incomp == 1))
		uerror("incomplete array in struct");
	if (incomp == 1)
		rpole->flags |= LASTELM;

	/*
	 * 6.7.2.1 clause 2:
	 * "...such a structure shall not be a member of a structure
	 *  or an element of an array."
	 */
	t = sp->stype;
	if (rpole->rsou != STNAME || BTYPE(t) != STRTY)
		return; /* not for unions */
	while (ISARY(t))
		t = DECREF(t);
	if (ISPTR(t))
		return;

	if ((lsp = strmemb(sp->td->ss)) != NULL) {
		for (; lsp->snext; lsp = lsp->snext)
			;
		if (ISARY(lsp->stype) && lsp->snext &&
		    lsp->sdf->ddim == NOOFFSET)
			uerror("incomplete struct in struct");
	}
}

/*
 * error printing routine in parser
 */
void
yyerror(char *s)
{
	uerror(s);
}

void yyaccpt(void);
void
yyaccpt(void)
{
	ftnend();
}


/*
 * Save argument symtab entry pointers in an array for later use in dclargs.
 */
void
argsave(P1ND *p)
{
	if (p->n_op == ELLIPSIS || p->n_type == VOID)
		return;
	if (nparams == maxastore) {
		argptr = memcpy(tmpalloc(maxastore*2 * sizeof(struct symtab *)),
		    argptr, maxastore * sizeof(struct symtab *));
		maxastore*=2;
	}
	argptr[nparams++] = p->n_sp;
}

/*
 * compute the alignment of an object with type ty, sizeoff index s
 */
int
talign(unsigned int ty, struct ssdesc *ss)
{
	int a;

	for (; ty > BTMASK; ty = DECREF(ty)) {
		switch (ty & TMASK) {
		case PTR:
			return(ALPOINT);
		case ARY:
			continue;
		case FTN:
			cerror("compiler takes alignment of function");
		}
	}

	if (ss && ss->al)
		return ss->al;

#ifndef NO_COMPLEX
	if (ISITY(ty))
		ty -= (FIMAG-FLOAT);
#endif
	ty = BTYPE(ty);
	if (ty >= CHAR && ty <= ULONGLONG && ISUNSIGNED(ty))
		ty = DEUNSIGN(ty);

	switch (ty) {
#ifdef GCC_COMPAT
	case VOID: a = ALCHAR; break; /* GCC */
#endif
	case BOOL: a = ALBOOL; break;
	case CHAR: a = ALCHAR; break;
	case SHORT: a = ALSHORT; break;
	case INT: a = ALINT; break;
	case LONG: a = ALLONG; break;
	case LONGLONG: a = ALLONGLONG; break;
	case FLOAT: a = ALFLOAT; break;
	case DOUBLE: a = ALDOUBLE; break;
	case LDOUBLE: a = ALLDOUBLE; break;
	default:
		uerror("no alignment");
		a = ALINT;
	}
	return a;
}

short sztable[] = { 0, SZBOOL, SZCHAR, SZCHAR, SZSHORT, SZSHORT, SZINT, SZINT,
	SZLONG, SZLONG, SZLONGLONG, SZLONGLONG, SZFLOAT, SZDOUBLE, SZLDOUBLE };

/* compute the size associated with type ty,
 *  dimoff d, and sizoff s */
/* BETTER NOT BE CALLED WHEN t, d, and s REFER TO A BIT FIELD... */
OFFSZ
tsize(TWORD ty, union dimfun *d, struct ssdesc *ss)
{
	OFFSZ mult, sz;

	mult = 1;

	for (; ty > BTMASK; ty = DECREF(ty)) {
		switch (ty & TMASK) {

		case FTN:
#ifdef GCC_COMPAT
			return SZCHAR;
#else
			uerror( "cannot take size of function");
#endif
		case PTR:
			return( SZPOINT(ty) * mult );
		case ARY:
			if (d->ddim == NOOFFSET)
				return 0;
			if (d->ddim < 0)
				cerror("tsize: dynarray");
			mult *= d->ddim;
			d++;
		}
	}

#ifndef NO_COMPLEX
	if (ISITY(ty))
		ty -= (FIMAG-FLOAT);
#endif

	if (ty == VOID)
		ty = CHAR;
	if (ty <= LDOUBLE)
		sz = sztable[ty];
	else if (ISSOU(ty)) {
		if (ss == NULL || ss->al == 0) {
			uerror("unknown structure/union/enum");
			sz = SZINT;
		} else
			sz = ss->sz;
	} else {
		uerror("unknown type");
		sz = SZINT;
	}

	return((unsigned int)sz * mult);
}

#ifndef MYINSTRING
/*
 * Print out a string of characters.
 * Assume that the assembler understands C-style escape
 * sequences.
 */
void
instring(struct symtab *sp)
{
	unsigned short sh[2];
	char *s, *str;
	TWORD t;
	NODE *p;

	locctr(STRNG, sp);
	defloc(sp);

	t = BTYPE(sp->stype);
	str = s = sp->sname;
	if (t == ctype(USHORT)) {
		/* convert to UTF-16 */
		p = xbcon(0, NULL, t);
		while (*s) {
			cp2u16(u82cp(&s), sh);
			if ((glval(p) = sh[0]))
				inval(0, SZSHORT, p);
			if ((glval(p) = sh[1]))
				inval(0, SZSHORT, p);
		}
		slval(p, 0);
		inval(0, SZSHORT, p);
		nfree(p);
	} else if (t == ctype(SZINT < 32 ? ULONG : UNSIGNED) ||
	    t == ctype(SZINT < 32 ? LONG : INT)) {
		/* convert to UTF-32 */
		p = xbcon(0, NULL, t);
		while (*s) {
			slval(p, u82cp(&s));
			inval(0, SZINT < 32 ? SZLONG : SZINT, p);
		}
		slval(p, 0);
		inval(0, SZINT < 32 ? SZLONG : SZINT, p);
		nfree(p);
	} else if (t == CHAR || t == UCHAR) {
		printf(PRTPREF "\t.ascii \"");
		while (*s) {
			if (*s == '\\')
				(void)esccon(&s);
			else
				s++;
	
			if (s - str > 60) {
				fwrite(str, 1, s - str, stdout);
				printf("\"\n" PRTPREF "\t.ascii \"");
				str = s;
			}
		}

		fwrite(str, 1, s - str, stdout);
		printf("\\0\"\n");
	} else
		cerror("instring %ld", t);
}
#endif

/*
 * update the offset pointed to by poff; return the
 * offset of a value of size `size', alignment `alignment',
 * given that off is increasing
 */
int
upoff(int size, int alignment, int *poff)
{
	int off;

	off = *poff;
	SETOFF(off, alignment);
	if (off < 0)
		cerror("structure or stack overgrown"); /* wrapped */
	*poff = off+size;
	return (off);
}

/*
 * allocate p with offset *poff, and update *poff.
 * This routine is used to create stack reference for arguments and automatics.
 * poff is always increasing even if the stack goes downwards, hence 
 * the off must must be calculated before/after the increase/decrease
 * of the stack pointer.
 */
int
oalloc(struct symtab *p, int *poff )
{
	int al, off, tsz;
	int noff;

	al = talign(p->stype, p->sss);
	noff = *poff;
	off = 0;
	tsz = (int)tsize(p->stype, p->sdf, p->sss);

#ifdef STACK_DOWN
	if (p->sclass == AUTO) {
		/* negative part of stack */
		noff += tsz;
		SETOFF(noff, al);
		off = -noff;
	} else if (p->sclass == PARAM) {
		/* positive part of stack */
		if (p->stype < INT || p->stype == BOOL)
			tsz = SZINT, al = ALINT;
		off = upoff(tsz, al, &noff);
	} else
		cerror("bad oalloc class %d", p->sclass);
#else
	if (p->sclass == AUTO) {
		/* positive part of stack */
		off = upoff(tsz, al, &noff);
	} else if (p->sclass == PARAM) {
		/* negative part of stack */
		noff += tsz;
		SETOFF(noff, al);
		off = -noff;
	} else
		cerror("bad oalloc class %d", p->sclass);
#endif

	if (p->soffset == NOOFFSET)
		p->soffset = off;
	else if(off != p->soffset)
		cerror("oalloc: reallocated");

	*poff = noff;
	return(0);
}

/*
 * Delay emission of code generated in argument headers.
 */
static void
edelay(NODE *p)
{
	if (blevel == 1) {
		/* Delay until after declarations */
		if (parlink == NULL)
			parlink = p;
		else
			parlink = block(COMOP, parlink, p, 0, 0, 0);
	} else
		ecomp(p);
}

/*
 * Return 1 if dynamic array, 0 otherwise.
 */
int
isdyn(struct symtab *sp)
{
	union dimfun *df = sp->sdf;
	TWORD t;

	for (t = sp->stype; t > BTMASK; t = DECREF(t)) {
		if (!ISARY(t))
			return 0;
		if (df->ddim < 0 && df->ddim != NOOFFSET)
			return 1;
		df++;
	}
	return 0;
}

/*
 * Allocate space on the stack for dynamic arrays (or at least keep track
 * of the index).
 * Strategy is as follows:
 * - first entry is a pointer to the dynamic datatype.
 * - if it's a one-dimensional array this will be the only entry used.
 * - if it's a multi-dimensional array the following (numdim-1) integers
 *   will contain the sizes to multiply the indexes with.
 * - code to write the dimension sizes this will be generated here.
 * - code to allocate space on the stack will be generated here.
 */
static void
dynalloc(struct symtab *p, int *poff)
{
	union dimfun *df;
	NODE *n, *tn, *pol;
	TWORD t;

	/*
	 * The pointer to the array is not necessarily stored in a
	 * TEMP node, but if it is, its number is in the soffset field;
	 */
	t = p->stype;
	p->sflags |= STNODE;
	p->stype = INCREF(p->stype); /* Make this an indirect pointer */
	tn = tempnode(0, p->stype, p->sdf, p->sss);
	p->soffset = regno(tn);

	df = p->sdf;

	pol = bcon(1);
	for (; t > BTMASK; t = DECREF(t)) {
		if (!ISARY(t))
			break;
		if (df->ddim < 0)
			n = tempnode(-df->ddim, INT, 0, 0);
		else
			n = bcon(df->ddim);

		pol = buildtree(MUL, pol, n);
		df++;
	}
	/* Create stack gap */
	spalloc(tn, pol, tsize(t, 0, p->sss));
}

/*
 * allocate a field of width w
 * new is 0 if new entry, 1 if redefinition, -1 if alignment
 */
int
falloc(struct symtab *p, int w, NODE *pty)
{
	TWORD otype, type;
	int al,sz;

	otype = type = p ? p->stype : pty->n_type;

	if (type == BOOL)
		type = BOOL_TYPE;
	if (!ISINTEGER(type)) {
		uerror("illegal field type");
		type = INT;
	}

	al = talign(type, NULL);
	sz = (int)tsize(type, NULL, NULL);

	if (w > sz) {
		uerror("field too big");
		w = sz;
	}

	if (w == 0) { /* align only */
		SETOFF(rpole->curpos, al);
		if (p != NULL)
			uerror("zero size field");
		return(0);
	}

	if (rpole->curpos%al + w > sz)
		SETOFF(rpole->curpos, al);
	if (p == NULL) {
		rpole->curpos += w;  /* we know it will fit */
		return(0);
	}

	/* establish the field */

	p->soffset = rpole->curpos;
	rpole->curpos += w;
	p->stype = otype;
	fldty(p);
	return(0);
}

/*
 * Check if this symbol should be a common or must be handled in data seg.
 */
static void
commchk(struct symtab *sp)
{
	if ((sp->sflags & STLS)
#ifdef GCC_COMPAT
		|| attr_find(sp->sap, GCC_ATYP_SECTION)
#endif
	    ) {
		/* TLS handled in data segment */
		if (sp->sclass == EXTERN)
			sp->sclass = EXTDEF;
		beginit(sp);
		endinit(1);
	} else {
		symdirec(sp);
		defzero(sp);
	}
}

void
nidcl(NODE *p, int class)
{
	nidcl2(p, class, 0);
}

/*
 * handle unitialized declarations assumed to be not functions:
 * int a;
 * extern int a;
 * static int a;
 */
void
nidcl2(NODE *p, int class, char *astr)
{
	struct symtab *sp;
	int commflag = 0;

	/* compute class */
	if (class == SNULL) {
		if (blevel > 1)
			class = AUTO;
		else if (blevel != 0 || rpole)
			cerror( "nidcl error" );
		else /* blevel = 0 */
			commflag = 1, class = EXTERN;
	}

	defid2(p, class, astr);

	sp = p->n_sp;
	/* check if forward decl */
	if (ISARY(sp->stype) && sp->sdf->ddim == NOOFFSET)
		return;

	if (sp->sflags & SASG)
		return; /* already initialized */

	switch (class) {
	case EXTDEF:
		/* simulate initialization by 0 */
		simpleinit(p->n_sp, bcon(0));
		break;
	case EXTERN:
		if (commflag)
			lcommadd(p->n_sp);
		else
			extdec(p->n_sp);
		break;
	case STATIC:
		if (blevel == 0)
			lcommadd(p->n_sp);
		else
			commchk(p->n_sp);
		break;
	}
}

struct lcd {
	SLIST_ENTRY(lcd) next;
	struct symtab *sp;
};

static SLIST_HEAD(, lcd) lhead = { NULL, &lhead.q_forw};

/*
 * Add a local common statement to the printout list.
 */
void
lcommadd(struct symtab *sp)
{
	struct lcd *lc, *lcp;

	lcp = NULL;
	SLIST_FOREACH(lc, &lhead, next) {
		if (lc->sp == sp)
			return; /* already exists */
		if (lc->sp == NULL && lcp == NULL)
			lcp = lc;
	}
	if (lcp == NULL) {
		lc = permalloc(sizeof(struct lcd));
		lcommsz += sizeof(struct lcd);
		lc->sp = sp;
		SLIST_INSERT_LAST(&lhead, lc, next);
	} else
		lcp->sp = sp;
}

/*
 * Delete a local common statement.
 */
void
lcommdel(struct symtab *sp)
{
	struct lcd *lc;

	SLIST_FOREACH(lc, &lhead, next) {
		if (lc->sp == sp) {
			lc->sp = NULL;
			return;
		}
	}
}

/*
 * Print out the remaining common statements.
 */
void
lcommprint(void)
{
	struct lcd *lc;

	SLIST_FOREACH(lc, &lhead, next) {
		if (lc->sp != NULL)
			commchk(lc->sp);
	}
}

/*
 * Merge given types to a single node.
 * Any type can end up here.
 * p is the old node, q is the old (if any).
 * CLASS is AUTO, EXTERN, REGISTER, STATIC or TYPEDEF.
 * QUALIFIER is VOL or CON
 * TYPE is CHAR, SHORT, INT, LONG, SIGNED, UNSIGNED, VOID, BOOL, FLOAT,
 * 	DOUBLE, STRTY, UNIONTY.
 */
struct typctx {
	int class, qual, sig, uns, cmplx, imag, err, align;
	TWORD type;
	NODE *saved;
	struct attr *pre, *post;
};

static void
typwalk(NODE *p, void *arg)
{
	struct typctx *tc = arg;

#define	cmop(x,y) block(CM, x, y, INT, 0, 0)
	switch (p->n_op) {
	case ALIGN:
		if (tc->align < glval(p))
			tc->align = (int)glval(p);
                break;
	case ATTRIB:
#ifdef GCC_COMPAT
		if (tc->saved && (tc->saved->n_qual & 1)) {
			tc->post = attr_add(tc->post,gcc_attr_parse(p->n_left));
		} else {
			tc->pre = attr_add(tc->pre, gcc_attr_parse(p->n_left));
		}
		p->n_left = bcon(0); /* For tfree() */
#else
		uerror("gcc type attribute used");
#endif
		break;
	case CLASS:
		if (p->n_type == 0)
			break;	/* inline hack */
		if (tc->class)
			tc->err = 1; /* max 1 class */
		tc->class = p->n_type;
		break;

	case FUNSPEC:
		if (p->n_type == INLINE) {
			fun_inline = 1;
		} else if (p->n_type == NORETURN) {
			tc->pre = attr_add(tc->pre, attr_new(ATTR_NORETURN, 3));
		} else
			tc->err = 1;
		break;

	case QUALIFIER:
		if (p->n_qual == 0 && 
		    ((tc->saved && !ISPTR(tc->saved->n_type)) ||
		    (tc->saved == 0)))
			uerror("invalid use of 'restrict'");
		tc->qual |= p->n_qual >> TSHIFT;
		break;

	case TYPE:
		if (p->n_sp != NULL || ISSOU(p->n_type)) {
			/* typedef, enum or struct/union */
			if (tc->saved || tc->type)
				tc->err = 1;
#ifdef GCC_COMPAT
			if (ISSOU(p->n_type) && p->n_left) {
				if (tc->post)
					cerror("typwalk");
				tc->post = gcc_attr_parse(p->n_left);
			}
#endif
			tc->saved = ccopy(p);
			break;
		}

		switch (p->n_type) {
		case BOOL:
		case CHAR:
		case FLOAT:
		case VOID:
			if (tc->type)
				tc->err = 1;
			tc->type = p->n_type;
			break;
		case DOUBLE:
			if (tc->type == 0)
				tc->type = DOUBLE;
			else if (tc->type == LONG)
				tc->type = LDOUBLE;
			else
				tc->err = 1;
			break;
		case SHORT:
			if (tc->type == 0 || tc->type == INT)
				tc->type = SHORT;
			else
				tc->err = 1;
			break;
		case INT:
			if (tc->type == SHORT || tc->type == LONG ||
			    tc->type == LONGLONG)
				break;
			else if (tc->type == 0)
				tc->type = INT;
			else
				tc->err = 1;
			break;
		case LONG:
			if (tc->type == 0)
				tc->type = LONG;
			else if (tc->type == INT)
				break;
			else if (tc->type == LONG)
				tc->type = LONGLONG;
			else if (tc->type == DOUBLE)
				tc->type = LDOUBLE;
			else
				tc->err = 1;
			break;
		case SIGNED:
			if (tc->sig || tc->uns)
				tc->err = 1;
			tc->sig = 1;
			break;
		case UNSIGNED:
			if (tc->sig || tc->uns)
				tc->err = 1;
			tc->uns = 1;
			break;
		case COMPLEX:
			tc->cmplx = 1;
			break;
		case IMAG:
			tc->imag = 1;
			break;
		default:
			cerror("typwalk");
		}
	}

}

NODE *
typenode(NODE *p)
{
	struct symtab *sp;
	struct typctx tc;
	NODE *q;
	char *c;

	memset(&tc, 0, sizeof(struct typctx));

	flist(p, typwalk, &tc);
	tfree(p);

	if (tc.err)
		goto bad;

	if (tc.cmplx || tc.imag) {
		if (tc.type == 0)
			tc.type = DOUBLE;
		if ((tc.cmplx && tc.imag) || tc.sig || tc.uns ||
		    !ISFTY(tc.type))
			goto bad;
		if (tc.cmplx) {
			c = tc.type == DOUBLE ? "0d" :
			    tc.type == FLOAT ? "0f" : "0l";
			sp = lookup(addname(c), 0);
			tc.type = STRTY;
			tc.saved = mkty(tc.type, sp->sdf, sp->sss);
			tc.saved->n_sp = sp;
			tc.type = 0;
		} else
			tc.type += (FIMAG-FLOAT);
	}

	if (tc.saved && tc.type)
		goto bad;
	if (tc.sig || tc.uns) {
		if (tc.type == 0)
			tc.type = tc.sig ? INT : UNSIGNED;
		if (tc.type > ULONGLONG)
			goto bad;
		if (tc.uns)
			tc.type = ENUNSIGN(tc.type);
	}

	if (xuchar && tc.type == CHAR && tc.sig == 0)
		tc.type = UCHAR;

#ifdef GCC_COMPAT
	if (pragma_packed) {
		q = bdty(CALL, bdty(NAME, "packed"), bcon(pragma_packed));
		tc.post = attr_add(tc.post, gcc_attr_parse(q));
	}
	if (pragma_aligned) {
		/* Deal with relevant pragmas */
		if (tc.align < pragma_aligned)
			tc.align = pragma_aligned;
	}
	pragma_aligned = pragma_packed = 0;
#endif
	if ((q = tc.saved) == NULL) {
		TWORD t;
		if ((t = BTYPE(tc.type)) > LDOUBLE && t != VOID &&
		    t != BOOL && !(t >= FIMAG && t <= LIMAG))
			cerror("typenode2 t %x", tc.type);
		if (t == UNDEF) {
			t = INT;
			MODTYPE(tc.type, INT);
		}
		q =  mkty(tc.type, 0, 0);
	}
	q->n_ap = attr_add(q->n_ap, tc.post);
	q->n_qual = tc.qual;
	slval(q, tc.class);
#ifdef GCC_COMPAT
	if (tc.post) {
		/* Can only occur for TYPEDEF, STRUCT or UNION */
		if (tc.saved == NULL)
			cerror("typenode");
		if (tc.saved->n_sp) /* trailer attributes for structs */
			tc.saved->n_sp->sap = q->n_ap;
	}
	if (tc.pre)
		q->n_ap = attr_add(q->n_ap, tc.pre);
	gcc_tcattrfix(q);
#endif

	if (tc.align) {
		if (q->pss == NULL) 
			q->pss = SEDESC();
		if (tc.align > talign(q->n_type, q->pss)/SZCHAR)
			q->pss->al = tc.align * tc.align;
	}

	return q;

bad:	uerror("illegal type combination");
	return mkty(INT, 0, 0);
}

struct tylnk {
	struct tylnk *next;
	union dimfun df;
};

static int numdfs;

static void
tylkadd(union dimfun dim, union dimfun *df)
{
	df[numdfs++] = dim;
	if (numdfs == MAXDF)
		uerror("too many dimensions (C11 5.2.4.1)");
}

/*
 * build a type, and stash away dimensions,
 * from a parse tree of the declaration
 * the type is build top down, the dimensions bottom up
 */
static void
tyreduce(NODE *p, union dimfun *df)
{
	union dimfun dim;
	NODE *r = NULL;
	int o;
	TWORD t, q;

	o = p->n_op;
	if (o == NAME) {
		p->n_qual = DECQAL(p->n_qual);
		return;
	}

	t = INCREF(p->n_type);
	q = p->n_qual;
	switch (o) {
	case CALL:
		t += (FTN-PTR);
		dim.dlst = pr_arglst(p->n_right);
		p1tfree(p->n_right);
		break;
	case UCALL:
		t += (FTN-PTR);
		dim.dlst = 0;
		break;
	case LB:
		t += (ARY-PTR);
		if (p->n_right->n_op != ICON) {
			r = p->n_right;
			o = RB;
		} else {
			dim.ddim = (int)glval(p->n_right);
			nfree(p->n_right);
#ifdef notdef
	/* XXX - check dimensions at usage time */
			if (dim.ddim == NOOFFSET && p->n_left->n_op == LB)
				uerror("null dimension");
#endif
		}
		break;
	case UMUL:
		break;
	default:
		cerror("bad node %d\n", o);
	}

	p->n_left->n_type = t;
	p->n_left->n_qual = INCQAL(q) | p->n_left->n_qual;
	tyreduce(p->n_left, df);

	if (o == LB || o == UCALL || o == CALL)
		tylkadd(dim, df);
	if (o == RB) {
		P1ND *qq = tempnode(0, INT, 0, 0);
		dim.ddim = -regno(qq);
		tylkadd(dim, df);
		edelay(buildtree(ASSIGN, qq, r));
	}
	if (p->n_op == LB || p->n_op == CALL)
		p->n_op = RB;

	p->n_sp = p->n_left->n_sp;
	p->n_type = p->n_left->n_type;
	p->n_qual = p->n_left->n_qual;
}

/*
 * merge type typ with identifier idp.
 * idp is returned as a NAME node with correct types,
 * typ is untouched since multiple declarations uses it.
 * typ has type attributes, idp can never carry such attributes
 * so on return just a pointer to the typ attributes is returned.
 */
NODE *
tymerge(NODE *typ, NODE *idp)
{
	TWORD t;
	union dimfun dfs[MAXDF];
	union dimfun *j;

#ifdef PCC_DEBUG
	if (ddebug > 2) {
		printf("tymerge(%p,%p)\n", typ, idp);
		fwalk(typ, eprint, 0);
		fwalk(idp, eprint, 0);
	}
#endif

	if (typ->n_op != TYPE)
		cerror("tymerge: arg 1");

	idp->n_type = typ->n_type;
	idp->n_qual |= typ->n_qual;

	numdfs = 0;

	tyreduce(idp, dfs);

	for (t = typ->n_type, j = typ->n_df; t&TMASK; t = DECREF(t))
		if (ISARY(t) || ISFTN(t))
			tylkadd(*j++, dfs);

	dimfuncnt += numdfs;
	if (numdfs) {
		union dimfun *a = permalloc(sizeof(union dimfun) * numdfs);
		idp->n_df = memcpy(a, dfs, sizeof(union dimfun) * numdfs);
	} else
		idp->n_df = NULL;
//{int i; for (i = 0; i < numdfs; i++)printf("tym%d: %p\n", i, &idp->n_df[i]); }

	/* now idp is a single node: fix up type */
	idp->n_type = ctype(idp->n_type);
	
	if (idp->n_op != NAME)
		p1tfree(idp->n_left);
	idp->n_op = NAME;

	/* carefully not destroy any type attributes */
	idp->n_ap = attr_add(typ->n_ap, idp->n_ap);
	idp->pss = typ->pss;

	return(idp);
}

int
suemeq(struct ssdesc *s1, struct ssdesc *s2)
{

	return (strmemb(s1) == strmemb(s2));
}

/*
 * Do prototype checking and add conversions before calling a function.
 * Argument f is function and a is a CM-separated list of arguments.
 * Returns a merged node (via buildtree() of function and arguments.
 */
NODE *
doacall(struct symtab *sp, NODE *f, NODE *a)
{
	NODE *w;

#ifdef PCC_DEBUG
	if (ddebug) {
		printf("doacall.\n");
		fwalk(f, eprint, 0);
		if (a)
			fwalk(a, eprint, 0);
	}
#endif
	if (ISARY(f->n_type))
		goto build; /* something bad happened */

	/* First let MD code do something */
	calldec(f, a);
/* XXX XXX hack */
	if ((f->n_op == CALL) &&
	    f->n_left->n_op == ADDROF &&
	    f->n_left->n_left->n_op == NAME &&
	    (f->n_left->n_left->n_type & 0x7e0) == 0x4c0)
		goto build;
/* XXX XXX hack */

	/* Check for undefined or late defined enums */
	if (BTYPE(f->n_type) == ENUMTY) {
		/* not-yet check if declared enum */
		struct symtab *sq = strmemb(f->n_td->ss);
		if (sq->stype != ENUMTY)
			MODTYPE(f->n_type, sq->stype);
		if (BTYPE(f->n_type) == ENUMTY)
			uerror("enum %s not declared", sq->sname);
	}

	/* Do prototype checking for function call */
	pr_callchk(sp, f, a);

build:	if (sp != NULL && (sp->sflags & SINLINE) && (w = inlinetree(sp, f, a)))
		return w;
	return buildtree(a == NIL ? UCALL : CALL, f, a);
}

void
fixtype(NODE *p, int class)
{
	unsigned int t, type;
	int mod1, mod2;
	/* fix up the types, and check for legality */

	/* forward declared enums */
	if (BTYPE(p->n_sp->stype) == ENUMTY) {
		MODTYPE(p->n_sp->stype, strmemb(p->n_sp->td->ss)->stype);
	}

	if( (type = p->n_type) == UNDEF ) return;
	if ((mod2 = (type&TMASK))) {
		t = DECREF(type);
		while( mod1=mod2, mod2 = (t&TMASK) ){
			if( mod1 == ARY && mod2 == FTN ){
				uerror( "array of functions is illegal" );
				type = 0;
				}
			else if( mod1 == FTN && ( mod2 == ARY || mod2 == FTN ) ){
				uerror( "function returns illegal type" );
				type = 0;
				}
			t = DECREF(t);
			}
		}

	/* detect function arguments, watching out for structure declarations */
	if (rpole && ISFTN(type)) {
		uerror("function illegal in structure or union");
		type = INCREF(type);
	}
	p->n_type = type;
}

/*
 * give undefined version of class
 */
int
uclass(int class)
{
	if (class == SNULL && !fun_inline)
		return(EXTERN);
	else if (class == STATIC)
		return(USTATIC);
	else
		return(class);
}

int
fixclass(int class, TWORD type)
{
	extern int fun_inline;

	/* first, fix null class */
	if (class == SNULL) {
		if (fun_inline && ISFTN(type))
			return SNULL;
		if (rpole)
			cerror("field8");
		else if (blevel == 0)
			class = EXTDEF;
		else
			class = AUTO;
	}

	/* now, do general checking */

	if( ISFTN( type ) ){
		switch( class ) {
		default:
			uerror( "function has illegal storage class" );
		case AUTO:
			class = EXTERN;
		case EXTERN:
		case EXTDEF:
		case TYPEDEF:
		case STATIC:
		case USTATIC:
			;
			}
		}

	if (class & FIELD) {
		cerror("field3");
	}

	switch (class) {

	case MOS:
	case MOU:
		cerror("field4");

	case REGISTER:
		if (blevel == 0)
			uerror("illegal register declaration");
		if (blevel == 1)
			return(PARAM);
		else
			return(REGISTER);

	case AUTO:
		if( blevel < 2 ) uerror( "illegal ULABEL class" );
		return( class );

	case EXTERN:
	case STATIC:
	case EXTDEF:
	case TYPEDEF:
	case USTATIC:
	case PARAM:
	case CCONST:
		return( class );

	default:
		cerror( "illegal class: %d", class );
		/* NOTREACHED */

	}
	return 0; /* XXX */
}

/*
 * Generates a goto statement; sets up label number etc.
 */
void
gotolabel(char *name)
{
	struct symtab *s = lookup(name, SLBLNAME|STEMP);

	if (s->soffset == 0) {
		s->soffset = -getlab();
		s->sclass = STATIC;
	}
	branch(s->soffset < 0 ? -s->soffset : s->soffset);
}

/*
 * Sets a label for gotos.
 */
void
deflabel(char *name, NODE *p)
{
	struct symtab *s = lookup(name, SLBLNAME|STEMP);

#ifdef GCC_COMPAT
	s->sap = gcc_attr_parse(p);
#endif
	if (s->soffset > 0)
		uerror("label '%s' redefined", name);
	if (s->soffset == 0) {
		s->soffset = getlab();
		s->sclass = STATIC;
	}
	if (s->soffset < 0)
		s->soffset = -s->soffset;
	plabel( s->soffset);
}

struct symtab *
getsymtab(char *name, int flags)
{
	struct symtab *s;

	if (flags & SSTMT) {
		s = stmtalloc(sizeof(struct symtab));
	} else if (flags & SBLK) {
		s = blkalloc(sizeof(struct symtab));
	} else if (flags & STEMP) {
		s = tmpalloc(sizeof(struct symtab));
	} else {
		s = permalloc(sizeof(struct symtab));
		symtabcnt++;
	}
	s->sname = name;
	s->snext = NULL;
	s->stype = UNDEF;
	s->squal = 0;
	s->sdf = NULL;
	s->sss = NULL;
	s->sclass = SNULL;
	s->sflags = (short)(flags & SMASK);
	s->soffset = 0;
	s->slevel = (char)blevel;
	s->sap = NULL;
	return s;
}

int
fldchk(int sz)
{
	if (rpole->rsou != STNAME && rpole->rsou != UNAME)
		uerror("field outside of structure");
	if (sz < 0 || sz >= FIELD) {
		uerror("illegal field size");
		return 1;
	}
	return 0;
}

#ifdef PCC_DEBUG
static char *
ccnames[] = { /* names of storage classes */
	"SNULL",
	"AUTO",
	"EXTERN",
	"STATIC",
	"REGISTER",
	"EXTDEF",
	"LABEL",
	"ULABEL",
	"MOS",
	"PARAM",
	"STNAME",
	"MOU",
	"UNAME",
	"TYPEDEF",
	"FORTRAN",
	"ENAME",
	"MOE",
	"UFORTRAN",
	"USTATIC",
	};

char *
scnames(int c)
{
	/* return the name for storage class c */
	static char buf[12];
	if( c&FIELD ){
		snprintf( buf, sizeof(buf), "FIELD[%d]", c&FLDSIZ );
		return( buf );
		}
	return( ccnames[c] );
	}
#endif

#if 0
static char *stack_chk_fail = "__stack_smash_handler";
static char *stack_chk_guard = "__guard";
#else
static char *stack_chk_fail = "__stack_chk_fail";
static char *stack_chk_guard = "__stack_chk_guard";
#endif
static char *stack_chk_canary = "__stack_chk_canary";

void
sspinit(void)
{
	NODE *p;

	p = block(NAME, NIL, NIL, FTN+VOID, 0, 0);
	p->n_sp = lookup(stack_chk_fail, SNORMAL);
	defid(p, EXTERN);
	nfree(p);

	p = block(NAME, NIL, NIL, INT, 0, 0);
	p->n_sp = lookup(stack_chk_guard, SNORMAL);
	defid(p, EXTERN);
	nfree(p);
}

void
sspstart(void)
{
	NODE *p, *q;

	q = block(NAME, NIL, NIL, INT, 0, 0);
 	q->n_sp = lookup(stack_chk_guard, SNORMAL);
	q = clocal(q);

	p = block(REG, NIL, NIL, INCREF(INT), 0, 0);
	slval(p, 0);
	p->n_rval = FPREG;
	p = cast(p, INT, 0);
	q = buildtree(ER, p, q);

	p = block(NAME, NIL, NIL, INT, 0, 0);
	p->n_qual = VOL >> TSHIFT;
	p->n_sp = lookup(stack_chk_canary, SNORMAL);
	defid(p, AUTO);
	p = clocal(p);
	ecomp(buildtree(ASSIGN, p, q));
}

void
sspend(void)
{
	NODE *p, *q;
	TWORD t;
	int lab;

	if (retlab != NOLAB) {
		plabel(retlab);
		retlab = getlab();
	}

	t = DECREF(cftnsp->stype);
	if (t == BOOL)
		t = BOOL_TYPE;

	p = block(NAME, NIL, NIL, INT, 0, 0);
	p->n_sp = lookup(stack_chk_canary, SNORMAL);
	p = clocal(p);

	q = block(REG, NIL, NIL, INCREF(INT), 0, 0);
	slval(q, 0);
	q->n_rval = FPREG;
	q = cast(q, INT, 0);
	q = buildtree(ER, p, q);

	p = block(NAME, NIL, NIL, INT, 0, 0);
	p->n_sp = lookup(stack_chk_guard, SNORMAL);
	p = clocal(p);

	lab = getlab();
	cbranch(buildtree(EQ, p, q), bcon(lab));

	p = block(NAME, NIL, NIL, FTN+VOID, 0, 0);
	p->n_sp = lookup(stack_chk_fail, SNORMAL);
	p = clocal(p);

	q = eve(bdty(STRING, cftnsp->sname, PTR|CHAR));
	ecomp(buildtree(CALL, p, q));

	plabel(lab);
}

/*
 * Fetch pointer to first member in a struct list.
 */
struct symtab *
strmemb(struct ssdesc *ss)
{

	if (ss == NULL)
		cerror("strmemb");
	return ss->sp;
}

void
incref(struct tdef *d, struct tdef *s)
{
	d->type = INCREF(s->type);
	d->qual = INCQAL(s->qual);
	d->df = s->df;
	d->ss = s->ss;
}

struct tdef *
mkqtyp(TWORD t)
{
	static struct tdef td[1];

	td->type = t;
	return td;
}
struct tdef tdint[] = { { INT, 0, 0, 0 } };

/*
 * Allocations:
 *	permalloc() Never freed. in pass2.
 *	tmpalloc() during a function lifetime, then freed. in pass2.
 *	blkalloc() during a block lifetime.  Variables etc.  In pass1.
 *	stmtalloc() during a statement lifetime.  Expression trees.  In pass1.
 */

/*
 * Short-time allocations during statements.
 */
#define MEMCHUNKSZ 8192 /* 8k per allocation */
struct balloc {
        char a1;
        union {
                long long l;
                long double d;
        } a2;
};
#define ALIGNMENT offsetof(struct balloc, a2)
#define ROUNDUP(x) (((x) + ((ALIGNMENT)-1)) & ~((ALIGNMENT)-1))

#define	MAXSZ	MEMCHUNKSZ-sizeof(struct xalloc *)
struct xalloc {
	struct xalloc *next;
	union {
		long long b; /* for initial alignment */
		long double d;
		char elm[MAXSZ];
	};
} *sapole, *bkpole;
int cstp, cbkp;

void *
stmtalloc(size_t size)
{
	struct xalloc *xp;
	void *rv;

	size = ROUNDUP(size);
	if (size > MAXSZ)
		cerror("stmtalloc");
	if (sapole == 0 || (size + cstp) > MAXSZ) {
		xp = xmalloc(sizeof(struct xalloc));
		xp->next = sapole;
		sapole = xp;
		cstp = 0;
	}
	rv = &sapole->elm[cstp];
	cstp += (int)size;
	return rv;
}

void
stmtfree(void)
{
	extern P1ND *frelink;
	extern int usdnodes;
	struct xalloc *x1;

	if (usdnodes != 0)
		cerror("stmtfree: usdnodes %d", usdnodes);
	frelink = NULL;

	while (sapole) {
		x1 = sapole->next;
		free(sapole);
		sapole = x1;
	}
	cstp = 0;
}

void *
blkalloc(size_t size)
{
	struct xalloc *xp;
	void *rv;

	if (blevel < 2)
		return permalloc(size);

	size = ROUNDUP(size);
	if (size > MAXSZ)
		cerror("blkalloc");
	if (bkpole == 0 || (size + cbkp) > MAXSZ) {
		xp = xmalloc(sizeof(struct xalloc));
		xp->next = bkpole;
		bkpole = xp;
		cbkp = 0;
	}
	rv = &bkpole->elm[cbkp];
	cbkp += (int)size;
	return rv;
}

void
blkfree(void)
{
	struct xalloc *x1;

	while (bkpole) {
		x1 = bkpole->next;
		free(bkpole);
		bkpole = x1;
	}
	cbkp = 0;
}

