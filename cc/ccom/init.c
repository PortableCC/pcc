/*	$Id$	*/

/*
 * Copyright (c) 2004, 2007 Anders Magnusson (ragge@ludd.ltu.se).
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
 * notice, this list of conditions and the following disclaimer in the
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

#include "pass1.h"
#include "unicode.h"
#include <string.h>

#define	NODE P1ND
#define	tfree p1tfree
#define	nfree p1nfree
#define	fwalk p1fwalk
#undef n_type
#define n_type ptype
#undef n_qual
#define n_qual pqual
#undef n_df
#define n_df pdf

/*
 * The following machine-dependent routines may be called during
 * initialization:
 * 
 * zbits(OFFSZ, int)	- sets int bits of zero at position OFFSZ.
 * infld(CONSZ off, int fsz, CONSZ val)
 *			- sets the bitfield val starting at off and size fsz.
 * ninval(CONSZ off, int fsz, NODE *)
 *			- prints an integer constant which may have
 *			  a label associated with it, located at off and
 *			  size fsz.
 *
 * Initialization may be of different kind:
 * - Initialization at compile-time, all values are constants and laid
 *   out in memory. Static or extern variables outside functions.
 * - Initialization at run-time, written to their values as code.
 *
 * Currently run-time-initialized variables are only initialized by using
 * move instructions.  An optimization might be to detect that it is
 * initialized with constants and therefore copied from readonly memory.
 */

/*
 * The base element(s) of an initialized variable is kept in a linked 
 * list, allocated while initialized.
 *
 * When a scalar is found, entries are popped of the instk until it's
 * possible to find an entry for a new scalar; then onstk() is called 
 * to get the correct type and size of that scalar.
 *
 * If a right brace is found, pop the stack until a matching left brace
 * were found while filling the elements with zeros.  This left brace is
 * also marking where the current level is for designated initializations.
 *
 * Position entries are increased when traversing back down into the stack.
 */

/*
 * Good-to-know entries from symtab:
 *	soffset - # of bits from beginning of this structure.
 */

/*
 * TO FIX:
 * - Alignment of structs on like i386 char members.
 */

/*
 * Struct used in array initialisation.
 */
struct instk {
	struct	instk *in_prev; /* linked list */
	struct	symtab *in_lnk;	/* member in structure initializations */
	struct	symtab *in_sym; /* symtab index */
	union	dimfun *in_df;	/* dimenston of array */
	TWORD	in_t;		/* type for this level */
	int	in_n;		/* number of arrays seen so far */
	int	in_fl;	/* flag which says if this level is controlled by {} */
};

int doing_init, statinit;

#ifdef PCC_DEBUG
static void prtstk(struct instk *in);
#define	ID(x) if (idebug) printf x
#else
#define ID(x)
#endif

/*
 * Linked lists for initializations.
 */
struct ilist {
	struct ilist *next;
	CONSZ off;	/* bit offset of this entry */
	int fsz;	/* bit size of this entry */
	NODE *n;	/* node containing this data info */
	NODE *oldp;	/* delayed unevaluated data */
};

struct llist {
	SLIST_ENTRY(llist) next;
	CONSZ begsz;	/* bit offset of this entry */
	struct ilist *il;
};

/*
 * Context for an initialization.
 */
struct initctx {
	struct instk *pstk;
	struct symtab *psym;
	SLIST_HEAD(llh, llist) lpole;
	CONSZ basesz;
	int numents;
};

static struct ilist *
getil(struct ilist *next, CONSZ b, int sz, NODE *n, NODE *oldp)
{
	struct ilist *il = tmpalloc(sizeof(struct ilist));

	il->off = b;
	il->fsz = sz;
	il->n = n;
	il->oldp = oldp;
	il->next = next;
	return il;
}

/*
 * Allocate a new struct defining a block of initializers appended to the
 * end of the llist. Return that entry.
 */
static struct llist *
getll(struct initctx *ctx)
{
	struct llist *ll;

	ll = tmpalloc(sizeof(struct llist));
	ll->begsz = ctx->numents * ctx->basesz;
	ll->il = NULL;
	SLIST_INSERT_LAST(&ctx->lpole, ll, next);
	ctx->numents++;
	return ll;
}

/*
 * Return structure containing off bitnumber.
 * Allocate more entries, if needed.
 */
static struct llist *
setll(struct initctx *ctx, OFFSZ off)
{
	struct llist *ll = NULL;

	/* Ensure that we have enough entries */
	while (off >= ctx->basesz * ctx->numents)
		 ll = getll(ctx);

	if (ll != NULL && ll->begsz <= off && ll->begsz + ctx->basesz > off)
		return ll;

	SLIST_FOREACH(ll, &ctx->lpole, next)
		if (ll->begsz <= off && ll->begsz + ctx->basesz > off)
			break;
	return ll; /* ``cannot fail'' */
}
char *astypnames[] = { 0, 0, "\t.byte", "\t.byte", "\t.short", "\t.short",
	"\t.word", "\t.word", "\t.long", "\t.long", "\t.quad", "\t.quad",
	"ERR", "ERR", "ERR",
};

void
inval(CONSZ off, int fsz, NODE *p)
{
	struct symtab *sp;
	CONSZ val;
	TWORD t;

#ifndef NO_COMPLEX
	if (ANYCX(p) && p->n_left->n_right->n_right->n_op == FCON &&
	    p->n_left->n_left->n_right->n_op == FCON) {
		NODE *r = p->n_left->n_right->n_right;
		int sz = (int)tsize(r->n_type, r->n_df, r->pss);
		ninval(off, sz, p->n_left->n_left->n_right);
		ninval(off, sz, r);
		tfree(p);
		return;
	}
#endif

	if (p->n_op != ICON && p->n_op != FCON) {
		uerror("constant required");
		return;
	}
	if (p->n_type == BOOL) {
		if ((U_CONSZ)glval(p) > 1)
			slval(p, 1);
		p->n_type = BOOL_TYPE;
	}
	if (ninval(off, fsz, p))
		return; /* dealt with in local.c */
	t = p->n_type;
	if (t > BTMASK)
		t = INTPTR;

	val = (CONSZ)(glval(p) & SZMASK(sztable[t]));
	if (t <= ULONGLONG) {
		sp = p->n_sp;
		printf(PRTPREF "%s ",astypnames[t]);
		if (val || sp == NULL)
			printf(CONFMT, val);
		if (val && sp != NULL)
			printf("+");
		if (sp != NULL) {
			if ((sp->sclass == STATIC && sp->slevel > 0)) {
				/* fix problem with &&label not defined yet */
				int o = sp->soffset;
				printf(LABFMT, o < 0 ? -o : o);
				if ((sp->sflags & SMASK) == SSTRING)
					sp->sflags |= SASG;
			} else
				printf("%s", getexname(sp));
		}
		printf("\n");
	} else if (t == FLOAT || t == DOUBLE || t == LDOUBLE) {
		uint32_t *ufp;
		int i, nbits;

		ufp = soft_toush(p->n_scon, t, &nbits);
#if TARGET_ENDIAN == TARGET_BE
		for (i = sztable[t] - 1; i >= 0; i -= SZINT) {
			printf(PRTPREF "%s %u\n", astypnames[INT], 
			    (i < nbits ? ufp[i/SZINT] : 0));
		}
#else
		for (i = 0; i < sztable[t]; i += SZINT) {
			printf(PRTPREF "%s %u\n", astypnames[INT], 
			    (i < nbits ? ufp[i/SZINT] : 0));
		}
#endif
	} else
		cerror("inval: unhandled type %d", (int)t);
}

#ifndef MYBFINIT

static int inbits;
static CONSZ xinval;
/*
 * Initialize a bitfield.
 * XXX - use U_CONSZ?
 */
void
infld(CONSZ off, int fsz, CONSZ val)
{
#ifdef PCC_DEBUG
	if (idebug)
		printf("infld off " CONFMT ", fsz %d, val " CONFMT " inbits %d\n",
		    off, fsz, val, inbits);
#endif
	val &= SZMASK(fsz);
#if TARGET_ENDIAN == TARGET_BE
	while (fsz + inbits >= SZCHAR) {
		int shsz = SZCHAR-inbits;
		xinval = (xinval << shsz) | (val >> (fsz - shsz));
		printf(PRTPREF "%s " CONFMT "\n",
		    astypnames[CHAR], (CONSZ)(xinval & SZMASK(SZCHAR)));
		fsz -= shsz;
		val &= SZMASK(fsz);
		xinval = inbits = 0;
	}
	if (fsz) {
		xinval = (xinval << fsz) | val;
		inbits += fsz;
	}
#else
	while (fsz + inbits >= SZCHAR) {
		int shsz = SZCHAR-inbits;
		xinval |= (val << inbits);
		printf(PRTPREF "%s " CONFMT "\n",
		    astypnames[CHAR], (CONSZ)(xinval & SZMASK(SZCHAR)));
		fsz -= shsz;
		val >>= shsz;
		xinval = inbits = 0;
	}
	if (fsz) {
		xinval |= (val << inbits);
		inbits += fsz;
	}
#endif
}

char *asspace = "\t.space";

/*
 * set fsz bits in sequence to zero.
 */
void
zbits(OFFSZ off, int fsz)
{
	int m;

#ifdef PCC_DEBUG
	if (idebug)
		printf("zbits off " CONFMT ", fsz %d inbits %d\n", off, fsz, inbits);
#endif
#if TARGET_ENDIAN == TARGET_BE
	if ((m = (inbits % SZCHAR))) {
		m = SZCHAR - m;
		if (fsz < m) {
			inbits += fsz;
			xinval <<= fsz;
			return;
		} else {
			fsz -= m;
			xinval <<= m;
			printf(PRTPREF "%s " CONFMT "\n", 
			    astypnames[CHAR], (CONSZ)(xinval & SZMASK(SZCHAR)));
			xinval = inbits = 0;
		}
	}
#else
	if ((m = (inbits % SZCHAR))) {
		m = SZCHAR - m;
		if (fsz < m) {
			inbits += fsz;
			return;
		} else {
			fsz -= m;
			printf(PRTPREF "%s " CONFMT "\n", 
			    astypnames[CHAR], (CONSZ)(xinval & SZMASK(SZCHAR)));
			xinval = inbits = 0;
		}
	}
#endif
	if (fsz >= SZCHAR) {
		printf(PRTPREF "%s " CONFMT "\n", asspace, (CONSZ)(fsz/SZCHAR));
		fsz -= (fsz/SZCHAR) * SZCHAR;
	}
	if (fsz) {
		xinval = 0;
		inbits = fsz;
	}
}
#endif

/*
 * beginning of initialization; allocate space to store initialized data.
 * remember storage class for writeout in endinit().
 * p is the newly declarated type.
 */
struct initctx *
beginit(struct symtab *sp)
{
	struct initctx *ict;
	struct instk *is;

	ID(("beginit(%p), sclass %s\n", sp, scnames(sp->sclass)));

	ict = tmpalloc(sizeof(struct initctx));
	ict->pstk = is = tmpalloc(sizeof(struct instk));
	ict->psym = sp;
	SLIST_INIT(&ict->lpole);
	ict->numents = 0;

	if (ISARY(sp->stype)) {
		ict->basesz = tsize(DECREF(sp->stype), sp->sdf+1, sp->sss);
		if (ict->basesz == 0) {
			uerror("array has incomplete type");
			ict->basesz = SZINT;
		}
	} else
		ict->basesz = tsize(sp->stype, sp->sdf, sp->sss);

	/* first element */
	if (ISSOU(sp->stype)) {
		is->in_lnk = strmemb(sp->td->ss);
	} else
		is->in_lnk = NULL;
	is->in_n = 0;
	is->in_t = sp->stype;
	is->in_sym = sp;
	is->in_df = sp->sdf;
	is->in_fl = 0;
	is->in_prev = NULL;
	doing_init++;
	if (sp->sclass == STATIC || sp->sclass == EXTDEF)
		statinit++;
	ID(("beginit(ctx=%p) end\n", ict));
	return ict;
}

/*
 * Push a new entry on the initializer stack.
 * The new entry will be "decremented" to the new sub-type of the previous
 * entry when called.
 * Popping of entries is done elsewhere.
 */
static void
stkpush(struct initctx *ctx)
{
	struct instk *is;
	struct symtab *sq, *sp;
	TWORD t;

	if (ctx->pstk == NULL) {
		sp = ctx->psym;
		t = 0;
	} else {
		t = ctx->pstk->in_t;
		sp = ctx->pstk->in_sym;
	}

#ifdef PCC_DEBUG
	if (idebug) {
		printf("stkpush: '%s' %s ", sp->sname, scnames(sp->sclass));
		tprint(t, 0);
	}
#endif

	/*
	 * Figure out what the next initializer will be, and push it on 
	 * the stack.  If this is an array, just decrement type, if it
	 * is a struct or union, extract the next element.
	 */
	is = tmpalloc(sizeof(struct instk));
	is->in_fl = 0;
	is->in_n = 0;
	if (ctx->pstk == NULL) {
		is->in_lnk = ISSOU(sp->stype) ? strmemb(sp->td->ss) : NULL;
		is->in_t = sp->stype;
		is->in_sym = sp;
		is->in_df = sp->sdf;
	} else if (ISSOU(t)) {
		sq = ctx->pstk->in_lnk;
		if (sq == NULL) {
			uerror("excess of initializing elements");
		} else {
			is->in_lnk = ISSOU(sq->stype) ? strmemb(sq->td->ss) : NULL;
			is->in_t = sq->stype;
			is->in_sym = sq;
			is->in_df = sq->sdf;
		}
	} else if (ISARY(t)) {
		is->in_lnk = ISSOU(DECREF(t)) ? strmemb(ctx->pstk->in_sym->td->ss) : 0;
		is->in_t = DECREF(t);
		is->in_sym = sp;
		if (ctx->pstk->in_df->ddim != NOOFFSET && ctx->pstk->in_df->ddim &&
		    ctx->pstk->in_n >= ctx->pstk->in_df->ddim) {
			werror("excess of initializing elements");
			ctx->pstk->in_n--;
		}
		is->in_df = ctx->pstk->in_df+1;
	} else
		uerror("too many left braces");
	is->in_prev = ctx->pstk;
	ctx->pstk = is;

#ifdef PCC_DEBUG
	if (idebug) {
		printf(" newtype ");
		tprint(is->in_t, 0);
		printf("\n");
	}
#endif
}

/*
 * pop down to either next level that can handle a new initializer or
 * to the next braced level.
 */
static void
stkpop(struct initctx *ctx)
{
#ifdef PCC_DEBUG
	if (idebug)
		printf("stkpop\n");
#endif
	for (; ctx->pstk; ctx->pstk = ctx->pstk->in_prev) {
		if (ctx->pstk->in_t == STRTY && ctx->pstk->in_lnk != NULL) {
			ctx->pstk->in_lnk = ctx->pstk->in_lnk->snext;
			if (ctx->pstk->in_lnk != NULL)
				break;
		}
		if (ISSOU(ctx->pstk->in_t) && ctx->pstk->in_fl)
			break; /* need } */
		if (ISARY(ctx->pstk->in_t)) {
			ctx->pstk->in_n++;
			if (ctx->pstk->in_fl)
				break;
			if (ctx->pstk->in_df->ddim == NOOFFSET ||
			    ctx->pstk->in_n < ctx->pstk->in_df->ddim)
				break; /* ger more elements */
		}
	}
#ifdef PCC_DEBUG
	if (idebug > 1)
		prtstk(ctx->pstk);
#endif
}

/*
 * Count how many elements an array may consist of.
 */
static int
acalc(struct instk *is, int n)
{
	if (is == NULL || !ISARY(is->in_t))
		return 0;
	return acalc(is->in_prev, n * is->in_df->ddim) + n * is->in_n;
}

/*
 * Find current bit offset of the top element on the stack from
 * the beginning of the aggregate.
 */
static CONSZ
findoff(struct initctx *ctx)
{
	struct instk *is;
	OFFSZ off;

#ifdef PCC_DEBUG
	if (ISARY(ctx->pstk->in_t))
		cerror("findoff on bad type %x", ctx->pstk->in_t);
#endif

	/*
	 * Offset calculations. If:
	 * - previous type is STRTY, soffset has in-struct offset.
	 * - this type is ARY, offset is ninit*stsize.
	 */
	for (off = 0, is = ctx->pstk; is; is = is->in_prev) {
		if (is->in_prev && is->in_prev->in_t == STRTY)
			off += is->in_sym->soffset;
		if (ISARY(is->in_t)) {
			/* suesize is the basic type, so adjust */
			TWORD t = is->in_t;
			OFFSZ o;
			while (ISARY(t))
				t = DECREF(t);
			if (ISPTR(t)) {
				o = SZPOINT(t); /* XXX use tsize() */
			} else {
				o = tsize(t, is->in_sym->sdf, is->in_sym->sss);
			}
			off += o * acalc(is, 1);
			while (is->in_prev && ISARY(is->in_prev->in_t)) {
				if (is->in_prev->in_prev &&
				    is->in_prev->in_prev->in_t == STRTY)
					off += is->in_sym->soffset;
				is = is->in_prev;
			}
		}
	}
#ifdef PCC_DEBUG
	if (idebug>1) {
		printf("findoff: off " CONFMT "\n", off);
		prtstk(ctx->pstk);
	}
#endif
	return off;
}

/*
 * Insert the node p with size fsz at position off.
 * Bit fields are already dealt with, so a node of correct type
 * with correct alignment and correct bit offset is given.
 */
static void
nsetval(struct initctx *ctx, CONSZ off, int fsz, NODE *p, NODE *oldp)
{
	struct llist *ll;
	struct ilist *il;

	if (idebug>1)
		printf("setval: off " CONFMT " fsz %d p %p\n", off, fsz, p);

	if (fsz == 0)
		return;

	ll = setll(ctx, off);
	off -= ll->begsz;
	if (ll->il == NULL) {
		ll->il = getil(NULL, off, fsz, p, oldp);
	} else {
		il = ll->il;
		if (il->off > off) {
			ll->il = getil(ll->il, off, fsz, p, oldp);
		} else {
			for (il = ll->il; il->next; il = il->next)
				if (il->off <= off && il->next->off > off)
					break;
			if (il->off == off) {
				/* replace */
				nfree(il->n);
				il->n = p;
			} else
				il->next = getil(il->next, off, fsz, p, oldp);
		}
	}
}

/*
 * take care of generating a value for the initializer p
 * inoff has the current offset (last bit written)
 * in the current word being generated
 * Returns the offset.
 */
static void
scalinit(struct initctx *ctx, NODE *p, NODE *oldp)
{
	CONSZ woff;
	NODE *q;
	int fsz;

	ID(("scalinit(ctx=%p, n=%p)\n", ctx, p));
#ifdef PCC_DEBUG
	if (idebug > 2) {
		fwalk(p, eprint, 0);
		prtstk(ctx->pstk);
	}
#endif

	if (nerrors)
		return;

	p = optim(p);

#ifdef notdef /* leave to the target to decide if useable */
	if (csym->sclass != AUTO && p->n_op != ICON &&
	    p->n_op != FCON && p->n_op != NAME)
		cerror("scalinit not leaf");
#endif

	/* Out of elements? */
	if (ctx->pstk == NULL) {
		uerror("excess of initializing elements");
		return;
	}

	/*
	 * Get to the simple type if needed.
	 */
	while (ISSOU(ctx->pstk->in_t) || ISARY(ctx->pstk->in_t)) {
		stkpush(ctx);
		/* If we are doing auto struct init */
		if (ISSOU(ctx->pstk->in_t) && ISSOU(p->n_type) &&
		    suemeq(ctx->pstk->in_sym->td->ss, p->n_td->ss)) {
			ctx->pstk->in_lnk = NULL; /* this elem is initialized */
			break;
		}
	}

	if (ISSOU(ctx->pstk->in_t) == 0) {
		/* let buildtree do typechecking (and casting) */
		q = block(NAME, NIL,NIL, ctx->pstk->in_t, ctx->pstk->in_df,
		    ctx->pstk->in_sym->sss);
		p = buildtree(ASSIGN, q, p);
		nfree(p->n_left);
		q = p->n_right;
		nfree(p);
	} else
		q = p;

	q = optloop(q);

	woff = findoff(ctx);

	/* bitfield sizes are special */
	if (ctx->pstk->in_sym->sclass & FIELD)
		fsz = -(ctx->pstk->in_sym->sclass & FLDSIZ);
	else
		fsz = (int)tsize(ctx->pstk->in_t, ctx->pstk->in_sym->sdf,
		    ctx->pstk->in_sym->sss);

	nsetval(ctx, woff, fsz, q, oldp);
	if (q->n_op == ICON && q->n_sp &&
	    ((q->n_sp->sflags & SMASK) == SSTRING))
		q->n_sp->sflags |= SASG;

	stkpop(ctx);
	ID(("scalinit end(%p)\n", q));
}

/*
 * Generate code to insert a value into a bitfield.
 */
static void
insbf(struct initctx *ctx, OFFSZ off, int fsz, int val)
{
	struct symtab sym;
	NODE *p, *r;
	TWORD typ;

#ifdef PCC_DEBUG
	if (idebug > 1)
		printf("insbf: off " CONFMT " fsz %d val %d\n", off, fsz, val);
#endif

	if (fsz == 0)
		return;

	/* small opt: do char instead of bf asg */
	if ((off & (ALCHAR-1)) == 0 && fsz == SZCHAR)
		typ = CHAR;
	else
		typ = INT;
	/* Fake a struct reference */
	p = buildtree(ADDROF, nametree(ctx->psym), NIL);
	sym.stype = typ;
	sym.squal = 0;
	sym.sdf = 0;
	sym.sss = 0;
	sym.sap = NULL;
	sym.soffset = (int)off;
	sym.sclass = (char)(typ == INT ? FIELD | fsz : MOU);
	r = xbcon(0, &sym, typ);
	p = block(STREF, p, r, INT, 0, 0);
	ecomp(buildtree(ASSIGN, stref(p), bcon(val)));
}

/*
 * Clear a bitfield, starting at off and size fsz.
 */
static void
clearbf(struct initctx *ctx, OFFSZ off, OFFSZ fsz)
{
	/* Pad up to the next even initializer */
	if ((off & (ALCHAR-1)) || (fsz < SZCHAR)) {
		int ba = (int)(((off + (SZCHAR-1)) & ~(SZCHAR-1)) - off);
		if (ba > fsz)
			ba = (int)fsz;
		insbf(ctx, off, ba, 0);
		off += ba;
		fsz -= ba;
	}
	while (fsz >= SZCHAR) {
		insbf(ctx, off, SZCHAR, 0);
		off += SZCHAR;
		fsz -= SZCHAR;
	}
	if (fsz)
		insbf(ctx, off, fsz, 0);
}

/*
 * final step of initialization.
 * print out init nodes and generate copy code (if needed).
 */
struct symtab *
endinit(struct initctx *ctx, int seg)
{
	struct llist *ll;
	struct ilist *il;
	int fsz;
	OFFSZ lastoff, tbit;

	ID(("endinit()\n"));

	/* Calculate total block size */
	if (ISARY(ctx->psym->stype) && ctx->psym->sdf->ddim == NOOFFSET) {
		tbit = ctx->numents*ctx->basesz; /* open-ended arrays */
		ctx->psym->sdf->ddim = ctx->numents;
		if (ctx->psym->sclass == AUTO) { /* Get stack space */
			ctx->psym->soffset = NOOFFSET;
			oalloc(ctx->psym, &autooff);
		}
	} else
		tbit = tsize(ctx->psym->stype, ctx->psym->sdf, ctx->psym->sss);

	/* Setup symbols */
	if (ctx->psym->sclass != AUTO) {
		locctr(seg ? UDATA : DATA, ctx->psym);
		defloc(ctx->psym);
	}

	/* Traverse all entries and print'em out */
	lastoff = 0;
	SLIST_FOREACH(ll, &ctx->lpole, next) {
		for (il = ll->il; il; il = il->next) {
#ifdef PCC_DEBUG
			if (idebug > 1) {
				printf("off " CONFMT " size %d val " CONFMT " type ",
				    ll->begsz+il->off, il->fsz, glval(il->n));
				tprint(il->n->n_type, 0);
				printf("\n");
			}
#endif
			fsz = il->fsz;
			if (ctx->psym->sclass == AUTO) {
				struct symtab sym;
				NODE *p, *r, *n;

				if (ll->begsz + il->off > lastoff)
					clearbf(ctx, lastoff,
					    (ll->begsz + il->off) - lastoff);

				if (il->oldp) {
					p1tfree(il->n);
					il->n = optloop(eve(il->oldp));
				}
				/* Fake a struct reference */
				p = buildtree(ADDROF, nametree(ctx->psym), NIL);
				n = il->n;
				sym.stype = n->n_type;
				sym.squal = n->n_qual;
				sym.sdf = n->n_df;
				sym.sss = n->pss;
				sym.sap = n->n_ap;
				sym.soffset = (int)(ll->begsz + il->off);
				sym.sclass = (char)(fsz < 0 ? FIELD | -fsz : 0);
				r = xbcon(0, &sym, INT);
				p = block(STREF, p, r, INT, 0, 0);
				ecomp(buildtree(ASSIGN, stref(p), il->n));
				if (fsz < 0)
					fsz = -fsz;

			} else {
				if (ll->begsz + il->off > lastoff)
					zbits(lastoff,
					    (ll->begsz + il->off) - lastoff);
				if (fsz < 0) {
					fsz = -fsz;
					infld(il->off, fsz, glval(il->n));
				} else
					inval(il->off, fsz, il->n);
				tfree(il->n);
			}
			lastoff = ll->begsz + il->off + fsz;
		}
	}
	if (ctx->psym->sclass == AUTO) {
		clearbf(ctx, lastoff, tbit-lastoff);
	} else
		zbits(lastoff, tbit-lastoff);
	
	doing_init--;
	if (ctx->psym->sclass == STATIC || ctx->psym->sclass == EXTDEF)
		statinit--;
	ID(("endinit() end\n"));
	return ctx->psym;
}

/*
 * process an initializer's left brace
 */
void
ilbrace(struct initctx *ctx)
{
#ifdef PCC_DEBUG
	if (idebug)
		printf("ilbrace(ctx=%p)\n", ctx);
#endif

	stkpush(ctx);
	ctx->pstk->in_fl = 1; /* mark lbrace */
#ifdef PCC_DEBUG
	if (idebug > 1)
		prtstk(ctx->pstk);
#endif
}

/*
 * called when a '}' is seen
 */
void
irbrace(struct initctx *ctx)
{
#ifdef PCC_DEBUG
	if (idebug)
		printf("irbrace()\n");
	if (idebug > 2)
		prtstk(ctx->pstk);
#endif

	/* Got right brace, search for corresponding in the stack */
	for (; ctx->pstk->in_prev != NULL; ctx->pstk = ctx->pstk->in_prev) {
		if(!ctx->pstk->in_fl)
			continue;

		/* we have one now */

		ctx->pstk->in_fl = 0;  /* cancel { */
		if (ISARY(ctx->pstk->in_t))
			ctx->pstk->in_n = ctx->pstk->in_df->ddim;
		else if (ctx->pstk->in_t == STRTY) {
			while (ctx->pstk->in_lnk != NULL &&
			    ctx->pstk->in_lnk->snext != NULL)
				ctx->pstk->in_lnk = ctx->pstk->in_lnk->snext;
		}
		stkpop(ctx);
		return;
	}
}

/*
 * Search for next element given.  If anon structs, must return each 
 * anon struct to make offset calculation happy.
 */
static struct symtab *
felem(struct symtab *sp, char *n)
{
	struct symtab *rs;

	for (; sp; sp = sp->snext) {
		if (sp->sname[0] == '*') {
			if ((rs = felem(strattr(sp->td)->sp, n)) != NULL)
				return sp;
		} else if (sp->sname == n)
			return sp;
	}
	return sp;
}

/*
 * Create a new init stack based on given elements.
 */
static void
mkstack(struct initctx *ctx, NODE *p)
{

	ID(("mkstack: ctx=%p,n=%p\n", ctx, p));
#ifdef PCC_DEBUG
	if (idebug > 1 && p)
		fwalk(p, eprint, 0);
#endif

	if (p == NULL)
		return;
	mkstack(ctx, p->n_left);

	switch (p->n_op) {
	case LB: /* Array index */
		if (p->n_right->n_op != ICON)
			cerror("mkstack");
		if (!ISARY(ctx->pstk->in_t))
			uerror("array indexing non-array");
		ctx->pstk->in_n = (int)glval(p->n_right);
		nfree(p->n_right);
		break;

	case NAME:
		ID(("mkstack name %s\n", (char *)p->n_sp));
		if (ctx->pstk->in_lnk) {
			ctx->pstk->in_lnk = felem(ctx->pstk->in_lnk, (char *)p->n_sp);
			if (ctx->pstk->in_lnk == NULL)
				uerror("member missing");
		} else {
			uerror("not a struct/union");
		}
		break;
	default:
		cerror("mkstack2");
	}
	nfree(p);
	stkpush(ctx);
	ID(("mkstack end: %p\n", p));
}

/*
 * Initialize a specific element, as per C99.
 */
void
desinit(struct initctx *ctx, NODE *p)
{
	int op = p->n_op;

	ID(("desinit ctx=%p, n=%p\n", ctx, p));
	if (ctx->pstk == NULL)
		stkpush(ctx); /* passed end of array */
	while (ctx->pstk->in_prev && ctx->pstk->in_fl == 0)
		ctx->pstk = ctx->pstk->in_prev; /* Empty stack */

	if (ISSOU(ctx->pstk->in_t))
		ctx->pstk->in_lnk = strmemb(ctx->pstk->in_sym->td->ss);

	mkstack(ctx, p);	/* Setup for assignment */

	/* pop one step if SOU, ilbrace will push */
	if (op == NAME || op == LB)
		ctx->pstk = ctx->pstk->in_prev;

	ID(("desinit end %p\n", p));
#ifdef PCC_DEBUG
	if (idebug > 1)
		prtstk(ctx->pstk);
#endif
}

/*
 * Convert a string to an array of char/wchar for asginit.
 */
static void
strcvt(struct initctx *ctx, NODE *p)
{
	NODE *q = p;
	char *s;
	int i;

#if defined(mach_arm) || defined(mach_aarch64)
	/* XXX */
	if (p->n_op == UMUL && p->n_left->n_op == ADDROF)
		p = p->n_left->n_left;
#endif

	for (s = p->n_sp->sname; *s != 0; ) {
		if (p->n_type == ARY+WCHAR_TYPE)
			i = (int)u82cp(&s);
		else if (*s == '\\')
			i = esccon(&s);
		else
			i = (unsigned char)*s++;
		asginit(ctx, bcon(i));
	} 
	tfree(q);
}

/*
 * Search for an initialization that reference itself (pre-eve).
 */
static int
refself(P1ND *p, char *s)
{
	int o = coptype(p->n_op);
	int n = 0;

	if (o == LTYPE) {
		if (p->n_op == NAME && (char *)p->n_sp == s)
			return 1;
		return 0;
	}
	if (o == BITYPE)
		n = refself(p->n_right, s);
	n |= refself(p->n_left, s);
	return n;
}

/*
 * Do an assignment to a struct element.
 */
void
asginit(struct initctx *ctx, P1ND *p)
{
	NODE *oldp;
	int g;

#ifdef PCC_DEBUG
	if (idebug)
		printf("asginit ctx=%p, n=%p\n", ctx, p);
	if (idebug > 1 && p)
		fwalk(p, eprint, 0);
#endif

	/* save an unaltered version of the initialization */
	oldp = NULL;
	if (p && ISARY(ctx->psym->stype) && ctx->psym->sdf->ddim == NOOFFSET &&
	    ctx->psym->sclass == AUTO) {
		if (refself(p, ctx->psym->sname))
			oldp = p1tcopy(p);
	}

	if (p)
		p = eve(p);

	/* convert string to array of char/wchar */
	if (p && (DEUNSIGN(p->n_type) == ARY+CHAR ||
	    p->n_type == ARY+WCHAR_TYPE)) {
		struct instk *is;
		TWORD t;

		t = p->n_type == ARY+WCHAR_TYPE ? ARY+WCHAR_TYPE : ARY+CHAR;
		/*
		 * ...but only if next element is ARY+CHAR, otherwise 
		 * just fall through.
		 */

		/* HACKHACKHACK */
		is = ctx->pstk;

		while (ISSOU(ctx->pstk->in_t) || ISARY(ctx->pstk->in_t))
			stkpush(ctx);
		if (ctx->pstk->in_prev && 
		    (DEUNSIGN(ctx->pstk->in_prev->in_t) == t ||
		    ctx->pstk->in_prev->in_t == t)) {
			ctx->pstk = ctx->pstk->in_prev;
			if ((g = ctx->pstk->in_fl) == 0)
				ctx->pstk->in_fl = 1; /* simulate ilbrace */

			strcvt(ctx, p);
			if (ctx->pstk->in_df->ddim == NOOFFSET)
				asginit(ctx, bcon(0));
			if (g == 0)
				irbrace(ctx); /* will fill with zeroes */
			return;
		} else
			ctx->pstk = is; /* no array of char */
		/* END HACKHACKHACK */
	}


	if (p == NULL) { /* only end of compound stmt */
		irbrace(ctx);
	} else /* assign next element */
		scalinit(ctx, p, oldp);
}

#ifdef PCC_DEBUG
void
prtstk(struct instk *in)
{
	int i, o = 0;

	printf("init stack:\n");
	for (; in != NULL; in = in->in_prev) {
		for (i = 0; i < o; i++)
			printf("  ");
		printf("%p) '%s' ", in, in->in_sym->sname);
		tprint(in->in_t, 0);
		printf(" %s ", scnames(in->in_sym->sclass));
		if (in->in_df /* && in->in_df->ddim */)
		    printf("arydim=%d ", in->in_df->ddim);
		printf("ninit=%d ", in->in_n);
		if (BTYPE(in->in_t) == STRTY || ISARY(in->in_t))
			printf("stsize=%d ",
			    (int)tsize(in->in_t, in->in_df, in->in_sym->sss));
		if (in->in_fl) printf("{ ");
		printf("soff=%d ", in->in_sym->soffset);
		if (in->in_t == STRTY) {
			if (in->in_lnk)
				printf("curel %s ", in->in_lnk->sname);
			else
				printf("END struct");
		}
		printf("\n");
		o++;
	}
}
#endif

/*
 * Do a simple initialization.
 * At block 0, just print out the value, at higher levels generate
 * appropriate code.
 */
void
simpleinit(struct symtab *sp, NODE *p)
{
	struct initctx *ctx;
	NODE *q, *r, *nt;
	TWORD t;
	int sz;

	/* May be an initialization of an array of char by a string */
	if ((DEUNSIGN(p->n_type) == ARY+CHAR &&
	    DEUNSIGN(sp->stype) == ARY+CHAR) ||
	    (DEUNSIGN(p->n_type) == DEUNSIGN(ARY+WCHAR_TYPE) &&
	    DEUNSIGN(sp->stype) == DEUNSIGN(ARY+WCHAR_TYPE))) {
		/* Handle "aaa" as { 'a', 'a', 'a' } */
		ctx = beginit(sp);
		strcvt(ctx, p);
		if (ctx->psym->sdf->ddim == NOOFFSET)
			scalinit(ctx, bcon(0), NULL); /* Null-term arrays */
		endinit(ctx, 0);
		return;
	}

	nt = nametree(sp);
	switch (sp->sclass) {
	case STATIC:
	case EXTDEF:
		q = nt;
		locctr(DATA, sp);
		defloc(sp);
#ifndef NO_COMPLEX
		if (ANYCX(q) || ANYCX(p)) {
			r = cxop(ASSIGN, q, p);
			/* XXX must unwind the code generated here */
			/* We can rely on correct code generated */
			p = r->n_left->n_right->n_left;
			r->n_left->n_right->n_left = bcon(0);
			tfree(r);
			r = p->n_left->n_right;
			sz = (int)tsize(r->n_type, r->n_df, r->pss);
			inval(0, sz, r);
			inval(0, sz, p->n_right->n_right);
			tfree(p);
			break;
		} else if (ISITY(p->n_type) || ISITY(q->n_type)) {
			/* XXX merge this with code from imop() */
			int li = 0, ri = 0;
			if (ISITY(p->n_type))
				li = 1, p->n_type = p->n_type - (FIMAG-FLOAT);
			if (ISITY(q->n_type))
				ri = 1, q->n_type = q->n_type - (FIMAG-FLOAT);
			if (!(li && ri)) {
				tfree(p);
				p = bcon(0);
			}
			/* continue below */
		}
#endif
#ifdef GCC_COMPAT
#ifdef TARGET_TIMODE
		struct attr *ap;
		if ((ap = attr_find(sp->sap, GCC_ATYP_MODE)) &&
		    strcmp(ap->aa[0].sarg, "TI") == 0) {
			if (p->n_op != ICON)
				uerror("need to handle TImode initializer ");
			sz = (int)tsize(sp->stype, sp->sdf, sp->sss);
			p->n_type = ctype(LONGLONG);
			inval(0, sz/2, p);
			slval(p, 0); /* XXX fix signed types */
			inval(0, sz/2, p);
			tfree(p);
			tfree(q);
			break;
		}
#endif
#endif
		if (p->n_op == NAME && p->n_sp &&
		    (p->n_sp->sflags & SMASK) == SSTRING)
			p->n_sp->sflags |= SASG;
		p = optloop(buildtree(ASSIGN, nt, p));
		q = p->n_right;
		t = q->n_type;
		sz = (int)tsize(t, q->n_df, q->pss);
		inval(0, sz, q);
		tfree(p);
		break;

	case AUTO:
	case REGISTER:
		if (ISARY(sp->stype))
			cerror("no array init");
		q = nt;
#ifdef TARGET_TIMODE
		if ((r = gcc_eval_timode(ASSIGN, q, p)) != NULL)
			;
		else
#endif
#ifndef NO_COMPLEX

		if (ANYCX(q) || ANYCX(p))
			r = cxop(ASSIGN, q, p);
		else if (ISITY(p->n_type) || ISITY(q->n_type))
			r = imop(ASSIGN, q, p);
		else
#endif
			r = buildtree(ASSIGN, q, p);
		ecomp(r);
		break;

	case CCONST:
		sp->soffset = icons(p);
		p1nfree(nt);
		break;

	default:
		uerror("illegal initialization");
	}
}
