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
