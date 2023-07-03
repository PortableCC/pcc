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

#include "pass1.h"

#ifndef NO_COMPLEX

extern int dimfuncnt;

static char *real, *imag;
static struct symtab *cxsp[3], *cxmul[3], *cxdiv[3];
static char *cxnmul[] = { "__mulsc3", "__muldc3", "__mulxc3" };
static char *cxndiv[] = { "__divsc3", "__divdc3", "__divxc3" };
/*
 * As complex numbers internally are handled as structs, create
 * these by hand-crafting them.
 */
void
complinit(void)
{
	struct attr *ap;
	struct rstack *rp;
	P1ND *p, *q;
	char *n[] = { "0f", "0d", "0l" };
	int i, d_debug;

	d_debug = ddebug;
	ddebug = 0;
	real = addname("__real");
	imag = addname("__imag");
	p = block(NAME, NULL, NULL, FLOAT, 0, 0);
	for (i = 0; i < 3; i++) {
		p->n_type = FLOAT+i;
		rpole = rp = bstruct(NULL, STNAME, NULL);
		soumemb(p, real, 0);
		soumemb(p, imag, 0);
		q = dclstruct(rp);
		cxsp[i] = q->n_sp = lookup(addname(n[i]), 0);
		defid(q, TYPEDEF);
		ap = attr_new(ATTR_COMPLEX, 0);
		q->n_sp->sap = attr_add(q->n_sp->sap, ap);
		p1nfree(q);
	}
	/* create function declarations for external ops */
	for (i = 0; i < 3; i++) {
		cxnmul[i] = addname(cxnmul[i]);
		p->n_sp = cxmul[i] = lookup(cxnmul[i], 0);
		p->n_type = FTN|STRTY;
		p->n_ap = cxsp[i]->sap;
		p->n_df = cxsp[i]->sdf;
		defid2(p, EXTERN, 0);
		cxmul[i]->sdf = permalloc(sizeof(union dimfun));
		dimfuncnt++;
		cxmul[i]->sdf->dfun = NULL;
		cxndiv[i] = addname(cxndiv[i]);
		p->n_sp = cxdiv[i] = lookup(cxndiv[i], 0);
		p->n_type = FTN|STRTY;
		p->n_ap = cxsp[i]->sap;
		p->n_df = cxsp[i]->sdf;
		defid2(p, EXTERN, 0);
		cxdiv[i]->sdf = permalloc(sizeof(union dimfun));
		dimfuncnt++;
		cxdiv[i]->sdf->dfun = NULL;
	}
	p1nfree(p);
	ddebug = d_debug;
}

static TWORD
maxtt(P1ND *p)
{
	TWORD t;

	t = ANYCX(p) ? strmemb(p->n_ap)->stype : p->n_type;
	t = BTYPE(t);
	if (t == VOID)
		t = CHAR; /* pointers */
	if (ISITY(t))
		t -= (FIMAG - FLOAT);
	return t;
}

/*
 * Return the highest real floating point type.
 * Known that at least one type is complex or imaginary.
 */
static TWORD
maxtyp(P1ND *l, P1ND *r)
{
	TWORD tl, tr, t;

	tl = maxtt(l);
	tr = maxtt(r);
	t = tl > tr ? tl : tr;
	if (!ISFTY(t))
		cerror("maxtyp");
	return t;
}

/*
 * Fetch space on stack for complex struct.
 */
static P1ND *
cxstore(TWORD t)
{
	struct symtab s;

	s = *cxsp[t - FLOAT];
	s.sclass = AUTO;
	s.soffset = NOOFFSET;
	oalloc(&s, &autooff);
	return nametree(&s);
}

#define	comop(x,y) buildtree(COMOP, x, y)

/*
 * Convert node p to complex type dt.
 */
P1ND *
mkcmplx(P1ND *p, TWORD dt)
{
	P1ND *q, *r, *i, *t;

	if (!ANYCX(p)) {
		/* Not complex, convert to complex on stack */
		q = cxstore(dt);
		if (ISITY(p->n_type)) {
			p->n_type = p->n_type - FIMAG + FLOAT;
			r = bcon(0);
			i = p;
		} else {
			if (ISPTR(p->n_type))
				p = cast(p, INTPTR, 0);
			r = p;
			i = bcon(0);
		}
		p = buildtree(ASSIGN, structref(p1tcopy(q), DOT, real), r);
		p = comop(p, buildtree(ASSIGN, structref(p1tcopy(q), DOT, imag), i));
		p = comop(p, q);
	} else {
		if (strmemb(p->n_ap)->stype != dt) {
			q = cxstore(dt);
			p = buildtree(ADDROF, p, NULL);
			t = tempnode(0, p->n_type, p->n_df, p->n_ap);
			p = buildtree(ASSIGN, p1tcopy(t), p);
			p = comop(p, buildtree(ASSIGN,
			    structref(p1tcopy(q), DOT, real),
			    structref(p1tcopy(t), STREF, real)));
			p = comop(p, buildtree(ASSIGN,
			    structref(p1tcopy(q), DOT, imag),
			    structref(t, STREF, imag)));
			p = comop(p, q);
		}
	}
	return p;
}

static P1ND *
cxasg(P1ND *l, P1ND *r)
{
	TWORD tl, tr;

	tl = strattr(l->n_ap) ? strmemb(l->n_ap)->stype : 0;
	tr = strattr(r->n_ap) ? strmemb(r->n_ap)->stype : 0;

	if (ANYCX(l) && ANYCX(r) && tl != tr) {
		/* different types in structs */
		r = mkcmplx(r, tl);
	} else if (!ANYCX(l))
		r = structref(r, DOT, ISITY(l->n_type) ? imag : real);
	else if (!ANYCX(r))
		r = mkcmplx(r, tl);
	return buildtree(ASSIGN, l, r);
}

/*
 * Fixup complex operations.
 * At least one operand is complex.
 */
P1ND *
cxop(int op, P1ND *l, P1ND *r)
{
	TWORD mxtyp;
	P1ND *p, *q;
	P1ND *ltemp, *rtemp;
	P1ND *real_l, *imag_l;
	P1ND *real_r, *imag_r;
	real_r = imag_r = NULL; /* bad uninit var warning */

	if (op == ASSIGN)
		return cxasg(l, r);

	mxtyp = maxtyp(l, r);
	l = mkcmplx(l, mxtyp);
	if (op != UMINUS)
		r = mkcmplx(r, mxtyp);

	if (op == COLON)
		return buildtree(COLON, l, r);

	/* put a pointer to left and right elements in a TEMP */
	l = buildtree(ADDROF, l, NULL);
	ltemp = tempnode(0, l->n_type, l->n_df, l->n_ap);
	l = buildtree(ASSIGN, p1tcopy(ltemp), l);

	if (op != UMINUS) {
		r = buildtree(ADDROF, r, NULL);
		rtemp = tempnode(0, r->n_type, r->n_df, r->n_ap);
		r = buildtree(ASSIGN, p1tcopy(rtemp), r);

		p = comop(l, r);
	} else
		p = l;

	/* create the four trees needed for calculation */
	real_l = structref(p1tcopy(ltemp), STREF, real);
	imag_l = structref(ltemp, STREF, imag);
	if (op != UMINUS) {
		real_r = structref(p1tcopy(rtemp), STREF, real);
		imag_r = structref(rtemp, STREF, imag);
	}

	/* get storage on stack for the result */
	q = cxstore(mxtyp);

	switch (op) {
	case NE:
	case EQ:
		p1tfree(q);
		p = buildtree(op, comop(p, real_l), real_r);
		q = buildtree(op, imag_l, imag_r);
		p = buildtree(op == EQ ? ANDAND : OROR, p, q);
		return p;

	case ANDAND:
	case OROR: /* go via EQ to get INT of it */
		p1tfree(q);
		p = buildtree(NE, comop(p, real_l), bcon(0)); /* gets INT */
		q = buildtree(NE, imag_l, bcon(0));
		p = buildtree(OR, p, q);

		q = buildtree(NE, real_r, bcon(0));
		q = buildtree(OR, q, buildtree(NE, imag_r, bcon(0)));

		p = buildtree(op, p, q);
		return p;

	case UMINUS:
		p = comop(p, buildtree(ASSIGN, structref(p1tcopy(q), DOT, real), 
		    buildtree(op, real_l, NULL)));
		p = comop(p, buildtree(ASSIGN, structref(p1tcopy(q), DOT, imag), 
		    buildtree(op, imag_l, NULL)));
		break;

	case PLUS:
	case MINUS:
		p = comop(p, buildtree(ASSIGN, structref(p1tcopy(q), DOT, real), 
		    buildtree(op, real_l, real_r)));
		p = comop(p, buildtree(ASSIGN, structref(p1tcopy(q), DOT, imag), 
		    buildtree(op, imag_l, imag_r)));
		break;

	case MUL:
	case DIV:
		/* Complex mul is "complex" */
		/* (u+iv)*(x+iy)=((u*x)-(v*y))+i(v*x+y*u) */
		/* Complex div is even more "complex" */
		/* (u+iv)/(x+iy)=(u*x+v*y)/(x*x+y*y)+i((v*x-u*y)/(x*x+y*y)) */
		/* but we need to do it via a subroutine */
		p1tfree(q);
		p = buildtree(CM, comop(p, real_l), imag_l);
		p = buildtree(CM, p, real_r);
		p = buildtree(CM, p, imag_r);
		q = nametree(op == DIV ?
		    cxdiv[mxtyp-FLOAT] : cxmul[mxtyp-FLOAT]);
		return buildtree(CALL, q, p);
		break;
	default:
		uerror("illegal operator %s", copst(op));
	}
	return comop(p, q);
}

/*
 * Fixup imaginary operations.
 * At least one operand is imaginary, none is complex.
 */
P1ND *
imop(int op, P1ND *l, P1ND *r)
{
	P1ND *p, *q;
	TWORD mxtyp;
	int li, ri;

	li = ri = 0;
	if (ISITY(l->n_type))
		li = 1, l->n_type = l->n_type - (FIMAG-FLOAT);
	if (ISITY(r->n_type))
		ri = 1, r->n_type = r->n_type - (FIMAG-FLOAT);

	mxtyp = maxtyp(l, r);
	switch (op) {
	case ASSIGN:
		/* if both are imag, store value, otherwise store 0.0 */
		if (!(li && ri)) {
			p1tfree(r);
			r = bcon(0);
		}
		p = buildtree(ASSIGN, l, r);
		p->n_type += (FIMAG-FLOAT);
		break;

	case PLUS:
		if (li && ri) {
			p = buildtree(PLUS, l, r);
			p->n_type += (FIMAG-FLOAT);
		} else {
			/* If one is imaginary and one is real, make complex */
			if (li)
				q = l, l = r, r = q; /* switch */
			q = cxstore(mxtyp);
			p = buildtree(ASSIGN,
			    structref(p1tcopy(q), DOT, real), l);
			p = comop(p, buildtree(ASSIGN,
			    structref(p1tcopy(q), DOT, imag), r));
			p = comop(p, q);
		}
		break;

	case MINUS:
		if (li && ri) {
			p = buildtree(MINUS, l, r);
			p->n_type += (FIMAG-FLOAT);
		} else if (li) {
			q = cxstore(mxtyp);
			p = buildtree(ASSIGN, structref(p1tcopy(q), DOT, real),
			    buildtree(UMINUS, r, NULL));
			p = comop(p, buildtree(ASSIGN,
			    structref(p1tcopy(q), DOT, imag), l));
			p = comop(p, q);
		} else /* if (ri) */ {
			q = cxstore(mxtyp);
			p = buildtree(ASSIGN,
			    structref(p1tcopy(q), DOT, real), l);
			p = comop(p, buildtree(ASSIGN,
			    structref(p1tcopy(q), DOT, imag),
			    buildtree(UMINUS, r, NULL)));
			p = comop(p, q);
		}
		break;

	case MUL:
		p = buildtree(MUL, l, r);
		if (li && ri)
			p = buildtree(UMINUS, p, NULL);
		if (li ^ ri)
			p->n_type += (FIMAG-FLOAT);
		break;

	case DIV:
		p = buildtree(DIV, l, r);
		if (ri && !li)
			p = buildtree(UMINUS, p, NULL);
		if (li ^ ri)
			p->n_type += (FIMAG-FLOAT);
		break;

	case EQ:
	case NE:
	case LT:
	case LE:
	case GT:
	case GE:
		if (li ^ ri) { /* always 0 */
			p1tfree(l);
			p1tfree(r);
			p = bcon(0);
		} else
			p = buildtree(op, l, r);
		break;

	default:
		cerror("imop");
		p = NULL;
	}
	return p;
}

P1ND *
cxelem(int op, P1ND *p)
{

	if (ANYCX(p)) {
		p = structref(p, DOT, op == XREAL ? real : imag);
	} else if (op == XIMAG) {
		/* XXX  sanitycheck? */
		p1tfree(p);
		p = bcon(0);
	}
	return p;
}

P1ND *
cxconj(P1ND *p)
{
	P1ND *q, *r;

	/* XXX side effects? */
	q = cxstore(strmemb(p->n_ap)->stype);
	r = buildtree(ASSIGN, structref(p1tcopy(q), DOT, real),
	    structref(p1tcopy(p), DOT, real));
	r = comop(r, buildtree(ASSIGN, structref(p1tcopy(q), DOT, imag),
	    buildtree(UMINUS, structref(p, DOT, imag), NULL)));
	return comop(r, q);
}

/*
 * Prepare for return.
 * There may be implicit casts to other types.
 */
P1ND *
imret(P1ND *p, P1ND *q)
{
	if (ISITY(q->n_type) && ISITY(p->n_type)) {
		if (p->n_type != q->n_type) {
			p->n_type -= (FIMAG-FLOAT);
			p = cast(p, q->n_type - (FIMAG-FLOAT), 0);
			p->n_type += (FIMAG-FLOAT);
		}
	} else {
		p1tfree(p);
		if (ISITY(q->n_type)) {
			p = block(FCON, 0, 0, q->n_type, 0, 0);
			p->n_scon = sfallo();
			FLOAT_INT2FP(p->n_scon, 0, INT);
		} else
			p = bcon(0);
	}
		
	return p;
}

/*
 * Prepare for return.
 * There may be implicit casts to other types.
 */
P1ND *
cxret(P1ND *p, P1ND *q)
{
	if (ANYCX(q)) { /* Return complex type */
		p = mkcmplx(p, strmemb(q->n_ap)->stype);
	} else if (q->n_type < STRTY || ISITY(q->n_type)) { /* real or imag */
		p = structref(p, DOT, ISITY(q->n_type) ? imag : real);
		if (p->n_type != q->n_type)
			p = cast(p, q->n_type, 0);
	} else
		cerror("cxred failing type");
	return p;
}

/*
 * either p1 or p2 is complex, so fixup the remaining type accordingly.
 */
P1ND *
cxcast(P1ND *p1, P1ND *p2)
{
	if (ANYCX(p1) && ANYCX(p2)) {
		if (p1->n_type != p2->n_type)
			p2 = mkcmplx(p2, p1->n_type);
	} else if (ANYCX(p1)) {
		p2 = mkcmplx(p2, strmemb(p1->n_ap)->stype);
	} else /* if (ANYCX(p2)) */ {
		p2 = cast(structref(p2, DOT, real), p1->n_type, 0);
	}
	p1nfree(p1);
	return p2;
}

void
cxargfixup(P1ND *a, TWORD dt, struct attr *ap)
{
	P1ND *p;
	TWORD t;

	p = p1alloc();
	*p = *a;
	if (dt == STRTY) {
		/* dest complex */
		t = strmemb(ap)->stype;
		p = mkcmplx(p, t);
	} else {
		/* src complex, not dest */
		p = structref(p, DOT, ISFTY(dt) ? real : imag);
	}
	*a = *p;
	p1nfree(p);
}
#endif
