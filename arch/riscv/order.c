/*	$Id$	*/
/*
 * Copyright (c) 2022, Tim Kelly/Dialectronics.com (gtkelly@). 
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


# include "pass2.h"

#include <string.h>

int canaddr(NODE *);
extern	char *opst[];

/* is it legal to make an OREG or NAME entry which has an
 * offset of off, (from a register of r), if the
 * resulting thing had type t */
int
notoff(TWORD t, int r, CONSZ off, char *cp)
{
	return(0);  /* YES */
}

/*
 * Turn a UMUL-referenced node into OREG.
 * Be careful about register classes, this is a place where classes change.
 */
void
offstar(NODE *p, int shape)
{
	NODE *r;

	if (x2debug)
		printf("offstar(%p)\n", p);

	if (isreg(p))
		return; /* Is already OREG */

	r = p->n_right;
	if( p->n_op == PLUS || p->n_op == MINUS ){
		if( r->n_op == ICON ){
			if (isreg(p->n_left) == 0)
				(void)geninsn(p->n_left, INAREG);
			/* Converted in ormake() */
			return;
		}
		/*
		if (r->n_op == LS && r->n_right->n_op == ICON &&
		    getlval(r->n_right) == 2 && p->n_op == PLUS) {
			if (isreg(p->n_left) == 0)
				(void)geninsn(p->n_left, INAREG);
			if (isreg(r->n_left) == 0)
				(void)geninsn(r->n_left, INAREG);
			return;
		}
		*/
	}
	(void)geninsn(p, INAREG);
}

/*
 * Do the actual conversion of offstar-found OREGs into real OREGs.
 */
void
myormake(NODE *q)
{
	NODE *p, *r;

	if (x2debug) {
		printf("myormake(%p)\n", q);
		fwalk(q, e2print, 0);
	}
	
	p = q->n_left;
	r = p->n_right;

//printf("l->n_op %s, r->n_op %s\n", opst[l->n_op], opst[r->n_op]);

	if (p->n_op == PLUS && r->n_op == LS &&
	    r->n_right->n_op == ICON && getlval(r->n_right) == 2 &&
	    p->n_left->n_op == REG && r->n_left->n_op == REG) {
		q->n_op = OREG;
		setlval(q, 0);
		q->n_rval = R2PACK(p->n_left->n_rval, r->n_left->n_rval, 0);
		tfree(p);
	}
}

/*
 * Shape matches for UMUL.  Cooperates with offstar().
 */
int
shumul(NODE *p, int shape)
{

	if (x2debug)
		printf("shumul %p shape 0x%x %s\n", p, shape,
			shape & SOREG ? "SOREG" : 
			shape & SROREG ? "SROREG" : 
			shape & SRDIR ? "SRDIR" :
			shape & TDOUBLE ? "TDOUBLE" : "Other");

	/* Return in registers */
	if (shape & SOREG)
		return SROREG;
	return SRNOPE;
}

/*
 * Rewrite operations on binary operators (like +, -, etc...).
 * Called as a result of table lookup.
 */
int
setbin(NODE *p)
{

	if (x2debug)
		printf("setbin(%p)\n", p);
	return 0;

}

/* setup for assignment operator */
int
setasg(NODE *p, int cookie)
{
	if (x2debug)
		printf("setasg(%p)\n", p);
	return(0);
}

/* setup for unary operator */
int
setuni(NODE *p, int cookie)
{
	return 0;
}

/*
 * Special handling of some instruction register allocation.
 */
struct rspecial *
nspecial(struct optab *q)
{

	if (x2debug)
		printf("nspecial: op=%d, visit=0x%x: %s", q->op, q->visit, q->cstring);
		
	switch (q->op) {
		case PLUS:
		case MINUS:
		case MUL:
		case DIV:
		case MOD:
		/*
			if (q->lshape == SBREG && 
				(q->ltype & (TDOUBLE|TLDOUBLE|TLONGLONG|TULONGLONG))) {
				static struct rspecial s[] = {
					{ NLEFT, R3R4 },
					{ NRIGHT, R5R6 },
					{ NRES, R3R4 },
					{ 0 }
				};
				return s;
			} else if (q->lshape == SAREG && q->ltype & TFLOAT) {
				static struct rspecial s[] = {
					{ NLEFT, R3 },
					{ NRIGHT, R4 },
					{ NRES, R3 },
					{ 0 }
				};
				return s;
			} else
			*/
			if (q->lshape == SAREG) {
				static struct rspecial s[] = {
					{ NOLEFT, TP },
					{ 0 } };
				return s;
			}
	
			cerror("nspecial mul");
			break;
		
		case ASSIGN:
			if (q->lshape & SNAME) {
				static struct rspecial s[] = {
					{ NEVER, TP },
					{ 0 } };
				return s;
			} else if (q->rshape & SNAME) {
				static struct rspecial s[] = {
					{ NOLEFT, TP },
					{ 0 } };
				return s;
			} else if (q->lshape & SOREG) {
				static struct rspecial s[] = {
					{ NOLEFT, TP },
					{ 0 } };
				return s;
			} else if (q->rshape & SOREG) {
				static struct rspecial s[] = {
					{ NORIGHT, TP },
					{ 0 } };
				return s;
		}		
	
		/* fallthough */

		case UMUL:
		case AND:
		case OR:
		case ER:
			{
				static struct rspecial s[] = {
					{ NOLEFT, TP },
					{ 0 } };
				return s;
			}

		
	default:
		break;
	}

	comperr("nspecial entry %d", q - table);
	return 0; /* XXX gcc */
}

/*
 * Set evaluation order of a binary node if it differs from default.
 */
int
setorder(NODE *p)
{
	return 0; /* nothing differs on riscv */
}

/*
 * set registers in calling conventions live.
 */
int *
livecall(NODE *p)
{
	static int r[] = { A7, A6, A5, A4, A3, A2, A1, A0, -1 };
	int num = 1;

        if (p->n_op != CALL && p->n_op != FORTCALL && p->n_op != STCALL)
                return &r[8-0];

        for (p = p->n_right; p->n_op == CM; p = p->n_left)
                num += szty(p->n_right->n_type);
        num += szty(p->n_right->n_type);

        num = (num > 8 ? 8 : num);

        return &r[8 - num];
}

/*
 * Signal whether the instruction is acceptable for this target.
 */
int
acceptable(struct optab *op)
{
	return 1;
}
