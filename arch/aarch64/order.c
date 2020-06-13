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
 *  Machine-dependent code-generation strategy (pass 2).
 */

#include <assert.h>
#include <string.h>

#include "pass2.h"

/*
 * Check size of offset in OREG.  Called by oregok() to see if an
 * OREG can be generated.
 */
int
notoff(TWORD ty, int r, CONSZ off, char *cp)
{
	if (cp && cp[0]) return 1;
	if (DEUNSIGN(ty) == INT || ty == UCHAR)
		return !(off < 4096 && off > -4096);
	else
		return !(off < 256 && off > -256);
}

/*
 * Generate instructions for an OREG.  Why is this routine MD?
 * Called by swmatch().
 */
void
offstar(NODE *p, int shape)
{
	NODE *r;

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
		/* usually for arraying indexing: */
		if (r->n_op == LS && r->n_right->n_op == ICON &&
		    getlval(r->n_right) == 2 && p->n_op == PLUS) {
			if (isreg(p->n_left) == 0)
				(void)geninsn(p->n_left, INAREG);
			if (isreg(r->n_left) == 0)
				(void)geninsn(r->n_left, INAREG);
			return;
		}
	}
	(void)geninsn(p, INAREG);
}

/*
 * Unable to convert to OREG (notoff() returned failure).  Output
 * suitable instructions to replace OREG.
 */
void
myormake(NODE *q)
{
        NODE *p, *r;

	if (x2debug)
		printf("myormake(%p)\n", q);

	p = q->n_left;

	/*
	 * This handles failed OREGs conversions, due to the offset
	 * being too large for an OREG.
	 */
	if ((p->n_op == PLUS || p->n_op == MINUS) && p->n_right->n_op == ICON) {
		if (isreg(p->n_left) == 0)
			(void)geninsn(p->n_left, INAREG);
		if (isreg(p->n_right) == 0)
			(void)geninsn(p->n_right, INAREG);
		(void)geninsn(p, INAREG);
	} else if (p->n_op == REG) {
		q->n_op = OREG;
		setlval(q, getlval(p));
		q->n_rval = p->n_rval;
		tfree(p);
	} else if (p->n_op == PLUS && (r = p->n_right)->n_op == LS &&
	    r->n_right->n_op == ICON && getlval(r->n_right) == 2 &&
 	    p->n_left->n_op == REG && r->n_left->n_op == REG) {
		q->n_op = OREG;
		setlval(q, 0);
		q->n_rval = R2PACK(p->n_left->n_rval, r->n_left->n_rval,
				   getlval(r->n_right));
		tfree(p);
	}
}

/*
 * Check to if the UMUL node can be converted into an OREG.
 */
int
shumul(NODE *p, int shape)
{
	/* Turns currently anything into OREG */
	if (shape & SOREG)
		return SROREG;
	return SRNOPE;
}

/*
 * Rewrite operations on binary operators (like +, -, etc...).
 * Called as a result of a failed table lookup.
 *
 * Return nonzero to retry table search on new tree, or zero to fail.
 */
int
setbin(NODE *p)
{
	return 0;

}

/*
 * Rewrite assignment operations.
 * Called as a result of a failed table lookup.
 *
 * Return nonzero to retry table search on new tree, or zero to fail.
 */
int
setasg(NODE *p, int cookie)
{
	return 0;
}

/*
 * Rewrite UMUL operation.
 * Called as a result of a failed table lookup.
 *
 * Return nonzero to retry table search on new tree, or zero to fail.
 */
int
setuni(NODE *p, int cookie)
{
	return 0;
}

/*
 * Special handling of some instruction register allocation.
 *
 * Called as a result of specifying NSPECIAL in the table.
 */
struct rspecial *
nspecial(struct optab *q)
{

	switch (q->op) {
#if !defined(ARM_HAS_FPA) && !defined(ARM_HAS_VFP)
		case UMINUS:
		case SCONV:
			if (q->lshape == SBREG && q->rshape == SAREG) {
				static struct rspecial s[] = {
					{ NLEFT, R16 },
					{ NRES, R0 },
					{ 0 }
				};
				return s;
			} else if (q->lshape == SAREG && q->rshape == SBREG) {
				static struct rspecial s[] = {
					{ NLEFT, R0 },
					{ NRES, R16 },
					{ 0 }
				};
				return s;
			} else if (q->lshape == SAREG && q->rshape == SAREG) {
				static struct rspecial s[] = {
					{ NLEFT, R0 },
					{ NRES, R0 },
					{ 0 }
				};
				return s;
			} else if (q->lshape == SBREG && q->rshape == SBREG) {
				static struct rspecial s[] = {
					{ NLEFT, R16 },
					{ NRES, R16 },
					{ 0 }
				};
				return s;
			}

		case OPLOG:
			if (q->lshape == SBREG) {
				static struct rspecial s[] = {
					{ NLEFT, R16 },
					{ NRIGHT, R18 },
					{ NRES, R0 },
					{ 0 }
				};
				return s;
			} else if (q->lshape == SAREG) {
				static struct rspecial s[] = {
					{ NLEFT, R0 },
					{ NRIGHT, R1 },
					{ NRES, R0 },
					{ 0 }
				};
				return s;
			}
		case PLUS:
		case MINUS:
		case MUL:
#endif
		case MOD:
		case DIV:
			if (q->lshape == SBREG) {
				static struct rspecial s[] = {
					{ NLEFT, R16 },
					{ NRIGHT, R18 },
					{ NRES, R16 },
					{ 0 }
				};
				return s;
			} else if (q->lshape == SAREG) {
				static struct rspecial s[] = {
					{ NLEFT, R0 },
					{ NRIGHT, R1 },
					{ NRES, R0 },
					{ 0 }
				};
				return s;
			}
		case LS:
		case RS:
			if (q->lshape == SBREG) {
				static struct rspecial s[] = {
					{ NLEFT, R16 },
					{ NRIGHT, R2 },
					{ NRES, R16 },
					{ 0 }
				};
				return s;
			} else if (q->lshape == SAREG) {
				static struct rspecial s[] = {
					{ NLEFT, R0 },
					{ NRIGHT, R1 },
					{ NRES, R0 },
					{ 0 }
				};
				return s;
			}
		case STASG:
			{
				static struct rspecial s[] = {
					{ NEVER, R0 },
					{ NRIGHT, R1 },
					{ NEVER, R2 },
					{ 0 } };
				return s;
			}
			break;

		default:
			break;
	}

#ifdef PCC_DEBUG
	comperr("nspecial entry %d [0x%x]: %s", q - table, q->op, q->cstring);
#endif
	return 0; /* XXX gcc */
}

/*
 * Set evaluation order of a binary node ('+','-', '*', '/', etc) if it
 * differs from default.
 */
int
setorder(NODE *p)
{
	return 0;
}

/*
 * Set registers "live" at function calls (like arguments in registers).
 * This is for liveness analysis of registers.
 */
int *
livecall(NODE *p)
{
        static int r[] = { R3, R2, R1, R0, -1 };
	int num = 1;

	if (p->n_op != CALL && p->n_op != FORTCALL && p->n_op != STCALL)
		return &r[4-0];

        for (p = p->n_right; p->n_op == CM; p = p->n_left)
                num += szty(p->n_right->n_type);
        num += szty(p->n_right->n_type);

	num = (num > 4 ? 4 : num);

        return &r[4 - num];
}

/*
 * Signal whether the instruction is acceptable for this target.
 */
int
acceptable(struct optab *op)
{
	return features(op->visit & 0xffff0000);
}
