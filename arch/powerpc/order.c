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

# include "pass2.h"

#include <string.h>

int canaddr(NODE *);

/*
 * Check size of offset in OREG.  Called by oregok() to see if an
 * OREG can be generated based on offset from register right now.
 *
 * returns 0 if it can, 1 otherwise.
 */
int
notoff(TWORD t, int r, CONSZ off, char *cp)
{
	if (cp && cp[0])
		return 1; /* cannot convert named constants to OREG */
	return (off >= 32768 || off <= -32769);
}

/*
 * Generate instructions for an OREG.
 * Called by swmatch(). Check if a UMUL can be converted to an OREG later.
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
	/*
	 * Can only convert a tree to an OREG if:
	 * 1) ICON is unnamed constant, and 2) constant is in range.
	 */
	if ((p->n_op == PLUS || p->n_op == MINUS) &&
	    r->n_op == ICON &&
	    notoff(0, 0, getlval(r), r->n_name) == 0 &&
	    isreg(p->n_left) == 0) {
		(void)geninsn(p->n_left, INAREG);
		return;
	}
	(void)geninsn(p, INAREG);
}

/*
 * Do the actual conversion of offstar-found OREGs into real OREGs.
 * We cannot fail here, the checks are already done.
 */
void
myormake(NODE *q)
{
	NODE *p;

	if (x2debug)
		printf("myormake(%p)\n", q);

	/* nothing to do here */
}

/*
 * Shape matches for UMUL.  Cooperates with offstar().
 */
int
shumul(NODE *p, int shape)
{

	if (x2debug)
		printf("shumul(%p)\n", p);

	/* Turns currently anything into OREG on x86 */
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
 * Set evaluation order of a binary node if it differs from default.
 */
int
setorder(NODE *p)
{
	return 0; /* nothing differs on x86 */
}

/*
 * Set registers "live" at function calls (like arguments in registers).
 * This is for liveness analysis of registers.
 */

#if 1
int *
livecall(NODE *p)
{
#if defined(ELFABI)
	static int r[] = { R10, R9, R8, R7, R6, R5, R4, R3, R30, R31, -1 };
#elif defined(MACHOABI)
	static int r[] = { R10, R9, R8, R7, R6, R5, R4, R3, -1 };
#else
#error need argument registers in order.c:livecall() for unknown ABI
#endif

	int num = 1;

        if (p->n_op != CALL && p->n_op != FORTCALL && p->n_op != STCALL)
                return &r[NARGREGS-0];

        for (p = p->n_right; p->n_op == CM; p = p->n_left)
                num += szty(p->n_right->n_type);
        num += szty(p->n_right->n_type);

        num = (num > NARGREGS ? NARGREGS : num);

        return &r[NARGREGS - num];
}

#else

int *
livecall(NODE *p)
{
#if defined(ELFABI)
	static int r[] = { R10, R9, R8, R7, R6, R5, R4, R3, R30, R31, -1 };
#elif defined(MACHOABI)
	static int r[] = { F13, F12, F11, F10, F9, F8, F7, F6, F5, F4, F3, F2, F1, \
				R10, R9, R8, R7, R6, R5, R4, R3, -1 };
#else
#error need argument registers in order.c:livecall() for unknown ABI
#endif

	int num = 1;

        if (p->n_op != CALL && p->n_op != FORTCALL && p->n_op != STCALL)
                return &r[NARGREGS-0];

        for (p = p->n_right; p->n_op == CM; p = p->n_left)
                num += szty(p->n_right->n_type);
        num += szty(p->n_right->n_type);

        num = (num > NARGREGS ? NARGREGS : num);

        return &r[NARGREGS - num];
}
#endif

/*
 * Signal whether the instruction is acceptable for this target.
 */
int
acceptable(struct optab *op)
{
	if ((op->visit & FEATURE_PIC) != 0)
		return (kflag != 0);
	return features(op->visit & 0xffff0000);
}
