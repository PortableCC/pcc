/*
 * Copyright (c) 2026 Michal Pleban.
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
 * pass2 instruction ordering for the Zilog Z8001 / Coherent target.
 *
 * On the Z8001, all pointer dereferences use a 32-bit segmented pair
 * register (SBREG class) as the base address.  Frame-relative access
 * (autos, params) uses r13 (a plain word register) with the implicit DS.
 *
 * An OREG can be formed from:
 *   - A pair register (rr0..rr10): pointer-based indirect access
 *   - r13 (FPREG): frame-relative access (already an OREG from clocal)
 *   - PLUS/MINUS of a pair register and a small integer constant
 */

#include "pass2.h"
#include <string.h>

int canaddr(NODE *);

/*
 * notoff: can we form an OREG with this offset?
 * Z8001 indirect addressing supports a 16-bit signed displacement,
 * so all offsets that fit in 16 bits are fine.
 */
int
notoff(TWORD t, int r, CONSZ off, char *cp)
{
	/* All offsets fit in 16 bits for our purposes */
	return off > 32767 || off < -32768;
}

/*
 * offstar: prepare the argument of a UMUL (pointer dereference) so that
 * it can be converted into an OREG by myormake().
 *
 * For Z8001, valid OREG bases are:
 *   - A pair register (SBREG): evaluate to INBREG
 *   - r13 (word reg): already handled as OREG by clocal
 *   - PLUS(pair_reg, ICON): evaluate left to INBREG
 */
void
offstar(NODE *p, int shape)
{
	if (x2debug)
		printf("offstar(%p)\n", p);

	if (isreg(p))
		return;

	if (p->n_op == PLUS || p->n_op == MINUS) {
		if (p->n_right->n_op == ICON) {
			/* base + constant offset: evaluate base into a pair reg */
			if (!isreg(p->n_left))
				(void)geninsn(p->n_left, INBREG);
			return;
		}
	}

	/* General case: evaluate p into a pair register */
	(void)geninsn(p, INBREG);
}

/*
 * myormake: convert an already-evaluated UMUL child into an OREG.
 *
 * Called after offstar() has arranged the child.  We look for the
 * patterns that offstar() prepared.
 */
void
myormake(NODE *p)
{
	NODE *q = p->n_left;

	if (x2debug) {
		printf("myormake(%p)\n", p);
		fwalk(p, e2print, 0);
	}

	if (q->n_op == OREG)
		return;

	if ((q->n_op == PLUS || q->n_op == MINUS) &&
	    q->n_right->n_op == ICON &&
	    q->n_left->n_op == REG) {
		/* PLUS/MINUS(reg, icon) → OREG with offset */
		CONSZ off = getlval(q->n_right);
		if (q->n_op == MINUS)
			off = -off;
		p->n_op = OREG;
		setlval(p, off);
		p->n_rval = regno(q->n_left);
		tfree(q);
		return;
	}

	if (q->n_op == REG) {
		/* bare register → OREG with zero offset */
		p->n_op = OREG;
		setlval(p, 0);
		p->n_rval = regno(q);
		tfree(q);
		return;
	}
}

/*
 * shumul: can a UMUL node be represented as a memory shape?
 *
 * Returns SROREG (will call offstar/myormake) or SRNOPE.
 */
int
shumul(NODE *p, int shape)
{
	if (x2debug)
		printf("shumul(%p)\n", p);

	if (p->n_op == NAME && (shape & STARNM))
		return SRDIR;

	if (shape & SOREG)
		return SROREG;

	return SRNOPE;
}

/*
 * setbin, setasg, setuni, setorder: instruction ordering hooks.
 * For Z8001 we rely entirely on the table and don't need special handling.
 */
int
setbin(NODE *p)
{
	return 0;
}

int
setasg(NODE *p, int cookie)
{
	return 0;
}

int
setuni(NODE *p, int cookie)
{
	return 0;
}

int
setorder(NODE *p)
{
	return 0;
}

/*
 * livecall: return registers that are live at a call instruction.
 *
 * On Z8001 with pure stack calling convention, no argument registers
 * are live at the call site; the callee reads everything from the stack.
 */
int *
livecall(NODE *p)
{
	static int r[] = { -1 };
	return r;
}

/*
 * acceptable: is this instruction acceptable for our target?
 *
 * Z8001 uses a simple flat instruction set with no variants that need
 * filtering, so all table entries are acceptable.
 */
int
acceptable(struct optab *op)
{
	return 1;
}
