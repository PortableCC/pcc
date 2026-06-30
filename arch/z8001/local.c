/*
 * Copyright (c) 2025 Michal Pleban.
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
 * pass1 local routines for the Zilog Z8001 / Coherent target.
 */

#include "pass1.h"

#ifndef LANG_CXX
#define NODE P1ND
#undef NIL
#define NIL NULL
#define fwalk p1fwalk
#define nfree p1nfree
#define talloc p1alloc
#define n_type ptype
#undef n_df
#define n_df pdf
#undef n_ap
#define n_ap pss
#define sap sss
#endif

#include <string.h>

/*
 * clocal: perform local pass-1 transformations.
 *
 * The main job here is to rewrite NAME nodes for AUTO and PARAM variables
 * into OREG nodes relative to the frame pointer (R13).
 *
 * Frame pointer (R13) model:
 *   - R13 points to the entry SP (just below the return address)
 *   - Locals:  negative OREG offsets from R13  (AUTOINIT=0)
 *   - Params:  positive OREG offsets from R13  (ARGINIT=32 bits = 4 bytes)
 */
NODE *
clocal(NODE *p)
{
	struct symtab *q;
	NODE *l;
	int o;
	TWORD m;

	switch (o = p->n_op) {

	case NAME:
		if ((q = p->n_sp) == NULL)
			return p;

		switch (q->sclass) {
		case AUTO:
		case REGISTER:
			/*
			 * Convert auto/register to frame-relative OREG.
			 * soffset is in bits; divide by SZCHAR to get bytes.
			 */
			p->n_op = OREG;
			slval(p, q->soffset / SZCHAR);
			p->n_rval = FPREG;
			break;

		case PARAM:
			/*
			 * Parameters arrive above the frame pointer.
			 * ARGINIT = 32 bits = 4 bytes above R13 for the first arg.
			 */
			p->n_op = OREG;
			slval(p, q->soffset / SZCHAR);
			p->n_rval = FPREG;
			break;

		case STATIC:
			/* Static local: use slevel to distinguish from globals */
			if (q->slevel == 0)
				break;
			slval(p, 0);
			break;

		case EXTERN:
		case EXTDEF:
			/* External: leave as NAME (will become a symbol reference) */
			break;
		}
		break;

	case PCONV:
		/*
		 * Pointer conversion: if the source is already pointer-sized
		 * (32-bit pair), this is a no-op.
		 */
		l = p->n_left;
		m = l->n_type;
		if (ISPTR(m) || m == LONG || m == ULONG) {
			/* Already 32-bit; just change the type label */
			l->n_type = p->n_type;
			l->n_df = p->n_df;
			l->n_ap = p->n_ap;
			nfree(p);
			return l;
		}
		break;

	case SCONV:
		/*
		 * Scalar conversion: try to eliminate no-ops.
		 */
		l = p->n_left;
		m = l->n_type;

		/* int/short <-> int/short in same class: no-op */
		if ((m == INT || m == UNSIGNED || m == SHORT || m == USHORT) &&
		    (p->n_type == INT || p->n_type == UNSIGNED ||
		     p->n_type == SHORT || p->n_type == USHORT)) {
			l->n_type = p->n_type;
			nfree(p);
			return l;
		}

		/* long <-> long in same class: no-op */
		if ((m == LONG || m == ULONG) &&
		    (p->n_type == LONG || p->n_type == ULONG)) {
			l->n_type = p->n_type;
			nfree(p);
			return l;
		}
		break;

	case FORCE:
		/*
		 * FORCE ensures the return value is in the correct register.
		 * On Z8001: int/short in R1, long/ptr in RR0.
		 */
		p->n_op = ASSIGN;
		p->n_right = p->n_left;
		p->n_left = block(REG, NIL, NIL, p->n_type, p->n_df, p->n_ap);
		slval(p->n_left, 0);
		regno(p->n_left) = RETREG(p->n_type);
		break;
	}

	return p;
}

/*
 * exname: return the external (mangled) name of a symbol.
 *
 * Coherent uses a TRAILING underscore convention: "printf" → "printf_".
 * This is the opposite of the leading-underscore convention used on many
 * other Unix systems.
 */
char *
exname(char *p)
{
#define NCHNAM	256
	static char text[NCHNAM + 1];
	int i;

	if (p == NULL)
		return "";

	for (i = 0; *p && i < NCHNAM - 1; ++i)
		text[i] = *p++;
	text[i++] = '_';	/* Coherent uses a trailing underscore */
	text[i] = '\0';
	text[NCHNAM] = '\0';	/* truncate */

	return text;
}

/*
 * cisreg: return 1 if the type can live in a register.
 *
 * On Z8001: char, short, int fit in a word register (SAREG).
 * long, float, and pointers fit in a pair register (SBREG).
 * double and long long require 4 word registers — not supported.
 */
int
cisreg(TWORD t)
{
	switch (t) {
	case CHAR:  case UCHAR:
	case SHORT: case USHORT:
	case INT:   case UNSIGNED:
	case LONG:  case ULONG:
	case FLOAT:
		return 1;
	default:
		return ISPTR(t) ? 1 : 0;
	}
}

/*
 * ninval: emit an initializer for a data item.
 * Returns 1 if handled here, 0 to let the generic code handle it.
 */
int
ninval(CONSZ off, int fsz, NODE *p)
{
	return 0;	/* let generic inval() handle all types */
}

/*
 * myp2tree: convert FCON (floating-point constant) nodes to named static
 * symbols in the data segment, so pass2 can handle them as memory references.
 */
void
myp2tree(NODE *p)
{
	struct symtab *sp;

	if (p->n_op != FCON)
		return;

	sp = isinlining ? permalloc(sizeof(struct symtab))
	                : tmpalloc(sizeof(struct symtab));
	sp->sclass  = STATIC;
	sp->sap     = 0;
	sp->slevel  = 1;		/* fake numeric label */
	sp->soffset = getlab();
	sp->sflags  = 0;
	sp->stype   = p->n_type;
	sp->squal   = (CON >> TSHIFT);
	sp->sname   = NULL;

	locctr(DATA, sp);
	defloc(sp);
	inval(0, tsize(sp->stype, sp->sdf, sp->sap), p);

	p->n_op = NAME;
	slval(p, 0);
	p->n_sp = sp;
}

/*
 * spalloc: allocate stack space for a struct return value.
 * The hidden pointer argument is passed in RR0 (first argument register).
 */
void
spalloc(NODE *t, NODE *p, OFFSZ off)
{
	NODE *sp;

	if (off & (ALSTACK - 1))
		off += ALSTACK - (off & (ALSTACK - 1));

	p->n_left->n_type = INCREF(p->n_left->n_type);
	sp = block(REG, NIL, NIL, INCREF(p->n_type), t->n_df, t->n_ap);
	slval(sp, 0);
	regno(sp) = RR0;
	p = buildtree(ASSIGN, t, sp);
	ecomp(p);
}

/*
 * Map a type to its canonical machine type.
 * Z8001 has no 16-bit/64-bit register types distinct from int/long, and
 * no long double, so collapse those onto the supported types.
 */
TWORD
ctype(TWORD type)
{
	switch (BTYPE(type)) {
	case SHORT:
		MODTYPE(type, INT);
		break;
	case USHORT:
		MODTYPE(type, UNSIGNED);
		break;
	case LDOUBLE:
		MODTYPE(type, DOUBLE);
		break;
	/* XXX no 64-bit integer support yet */
	case LONGLONG:
		MODTYPE(type, LONG);
		break;
	case ULONGLONG:
		MODTYPE(type, ULONG);
		break;
	}
	return type;
}

/* Every name can have its address taken. */
int
andable(NODE *p)
{
	return 1;
}

/* No target-specific pragmas. */
int
mypragma(char *str)
{
	return 0;
}

/* No fixup needed when a symbol is defined. */
void
fixdef(struct symtab *sp)
{
}

/* No last-minute pass1 rewriting. */
void
pass1_lastchance(struct interpass *ip)
{
}

/* Function declaration hook - nothing to emit. */
void
calldec(NODE *p, NODE *q)
{
}

/* External declaration hook - nothing to emit. */
void
extdec(struct symtab *q)
{
}

/*
 * Emit an uninitialized (common) data definition.
 * Coherent's assembler uses ".comm <name> <size>" (whitespace separated).
 */
void
defzero(struct symtab *sp)
{
	int off;
	char *name;

	name = getexname(sp);
	off = (int)tsize(sp->stype, sp->sdf, sp->sap);
	SETOFF(off, SZCHAR);
	off /= SZCHAR;

	if (sp->slevel == 0)
		printf("\t.comm\t%s\t%d\n", name, off);
	else
		printf("\t.comm\t" LABFMT "\t%d\n", sp->soffset, off);
}

