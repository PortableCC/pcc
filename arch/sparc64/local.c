/*	$Id$	*/

/*
 * Copyright (c) 2008 David Crawshaw <david@zentus.com>
 * 
 * Permission to use, copy, modify, and/or distribute this software for any
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

#include "pass1.h"

#ifdef LANG_CXX
#else
#define	fwalk p1fwalk
#define	nfree p1nfree
#undef NIL
#define NIL NULL
#define NODE P1ND
#define sap sss
#define n_type ptype
#define n_qual pqual
#undef  n_df
#define n_df pdf
#undef  n_ap
#define n_ap pss
#endif


NODE *
clocal(NODE *p)
{
	struct symtab *sp;
	int op;
	NODE *r, *l;

	op = p->n_op;
	sp = p->n_sp;
	l  = p->n_left;
	r  = p->n_right;

#ifdef PCC_DEBUG
	if (xdebug) {
		printf("clocal in: %p, %s\n", p, copst(op));
		fwalk(p, eprint, 0);
	}
#endif

	switch (op) {

	case NAME:
		if (sp->sclass == PARAM || sp->sclass == AUTO) {
			/*
			 * Use a fake structure reference to
			 * write out frame pointer offsets.
			 */
			l = block(REG, NIL, NIL, PTR+STRTY, 0, 0);
			slval(l, 0);
			l->n_rval = FP;
			r = p;
			p = stref(block(STREF, l, r, 0, 0, 0));
		}
		break;
	case PCONV: /* Remove what PCONVs we can. */
		if (l->n_op == SCONV)
			break;

		if (l->n_op == ICON || (ISPTR(p->n_type) && ISPTR(l->n_type))) {
			l->n_type = p->n_type;
			l->n_qual = p->n_qual;
			l->n_df = p->n_df;
			l->n_ap = p->n_ap;
			nfree(p);
			p = l;
		}
		break;

	case SCONV:
        /* Remove redundant conversions. */
		if ((p->n_type & TMASK) == 0 && (l->n_type & TMASK) == 0 &&
		    tsize(p->n_type, p->n_df, p->n_ap) ==
		    tsize(l->n_type, l->n_df, l->n_ap) &&
		    p->n_type != FLOAT && p->n_type != DOUBLE &&
		    l->n_type != FLOAT && l->n_type != DOUBLE &&
		    l->n_type != DOUBLE && p->n_type != LDOUBLE) {
			if (l->n_op == NAME || l->n_op == UMUL ||
			    l->n_op == TEMP) {
				l->n_type = p->n_type;
				nfree(p);
				p = l;
				break;
			}
		}

        /* Convert floating point to int before to char or short. */
        if ((l->n_type == FLOAT || l->n_type == DOUBLE || l->n_type == LDOUBLE)
            && (DEUNSIGN(p->n_type) == CHAR || DEUNSIGN(p->n_type) == SHORT)) {
            p = block(SCONV, p, NIL, p->n_type, p->n_df, p->n_ap);
            p->n_left->n_type = INT;
            break;
        }

        /* Transform constants now. */
		if (l->n_op != ICON)
			break;

		if (ISPTR(p->n_type)) {
			l->n_type = p->n_type;
			nfree(p);
			p = l;
			break;
		}

		switch (p->n_type) {
		case BOOL:      slval(l, glval(l) != 0); break;
		case CHAR:      slval(l, (char)glval(l)); break;
		case UCHAR:     slval(l, glval(l) & 0377); break;
		case SHORT:     slval(l, (short)glval(l)); break;
		case USHORT:    slval(l, glval(l) & 0177777); break;
		case UNSIGNED:  slval(l, glval(l) & 0xffffffff); break;
		case INT:       slval(l, (int)glval(l)); break;
		case ULONG:
		case ULONGLONG: break;
		case LONG:
		case LONGLONG:	slval(l,  (long long)glval(l)); break;
		case VOID:
			break;
		default:
			cerror("sconv type unknown %d", p->n_type);
		}

		l->n_type = p->n_type;
		nfree(p);
		p = l;
		break;

	case FORCE:
		/* Put attached value into the return register. */
		p->n_op = ASSIGN;
		p->n_right = p->n_left;
		p->n_left = block(REG, NIL, NIL, p->n_type, 0, 0);
		p->n_left->n_rval = RETREG_PRE(p->n_type);
		break;
	}

#ifdef PCC_DEBUG
	if (xdebug) {
		printf("clocal out: %p, %s\n", p, copst(op));
		fwalk(p, eprint, 0);
	}
#endif

	return p;
}

void
myp2tree(NODE *p)
{
	struct symtab *sp;

	if (p->n_op != FCON)
		return;

	sp = tmpalloc(sizeof(struct symtab));
	sp->sclass = STATIC;
	sp->slevel = 1;
	sp->soffset = getlab();
	sp->sflags = 0;
	sp->stype = p->n_type;
	sp->squal = (CON >> TSHIFT);

	defloc(sp);
	ninval(0, tsize(p->n_type, p->n_df, p->n_ap), p);

	p->n_op = NAME;
	slval(p, 0);
	p->n_sp = sp;
}

int
andable(NODE *p)
{
	return 1;
}

int
cisreg(TWORD t)
{
	/* SPARCv9 registers are all 64-bits wide. */
	return 1;
}

void
spalloc(NODE *t, NODE *p, OFFSZ off)
{
	cerror("spalloc");
}

int
ninval(CONSZ off, int fsz, NODE *p)
{
	return 0;
}

char *
exname(char *p)
{
	return p ? p : "";
}

TWORD
ctype(TWORD type)
{
	switch (BTYPE(type)) {
	case LONGLONG:
		MODTYPE(type,LONG);
		break;
	case ULONGLONG:
		MODTYPE(type,ULONG);

	}
	return type;
}

void
calldec(NODE *p, NODE *q) 
{
}

void
extdec(struct symtab *q)
{
}

void
defzero(struct symtab *sp)
{
	int off;
	char *name;

	name = getexname(sp);
	off = tsize(sp->stype, sp->sdf, sp->sap);
	SETOFF(off,SZCHAR);
	off /= SZCHAR;

	if (sp->sclass == STATIC)
		printf("\t.local %s\n", name);
	if (sp->slevel == 0)
		printf("\t.comm %s,%d\n", name, off);
	else
		printf("\t.comm " LABFMT ",%d\n", sp->soffset, off);
}

int
mypragma(char *str)
{
	return 0;
}

void
fixdef(struct symtab *sp)
{
}

void
pass1_lastchance(struct interpass *ip)
{
}

