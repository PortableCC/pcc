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
 * pass1 code generation for the Zilog Z8001 / Coherent target.
 */

#include "pass1.h"

#ifndef LANG_CXX
#define NODE P1ND
#undef NIL
#define NIL NULL
#define talloc p1alloc
#define tcopy p1tcopy
#define sap sss
#define n_type ptype
#undef n_ap
#define n_ap pss
#undef n_df
#define n_df pdf
#endif

/*
 * Print out assembler segment name.
 * Coherent uses its own segment directives instead of .text/.data/.bss.
 */
void
setseg(int seg, char *name)
{
	switch (seg) {
	case PROG:	name = "\t.shri"; break;	/* code segment */
	case STRNG:	name = "\t.strn"; break;	/* string literals */
	case DATA:
	case LDATA:
	case RDATA:	name = "\t.prvd"; break;	/* private (initialized) data */
	case UDATA:	name = "\t.bssd"; break;	/* BSS (uninitialized) data */
	default:
		cerror("setseg: unknown segment %d", seg);
	}
	printf("%s\n", name);
}

/*
 * Emit alignment directive.
 * Z8001 only has .even/.odd; everything wider than a byte needs .even.
 */
void
defalign(int al)
{
	if (al > ALCHAR)
		printf("\t.even\n");
}

/*
 * Define everything needed to print out some data (or text):
 * segment switch, global visibility, and the symbol label.
 */
void
defloc(struct symtab *sp)
{
	TWORD t;
	char *n;
	int s;

	t = sp->stype;
	s = ISFTN(t) ? PROG :
	    ISCON(cqual(t, sp->squal)) ? RDATA : DATA;

	if (s != lastloc) {
		setseg(s, NULL);
		lastloc = s;
	}

	n = getexname(sp);
	if (sp->sclass == EXTDEF)
		printf("\t.globl\t%s\n", n);

	if (sp->slevel == 0)
		printf("%s:\n", n);
	else
		printf(LABFMT ":\n", sp->soffset);
}

/*
 * End-of-function code.
 * For struct/union return, Coherent uses a hidden first argument:
 * the caller passes a pointer to the result area, and the callee
 * copies the return value there, then returns the pointer in rr0.
 * PCC handles the caller side automatically; here we just need to
 * copy the local struct to the hidden pointer and load rr0 with it.
 */
void
efcode(void)
{
	NODE *p, *q;

	if (cftnsp->stype != STRTY+FTN && cftnsp->stype != UNIONTY+FTN)
		return;

	/*
	 * The hidden pointer arrives as the first argument.
	 * Build: *hidden_ptr = return_value; rr0 = hidden_ptr.
	 */
	q = block(REG, NIL, NIL, INCREF(cftnsp->stype - FTN),
	    cftnsp->sdf, cftnsp->sap);
	slval(q, 0);
	regno(q) = RR0;

	p = buildtree(UMUL, tcopy(q), NIL);
	p = buildtree(ASSIGN, p,
	    block(REG, NIL, NIL, cftnsp->stype - FTN,
	        cftnsp->sdf, cftnsp->sap));
	ecomp(p);

	/* return the pointer in rr0 (already there from the hidden arg) */
}

/*
 * Beginning-of-function code.
 * Z8001 ABI is pure stack-based (no argument registers), so there
 * is nothing to do here unless we are optimising args into temps.
 */
void
bfcode(struct symtab **sp, int cnt)
{
	struct symtab *sp2;
	NODE *n;
	int i;

	if (xtemps == 0)
		return;

	for (i = 0; i < cnt; i++) {
		if (sp[i]->stype == STRTY || sp[i]->stype == UNIONTY ||
		    cisreg(sp[i]->stype) == 0)
			continue;
		sp2 = sp[i];
		n = tempnode(0, sp[i]->stype, sp[i]->sdf, sp[i]->sap);
		n = buildtree(ASSIGN, n, nametree(sp2));
		sp[i]->soffset = regno(n->n_left);
		sp[i]->sflags |= STNODE;
		ecomp(n);
	}
}

/*
 * Called just before compiler exits.
 */
void
ejobcode(int flag)
{
}

/*
 * Called at the very beginning of compilation.
 * Set up assembler type names for Coherent's assembler syntax:
 *   .byte  - 8-bit
 *   .word  - 16-bit (int and short are both 16-bit on Z8001)
 *   .long  - 32-bit
 */
void
bjobcode(void)
{
	extern char *asspace;

	astypnames[SHORT]   = astypnames[USHORT]   = "\t.word";
	astypnames[INT]     = astypnames[UNSIGNED]  = "\t.word";
	astypnames[LONG]    = astypnames[ULONG]     = "\t.long";
	asspace = "\t.blkb";
}

/*
 * Emit a string literal.
 * Coherent's assembler has no .ascii directive, so emit the bytes one per
 * line with .byte (decimal), matching the native Coherent compiler output,
 * terminated by a NUL byte.  The string lives in the .strn segment.
 */
void
instring(struct symtab *sp)
{
	char *s;
	int val;
	TWORD t;

	/* Switch to the string segment (.strn) */
	locctr(STRNG, sp);

	/* Emit the label for this string literal */
	if (sp->slevel == 0)
		printf("%s:\n", getexname(sp));
	else
		printf(LABFMT ":\n", sp->soffset);

	t = BTYPE(sp->stype);
	s = sp->sname;
	if (t == CHAR || t == UCHAR) {
		while (*s) {
			if (*s == '\\')
				val = (int)esccon(&s);
			else
				val = *s++;
			printf("\t.byte\t%d\n", val & 0377);
		}
		printf("\t.byte\t0\n");
	} else
		cerror("instring: wide strings not supported");
}

/*
 * Prepare a function call: wrap each argument in a FUNARG node
 * so pass2 knows to push them onto the stack.
 */
NODE *
funcode(NODE *p)
{
	NODE *r, *l;

	for (r = p->n_right; r->n_op == CM; r = r->n_left) {
		if (r->n_right->n_op != STARG)
			r->n_right = block(FUNARG, r->n_right, NIL,
			    r->n_right->n_type, r->n_right->n_df,
			    r->n_right->n_ap);
	}
	if (r->n_op != STARG) {
		l = talloc();
		*l = *r;
		r->n_op = FUNARG;
		r->n_left = l;
		r->n_type = l->n_type;
	}
	return p;
}

/* Fix up type of a bit-field. */
void
fldty(struct symtab *p)
{
}

/* Use PCC's default switch generation. */
int
mygenswitch(int num, TWORD type, struct swents **p, int n)
{
	return 0;
}

NODE *
builtin_cfa(const struct bitable *bt, NODE *a)
{
	uerror("__builtin_cfa not supported");
	return bcon(0);
}

NODE *
builtin_return_address(const struct bitable *bt, NODE *a)
{
	uerror("__builtin_return_address not supported");
	return bcon(0);
}

NODE *
builtin_frame_address(const struct bitable *bt, NODE *a)
{
	uerror("__builtin_frame_address not supported");
	return bcon(0);
}
