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
 * pass1 code generation for the Zilog Z8001 / Coherent target.
 */

#include "pass1.h"

#include <string.h>
#include <stdlib.h>
#include <unistd.h>	/* dup, dup2, close, fileno (output-capture peephole) */

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
 * Struct/union return, hidden-pointer ABI (invented here: the Coherent
 * K&R compiler has no struct-by-value at all, so this only has to be
 * self-consistent).  The caller reserves a buffer in its frame and
 * pushes its address LAST, so it sits at the first-argument slot
 * (+ARGINIT); all declared arguments are one pointer higher (bfcode
 * shifts them).  On "return expr", clocal(FORCE) puts &expr in rr0;
 * efcode copies *rr0 into the caller's buffer and returns the buffer
 * address in rr0.
 */
int strtemp;	/* pass1 temp holding the incoming hidden pointer */

void
efcode(void)
{
	extern NODE *cftnod;
	NODE *p, *q;
	TWORD t;
	int i;

	if (cftnsp->stype != STRTY+FTN && cftnsp->stype != UNIONTY+FTN)
		return;
	t = DECREF(cftnsp->stype);

	if (cftnod != NIL) {
		/* *(hidden pointer) = *(rr0): copy the returned value out.
		 * If the function never executed "return expr" (cftnod
		 * unset), rr0 is garbage - skip the copy.
		 *
		 * rr0 must first move into a temp: rr0 cannot be an
		 * indirect base on the Z8001, and a literal REG rr0 node
		 * as the STASG source would end up as "ldirb ...,(rr0)". */
		q = block(REG, NIL, NIL, INCREF(t),
		    cftnsp->sdf, cftnsp->sap);
		slval(q, 0);
		regno(q) = RR0;
		p = tempnode(0, INCREF(t), cftnsp->sdf, cftnsp->sap);
		i = regno(p);
		ecomp(buildtree(ASSIGN, p, q));

		q = tempnode(i, INCREF(t), cftnsp->sdf, cftnsp->sap);
		q = buildtree(UMUL, q, NIL);
		p = tempnode(strtemp, INCREF(t), cftnsp->sdf, cftnsp->sap);
		p = buildtree(UMUL, p, NIL);
		ecomp(buildtree(ASSIGN, p, q));
	}

	/* return the caller's buffer address in rr0 */
	p = block(REG, NIL, NIL, INCREF(t), cftnsp->sdf, cftnsp->sap);
	slval(p, 0);
	regno(p) = RR0;
	q = tempnode(strtemp, INCREF(t), cftnsp->sdf, cftnsp->sap);
	ecomp(buildtree(ASSIGN, p, q));
}

/*
 * Beginning-of-function code.
 * Z8001 ABI is pure stack-based (no argument registers), so apart from
 * the struct-return hidden pointer there is nothing to do here unless
 * we are optimising args into temps.
 */
void
bfcode(struct symtab **sp, int cnt)
{
	struct symtab *sp2;
	NODE *n, *p;
	int i;

	if (cftnsp->stype == STRTY+FTN || cftnsp->stype == UNIONTY+FTN) {
		/*
		 * The hidden pointer occupies the first-argument slot, so
		 * every declared argument really sits one pointer (32 bits)
		 * higher than pass 1 assigned it.  Fix the offsets, then
		 * save the hidden pointer in a temp for efcode().
		 */
		for (i = 0; i < cnt; i++)
			sp[i]->soffset += SZPOINT(CHAR);
		n = tempnode(0, INCREF(CHAR), 0, 0);
		p = block(OREG, NIL, NIL, INCREF(CHAR), 0, 0);
		slval(p, ARGINIT/SZCHAR);
		regno(p) = FPREG;
		strtemp = regno(n);
		ecomp(buildtree(ASSIGN, n, p));
	}

	/*
	 * A char argument is pushed as a word; on big-endian its value
	 * lives in the LOW byte of that slot, one byte past the slot
	 * start.  Adjust the offset once here so every access - including
	 * &param - sees the true byte address (clocal used to add the
	 * correction per-access, which the stref/&-able rewrite can't).
	 */
	for (i = 0; i < cnt; i++) {
		TWORD t = sp[i]->stype;

		if (t == CHAR || t == UCHAR || t == BOOL)
			sp[i]->soffset += SZINT - SZCHAR;
	}

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
 *
 * NB: programs that print floating point must be linked with
 * "ld -u _dtoa_" so the real _dtefg printf formatter (libc
 * crt/dtefg.o) is pulled in instead of the "No floating point!"
 * dummy (gen/sdtoa.o).  That is a link-time policy - the native
 * "cc -f" flag - and deliberately NOT emitted by the compiler:
 * it would drag the formatter into every FP program whether or
 * not it prints, and would tie generated code to one libc layout.
 */
/*
 * Post-emit stack-cleanup peephole.
 *
 * A call's caller-cleanup "inc r15,$K" immediately followed by the next
 * call's first argument push of exactly K bytes is a wasteful SP round-trip:
 * the inc frees K bytes and the push re-allocates the same K, so the pair
 * collapses to a single in-place store - drop the inc and turn that push
 * into a store to (rr14).  SP is unchanged, the value lands in the same slot,
 * and any further pushes proceed normally from the unchanged SP:
 *
 *	inc r15,$2 ; push (rr14),x ; push (rr14),y
 *   -> store (rr14),x ; push (rr14),y
 *
 * The store re-provides the argument from the (callee-saved, preserved)
 * register, so this stays correct even if the first callee overwrote its own
 * argument slot; only a *register* push source qualifies (a memory/immediate
 * push has no legal mem<-mem / mem<-imm store form).  A label between the two
 * lines is a separate line, so the required adjacency naturally respects
 * basic-block boundaries (a jump target between them blocks the collapse).
 *
 * All pass-2 assembly is printf'd straight to stdout with no instruction or
 * line buffer to peephole over, so the whole compilation's stdout is captured
 * to a temp file between bjobcode() and ejobcode() (which bracket every
 * emission in the combined ccom) and streamed back through the line filter.
 * z8001-only - no shared MIP changes.  If capture cannot be set up the output
 * is left direct (no peephole), never wrong.
 */
static int argcse_savefd = -1;
static FILE *argcse_cap;

/* SRC (the text after "(rr14),") a plain word/long register? */
static int
argcse_isreg(const char *p, int longp)
{
	if (longp) {
		if (p[0] != 'r' || p[1] != 'r')
			return 0;
		p += 2;
	} else {
		if (p[0] != 'r')
			return 0;
		p += 1;
	}
	if (*p < '0' || *p > '9')
		return 0;
	while (*p >= '0' && *p <= '9')
		p++;
	return *p == '\0';
}

static void
argcse_filter(FILE *in, FILE *out)
{
	char prev[4096], cur[4096];
	int haveprev = 0, prevk = 0;

	while (fgets(cur, sizeof(cur), in) != NULL) {
		char *e;
		const char *src;
		int longp, matched = 0;

		/* strip trailing CR/LF; a single \n is re-added on output */
		e = cur + strlen(cur);
		while (e > cur && (e[-1] == '\n' || e[-1] == '\r'))
			*--e = '\0';

		if (haveprev) {
			src = NULL;
			longp = 0;
			if (strncmp(cur, "\tpushl\t(rr14),", 14) == 0) {
				src = cur + 14;
				longp = 1;
			} else if (strncmp(cur, "\tpush\t(rr14),", 13) == 0) {
				src = cur + 13;
				longp = 0;
			}
			if (src != NULL && prevk == (longp ? 4 : 2) &&
			    argcse_isreg(src, longp)) {
				fprintf(out, "\t%s\t(rr14),%s\n",
				    longp ? "ldl" : "ld", src);
				haveprev = 0;		/* both lines consumed */
				matched = 1;
			}
		}
		if (matched)
			continue;

		if (haveprev)
			fprintf(out, "%s\n", prev);

		if (strncmp(cur, "\tinc\tr15,$", 10) == 0 ||
		    strncmp(cur, "\tadd\tr15,$", 10) == 0) {
			prevk = atoi(cur + 10);
			strcpy(prev, cur);
			haveprev = 1;
		} else {
			fprintf(out, "%s\n", cur);
			haveprev = 0;
		}
	}
	if (haveprev)
		fprintf(out, "%s\n", prev);
}

void
ejobcode(int flag)
{
	if (argcse_cap != NULL) {
		fflush(stdout);
		dup2(argcse_savefd, fileno(stdout));	/* restore real stdout */
		close(argcse_savefd);
		argcse_savefd = -1;
		rewind(argcse_cap);
		argcse_filter(argcse_cap, stdout);	/* peephole -> real out */
		fclose(argcse_cap);
		argcse_cap = NULL;
		fflush(stdout);
	}
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
	extern int clregs[];

	astypnames[SHORT]   = astypnames[USHORT]   = "\t.word";
	astypnames[INT]     = astypnames[UNSIGNED]  = "\t.word";
	astypnames[LONG]    = astypnames[ULONG]     = "\t.long";
	asspace = "\t.blkb";

	/*
	 * RR0 (color 0 of class B) is the long/ptr return register, so it must
	 * stay a valid color so the MIP call-result coalescing move (regs.c
	 * moveadd(rv, RETREG)) can be mapped by colfind.  But the Z8000 cannot
	 * use RR0 as an indirect base "(rr0)", so we must never *allocate* it.
	 * Clear its bit from class B's selectable-color mask: the allocator
	 * then picks only rr2..rr10, while color2reg/regK still know RR0.
	 * (COLORMAP CLASSB is set to 5 accordingly.)
	 *
	 * clregs is indexed by class-1; class B is index 1 (CLASSB is a pass2
	 * macro not visible in this pass1 file, so the literal 1 is used).
	 */
	clregs[1] &= ~1;		/* class B: drop color 0 (== RR0) */

	/*
	 * Redirect all pass-2 assembly output through a temp file so ejobcode()
	 * can run the stack-cleanup peephole over the emitted text.  bjobcode
	 * emits no assembly itself, so capturing from here is complete.  On any
	 * failure leave stdout untouched (output stays direct, no peephole).
	 */
	fflush(stdout);
	argcse_savefd = dup(fileno(stdout));
	argcse_cap = tmpfile();
	if (argcse_savefd >= 0 && argcse_cap != NULL) {
		dup2(fileno(argcse_cap), fileno(stdout));
	} else {
		if (argcse_savefd >= 0) {
			close(argcse_savefd);
			argcse_savefd = -1;
		}
		if (argcse_cap != NULL) {
			fclose(argcse_cap);
			argcse_cap = NULL;
		}
	}
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
 * Default integer argument promotion: char/short arguments occupy a
 * full word slot and a K&R callee ("int fd;") reads the whole word,
 * but a class-D char value only defines the LOW byte of its containing
 * word, so a bare word push would carry a garbage high byte.  Widen to
 * int/unsigned so the push is a properly extended word, exactly like
 * the native compiler.  (The front end only promotes FLOAT to DOUBLE
 * for unprototyped calls, in params.c oldarg(); the integer promotions
 * land here.)
 */
static NODE *
argwiden(NODE *q)
{
	TWORD t = q->n_type;

	/* short/ushort are already full 16-bit words on this target */
	if (t == CHAR)
		q = block(SCONV, q, NIL, INT, 0, 0);
	else if (t == UCHAR)
		q = block(SCONV, q, NIL, UNSIGNED, 0, 0);
	return q;
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
		if (r->n_right->n_op != STARG) {
			l = argwiden(r->n_right);
			r->n_right = block(FUNARG, l, NIL,
			    l->n_type, l->n_df, l->n_ap);
		}
	}
	if (r->n_op != STARG) {
		l = talloc();
		*l = *r;
		r->n_op = FUNARG;
		r->n_left = argwiden(l);
		r->n_type = r->n_left->n_type;
	}
	return p;
}

/* Fix up type of a bit-field. */
void
fldty(struct symtab *p)
{
}

/*
 * Sparse-switch dispatch via the Z8000 cpir block-search idiom.
 *
 * Native Coherent cc dispatches a scattered set of case values (typically
 * ASCII character codes) not with a compare ladder but with a single cpir
 * that linearly searches a compact .word table of the case values, then
 * indexes a parallel .long table of target addresses and jumps through it:
 *
 *	ld	rC, $N
 *	ldl	rrP, $LTAB
 *	cpir	rX, (rrP), rC, eq	; rX = switch value
 *	jr	ne, DEFAULT
 *	sub	r(P+1), $LTAB		; r(P+1) = 2*(idx+1)
 *	add	r(P+1), r(P+1)		; = 4*(idx+1)
 *	ldl	rrP, LTAB+(2N-4)(r(P+1))
 *	jp	un, (rrP)
 * LTAB: .word v0..v(N-1) ; .long t0..t(N-1)
 *
 * The search is one instruction regardless of N, so eight instructions
 * dispatch any number of cases - a large win over the 2-per-case ladder once
 * N grows.  The idiom cannot be built from pass1 trees (there is no C-level
 * "search", and cpir's fixed register roles need pass2 allocation), so we
 * only MARK the switch here in comment interpasses carrying the case table;
 * myreader() rewrites the marks into a GOTO(SWDISP(value)) node plus the data
 * table, once pass2 can reserve the scratch pair + count register.
 *
 * Eligibility: a word-sized (int/unsigned) switch value - cpir compares
 * 16-bit words, so a long switch cannot use it - and a SIZE gate.  The
 * dispatch is ~28 bytes plus 4 bytes per case (a .word value + a .word
 * target offset); a compare ladder is ~6 bytes per case (cp $imm; jr) with
 * no tables.  So cpir is only smaller for the larger switches; use it just
 * when 28 + 4N < 6N (+2 if there is a default branch), i.e. N >= ~14.  Below
 * that the ladder is smaller (and smaller than native's cpir).
 */
int
mygenswitch(int num, TWORD type, struct swents **p, int n)
{
	char buf[64];
	int i, deflab, ltab;

	if (type != INT && type != UNSIGNED)
		return 0;
	if (28 + 4 * n >= 6 * n + (p[0]->slab > 0 ? 2 : 0))
		return 0;			/* ladder is at least as small */

	/* default target: the real default label, or a fresh label placed
	 * just after the dispatch (falls through past the switch) */
	deflab = p[0]->slab > 0 ? p[0]->slab : getlab();
	ltab = getlab();

	snprintf(buf, sizeof(buf), "\t/SWH %d %u %d %d %d\n",
	    num, (unsigned)type, n, deflab, ltab);
	send_passt(IP_ASM, buf);
	for (i = 1; i <= n; i++) {
		snprintf(buf, sizeof(buf), "\t/SWC %d %d\n",
		    (int)p[i]->sval, p[i]->slab);
		send_passt(IP_ASM, buf);
	}
	send_passt(IP_ASM, "\t/SWE\n");

	if (p[0]->slab <= 0)
		send_passt(IP_DEFLAB, deflab);

	return 1;
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
