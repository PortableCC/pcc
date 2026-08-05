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
 * offword: rewrite a pointer-arithmetic index subtree to word type.
 *
 * The front end converts the index of pointer arithmetic to the 32-bit
 * offset type before scaling, so pass 2 widens it into a pair (exts)
 * and adds with addl.  Under the Coherent segmented assumption (no
 * object crosses a segment boundary - the license recorded on the
 * TPOINT SP16/SPCON rules in table.c) only the low 16 bits of the
 * index ever reach the pointer's offset word, so the widen is dead:
 * strip it and compute the index in word registers; the TPOINT
 * "add/sub UL,AR" rules then operate on the offset word alone, like
 * native cc ("sla r9,$2; add r11,r9").  Scaling (LS/MUL by a constant)
 * moves into the word domain with it - the low 16 product/shift bits
 * are identical.  Returns the rewritten subtree, or NULL to leave the
 * tree (and thus the full-width addl/subl) alone.  POINTERS ONLY: the
 * caller checks the PLUS/MINUS node is pointer-typed, a plain long
 * addition keeps its real 32-bit carry.
 */
static NODE *
offword(NODE *p)
{
	NODE *l;

	if (p->n_type != LONG && p->n_type != ULONG)
		return NULL;
	switch (p->n_op) {
	case SCONV:
		l = p->n_left;
		if (l->n_op == FLD)
			return NULL;	/* keep bitfield extraction intact */
		switch (l->n_type) {
		case INT:
		case UNSIGNED:
		case SHORT:
		case USHORT:
			/* the widen becomes a no-op: use the word value */
			nfree(p);
			return l;
		case CHAR:
		case UCHAR:
			/* widen to a word instead of a pair */
			p->n_type = l->n_type == CHAR ? INT : UNSIGNED;
			return p;
		}
		return NULL;
	case LS:
	case MUL:
		/* constant elsize scaling: scale the word instead of the
		 * pair (word mult/sla, exactly the native idiom) */
		if (p->n_right->n_op != ICON || p->n_right->n_sp != NULL)
			return NULL;
		if (glval(p->n_right) < 0 || glval(p->n_right) > 32767)
			return NULL;
		if ((l = offword(p->n_left)) == NULL)
			return NULL;
		p->n_left = l;
		p->n_type = INT;
		p->n_right->n_type = INT;
		return p;
	}
	return NULL;
}

/*
 * conaddr: a compare operand that is, or will fold to, a constant.
 *
 * Besides a bare ICON, an ADDROF of a static-duration NAME (an array
 * name in an expression, "&global") counts: optim folds it to a named
 * ICON, but only after the compare node has been through clocal, so
 * the const-to-right swap below must recognize the pre-fold form.
 * The andable() gate mirrors the fold's own condition.
 */
static int
conaddr(NODE *q)
{
	return q->n_op == ICON ||
	    (q->n_op == ADDROF && q->n_left->n_op == NAME &&
	    andable(q->n_left));
}

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
		case PARAM:
			/*
			 * Every local and parameter - scalar or aggregate -
			 * becomes a frame structure reference *(r13 + off),
			 * the arch/i86 idiom.  Pass 2's canon folds the plain
			 * accesses back into OREG(r13) (identical code), while
			 * &x cancels ADDROF(UMUL) in buildtree instead of
			 * hitting "unacceptable operand of &" - a direct OREG
			 * here broke &scalar-local whenever the variable was
			 * not an xtemps TEMP (always, for doubles).
			 *
			 * The big-endian char-parameter byte correction
			 * (value in the low byte of the pushed word slot)
			 * is applied once to soffset in bfcode(), not here.
			 */
			l = block(REG, NIL, NIL, PTR+STRTY, 0, 0);
			slval(l, 0);
			l->n_rval = FPREG;
			p = stref(block(STREF, l, p, 0, 0, 0));
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

	case LS:
	case RS:
		/*
		 * Integer-promote a byte shift count.  buildtree() promotes
		 * the value being shifted, but only *demotes* an oversized
		 * count (long -> int); a char/uchar count is left as-is.  The
		 * dynamic shift instructions (sdl/sda/sdll/sdal) take the
		 * count in a word register, so the register-count table rules
		 * require a TWORD right operand - a byte count would match no
		 * rule ("Cannot generate code ... op >>").  SHORT/USHORT are
		 * already word-sized here, so only CHAR/UCHAR need widening.
		 *
		 * Built with block()/direct retype rather than makety() so the
		 * shared file compiles under both ccom and cxxcom (whose
		 * makety() prototypes differ).  A constant count is retyped in
		 * place (no widen needed); a loaded byte gets a real SCONV.
		 */
		if (p->n_right->n_type == CHAR || p->n_right->n_type == UCHAR) {
			if (p->n_right->n_op == ICON)
				p->n_right->n_type = INT;
			else
				p->n_right = block(SCONV, p->n_right, NIL,
				    INT, 0, 0);
		}
		break;

	case SCONV:
		/*
		 * Scalar conversion: try to eliminate no-ops.
		 */
		l = p->n_left;
		m = l->n_type;

		/*
		 * These same-size folds RETYPE the child, which is only a
		 * bit-level no-op.  Never do it to a FLD: its signedness
		 * controls how rmfldops extracts the bitfield (sra vs srl),
		 * so stref's SCONV wrapper must stay and the field keep its
		 * declared type.  (Seen as: unsigned fields read back
		 * sign-extended.)
		 */
		if (l->n_op == FLD)
			break;

		/* int/short <-> int/short in same class: no-op */
		if ((m == INT || m == UNSIGNED || m == SHORT || m == USHORT) &&
		    (p->n_type == INT || p->n_type == UNSIGNED ||
		     p->n_type == SHORT || p->n_type == USHORT)) {
			l->n_type = p->n_type;
			nfree(p);
			return l;
		}

		/* long/pointer <-> long in same class: no-op.  A pointer
		 * source shows up as SCONV from an explicit (long)ptr cast
		 * (conversions TO pointers are PCONV); both are 32-bit
		 * pairs, so it is the same bit-level no-op as long<->long.
		 * (Seen as: "Cannot generate code op SCONV" on units.c
		 * "u_name += (long)sstart".) */
		if ((m == LONG || m == ULONG || ISPTR(m)) &&
		    (p->n_type == LONG || p->n_type == ULONG)) {
			l->n_type = p->n_type;
			nfree(p);
			return l;
		}
		break;

	case PLUS:
	case MINUS:
		/*
		 * Variable pointer index: strip the int->long widen from
		 * the index subtree so the arithmetic happens on the
		 * offset word (see offword above).  Pointer-typed nodes
		 * only; the index is always the right operand (buildtree
		 * puts the pointer on the left), and pointer difference
		 * is not pointer-typed so it never gets here.
		 */
		if (!ISPTR(p->n_type) || ISPTR(p->n_right->n_type))
			break;
		if ((l = offword(p->n_right)) != NULL)
			p->n_right = l;
		break;

	case EQ:
	case NE:
	case LT:
	case LE:
	case GT:
	case GE:
	case ULT:
	case ULE:
	case UGT:
	case UGE: {
		/*
		 * Narrow a char compare against a constant: the front end
		 * promotes both sides to int, hiding the byte operand
		 * behind an SCONV so pass 2 can never use testb/cpb/andb.
		 * For EQ/NE the promotion is value-preserving in both
		 * directions whenever the constant fits the char's value
		 * range.  For the ORDERED compares the promoted word
		 * compare maps to the byte compare with the char's own
		 * extension: sign-extension preserves signed order (char
		 * keeps the signed operator), zero-extension puts both
		 * sides in 0..255 where the signed word compare equals
		 * the UNSIGNED byte compare (uchar flips the operator to
		 * the unsigned condition).  A sign-extended char under an
		 * already-unsigned word compare has no byte equivalent
		 * and is left alone.
		 */
		NODE *sc, *cn;

		/*
		 * Constant to the right, for every compare width: the
		 * parser builds a>b and a<=b as b<a / b>=a (cgram.y
		 * eve()), leaving the constant on the left where pass 2
		 * has no imm-compare rule and detours it through a
		 * register ("ldk r1,$0; cp r1,r0").  Swapping a (side-
		 * effect-free) constant reverses the ordered operator;
		 * EQ/NE are symmetric.  conaddr() also catches address
		 * constants still in their pre-fold ADDROF(NAME) form
		 * ("sp > fname" against an array).
		 */
		if (conaddr(p->n_left) && !conaddr(p->n_right)) {
			cn = p->n_left;
			p->n_left = p->n_right;
			p->n_right = cn;
			switch (p->n_op) {
			case LT:  p->n_op = GT;  break;
			case GT:  p->n_op = LT;  break;
			case LE:  p->n_op = GE;  break;
			case GE:  p->n_op = LE;  break;
			case ULT: p->n_op = UGT; break;
			case UGT: p->n_op = ULT; break;
			case ULE: p->n_op = UGE; break;
			case UGE: p->n_op = ULE; break;
			}
		}

		sc = p->n_left;
		cn = p->n_right;
		if (cn->n_op != ICON || cn->n_sp != NULL)
			break;

		/*
		 * Truth test of a masked char: EQ/NE(AND(SCONV(char->int),
		 * ICON m), ICON k) with m and k both in 0..255.  The mask
		 * clears every promoted high bit no matter how the char
		 * extended, so the equality is decided by the low byte
		 * alone: strip the SCONV and retype the AND to the char
		 * type.  Pass 2 then emits andb, whose Z flag feeds the
		 * eq/ne branch directly (native: "andb rlN,$m; jr ne").
		 */
		if ((p->n_op == EQ || p->n_op == NE) && sc->n_op == AND &&
		    glval(cn) >= 0 && glval(cn) <= 255) {
			NODE *a = sc->n_left, *msk = sc->n_right;

			if (a->n_op != SCONV || msk->n_op != ICON ||
			    msk->n_sp != NULL ||
			    glval(msk) < 0 || glval(msk) > 255)
				break;
			if (a->n_type != INT && a->n_type != UNSIGNED)
				break;
			if (a->n_left->n_op == FLD)
				break;	/* keep bitfield extraction intact */
			m = a->n_left->n_type;
			if (m != CHAR && m != UCHAR)
				break;
			sc->n_left = a->n_left;
			nfree(a);
			sc->n_type = m;
			msk->n_type = m;
			cn->n_type = m;
			break;
		}

		if (sc->n_op != SCONV)
			break;
		if (sc->n_type != INT && sc->n_type != UNSIGNED)
			break;
		if (sc->n_left->n_op == FLD)
			break;	/* keep bitfield extraction intact */
		m = sc->n_left->n_type;
		if (m == CHAR) {
			if (glval(cn) < -128 || glval(cn) > 127)
				break;
		} else if (m == UCHAR) {
			if (glval(cn) < 0 || glval(cn) > 255)
				break;
		} else
			break;
		if (p->n_op != EQ && p->n_op != NE) {
			if (m == CHAR) {
				/* sign-extended: only the SIGNED word
				 * compare maps to the signed byte compare */
				if (p->n_op != LT && p->n_op != LE &&
				    p->n_op != GT && p->n_op != GE)
					break;
			} else {
				/* zero-extended: both sides are 0..255, so
				 * signed and unsigned word compares agree
				 * and both map to the UNSIGNED byte compare */
				if (p->n_op == LT)
					p->n_op = ULT;
				else if (p->n_op == LE)
					p->n_op = ULE;
				else if (p->n_op == GT)
					p->n_op = UGT;
				else if (p->n_op == GE)
					p->n_op = UGE;
			}
		}
		p->n_left = sc->n_left;
		nfree(sc);
		cn->n_type = m;
		break;
	}

	case NOT:
		/*
		 * !(a REL b) on integer/pointer operands folds to the
		 * negated relation - cgram negates every if/while
		 * condition with a NOT wrapper, and wrapping the relop
		 * in EQ(rel, 0) instead would push it into VALUE context
		 * (KEEPLOGOPVALUE) and pessimize every branch.  Float
		 * compares keep their NOT: andorbr's label swap tracks
		 * their negation (ATTR_FP_SWAPPED).
		 *
		 * For a plain scalar, !e is exactly (e == 0): rewriting
		 * lets "f = !x" materialize through clr+tcc instead of
		 * the branch diamond; in branch context andorbr treats
		 * NOT(e) and EQ(e, 0) identically.  ANDAND/OROR/NOT
		 * operands need andorbr's lazy evaluation: left alone.
		 * The clocal re-run applies the compare canonicalization
		 * above (char narrowing) to the new node.
		 */
		l = p->n_left;
		if (l->n_op >= EQ && l->n_op <= UGT) {
			static int negrel[] = { NE, EQ, GT, GE, LT, LE,
			    UGT, UGE, ULT, ULE };

			if (KEEPLOGOPVALUE_T(l->n_left->n_type) &&
			    KEEPLOGOPVALUE_T(l->n_right->n_type)) {
				l->n_op = negrel[l->n_op - EQ];
				*p = *l;
				nfree(l);
			}
			break;
		}
		if (l->n_op == ANDAND || l->n_op == OROR || l->n_op == NOT)
			break;
		if (KEEPLOGOPVALUE_T(l->n_type)) {
			p->n_op = EQ;
			p->n_right = bcon(0);
			return clocal(p);
		}
		break;

	case FORCE:
		/*
		 * FORCE ensures the return value is in the correct register.
		 * On Z8001: int/short in R1, long/ptr in RR0.  A struct
		 * value is returned by ADDRESS in RR0 (hidden-pointer ABI);
		 * efcode() then copies it into the caller's buffer.
		 */
		if (p->n_type == STRTY || p->n_type == UNIONTY) {
			p->n_right = buildtree(ADDROF, p->n_left, NIL);
			p->n_op = ASSIGN;
			p->n_type = p->n_right->n_type;
			p->n_left = block(REG, NIL, NIL, p->n_right->n_type,
			    p->n_right->n_df, p->n_right->n_ap);
			slval(p->n_left, 0);
			regno(p->n_left) = RETREG(p->n_type);
			break;
		}
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
 * double lives in a quad (SCREG) transiently, but with only 3 quads and
 * every FP operation being a helper call, register-resident doubles buy
 * nothing: keep them memory-resident (matches the native compiler).
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
 *
 * Floating-point values are done here: the generic inval() emits them
 * as astypnames[INT] units assuming soft_toush() returns SZINT-sized
 * chunks, but it returns uint32_t chunks (least significant first) -
 * on a 16-bit-int target that prints 32-bit values as ".word" in the
 * wrong positions.  Emit big-endian 16-bit words explicitly.
 */
int
ninval(CONSZ off, int fsz, NODE *p)
{
#ifndef LANG_CXX	/* n_scon is a C-frontend node field */
	TWORD t = p->n_type;
	uint32_t *ufp;
	int nbits, i;

	if (t != FLOAT && t != DOUBLE && t != LDOUBLE)
		return 0;	/* generic inval() handles integers fine */

	ufp = soft_toush(p->n_scon, t, &nbits);
	for (i = nbits/32 - 1; i >= 0; i--) {
		printf("\t.word\t%u\n", (unsigned)((ufp[i] >> 16) & 0xffff));
		printf("\t.word\t%u\n", (unsigned)(ufp[i] & 0xffff));
	}
	return 1;
#else
	return 0;
#endif
}

/*
 * myp2tree: convert FCON (floating-point constant) nodes to named static
 * symbols in the data segment, so pass2 can handle them as memory references.
 */
void
myp2tree(NODE *p)
{
	struct symtab *sp;

	/*
	 * Struct-return calls need ATTR_P2STRUCT in pass 2 (the caller
	 * reserves the return buffer from it), which p2tree only attaches
	 * when p->pss is set.  Member access directly on a call result
	 * ("f().y") retypes the STCALL via pprop and loses pss; restore
	 * it from the function designator node.  (pss is a C-frontend
	 * P1ND field; the C++ frontend has its own node layout.)
	 */
#ifndef LANG_CXX
	if ((p->n_op == STCALL || p->n_op == USTCALL) && p->pss == NULL)
		p->pss = p->n_left->pss;
#endif

	if (p->n_op != FCON)
		return;

	sp = isinlining ? permalloc(sizeof(struct symtab))
	                : tmpalloc(sizeof(struct symtab));
	/*
	 * Zero the whole struct: the "#define sap sss" compat macro above
	 * makes the real attribute-list field unnameable here, and leaving
	 * it as tmpalloc garbage sends locctr()'s attr_find() down a wild
	 * pointer (crashed layout-dependently on the first FCON in any
	 * function after one containing FP helper calls).
	 */
	memset(sp, 0, sizeof(struct symtab));
	sp->sclass  = STATIC;
	sp->slevel  = 1;		/* fake numeric label */
	sp->soffset = getlab();
	sp->stype   = p->n_type;
	sp->squal   = (CON >> TSHIFT);

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
 * Coherent's assembler S_COMM handler requires ".comm <name>,<size>" with a
 * COMMA: it does getid(name) then "if (getnb() != ',') qerr()".  A tab makes
 * getnb() return the size digit instead of ',', so as reports a 'q' error.
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

	if (sp->sclass == STATIC || sp->sclass == USTATIC) {
		/*
		 * Statics must NOT use .comm: Coherent commons are
		 * linker-global, so a static would leak into the global
		 * namespace, and same-numbered L labels from two modules
		 * would be merged into one shared common.  Reserve zeroed
		 * .bssd storage under the label instead, like the native
		 * compiler (".bssd; .even; L85: .blkb 4").
		 */
		if (lastloc != UDATA) {
			setseg(UDATA, NULL);
			lastloc = UDATA;
		}
		printf("\t.even\n");
		if (sp->slevel == 0)
			printf("%s:\n", name);
		else
			printf(LABFMT ":\n", sp->soffset);
		printf("\t.blkb\t%d\n", off);
		return;
	}

	/* Ensure a data segment is active (see comment above). */
	if (lastloc != DATA) {
		setseg(DATA, NULL);
		lastloc = DATA;
	}

	if (sp->slevel == 0)
		printf("\t.comm\t%s,%d\n", name, off);
	else
		printf("\t.comm\t" LABFMT ",%d\n", sp->soffset, off);
}

