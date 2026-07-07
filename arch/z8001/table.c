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
 * Instruction selection table for the Zilog Z8001 (segmented) targeting
 * Coherent OS on the Commodore 900.
 *
 * Register model:
 *   SAREG (class A) - 16-bit word registers r0..r12
 *   SBREG (class B) - 32-bit register pairs rr0,rr2,rr4,rr6,rr8,rr10
 *   SCREG (class C) - 64-bit register quads rq0,rq4,rq8 (doubles)
 *   SDREG (class D) - 8-bit byte registers rl0..rl7 (char values)
 *
 * Key calling convention facts:
 *   - Pure stack, right-to-left push, caller cleans
 *   - int result in r1; long/ptr/float result in rr0; double in rq0
 *   - Stack pointer is the 32-bit pair rr14 (r14:r15)
 *   - Frame pointer is r13
 *
 * Assembler syntax (Coherent as):
 *   Dest-first:  ld r1, r0   (r1 <- r0)
 *   Indirect:    (rr0)       (MUST be a 32-bit pair register)
 *   Disp+ind:    4(rr0)
 *   Immediate:   $N
 *   Push word:   push (rr14), r1
 *   Push long:   pushl (rr14), rr0
 *   Call:        calr sym_   (pc-relative) / call (rr0) (indirect)
 *   Return:      ret un
 */

#include "pass2.h"

/* Type groupings */
#define TWORD	(TINT|TUNSIGNED)
#define TLNG	(TLONG|TULONG)
#define TFLT	TFLOAT
#define TDBL	(TDOUBLE|TLDOUBLE)

/* Convenience NEEDS shorthands (new-style) */
#define NAREG		NEEDS(NREG(A, 1))
#define NBREG		NEEDS(NREG(B, 1))
#define NDREG		NEEDS(NREG(D, 1))
#define XSL(c)		NEEDS(NREG(c, 1), NSL(c))
#define XSR(c)		NEEDS(NREG(c, 1), NSR(c))

/*
 * Char values live in register class D (the byte registers rl0-rl7,
 * i.e. the low halves of r0-r7), so the "byte instructions can only
 * name r0-r7's halves" hardware restriction is enforced by register
 * class membership - byte rules need no NOLEFT/NORIGHT/NEVER
 * constraints (whose addalledges clobber semantics used to poison
 * r8-r12 for everything live near a char access).
 *
 * Conversions between class D and the word/pair classes exploit the
 * fact that WORD instructions (ld/extsb/and/neg/push) work on any
 * register and a char value sits in its containing word's low byte:
 * they move the containing word (ZG/ZH print it, ZK/ZI move it with
 * NSL sharing usually reducing the move to nothing) and extend with
 * word ops.  No fixed registers, no constraints.
 */

struct optab table[] = {

/* First entry must be an empty entry */
{ -1, FOREFF, SANY, TANY, SANY, TANY, 0, 0, "", },

/*
 * PCONVs - pointer conversions.
 * On Z8001 pointers are 32-bit pairs (SBREG), same as long.
 * PCONV between two pair types is a no-op.
 */
{ PCONV,	INBREG,
	SBREG,		TPOINT|TLONG|TULONG,
	SANY,		TPOINT|TLONG|TULONG,
		0,	RLEFT,
		"", },

/* ptr/long from memory into a pair register */
{ PCONV,	INBREG,
	SOREG|SNAME,	TPOINT|TLONG|TULONG,
	SANY,		TPOINT,
		XSL(B),	RESC1,
		"	ldl	A1,AL\n", },

/* word reg to pointer pair: value into the low (offset) word, clear
 * the high (segment) word.  (ZM names the high word explicitly; a bare
 * "clr A1" would print the pair name, which Coherent as encodes as the
 * high word by symbol-value luck - and the old "ld A1,AL; clr U1" form
 * had it backwards: value into the segment, offset cleared.) */
{ PCONV,	INBREG,
	SAREG,		TWORD,
	SANY,		TPOINT,
		XSL(B),	RESC1,
		"	ld	U1,AL\n	clr	ZM\n", },

/*
 * SCONVs - scalar type conversions.
 */

/* (u)int <-> (u)int: already the right size in a word reg */
{ SCONV,	INAREG,
	SAREG,		TWORD|TSHORT|TUSHORT,
	SANY,		TWORD|TSHORT|TUSHORT,
		0,	RLEFT,
		"", },

/* pointer (pair) <-> pointer: no-op */
{ SCONV,	INBREG,
	SBREG,		TPOINT,
	SANY,		TPOINT,
		0,	RLEFT,
		"", },

/* long (pair) <-> long (pair): no-op */
{ SCONV,	INBREG,
	SBREG,		TLONG|TULONG,
	SANY,		TLONG|TULONG,
		0,	RLEFT,
		"", },

/* int -> (u)long: sign-extend word into pair (the SOURCE type picks
 * sign- vs zero-extension; the result signedness is bit-identical) */
{ SCONV,	INBREG,
	SAREG,		TINT,
	SANY,		TLNG,
		XSL(B),	RESC1,
		"	ld	U1,AL\n	exts	A1\n", },

/* unsigned int -> (u)long: zero-extend word into pair */
{ SCONV,	INBREG,
	SAREG,		TUNSIGNED,
	SANY,		TLNG,
		XSL(B),	RESC1,
		"	ld	U1,AL\n	clr	ZM\n", },

/* int/short from memory -> (u)long */
{ SCONV,	INBREG,
	SOREG|SNAME,	TINT|TSHORT,
	SANY,		TLNG,
		NBREG,	RESC1,
		"	ld	U1,AL\n	exts	A1\n", },

/* unsigned/ushort from memory -> (u)long */
{ SCONV,	INBREG,
	SOREG|SNAME,	TUNSIGNED|TUSHORT,
	SANY,		TLNG,
		NBREG,	RESC1,
		"	ld	U1,AL\n	clr	ZM\n", },

/* long/ptr pair -> int: take low word of pair */
{ SCONV,	INAREG,
	SBREG|SOREG|SNAME,	TLONG|TULONG|TPOINT,
	SANY,			TWORD,
		XSL(A),	RESC1,
		"	ld	A1,UL\n", },

/* char <-> char: same byte register either way */
{ SCONV,	INDREG,
	SDREG,		TCHAR|TUCHAR,
	SANY,		TCHAR|TUCHAR,
		0,	RLEFT,
		"", },

/* char (byte reg) -> int: copy the containing word (ZK, elided when
 * NSL sharing makes A1 that word), then sign-extend its low byte in
 * place - extsb is a word op, legal on any register.  Memory chars are
 * first materialized into a byte register by the OPLTYPE rule; with the
 * shared A1 the pair is "ldb rlN,mem; extsb rN", same as a fused rule. */
{ SCONV,	INAREG,
	SDREG,		TCHAR,
	SANY,		TWORD,
		NEEDS(NREG(A, 1), NSL(A)),	RESC1,
		"ZK	extsb	A1\n", },

/* unsigned char (byte reg) -> (u)int: zero-extend in place.  ZU picks
 * the native idiom "subb rhN,rhN" (2 bytes) when A1's word has an
 * addressable high byte (r0-r7), else the word "and A1,$0xff". */
{ SCONV,	INAREG,
	SDREG,		TUCHAR,
	SANY,		TWORD,
		NEEDS(NREG(A, 1), NSL(A)),	RESC1,
		"ZKZU", },

/* char -> (u)long: word-copy the containing word into the pair's low
 * word, extend byte->word->pair.  No NSL: "ld U1,ZG" writes U1 before
 * the (word-op) extensions, so A1 must stay disjoint from the source. */
{ SCONV,	INBREG,
	SDREG,		TCHAR,
	SANY,		TLNG,
		NBREG,	RESC1,
		"	ld	U1,ZG\n	extsb	U1\n	exts	A1\n", },

/* unsigned char -> (u)long */
{ SCONV,	INBREG,
	SDREG,		TUCHAR,
	SANY,		TLNG,
		NBREG,	RESC1,
		"	ld	U1,ZG\n	and	U1,$0xff\n	clr	ZM\n", },

/* int -> char: word-copy into the result's containing word (ZI, elided
 * when NSL sharing makes them coincide); the low byte IS the truncated
 * char, the high byte is dead space. */
{ SCONV,	INDREG,
	SAREG,		TWORD,
	SANY,		TCHAR|TUCHAR,
		NEEDS(NREG(D, 1), NSL(D)),	RESC1,
		"ZI", },

/* (u)long/ptr -> char: word-copy the LOW word (UL) into the result's
 * containing word; works for any pair (rr8/rr10 included) and for
 * memory (low word at offset+2), unlike a byte-register ldb. */
{ SCONV,	INDREG,
	SBREG|SOREG|SNAME,	TLNG|TPOINT,
	SANY,		TCHAR|TUCHAR,
		NDREG,	RESC1,
		"	ld	ZH,UL\n", },

/*
 * Floating-point conversions.  Integer<->fp conversions are rewritten
 * into runtime calls by fixfloatops() in local2.c; only the same-size
 * no-ops and the register-based float<->double pack helpers remain as
 * table rules.  dfpack takes a float in rr0 and returns a double in
 * rq0 (clobbering r5); fdpack takes rq0 and returns rr0 (its scratch,
 * r2/r3, lies inside the consumed rq0).
 */

/* double <-> double: no-op */
{ SCONV,	INCREG,
	SCREG,		TDBL,
	SANY,		TDBL,
		0,	RLEFT,
		"", },

/* float <-> float: no-op */
{ SCONV,	INBREG,
	SBREG,		TFLT,
	SANY,		TFLT,
		0,	RLEFT,
		"", },

/* float -> double: dfpack, rr0 -> rq0 */
{ SCONV,	INCREG,
	SBREG,		TFLT,
	SANY,		TDBL,
		NEEDS(NREG(C, 1), NLEFT(RR0), NRES(RQ0), NEVER(R5)),	RESC1,
		"	calr	dfpack\n", },

/* double -> float: fdpack, rq0 -> rr0 */
{ SCONV,	INBREG,
	SCREG,		TDBL,
	SANY,		TFLT,
		NEEDS(NREG(B, 1), NLEFT(RQ0), NRES(RR0)),	RESC1,
		"	calr	fdpack\n", },

/*
 * Subroutine calls.
 *
 * Z8001 uses:
 *   calr  sym_          (relative call by name)
 *   call  (rr0)         (indirect call through pair register)
 *
 * ZA expands to the function name (via zzzcode 'A').
 * ZB expands to the stack adjustment after the call (via zzzcode 'B').
 */

/* Named call, result is word (int/short) in SAREG */
{ CALL,		INAREG,
	SCON,		TANY,
	SANY,		TWORD,
		XSL(A),	RESC1,
		"	calr	CL\nZB", },

{ UCALL,	INAREG,
	SCON,		TANY,
	SANY,		TWORD,
		XSL(A),	RESC1,
		"	calr	CL\n", },

/* Indirect call (function pointer in pair), word result */
{ CALL,		INAREG,
	SBREG,		TANY,
	SANY,		TWORD,
		XSL(A),	RESC1,
		"	call	(AL)\nZB", },

{ UCALL,	INAREG,
	SBREG,		TANY,
	SANY,		TWORD,
		XSL(A),	RESC1,
		"	call	(AL)\n", },

/* Call with a char result: the value comes back in rl1 (RETREG(CHAR),
 * the class-D face of the native "int result in r1" convention) */
{ CALL,		INDREG,
	SCON,		TANY,
	SANY,		TCHAR|TUCHAR,
		XSL(D),	RESC1,
		"	calr	CL\nZB", },

{ UCALL,	INDREG,
	SCON,		TANY,
	SANY,		TCHAR|TUCHAR,
		XSL(D),	RESC1,
		"	calr	CL\n", },

{ CALL,		INDREG,
	SBREG,		TANY,
	SANY,		TCHAR|TUCHAR,
		XSL(D),	RESC1,
		"	call	(AL)\nZB", },

{ UCALL,	INDREG,
	SBREG,		TANY,
	SANY,		TCHAR|TUCHAR,
		XSL(D),	RESC1,
		"	call	(AL)\n", },

/* Named call, result is long/ptr/float in SBREG */
{ CALL,		INBREG,
	SCON,		TANY,
	SANY,		TLONG|TULONG|TPOINT|TFLT,
		NEEDS(NREG(B, 1), NSL(B), NEVER(RR0)),	RESC1,
		"	calr	CL\nZB", },

{ UCALL,	INBREG,
	SCON,		TANY,
	SANY,		TLONG|TULONG|TPOINT|TFLT,
		NEEDS(NREG(B, 1), NSL(B), NEVER(RR0)),	RESC1,
		"	calr	CL\n", },

/* Indirect call (function pointer in pair), long/ptr/float result */
{ CALL,		INBREG,
	SBREG,		TANY,
	SANY,		TLONG|TULONG|TPOINT|TFLT,
		NEEDS(NREG(B, 1), NSL(B), NEVER(RR0)),	RESC1,
		"	call	(AL)\nZB", },

{ UCALL,	INBREG,
	SBREG,		TANY,
	SANY,		TLONG|TULONG|TPOINT|TFLT,
		NEEDS(NREG(B, 1), NSL(B), NEVER(RR0)),	RESC1,
		"	call	(AL)\n", },

/* Call with a double result in a quad (rq0 per the native convention;
 * doubles are never indirect bases, so coalescing with rq0 is fine) */
{ CALL,		INCREG,
	SCON,		TANY,
	SANY,		TDBL,
		NEEDS(NREG(C, 1), NSL(C)),	RESC1,
		"	calr	CL\nZB", },

{ UCALL,	INCREG,
	SCON,		TANY,
	SANY,		TDBL,
		NEEDS(NREG(C, 1), NSL(C)),	RESC1,
		"	calr	CL\n", },

{ CALL,		INCREG,
	SBREG,		TANY,
	SANY,		TDBL,
		NEEDS(NREG(C, 1), NSL(C)),	RESC1,
		"	call	(AL)\nZB", },

{ UCALL,	INCREG,
	SBREG,		TANY,
	SANY,		TDBL,
		NEEDS(NREG(C, 1), NSL(C)),	RESC1,
		"	call	(AL)\n", },

/*
 * Struct-return calls (hidden-pointer ABI).  ZR pushes the address of
 * the frame buffer reserved by myreader() as the hidden argument (its
 * 4 bytes are included in the ZB cleanup count n_qual); the callee
 * copies the value there and returns the buffer address in rr0, which
 * becomes the call's result.  USTCALL needs ZB too: even with no
 * declared arguments the hidden pointer was pushed.
 */
{ STCALL,	INBREG,
	SCON,		TANY,
	SANY,		TANY,
		NEEDS(NREG(B, 1), NSL(B), NEVER(RR0)),	RESC1,
		"ZR	calr	CL\nZB", },

{ USTCALL,	INBREG,
	SCON,		TANY,
	SANY,		TANY,
		NEEDS(NREG(B, 1), NSL(B), NEVER(RR0)),	RESC1,
		"ZR	calr	CL\nZB", },

{ STCALL,	INBREG,
	SBREG,		TANY,
	SANY,		TANY,
		NEEDS(NREG(B, 1), NSL(B), NEVER(RR0)),	RESC1,
		"ZR	call	(AL)\nZB", },

{ USTCALL,	INBREG,
	SBREG,		TANY,
	SANY,		TANY,
		NEEDS(NREG(B, 1), NSL(B), NEVER(RR0)),	RESC1,
		"ZR	call	(AL)\nZB", },

/* Named call, for effect only (void return) */
{ CALL,		FOREFF,
	SCON,		TANY,
	SANY,		TANY,
		0,	0,
		"	calr	CL\nZB", },

{ UCALL,	FOREFF,
	SCON,		TANY,
	SANY,		TANY,
		0,	0,
		"	calr	CL\n", },

/* Indirect call, for effect only */
{ CALL,		FOREFF,
	SBREG,		TANY,
	SANY,		TANY,
		0,	0,
		"	call	(AL)\nZB", },

{ UCALL,	FOREFF,
	SBREG,		TANY,
	SANY,		TANY,
		0,	0,
		"	call	(AL)\n", },

/* Struct calls for effect only (result ignored): the hidden pointer
 * must STILL be pushed (ZR) - the callee unconditionally writes the
 * returned value through it - and ZB must clean it up. */
{ STCALL,	FOREFF,
	SCON,		TANY,
	SANY,		TANY,
		0,	0,
		"ZR	calr	CL\nZB", },

{ USTCALL,	FOREFF,
	SCON,		TANY,
	SANY,		TANY,
		0,	0,
		"ZR	calr	CL\nZB", },

{ STCALL,	FOREFF,
	SBREG,		TANY,
	SANY,		TANY,
		0,	0,
		"ZR	call	(AL)\nZB", },

{ USTCALL,	FOREFF,
	SBREG,		TANY,
	SANY,		TANY,
		0,	0,
		"ZR	call	(AL)\nZB", },

/*
 * PLUS - integer addition.
 */

/* inc word by 1 */
{ PLUS,		FOREFF|INAREG|FORCC,
	SAREG|SNAME,	TWORD,
	SONE,		TANY,
		0,	RLEFT|RESCC,
		"	inc	AL,$1\n", },

/* inc word in memory by 1 (inc dst is R/IR/DA/X - no BA) */
{ PLUS,		FOREFF|FORCC,
	SNBA,		TWORD,
	SONE,		TANY,
		0,	RLEFT|RESCC,
		"	inc	AL,$1\n", },

/* dec word by 1 (represented as PLUS SMONE in PCC tree) */
{ PLUS,		FOREFF|INAREG|FORCC,
	SAREG|SNAME,	TWORD,
	SMONE,		TANY,
		0,	RLEFT|RESCC,
		"	dec	AL,$1\n", },

{ PLUS,		FOREFF|FORCC,
	SNBA,		TWORD,
	SMONE,		TANY,
		0,	RLEFT|RESCC,
		"	dec	AL,$1\n", },

/* add word reg + reg/name/const (add src is R/IM/IR/DA/X - no BA) */
{ PLUS,		INAREG|FOREFF|FORCC,
	SAREG,		TWORD,
	SAREG|SNAME|SCON,	TWORD,
		0,	RLEFT|RESCC,
		"	add	AL,AR\n", },

/* add word reg + encodable OREG */
{ PLUS,		INAREG|FOREFF|FORCC,
	SAREG,		TWORD,
	SNBA,		TWORD,
		0,	RLEFT|RESCC,
		"	add	AL,AR\n", },

/*
 * Pointer + constant: operate on the OFFSET WORD of the pair only (UL =
 * low word; the segment word is untouched).  Legal under the Coherent
 * segmented model: no object crosses a segment boundary, so valid pointer
 * arithmetic can never carry out of the 16-bit offset - the same
 * assumption native cc makes (it emits inc r9,$1 on pointer pairs).
 * PLAIN LONGS ARE EXCLUDED: for a real 32-bit integer the carry is
 * arithmetic, so TLONG/TULONG keep the full addl/subl rules below.
 * These must precede the generic pair rules (first match wins).
 * inc/dec take 1..16 (2 bytes); add/sub take any word immediate
 * (4 bytes, vs 6 for addl) but only a REGISTER destination, hence no
 * SPCON memory forms.  Memory forms use SNAME (DA+2) and SFRAME
 * (X mode, off+2) - NOT SNBA: the low word of a zero-displacement
 * pair-base OREG would be BA mode, which inc cannot encode.
 */
{ PLUS,		INBREG|FOREFF,
	SBREG,		TPOINT,
	SP16,		TANY,
		0,	RLEFT,
		"	inc	UL,AR\n", },

{ PLUS,		INBREG|FOREFF,
	SBREG,		TPOINT,
	SMONE,		TANY,
		0,	RLEFT,
		"	dec	UL,$1\n", },

{ PLUS,		INBREG|FOREFF,
	SBREG,		TPOINT,
	SPCON,		TANY,
		0,	RLEFT,
		"	add	UL,AR\n", },

/* pointer in memory += 1..16 (via FINDMOPS, like the word inc rules) */
{ PLUS,		FOREFF,
	SNAME,		TPOINT,
	SP16,		TANY,
		0,	RLEFT,
		"	inc	UL,AR\n", },

{ PLUS,		FOREFF,
	SFRAME,		TPOINT,
	SP16,		TANY,
		0,	RLEFT,
		"	inc	UL,AR\n", },

/*
 * pointer + variable word index: clocal rewrites the index subtree of
 * a pointer PLUS/MINUS to word type (stripping the int->long widen -
 * the same segment-invariant license as the constant rules above), so
 * the add happens on the offset word alone like native "add UL,rN"
 * instead of exts+addl on a widened pair.  add src is R/IM/IR/DA/X -
 * no BA, hence the separate SNBA rule.
 */
{ PLUS,		INBREG|FOREFF,
	SBREG,		TPOINT,
	SAREG|SNAME,	TWORD|TSHORT|TUSHORT,
		0,	RLEFT,
		"	add	UL,AR\n", },

{ PLUS,		INBREG|FOREFF,
	SBREG,	TPOINT,
	SNBA,	TWORD|TSHORT|TUSHORT,
		0,	RLEFT,
		"	add	UL,AR\n", },

/* add pair + pair (long/ptr); pointer offsets are widened to a pair */
{ PLUS,		INBREG|FOREFF,
	SBREG,		TLONG|TULONG|TPOINT,
	SBREG|SNAME|SCON,	TLONG|TULONG|TPOINT,
		0,	RLEFT,
		"	addl	AL,AR\n", },

{ PLUS,		INBREG|FOREFF,
	SBREG,		TLONG|TULONG|TPOINT,
	SNBA,		TLONG|TULONG|TPOINT,
		0,	RLEFT,
		"	addl	AL,AR\n", },

/*
 * Address of a frame object.  ADDROF(OREG(r13,off)) is lowered by the MIP
 * reader to PLUS(REG r13, ICON off) with pointer type.  Since r13 is a
 * word register (not SBREG), this falls through the addl rule above; the ZF
 * escape emits "lda A1,L<n>+off(r13); and A1hi,$32512" using the per-function
 * frame-base equate (L<n>=SS|framesize), which supplies the stack segment.
 * The left shape must be SR13 (REG r13 exactly), NOT SANY: SANY also gives
 * a direct match for NAME/OREG pointers (global_ptr + 1), stealing them
 * from the addl rule (which needs a rewrite) and feeding garbage to ZF.
 */
{ PLUS,		INBREG,
	SR13,		TPOINT,
	SCON,		TANY,
		NBREG,	RESC1,
		"ZF", },

/*
 * MINUS - integer subtraction.
 */

/* dec word by 1 */
{ MINUS,	FOREFF|INAREG|FORCC,
	SAREG|SNAME,	TWORD,
	SONE,		TANY,
		0,	RLEFT|RESCC,
		"	dec	AL,$1\n", },

{ MINUS,	FOREFF|FORCC,
	SNBA,		TWORD,
	SONE,		TANY,
		0,	RLEFT|RESCC,
		"	dec	AL,$1\n", },

/* inc word by 1 (MINUS SMONE) */
{ MINUS,	FOREFF|INAREG|FORCC,
	SAREG|SNAME,	TWORD,
	SMONE,		TANY,
		0,	RLEFT|RESCC,
		"	inc	AL,$1\n", },

{ MINUS,	FOREFF|FORCC,
	SNBA,		TWORD,
	SMONE,		TANY,
		0,	RLEFT|RESCC,
		"	inc	AL,$1\n", },

/* subtract word reg - reg/name/const (sub src is R/IM/IR/DA/X - no BA) */
{ MINUS,	INAREG|FOREFF|FORCC,
	SAREG,		TWORD,
	SAREG|SNAME|SCON,	TWORD,
		0,	RLEFT|RESCC,
		"	sub	AL,AR\n", },

/* subtract word reg - encodable OREG */
{ MINUS,	INAREG|FOREFF|FORCC,
	SAREG,		TWORD,
	SNBA,		TWORD,
		0,	RLEFT|RESCC,
		"	sub	AL,AR\n", },

/* pointer - constant on the offset word only (see the PLUS comment:
 * Coherent objects never cross a segment boundary; plain longs excluded) */
{ MINUS,	INBREG|FOREFF,
	SBREG,		TPOINT,
	SP16,		TANY,
		0,	RLEFT,
		"	dec	UL,AR\n", },

{ MINUS,	INBREG|FOREFF,
	SBREG,		TPOINT,
	SMONE,		TANY,
		0,	RLEFT,
		"	inc	UL,$1\n", },

{ MINUS,	INBREG|FOREFF,
	SBREG,		TPOINT,
	SPCON,		TANY,
		0,	RLEFT,
		"	sub	UL,AR\n", },

/* pointer in memory -= 1..16 (via FINDMOPS) */
{ MINUS,	FOREFF,
	SNAME,		TPOINT,
	SP16,		TANY,
		0,	RLEFT,
		"	dec	UL,AR\n", },

{ MINUS,	FOREFF,
	SFRAME,		TPOINT,
	SP16,		TANY,
		0,	RLEFT,
		"	dec	UL,AR\n", },

/* pointer - variable word index (see the PLUS twin above) */
{ MINUS,	INBREG|FOREFF,
	SBREG,		TPOINT,
	SAREG|SNAME,	TWORD|TSHORT|TUSHORT,
		0,	RLEFT,
		"	sub	UL,AR\n", },

{ MINUS,	INBREG|FOREFF,
	SBREG,	TPOINT,
	SNBA,	TWORD|TSHORT|TUSHORT,
		0,	RLEFT,
		"	sub	UL,AR\n", },

/* subtract pair (long/ptr); pointer offsets are widened to a pair */
{ MINUS,	INBREG|FOREFF,
	SBREG,		TLONG|TULONG|TPOINT,
	SBREG|SNAME|SCON,	TLONG|TULONG|TPOINT,
		0,	RLEFT,
		"	subl	AL,AR\n", },

{ MINUS,	INBREG|FOREFF,
	SBREG,		TLONG|TULONG|TPOINT,
	SNBA,		TLONG|TULONG|TPOINT,
		0,	RLEFT,
		"	subl	AL,AR\n", },

/*
 * Address of a frame object at a negative offset: &local becomes
 * MINUS(REG r13, ICON off) via stref/offplus (cf. the PLUS rule above).
 * The ZF escape emits the same "lda A1,L<n>+off(r13); and A1hi,$32512" using
 * the frame-base equate.  SR13 left shape for the same reason as the PLUS
 * rule: SANY would steal global_ptr - 1 from the subl rule.
 */
{ MINUS,	INBREG,
	SR13,		TPOINT,
	SCON,		TANY,
		NBREG,	RESC1,
		"ZF", },

/*
 * MUL - multiplication.
 */

/*
 * word multiply: mult rr0,src multiplies the low word (r1) by src,
 * leaving the 32-bit product in rr0.  We force the multiplicand into
 * r1, clobber r0 (the high word), and reclaim the low word r1 as the
 * int result via RLEFT (which also avoids the RESCx class check).
 */
{ MUL,		INAREG,
	SAREG,		TWORD,
	SAREG|SNAME|SCON,	TWORD,
		NEEDS(NLEFT(R1), NEVER(R0), NRES(R1), NORIGHT(R0), NORIGHT(R1)),	RLEFT,
		"	mult	rr0,AR\n", },

/*
 * long multiply: multl rq0,src multiplies the low pair (rr2) by src,
 * leaving the 64-bit product in the rq0 quad (rr0:rr2).  We force the
 * multiplicand into rr2, clobber the high pair rr0, and reclaim the low
 * pair rr2 as the long result via RLEFT.
 */
{ MUL,		INBREG,
	SBREG,		TLONG|TULONG,
	SBREG|SNAME|SCON,	TLONG|TULONG,
		NEEDS(NLEFT(RR2), NEVER(RR0), NRES(RR2), NORIGHT(RR0), NORIGHT(RR2)),	RLEFT,
		"	multl	rq0,AR\n", },

/*
 * DIV - division.
 */

/*
 * word divide: div r0,src divides the 32-bit dividend in rr0 by the
 * word src, leaving the quotient in r1 (low) and remainder in r0 (high).
 * The dividend word is forced into r1 then sign/zero-extended into rr0.
 * The quotient (r1) is reclaimed as the int result via RLEFT.  The Z8001
 * has only a signed divide (div); unsigned divide zero-extends instead.
 */
{ DIV,		INAREG,
	SAREG,		TINT,
	SAREG|SNAME|SCON,	TINT,
		NEEDS(NLEFT(R1), NEVER(R0), NRES(R1), NORIGHT(R0), NORIGHT(R1)),	RLEFT,
		"	exts	rr0\n	div	r0,AR\n", },

/* unsigned word divide */
{ DIV,		INAREG,
	SAREG,		TUNSIGNED,
	SAREG|SNAME|SCON,	TUNSIGNED,
		NEEDS(NLEFT(R1), NEVER(R0), NRES(R1), NORIGHT(R0), NORIGHT(R1)),	RLEFT,
		"	clr	r0\n	div	r0,AR\n", },

/*
 * long divide: dividend forced into low pair rr2, extended into the rq0
 * quad, divl rr0,src leaves the quotient in rr2 (low) and remainder in
 * rr0 (high).  Quotient reclaimed via RLEFT.
 */
{ DIV,		INBREG,
	SBREG,		TLONG,
	SBREG|SNAME|SCON,	TLONG,
		NEEDS(NLEFT(RR2), NEVER(RR0), NRES(RR2), NORIGHT(RR0), NORIGHT(RR2)),	RLEFT,
		"	extsl	rq0\n	divl	rr0,AR\n", },

/* unsigned long divide */
{ DIV,		INBREG,
	SBREG,		TULONG,
	SBREG|SNAME|SCON,	TULONG,
		NEEDS(NLEFT(RR2), NEVER(RR0), NRES(RR2), NORIGHT(RR0), NORIGHT(RR2)),	RLEFT,
		"	subl	rr0,rr0\n	divl	rr0,AR\n", },

/*
 * MOD - remainder.
 * Word: div leaves the remainder in r0 (high word); copy it down to r1
 * so the result lands in the register RLEFT reclaims.
 */
{ MOD,		INAREG,
	SAREG,		TINT,
	SAREG|SNAME|SCON,	TINT,
		NEEDS(NLEFT(R1), NEVER(R0), NRES(R1), NORIGHT(R0), NORIGHT(R1)),	RLEFT,
		"	exts	rr0\n	div	r0,AR\n	ld	r1,r0\n", },

{ MOD,		INAREG,
	SAREG,		TUNSIGNED,
	SAREG|SNAME|SCON,	TUNSIGNED,
		NEEDS(NLEFT(R1), NEVER(R0), NRES(R1), NORIGHT(R0), NORIGHT(R1)),	RLEFT,
		"	clr	r0\n	div	r0,AR\n	ld	r1,r0\n", },

/*
 * Long remainder: divl leaves the remainder in the high pair rr0; copy
 * it down to rr2 so the result lands in the register RLEFT reclaims.
 */
{ MOD,		INBREG,
	SBREG,		TLONG,
	SBREG|SNAME|SCON,	TLONG,
		NEEDS(NLEFT(RR2), NEVER(RR0), NRES(RR2), NORIGHT(RR0), NORIGHT(RR2)),	RLEFT,
		"	extsl	rq0\n	divl	rr0,AR\n	ldl	rr2,rr0\n", },

{ MOD,		INBREG,
	SBREG,		TULONG,
	SBREG|SNAME|SCON,	TULONG,
		NEEDS(NLEFT(RR2), NEVER(RR0), NRES(RR2), NORIGHT(RR0), NORIGHT(RR2)),	RLEFT,
		"	subl	rr0,rr0\n	divl	rr0,AR\n	ldl	rr2,rr0\n", },

/*
 * Shifts.
 */

/* logical shift left word, constant count */
{ LS,		INAREG|FOREFF,
	SAREG,		TWORD,
	SCON,		TWORD,
		0,	RLEFT,
		"	sll	AL,AR\n", },

/* arithmetic shift right (signed), constant count */
{ RS,		INAREG|FOREFF,
	SAREG,		TINT|TSHORT,
	SCON,		TWORD,
		0,	RLEFT,
		"	sra	AL,AR\n", },

/* logical shift right (unsigned), constant count */
{ RS,		INAREG|FOREFF,
	SAREG,		TUNSIGNED|TUSHORT,
	SCON,		TWORD,
		0,	RLEFT,
		"	srl	AL,AR\n", },

/* shift left long pair, constant count */
{ LS,		INBREG|FOREFF,
	SBREG,		TLONG|TULONG,
	SCON,		TWORD,
		0,	RLEFT,
		"	slll	AL,AR\n", },

/* arithmetic shift right long pair (signed), constant count */
{ RS,		INBREG|FOREFF,
	SBREG,		TLONG,
	SCON,		TWORD,
		0,	RLEFT,
		"	sral	AL,AR\n", },

/* logical shift right long pair (unsigned), constant count */
{ RS,		INBREG|FOREFF,
	SBREG,		TULONG,
	SCON,		TWORD,
		0,	RLEFT,
		"	srll	AL,AR\n", },

/*
 * Variable (register) counts need the dynamic shift instructions
 * sdl/sda/sdll/sdal: count in a word register, SIGNED - positive
 * shifts left, negative shifts right.  So left shifts use the count
 * as-is and right shifts negate a copy of it into a scratch register.
 * (sll/sra/srl only accept immediate counts; Coherent as crashes on
 * a register operand there.)
 */

/* logical shift left word, register count */
{ LS,		INAREG|FOREFF,
	SAREG,		TWORD,
	SAREG,		TWORD,
		0,	RLEFT,
		"	sdl	AL,AR\n", },

/* arithmetic shift right (signed), register count */
{ RS,		INAREG|FOREFF,
	SAREG,		TINT|TSHORT,
	SAREG,		TWORD,
		NAREG,	RLEFT,
		"	ld	A1,AR\n	neg	A1\n	sda	AL,A1\n", },

/* logical shift right (unsigned), register count */
{ RS,		INAREG|FOREFF,
	SAREG,		TUNSIGNED|TUSHORT,
	SAREG,		TWORD,
		NAREG,	RLEFT,
		"	ld	A1,AR\n	neg	A1\n	sdl	AL,A1\n", },

/* shift left long pair, register count */
{ LS,		INBREG|FOREFF,
	SBREG,		TLONG|TULONG,
	SAREG,		TWORD,
		0,	RLEFT,
		"	sdll	AL,AR\n", },

/* arithmetic shift right long pair (signed), register count */
{ RS,		INBREG|FOREFF,
	SBREG,		TLONG,
	SAREG,		TWORD,
		NAREG,	RLEFT,
		"	ld	A1,AR\n	neg	A1\n	sdal	AL,A1\n", },

/* logical shift right long pair (unsigned), register count */
{ RS,		INBREG|FOREFF,
	SBREG,		TULONG,
	SAREG,		TWORD,
		NAREG,	RLEFT,
		"	ld	A1,AR\n	neg	A1\n	sdll	AL,A1\n", },

/*
 * AND - bitwise and.
 */

/* and/or/xor: dst must be a register; src is R/IM/IR/DA/X - no BA.
 * The long ZL forms touch both pair halves (off and off+2), so their
 * memory operand must be a name or a frame slot (SFRAME), never
 * pair-based. */

/*
 * Single-bit truth test: for "(x & pow2) ==/!= 0" the compare-vs-zero
 * elision hands the AND a FORCC cookie (gated to EQ/NE consumers by
 * CCOKFORCOMP in macdefs.h - BIT sets ONLY Z, with the same sense as
 * the and: Z = 1 iff the tested bit is 0).  bit is 2 bytes vs 4 for
 * and-immediate, leaves the operand register intact, and the memory
 * forms (dst R/IR/DA/X - no BA) absorb the operand load entirely.
 * Pure-FORCC rules: never selected in value contexts, and they must
 * precede the general and rules (first match at equal shape level).
 */
{ AND,	FORCC,
	SAREG|SNAME,	TWORD,
	SPOW2,		TANY,
		0,	RESCC,
		"	bit	AL,ZJ\n", },

{ AND,	FORCC,
	SNBA,	TWORD,
	SPOW2,	TANY,
		0,	RESCC,
		"	bit	AL,ZJ\n", },

{ AND,		INAREG|FOREFF|FORCC,
	SAREG,		TWORD,
	SAREG|SNAME|SCON,	TWORD,
		0,	RLEFT|RESCC,
		"	and	AL,AR\n", },

{ AND,		INAREG|FOREFF|FORCC,
	SAREG,		TWORD,
	SNBA,		TWORD,
		0,	RLEFT|RESCC,
		"	and	AL,AR\n", },

{ AND,		INBREG|FOREFF,
	SBREG,		TLONG|TULONG,
	SBREG|SNAME|SCON,	TLONG|TULONG,
		0,	RLEFT,
		"ZL", },

{ AND,		INBREG|FOREFF,
	SBREG,		TLONG|TULONG,
	SFRAME,		TLONG|TULONG,
		0,	RLEFT,
		"ZL", },

/* char AND: clocal narrows char-mask truth tests ((c & m) ==/!= k with
 * m,k in 0..255) back to byte width, so these only ever compute an
 * EQ/NE condition.  andb dst is a register, src R/IM/IR/DA/X (as
 * S_RSRC); a byte immediate is replicated into both halves by as
 * (op&W==0), the same encoding path as cpb Rb,IM.  RESCC is safe for
 * the eq/ne consumer only: andb sets Z from the result but P/V is
 * parity, exactly like testb. */

/* single-bit char truth test: bitb, exactly as the word bit rules
 * above (the byte IR form absorbs the ldb of a pair-based deref) */
{ AND,	FORCC,
	SDREG|SNAME,	TCHAR|TUCHAR,
	SPOW2,		TANY,
		0,	RESCC,
		"	bitb	AL,ZJ\n", },

{ AND,	FORCC,
	SNBA,	TCHAR|TUCHAR,
	SPOW2,	TANY,
		0,	RESCC,
		"	bitb	AL,ZJ\n", },

{ AND,		INDREG|FOREFF|FORCC,
	SDREG,			TCHAR|TUCHAR,
	SDREG|SNAME|SCON,	TCHAR|TUCHAR,
		0,	RLEFT|RESCC,
		"	andb	AL,AR\n", },

{ AND,		INDREG|FOREFF|FORCC,
	SDREG,	TCHAR|TUCHAR,
	SNBA,	TCHAR|TUCHAR,
		0,	RLEFT|RESCC,
		"	andb	AL,AR\n", },

/*
 * OR - bitwise or.
 */

{ OR,		INAREG|FOREFF|FORCC,
	SAREG,		TWORD,
	SAREG|SNAME|SCON,	TWORD,
		0,	RLEFT|RESCC,
		"	or	AL,AR\n", },

{ OR,		INAREG|FOREFF|FORCC,
	SAREG,		TWORD,
	SNBA,		TWORD,
		0,	RLEFT|RESCC,
		"	or	AL,AR\n", },

{ OR,		INBREG|FOREFF,
	SBREG,		TLONG|TULONG,
	SBREG|SNAME|SCON,	TLONG|TULONG,
		0,	RLEFT,
		"ZL", },

{ OR,		INBREG|FOREFF,
	SBREG,		TLONG|TULONG,
	SFRAME,		TLONG|TULONG,
		0,	RLEFT,
		"ZL", },

/*
 * ER - bitwise exclusive or.
 */

{ ER,		INAREG|FOREFF|FORCC,
	SAREG,		TWORD,
	SAREG|SNAME|SCON,	TWORD,
		0,	RLEFT|RESCC,
		"	xor	AL,AR\n", },

{ ER,		INAREG|FOREFF|FORCC,
	SAREG,		TWORD,
	SNBA,		TWORD,
		0,	RLEFT|RESCC,
		"	xor	AL,AR\n", },

{ ER,		INBREG|FOREFF,
	SBREG,		TLONG|TULONG,
	SBREG|SNAME|SCON,	TLONG|TULONG,
		0,	RLEFT,
		"ZL", },

{ ER,		INBREG|FOREFF,
	SBREG,		TLONG|TULONG,
	SFRAME,		TLONG|TULONG,
		0,	RLEFT,
		"ZL", },

/*
 * ASSIGN - assignments.
 */

/* word reg <- zero */
{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TWORD,
	SZERO,		TANY,
		0,	RDEST,
		"	clr	AL\n", },

/* word mem <- zero (clr dst is R/IR/DA/X - no BA) */
{ ASSIGN,	FOREFF,
	SNAME,		TWORD,
	SZERO,		TANY,
		0,	0,
		"	clr	AL\n", },

{ ASSIGN,	FOREFF,
	SNBA,		TWORD,
	SZERO,		TANY,
		0,	0,
		"	clr	AL\n", },

/* pair reg <- zero (long); RDEST valid: the cleared pair IS the value */
{ ASSIGN,	FOREFF|INBREG,
	SBREG,		TLONG|TULONG|TPOINT,
	SZERO,		TANY,
		0,	RDEST,
		"ZQ", },

/* pair in memory <- zero; FOREFF ONLY.  ZQ clears the two memory words
 * and leaves NO register holding the value, so this must not offer
 * INBREG+RDEST: a chained assignment (chars = words = lines = 0) would
 * reclaim an uninitialized pair as the inner assignment's value.  The
 * chained case falls back to the reg path (ldl rrN,$0; ldl mem,rrN). */
{ ASSIGN,	FOREFF,
	SNAME,		TLONG|TULONG|TPOINT,
	SZERO,		TANY,
		0,	0,
		"ZQ", },

{ ASSIGN,	FOREFF,
	SFRAME,		TLONG|TULONG|TPOINT,
	SZERO,		TANY,
		0,	0,
		"ZQ", },

/* word reg <- small constant: 2-byte ldk.  ldk sets no flags, so no
 * FORCC/RESCC here - a compare-context assign falls back to the generic
 * rule below.  Must precede it (first match wins at equal level). */
{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TWORD,
	SLDK,		TANY,
		0,	RDEST,
		"	ldk	AL,AR\n", },

/* word reg <- reg */
{ ASSIGN,	FOREFF|INAREG|FORCC,
	SAREG,		TWORD,
	SAREG|SNAME|SOREG|SCON,	TWORD,
		0,	RDEST|RESCC,
		"	ld	AL,AR\n", },

/* word mem <- reg (INAREG: the stored value stays available in AR) */
{ ASSIGN,	FOREFF|INAREG|FORCC,
	SNAME|SOREG,	TWORD,
	SAREG,		TWORD,
		0,	RDEST|RESCC,
		"	ld	AL,AR\n", },

/* word mem <- const (ld dst,#imm takes IR/DA/X - no BA; a BA dest falls
 * back to the mem <- reg rule with the constant loaded first) */
{ ASSIGN,	FOREFF,
	SNAME,		TWORD,
	SCON,		TANY,
		0,	0,
		"	ld	AL,AR\n", },

{ ASSIGN,	FOREFF,
	SNBA,		TWORD,
	SCON,		TANY,
		0,	0,
		"	ld	AL,AR\n", },

/* pair reg <- pair reg or mem (long/ptr/float).
 * NORIGHT(RR0): clocal rewrites return into ASSIGN(REG-rr0, value); for
 * a reg-reg assign insnwalk moveadds the right side with the precolored
 * rr0 node, and coalescing bypasses the clregs selectable mask (same
 * bug class as the session-5 CALL-result coalesce).  If the returned
 * pair is also used as an indirect base that yields the forbidden
 * (rr0).  The conflict edge blocks only that coalesce, so such returns
 * emit an explicit ldl rr0,rrN like native. */
{ ASSIGN,	FOREFF|INBREG,
	SBREG,		TLONG|TULONG|TPOINT|TFLT,
	SBREG|SNAME|SOREG|SCON,	TLONG|TULONG|TPOINT|TFLT,
		NEEDS(NORIGHT(RR0)),	RDEST,
		"	ldl	AL,AR\n", },

/* pair mem <- pair reg (long/ptr/float) */
{ ASSIGN,	FOREFF|INBREG,
	SNAME|SOREG,	TLONG|TULONG|TPOINT|TFLT,
	SBREG,		TLONG|TULONG|TPOINT|TFLT,
		0,	RDEST,
		"	ldl	AL,AR\n", },

/* double: quad reg <- quad reg or mem, and mem <- quad reg.  ZD picks
 * ldm for frame/name memory and two ldl (IR/BA) for pair-based memory,
 * ordering the halves so a base pair inside the target quad survives. */
{ ASSIGN,	FOREFF|INCREG,
	SCREG,		TDBL,
	SCREG|SNAME|SOREG,	TDBL,
		0,	RDEST,
		"ZD", },

{ ASSIGN,	FOREFF|INCREG,
	SNAME|SOREG,	TDBL,
	SCREG,		TDBL,
		0,	RDEST,
		"ZD", },

/* pair mem <- const long: there is NO direct rule on purpose.  The
 * hardware has no "ldl mem,#imm" form (Coherent as mchld: only word/byte
 * have the LDI store path), so the constant is materialized into a pair
 * register (OPLTYPE ldl $imm) and stored via the mem <- pair rule above. */

/* byte reg <- zero: clrb sets no flags (manual: "No flags affected"),
 * so no FORCC/RESCC - a compare-context assign falls back to the
 * generic rules below (first match wins at equal level). */
{ ASSIGN,	FOREFF|INDREG,
	SDREG,		TCHAR|TUCHAR,
	SZERO,		TANY,
		0,	RDEST,
		"	clrb	AL\n", },

/* byte mem <- zero (clrb dst is R/IR/DA/X - no BA, like clr) */
{ ASSIGN,	FOREFF,
	SNAME,		TCHAR|TUCHAR,
	SZERO,		TANY,
		0,	0,
		"	clrb	AL\n", },

{ ASSIGN,	FOREFF,
	SNBA,		TCHAR|TUCHAR,
	SZERO,		TANY,
		0,	0,
		"	clrb	AL\n", },

/* byte/char reg <- reg, mem or const (byte registers print as rlN) */
{ ASSIGN,	FOREFF|INDREG|FORCC,
	SDREG,		TCHAR|TUCHAR,
	SDREG|SNAME|SOREG|SCON,	TCHAR|TUCHAR,
		0,	RDEST|RESCC,
		"	ldb	AL,AR\n", },

/* byte mem <- reg */
{ ASSIGN,	FOREFF|INDREG|FORCC,
	SNAME|SOREG,	TCHAR|TUCHAR,
	SDREG,		TCHAR|TUCHAR,
		0,	RDEST|RESCC,
		"	ldb	AL,AR\n", },

/* byte mem <- const (ldb dst,#imm takes IR/DA/X - no BA) */
{ ASSIGN,	FOREFF,
	SNAME,		TCHAR|TUCHAR,
	SCON,		TANY,
		0,	0,
		"	ldb	AL,AR\n", },

{ ASSIGN,	FOREFF,
	SNBA,		TCHAR|TUCHAR,
	SCON,		TANY,
		0,	0,
		"	ldb	AL,AR\n", },

/* struct assignment: block-copy via ldirb.  A1 = dest-address pair,
 * A2 = byte count; the source pointer (right) is a pair.  NORIGHT(RR0)
 * keeps the source out of rr0 - it becomes an ldirb indirect base, and
 * rr0 cannot be one.  A struct-call result coalesces with the
 * precolored rr0 (bypassing the clregs mask), so without this the
 * copy-out of a struct return emits "ldirb ...,(rr0)". */
{ STASG,	FOREFF|INAREG,
	SOREG|SNAME,	TANY,
	SBREG,		TPTRTO|TANY,
		NEEDS(NREG(A, 1), NREG(B, 1), NORIGHT(RR0)),	RDEST,
		"ZS", },

/*
 * UMUL - indirection (load through pointer).
 * On Z8001 the address MUST be in a 32-bit pair register.
 * SOREG is used by the MIP layer after offstar() converts an UMUL
 * whose operand is a pair-register OREG.
 */

/* load word through pair register (SOREG) */
{ UMUL,		INAREG,
	SANY,		TANY,
	SOREG,		TWORD|TSHORT|TUSHORT,
		XSL(A),	RESC1,
		"	ld	A1,AL\n", },

/* load long/ptr/float through pair register */
{ UMUL,		INBREG,
	SANY,		TANY,
	SOREG,		TLONG|TULONG|TPOINT|TFLT,
		XSL(B),	RESC1,
		"	ldl	A1,AL\n", },

/* load double through pair register.  No NSL: the result quad spans
 * two pairs and ZE's ordered two-ldl only protects the base pair's own
 * half; keeping the temp disjoint from the left operand is the safe
 * default (the base may also be a regw-less OREG). */
{ UMUL,		INCREG,
	SANY,		TANY,
	SOREG,		TDBL,
		NEEDS(NREG(C, 1)),	RESC1,
		"ZE", },

/* load char through pair register into a byte register.  No extension
 * here: promotion to int is a separate SCONV (usually fused back to
 * "ldb rlN,(rrM); extsb rN" by NSL sharing).  A single ldb reads its
 * address before writing the destination, so even a destination whose
 * word lies inside the base pair is safe. */
{ UMUL,		INDREG,
	SANY,		TANY,
	SOREG,		TCHAR|TUCHAR,
		NDREG,	RESC1,
		"	ldb	A1,AL\n", },

/*
 * Logical/comparison operators.
 * OPLOG covers EQ, NE, LE, GE, LT, GT, ULE, UGE, ULT, UGT.
 */

/*
 * Compare vs zero.  For the ORDERED conditions we must use cp/cpl (a real
 * subtraction), NOT test/testl: TEST performs "dst OR 0" (Z8000 manual), so
 * it sets S and Z but leaves the P/V flag as parity rather than signed-
 * overflow.  The signed conditions lt/ge/gt/le are (S xor V), so after TEST
 * they misfire at the 0 boundary (e.g. "0 < 0" wrongly taken).  cp/cpl set
 * S, V, C and Z correctly for all signed and unsigned conditions.
 *
 * EQ/NE read ONLY the Z flag, which TEST does set correctly - so equality
 * against zero uses test/testl/testb like native cc.  test takes dst =
 * R/IR/DA/X (as S_CLR class), so it also works directly on memory: testl
 * mem replaces an ldl+cpl pair and testb mem a ldb/extsb/cp triple.  The
 * EQ/NE rules must precede the OPLOG cp rules: for an equality compare
 * both match at the same level and the first table entry wins.
 */
/*
 * cp/cpb have two hardware forms (Coherent as S_CP): "cp Rd,src" with
 * src = R/IM/IR/DA/X, and the immediate-compare "cp dst,#imm" with
 * dst = IR/DA/X.  There is NO mem-vs-reg compare and NO BA operand.
 * cpl has ONLY the register-dst form: "cpl RRd,src".
 */

/* equality vs zero, word */
{ EQ,	FORCC,
	SAREG|SNAME,	TWORD,
	SZERO,	TANY,
		0,	RESCC,
		"	test	AL\n", },

{ NE,	FORCC,
	SAREG|SNAME,	TWORD,
	SZERO,	TANY,
		0,	RESCC,
		"	test	AL\n", },

{ EQ,	FORCC,
	SNBA,	TWORD,
	SZERO,	TANY,
		0,	RESCC,
		"	test	AL\n", },

{ NE,	FORCC,
	SNBA,	TWORD,
	SZERO,	TANY,
		0,	RESCC,
		"	test	AL\n", },

/* equality vs zero, long/pointer: unlike cpl, testl also takes memory */
{ EQ,	FORCC,
	SBREG|SNAME,	TLONG|TULONG|TPOINT,
	SZERO,	TANY,
		0,	RESCC,
		"	testl	AL\n", },

{ NE,	FORCC,
	SBREG|SNAME,	TLONG|TULONG|TPOINT,
	SZERO,	TANY,
		0,	RESCC,
		"	testl	AL\n", },

{ EQ,	FORCC,
	SNBA,	TLONG|TULONG|TPOINT,
	SZERO,	TANY,
		0,	RESCC,
		"	testl	AL\n", },

{ NE,	FORCC,
	SNBA,	TLONG|TULONG|TPOINT,
	SZERO,	TANY,
		0,	RESCC,
		"	testl	AL\n", },

/* equality vs zero, char (byte registers print as rlN) */
{ EQ,	FORCC,
	SDREG|SNAME,	TCHAR|TUCHAR,
	SZERO,	TANY,
		0,	RESCC,
		"	testb	AL\n", },

{ NE,	FORCC,
	SDREG|SNAME,	TCHAR|TUCHAR,
	SZERO,	TANY,
		0,	RESCC,
		"	testb	AL\n", },

{ EQ,	FORCC,
	SNBA,	TCHAR|TUCHAR,
	SZERO,	TANY,
		0,	RESCC,
		"	testb	AL\n", },

{ NE,	FORCC,
	SNBA,	TCHAR|TUCHAR,
	SZERO,	TANY,
		0,	RESCC,
		"	testb	AL\n", },

/*
 * Sign test vs zero: LT and GE against 0 are decided by the S flag
 * alone, which test/testl set correctly - the ZO escape makes cbgen
 * branch on mi/pl instead of the generic lt/ge (those are S xor V,
 * and TEST leaves P/V as parity/stale; native cc uses the same
 * "test; jr mi/pl" idiom).  GT/LE also need Z and V, so they fall
 * through to the cp/cpl rules below.  Like the EQ/NE test rules
 * these must precede the OPLOG cp rules.
 */
{ LT,	FORCC,
	SAREG|SNAME,	TWORD,
	SZERO,	TANY,
		0,	RESCC,
		"	test	AL\nZO", },

{ GE,	FORCC,
	SAREG|SNAME,	TWORD,
	SZERO,	TANY,
		0,	RESCC,
		"	test	AL\nZO", },

{ LT,	FORCC,
	SNBA,	TWORD,
	SZERO,	TANY,
		0,	RESCC,
		"	test	AL\nZO", },

{ GE,	FORCC,
	SNBA,	TWORD,
	SZERO,	TANY,
		0,	RESCC,
		"	test	AL\nZO", },

{ LT,	FORCC,
	SBREG|SNAME,	TLONG|TULONG|TPOINT,
	SZERO,	TANY,
		0,	RESCC,
		"	testl	AL\nZO", },

{ GE,	FORCC,
	SBREG|SNAME,	TLONG|TULONG|TPOINT,
	SZERO,	TANY,
		0,	RESCC,
		"	testl	AL\nZO", },

{ LT,	FORCC,
	SNBA,	TLONG|TULONG|TPOINT,
	SZERO,	TANY,
		0,	RESCC,
		"	testl	AL\nZO", },

{ GE,	FORCC,
	SNBA,	TLONG|TULONG|TPOINT,
	SZERO,	TANY,
		0,	RESCC,
		"	testl	AL\nZO", },

/* compare word vs zero */
{ OPLOG,	FORCC,
	SAREG|SNAME,	TWORD,
	SZERO,	TANY,
		0,	RESCC,
		"	cp	AL,$0\n", },

{ OPLOG,	FORCC,
	SNBA,	TWORD,
	SZERO,	TANY,
		0,	RESCC,
		"	cp	AL,$0\n", },

/* compare pair vs zero: register only (no cpl mem,#imm form exists) */
{ OPLOG,	FORCC,
	SBREG,	TLONG|TULONG|TPOINT,
	SZERO,	TANY,
		0,	RESCC,
		"	cpl	AL,$0\n", },

/* compare word reg vs reg/name/const */
{ OPLOG,	FORCC,
	SAREG,			TWORD,
	SAREG|SNAME|SCON,	TWORD,
		0,	RESCC,
		"	cp	AL,AR\n", },

{ OPLOG,	FORCC,
	SAREG,	TWORD,
	SNBA,	TWORD,
		0,	RESCC,
		"	cp	AL,AR\n", },

/* compare word mem vs const (immediate-compare form) */
{ OPLOG,	FORCC,
	SNAME,	TWORD,
	SCON,	TWORD,
		0,	RESCC,
		"	cp	AL,AR\n", },

{ OPLOG,	FORCC,
	SNBA,	TWORD,
	SCON,	TWORD,
		0,	RESCC,
		"	cp	AL,AR\n", },

/* compare pair vs pair (long/ptr): left must be a register */
{ OPLOG,	FORCC,
	SBREG,			TLONG|TULONG|TPOINT,
	SBREG|SNAME|SCON,	TLONG|TULONG|TPOINT,
		0,	RESCC,
		"	cpl	AL,AR\n", },

{ OPLOG,	FORCC,
	SBREG,	TLONG|TULONG|TPOINT,
	SNBA,	TLONG|TULONG|TPOINT,
		0,	RESCC,
		"	cpl	AL,AR\n", },

/* compare char vs char (byte registers print as rlN) */
{ OPLOG,	FORCC,
	SDREG,			TCHAR|TUCHAR,
	SDREG|SNAME|SCON,	TCHAR|TUCHAR,
		0,	RESCC,
		"	cpb	AL,AR\n", },

{ OPLOG,	FORCC,
	SDREG,	TCHAR|TUCHAR,
	SNBA,	TCHAR|TUCHAR,
		0,	RESCC,
		"	cpb	AL,AR\n", },

/* compare char mem vs const (immediate-compare form) */
{ OPLOG,	FORCC,
	SNAME,	TCHAR|TUCHAR,
	SCON,	TCHAR|TUCHAR,
		0,	RESCC,
		"	cpb	AL,AR\n", },

{ OPLOG,	FORCC,
	SNBA,	TCHAR|TUCHAR,
	SCON,	TCHAR|TUCHAR,
		0,	RESCC,
		"	cpb	AL,AR\n", },

/*
 * Value-context relationals (kept in the tree by KEEPLOGOPVALUE):
 * materialize the 0/1 result with "compare ; clr A1 ; tcc cc,A1".
 * TCC cc,Rd sets only bit 0 of Rd when cc holds - all other bits and
 * all flags untouched - and CLR sets no flags, so the order compare/
 * clr/tcc is mandatory and also makes it safe for A1 to share a
 * register with a compare operand (XSL sharing; the compare reads
 * first).  ZV prints the relop's own cc name, non-negated (value
 * sense).
 *
 * Like the FORCC set: EQ/NE against zero go through test/testl/testb
 * (2 bytes shorter than the cp $0 immediate form, and the memory forms
 * absorb the operand load); everything else through cp/cpl/cpb, which
 * set all flags correctly for the ordered and unsigned conditions
 * (LT/GE-vs-0 need no mi/pl escape here: cp's V is valid).  The
 * result is always a word (relop type is INT), so the tcc is always
 * the word form regardless of operand width.
 */

/* equality vs zero -> 0/1, word */
{ EQ,	INAREG,
	SAREG|SNAME,	TWORD,
	SZERO,	TANY,
		XSL(A),		RESC1,
		"	test	AL\n	clr	A1\n	tcc	ZV,A1\n", },

{ NE,	INAREG,
	SAREG|SNAME,	TWORD,
	SZERO,	TANY,
		XSL(A),		RESC1,
		"	test	AL\n	clr	A1\n	tcc	ZV,A1\n", },

{ EQ,	INAREG,
	SNBA,	TWORD,
	SZERO,	TANY,
		XSL(A),		RESC1,
		"	test	AL\n	clr	A1\n	tcc	ZV,A1\n", },

{ NE,	INAREG,
	SNBA,	TWORD,
	SZERO,	TANY,
		XSL(A),		RESC1,
		"	test	AL\n	clr	A1\n	tcc	ZV,A1\n", },

/* equality vs zero -> 0/1, long/pointer */
{ EQ,	INAREG,
	SBREG|SNAME,	TLONG|TULONG|TPOINT,
	SZERO,	TANY,
		XSL(A),		RESC1,
		"	testl	AL\n	clr	A1\n	tcc	ZV,A1\n", },

{ NE,	INAREG,
	SBREG|SNAME,	TLONG|TULONG|TPOINT,
	SZERO,	TANY,
		XSL(A),		RESC1,
		"	testl	AL\n	clr	A1\n	tcc	ZV,A1\n", },

{ EQ,	INAREG,
	SNBA,	TLONG|TULONG|TPOINT,
	SZERO,	TANY,
		XSL(A),		RESC1,
		"	testl	AL\n	clr	A1\n	tcc	ZV,A1\n", },

{ NE,	INAREG,
	SNBA,	TLONG|TULONG|TPOINT,
	SZERO,	TANY,
		XSL(A),		RESC1,
		"	testl	AL\n	clr	A1\n	tcc	ZV,A1\n", },

/* equality vs zero -> 0/1, char */
{ EQ,	INAREG,
	SDREG|SNAME,	TCHAR|TUCHAR,
	SZERO,	TANY,
		XSL(A),		RESC1,
		"	testb	AL\n	clr	A1\n	tcc	ZV,A1\n", },

{ NE,	INAREG,
	SDREG|SNAME,	TCHAR|TUCHAR,
	SZERO,	TANY,
		XSL(A),		RESC1,
		"	testb	AL\n	clr	A1\n	tcc	ZV,A1\n", },

{ EQ,	INAREG,
	SNBA,	TCHAR|TUCHAR,
	SZERO,	TANY,
		XSL(A),		RESC1,
		"	testb	AL\n	clr	A1\n	tcc	ZV,A1\n", },

{ NE,	INAREG,
	SNBA,	TCHAR|TUCHAR,
	SZERO,	TANY,
		XSL(A),		RESC1,
		"	testb	AL\n	clr	A1\n	tcc	ZV,A1\n", },

/* any relop vs zero -> 0/1, word (ordered/unsigned land here) */
{ OPLOG,	INAREG,
	SAREG|SNAME,	TWORD,
	SZERO,	TANY,
		XSL(A),		RESC1,
		"	cp	AL,$0\n	clr	A1\n	tcc	ZV,A1\n", },

{ OPLOG,	INAREG,
	SNBA,	TWORD,
	SZERO,	TANY,
		XSL(A),		RESC1,
		"	cp	AL,$0\n	clr	A1\n	tcc	ZV,A1\n", },

/* any relop -> 0/1, word reg vs reg/name/const */
{ OPLOG,	INAREG,
	SAREG,			TWORD,
	SAREG|SNAME|SCON,	TWORD,
		XSL(A),		RESC1,
		"	cp	AL,AR\n	clr	A1\n	tcc	ZV,A1\n", },

{ OPLOG,	INAREG,
	SAREG,	TWORD,
	SNBA,	TWORD,
		XSL(A),		RESC1,
		"	cp	AL,AR\n	clr	A1\n	tcc	ZV,A1\n", },

/* any relop -> 0/1, word mem vs const (immediate-compare form) */
{ OPLOG,	INAREG,
	SNAME,	TWORD,
	SCON,	TWORD,
		XSL(A),		RESC1,
		"	cp	AL,AR\n	clr	A1\n	tcc	ZV,A1\n", },

{ OPLOG,	INAREG,
	SNBA,	TWORD,
	SCON,	TWORD,
		XSL(A),		RESC1,
		"	cp	AL,AR\n	clr	A1\n	tcc	ZV,A1\n", },

/* any relop vs zero -> 0/1, pair: register only (no cpl mem,#imm) */
{ OPLOG,	INAREG,
	SBREG,	TLONG|TULONG|TPOINT,
	SZERO,	TANY,
		XSL(A),		RESC1,
		"	cpl	AL,$0\n	clr	A1\n	tcc	ZV,A1\n", },

/* any relop -> 0/1, pair vs pair */
{ OPLOG,	INAREG,
	SBREG,			TLONG|TULONG|TPOINT,
	SBREG|SNAME|SCON,	TLONG|TULONG|TPOINT,
		XSL(A),		RESC1,
		"	cpl	AL,AR\n	clr	A1\n	tcc	ZV,A1\n", },

{ OPLOG,	INAREG,
	SBREG,	TLONG|TULONG|TPOINT,
	SNBA,	TLONG|TULONG|TPOINT,
		XSL(A),		RESC1,
		"	cpl	AL,AR\n	clr	A1\n	tcc	ZV,A1\n", },

/* any relop -> 0/1, char vs char */
{ OPLOG,	INAREG,
	SDREG,			TCHAR|TUCHAR,
	SDREG|SNAME|SCON,	TCHAR|TUCHAR,
		XSL(A),		RESC1,
		"	cpb	AL,AR\n	clr	A1\n	tcc	ZV,A1\n", },

{ OPLOG,	INAREG,
	SDREG,	TCHAR|TUCHAR,
	SNBA,	TCHAR|TUCHAR,
		XSL(A),		RESC1,
		"	cpb	AL,AR\n	clr	A1\n	tcc	ZV,A1\n", },

/* any relop -> 0/1, char mem vs const (immediate-compare form) */
{ OPLOG,	INAREG,
	SNAME,	TCHAR|TUCHAR,
	SCON,	TCHAR|TUCHAR,
		XSL(A),		RESC1,
		"	cpb	AL,AR\n	clr	A1\n	tcc	ZV,A1\n", },

{ OPLOG,	INAREG,
	SNBA,	TCHAR|TUCHAR,
	SCON,	TCHAR|TUCHAR,
		XSL(A),		RESC1,
		"	cpb	AL,AR\n	clr	A1\n	tcc	ZV,A1\n", },

/*
 * GOTO - unconditional jump.
 */
{ GOTO,		FOREFF,
	SCON,	TANY,
	SANY,	TANY,
		0,	RNOP,
		"	jr	LL\n", },

/* indirect jump through pair register */
{ GOTO,		FOREFF,
	SBREG,	TANY,
	SANY,	TANY,
		0,	RNOP,
		"	jp	(AL)\n", },

/*
 * OPLTYPE - load leaf type into register.
 * Used to materialize NAME/ICON/OREG into a register.
 */

/* load small word constant: ldk takes exactly 0..15 (2 bytes vs 4 for
 * ld $imm; as S_LDK).  Must precede the generic rule - findleaf takes
 * the first direct match. */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SLDK,	TWORD|TSHORT|TUSHORT,
		NAREG,	RESC1,
		"	ldk	A1,AL\n", },

/* load word constant/name/oreg into word register */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SAREG|SCON|SOREG|SNAME,	TWORD|TSHORT|TUSHORT,
		NAREG,	RESC1,
		"	ld	A1,AL\n", },

/* load long/ptr/float constant/name/oreg into pair register */
{ OPLTYPE,	INBREG,
	SANY,	TANY,
	SBREG|SCON|SOREG|SNAME,	TLONG|TULONG|TPOINT|TFLT,
		NBREG,	RESC1,
		"	ldl	A1,AL\n", },

/* load double from memory (or move a quad) into a quad register.
 * No double constants reach pass 2: myp2tree materializes FCONs into
 * the data segment as NAMEs. */
{ OPLTYPE,	INCREG,
	SANY,	TANY,
	SCREG|SOREG|SNAME,	TDBL,
		NEEDS(NREG(C, 1)),	RESC1,
		"ZE", },

/* materialize a char leaf (reg, mem or constant) into a byte register.
 * No extension here: byte registers hold raw bytes, promotion is an
 * SCONV.  ldb rlN,$imm is the byte immediate-load form. */
{ OPLTYPE,	INDREG,
	SANY,	TANY,
	SDREG|SOREG|SNAME|SCON,	TCHAR|TUCHAR,
		NDREG,	RESC1,
		"	ldb	A1,AL\n", },

/* load address (lda) of SOREG/SNAME into pair register */
{ OPLTYPE,	INBREG,
	SANY,	TANY,
	SOREG|SNAME,	TPOINT|TLONG|TULONG,
		NBREG,	RESC1,
		"	lda	A1,AL\n	and	ZM,$32512\n", },

/*
 * UMINUS - unary negation.
 */

{ UMINUS,	INAREG|FOREFF,
	SAREG,	TWORD,
	SANY,	TANY,
		0,	RLEFT,
		"	neg	AL\n", },

/* negate a char: neg its containing word (a word op, any register);
 * the low byte is the two's-complement byte result */
{ UMINUS,	INDREG|FOREFF,
	SDREG,	TCHAR|TUCHAR,
	SANY,	TANY,
		0,	RLEFT,
		"	neg	ZG\n", },

{ UMINUS,	INBREG|FOREFF,
	SBREG,	TLONG|TULONG,
	SANY,	TANY,
		0,	RLEFT,
		"ZN", },

/* fp negation is an inline sign-bit flip on the high word (native:
 * "xor r0,$-32768" in modf.s), not a runtime call */
{ UMINUS,	INCREG|FOREFF,
	SCREG,	TDBL,
	SANY,	TANY,
		0,	RLEFT,
		"	xor	ZW,$-32768\n", },

{ UMINUS,	INBREG|FOREFF,
	SBREG,	TFLT,
	SANY,	TANY,
		0,	RLEFT,
		"	xor	ZW,$-32768\n", },

/*
 * COMPL - bitwise complement.
 */

{ COMPL,	INAREG,
	SAREG,	TWORD,
	SANY,	TANY,
		0,	RLEFT,
		"	com	AL\n", },

{ COMPL,	INBREG,
	SBREG,	TLONG|TULONG,
	SANY,	TANY,
		0,	RLEFT,
		"ZC", },

/*
 * FUNARG - push argument onto stack before a call.
 *
 * Z8001 ABI: pure stack, right-to-left, caller cleans.
 * Stack pointer is rr14 (pair), push uses:
 *   push  (rr14), rN      (word)
 *   pushl (rr14), rrN     (long/ptr)
 *
 * "AL" in template expands to the argument source operand.
 */

/* push word register */
{ FUNARG,	FOREFF,
	SAREG,		TWORD|TSHORT|TUSHORT,
	SANY,		TWORD,
		0,	RNULL,
		"	push	(rr14),AL\n", },

/* push src is R/IM/IR/DA/X - no BA (same encodable set as pushl below,
 * as machine.c S_PUSH).  Constants, globals and frame words push
 * directly like native (`push (rr14), $1` / `, errno_` / `, L5+4(r13)`);
 * only BA OREGs (pair base + displacement) need the register detour.
 * SNBA is a special shape so it cannot be OR'd into one rule with
 * SCON/SNAME (tshape switches on the whole shape value). */
{ FUNARG,	FOREFF,
	SCON,		TWORD|TSHORT|TUSHORT,
	SANY,		TWORD,
		0,	RNULL,
		"	push	(rr14),AL\n", },

{ FUNARG,	FOREFF,
	SNAME,		TWORD|TSHORT|TUSHORT,
	SANY,		TWORD,
		0,	RNULL,
		"	push	(rr14),AL\n", },

{ FUNARG,	FOREFF,
	SNBA,		TWORD|TSHORT|TUSHORT,
	SANY,		TWORD,
		0,	RNULL,
		"	push	(rr14),AL\n", },

/* push word from BA memory */
{ FUNARG,	FOREFF,
	SOREG,		TWORD|TSHORT|TUSHORT,
	SANY,		TWORD,
		NAREG,	RNULL,
		"	ld	A1,AL\n	push	(rr14),A1\n", },

/* push long/ptr/float pair register */
{ FUNARG,	FOREFF,
	SBREG,		TLONG|TULONG|TPOINT|TFLT,
	SANY,		TLONG|TULONG|TPOINT|TFLT,
		0,	RNULL,
		"	pushl	(rr14),AL\n", },

/* pushl globals and frame longs directly (DA/X/IR; native uses all
 * three).  Long constants keep the ldl detour: native never emits
 * pushl-immediate, and symbolic address constants would need the
 * assembler's long-form segmented-immediate path. */
{ FUNARG,	FOREFF,
	SNAME,		TLONG|TULONG|TPOINT|TFLT,
	SANY,		TLONG|TULONG|TPOINT|TFLT,
		0,	RNULL,
		"	pushl	(rr14),AL\n", },

{ FUNARG,	FOREFF,
	SNBA,		TLONG|TULONG|TPOINT|TFLT,
	SANY,		TLONG|TULONG|TPOINT|TFLT,
		0,	RNULL,
		"	pushl	(rr14),AL\n", },

/* push long/ptr/float from a constant or BA memory */
{ FUNARG,	FOREFF,
	SCON|SOREG,	TLONG|TULONG|TPOINT|TFLT,
	SANY,		TLONG|TULONG|TPOINT|TFLT,
		NBREG,	RNULL,
		"	ldl	A1,AL\n	pushl	(rr14),A1\n", },

/* push a double (8 bytes): low pair first so the sign+exponent word
 * lands at the lower address (native: "pushl rr2; pushl rr0").  Name
 * and frame memory push directly (pushl src is R/IM/IR/DA/X - no BA,
 * so pair-based OREGs go through a quad register instead). */
{ FUNARG,	FOREFF,
	SCREG,		TDBL,
	SANY,		TDBL,
		0,	RNULL,
		"ZP", },

/* NB: SFRAME is a special shape - OR'ing it with SNAME makes a value
 * tshape/special() match nothing (the old combined rule was dead and
 * doubles always took the SCREG path); they must be separate rules. */
{ FUNARG,	FOREFF,
	SNAME,		TDBL,
	SANY,		TDBL,
		0,	RNULL,
		"ZP", },

{ FUNARG,	FOREFF,
	SFRAME,		TDBL,
	SANY,		TDBL,
		0,	RNULL,
		"ZP", },

/* push char: push its containing word (the value is in the low byte of
 * the word-sized argument slot; the high byte is don't-care, exactly as
 * with the old word-register convention) */
{ FUNARG,	FOREFF,
	SDREG,		TCHAR|TUCHAR,
	SANY,		TCHAR|TUCHAR,
		0,	RNULL,
		"	push	(rr14),ZG\n", },

/* push zero word */
{ FUNARG,	FOREFF,
	SZERO,	TANY,
	SANY,	TANY,
		0,	RNULL,
		"	push	(rr14),$0\n", },

/* struct argument (by-value struct copy onto stack) via ldirb.
 * A1 = scratch dest-address pair, A2 = byte count; n_left = source pair.
 * NOLEFT(RR0): the source becomes an ldirb indirect base (see STASG). */
{ STARG,	FOREFF,
	SBREG,		TPTRTO|TANY,
	SANY,		TSTRUCT,
		NEEDS(NREG(A, 1), NREG(B, 1), NOLEFT(RR0)),	0,
		"ZT", },

/*
 * Catch-all rewrite rules: delegate complex patterns back to the
 * generic rewriter, which will break them into simpler pieces.
 */
#define DF(x) FORREW, SANY, TANY, SANY, TANY, NEEDS(NREWRITE), x, ""

{ UMUL,		DF(UMUL), },
{ ASSIGN,	DF(ASSIGN), },
{ STASG,	DF(STASG), },
{ FLD,		DF(FLD), },
{ OPLEAF,	DF(NAME), },
{ OPUNARY,	DF(UMINUS), },
{ OPANY,	DF(BITYPE), },

{ FREE, FREE, FREE, FREE, FREE, FREE, 0, FREE, "help; I'm in trouble\n" },
};

int tablesize = sizeof(table)/sizeof(table[0]);
