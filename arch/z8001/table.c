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
 *
 * Key calling convention facts:
 *   - Pure stack, right-to-left push, caller cleans
 *   - int result in r1; long/ptr result in rr0 (r0:r1)
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

/* Convenience NEEDS shorthands (new-style) */
#define NAREG		NEEDS(NREG(A, 1))
#define NBREG		NEEDS(NREG(B, 1))
#define XSL(c)		NEEDS(NREG(c, 1), NSL(c))
#define XSR(c)		NEEDS(NREG(c, 1), NSR(c))

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

/* word reg to pointer pair (zero-extend) */
{ PCONV,	INBREG,
	SAREG,		TWORD,
	SANY,		TPOINT,
		XSL(B),	RESC1,
		"	ld	A1,AL\n	clr	U1\n", },

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

/* int -> long: sign-extend word into pair */
{ SCONV,	INBREG,
	SAREG,		TINT,
	SANY,		TLONG,
		XSL(B),	RESC1,
		"	ld	U1,AL\n	exts	A1\n", },

/* unsigned int -> unsigned long: zero-extend word into pair */
{ SCONV,	INBREG,
	SAREG,		TUNSIGNED,
	SANY,		TULONG,
		XSL(B),	RESC1,
		"	ld	U1,AL\n	clr	A1\n", },

/* int/short from memory -> long */
{ SCONV,	INBREG,
	SOREG|SNAME,	TINT|TSHORT,
	SANY,		TLONG,
		NBREG,	RESC1,
		"	ld	U1,AL\n	exts	A1\n", },

/* unsigned/ushort from memory -> unsigned long */
{ SCONV,	INBREG,
	SOREG|SNAME,	TUNSIGNED|TUSHORT,
	SANY,		TULONG,
		NBREG,	RESC1,
		"	ld	U1,AL\n	clr	A1\n", },

/* long/ptr pair -> int: take low word of pair */
{ SCONV,	INAREG,
	SBREG|SOREG|SNAME,	TLONG|TULONG|TPOINT,
	SANY,			TWORD,
		XSL(A),	RESC1,
		"	ld	A1,UL\n", },

/* char in reg -> int (sign-extend) */
{ SCONV,	INAREG,
	SAREG,		TCHAR,
	SANY,		TINT|TUNSIGNED,
		0,	RLEFT,
		"	extsb	AL\n", },

/* unsigned char in reg -> (u)int (zero-extend) */
{ SCONV,	INAREG,
	SAREG,		TUCHAR,
	SANY,		TINT|TUNSIGNED,
		0,	RLEFT,
		"	and	AL,$0xff\n", },

/* char from memory -> int */
{ SCONV,	INAREG,
	SOREG|SNAME,	TCHAR,
	SANY,		TINT|TUNSIGNED,
		NAREG,	RESC1,
		"	ldb	ZH,AL\n	extsb	A1\n", },

/* unsigned char from memory -> (u)int */
{ SCONV,	INAREG,
	SOREG|SNAME,	TUCHAR,
	SANY,		TINT|TUNSIGNED,
		NAREG,	RESC1,
		"	clr	A1\n	ldb	ZH,AL\n", },

/* char -> long */
{ SCONV,	INBREG,
	SAREG,		TCHAR,
	SANY,		TLONG,
		XSL(B),	RESC1,
		"	extsb	AL\n	ld	U1,AL\n	exts	A1\n", },

/* unsigned char -> unsigned long */
{ SCONV,	INBREG,
	SAREG,		TUCHAR,
	SANY,		TULONG,
		XSL(B),	RESC1,
		"	and	AL,$0xff\n	ld	U1,AL\n	clr	A1\n", },

/* int -> char: keep low byte (already in register) */
{ SCONV,	INAREG,
	SAREG,		TWORD,
	SANY,		TCHAR|TUCHAR,
		0,	RLEFT,
		"", },

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

/* Named call, result is word (int/short/char/ptr-lo) in SAREG */
{ CALL,		INAREG,
	SCON,		TANY,
	SANY,		TWORD|TCHAR|TUCHAR,
		XSL(A),	RESC1,
		"	calr	CL\nZB", },

{ UCALL,	INAREG,
	SCON,		TANY,
	SANY,		TWORD|TCHAR|TUCHAR,
		XSL(A),	RESC1,
		"	calr	CL\n", },

/* Indirect call (function pointer in pair), word result */
{ CALL,		INAREG,
	SBREG,		TANY,
	SANY,		TWORD|TCHAR|TUCHAR,
		XSL(A),	RESC1,
		"	call	(AL)\nZB", },

{ UCALL,	INAREG,
	SBREG,		TANY,
	SANY,		TWORD|TCHAR|TUCHAR,
		XSL(A),	RESC1,
		"	call	(AL)\n", },

/* Named call, result is long/ptr in SBREG */
{ CALL,		INBREG,
	SCON,		TANY,
	SANY,		TLONG|TULONG|TPOINT,
		XSL(B),	RESC1,
		"	calr	CL\nZB", },

{ UCALL,	INBREG,
	SCON,		TANY,
	SANY,		TLONG|TULONG|TPOINT,
		XSL(B),	RESC1,
		"	calr	CL\n", },

/* Indirect call (function pointer in pair), long/ptr result */
{ CALL,		INBREG,
	SBREG,		TANY,
	SANY,		TLONG|TULONG|TPOINT,
		XSL(B),	RESC1,
		"	call	(AL)\nZB", },

{ UCALL,	INBREG,
	SBREG,		TANY,
	SANY,		TLONG|TULONG|TPOINT,
		XSL(B),	RESC1,
		"	call	(AL)\n", },

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

/* Struct call (result by hidden pointer) */
{ STCALL,	INAREG,
	SCON,		TANY,
	SANY,		TANY,
		XSL(A),	RESC1,
		"	calr	CL\nZB", },

{ USTCALL,	INAREG,
	SCON,		TANY,
	SANY,		TANY,
		XSL(A),	RESC1,
		"	calr	CL\n", },

{ STCALL,	FOREFF,
	SCON,		TANY,
	SANY,		TANY,
		0,	0,
		"	calr	CL\nZB", },

{ USTCALL,	FOREFF,
	SCON,		TANY,
	SANY,		TANY,
		0,	0,
		"	calr	CL\n", },

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
 */
{ PLUS,		INBREG,
	SANY,		TPOINT,
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
 * the frame-base equate.
 */
{ MINUS,	INBREG,
	SANY,		TPOINT,
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

/* pair <- zero (long); ZQ clears both halves (off and off+2), so the
 * memory form is name/frame only */
{ ASSIGN,	FOREFF|INBREG,
	SBREG|SNAME,	TLONG|TULONG|TPOINT,
	SZERO,		TANY,
		0,	RDEST,
		"ZQ", },

{ ASSIGN,	FOREFF,
	SFRAME,		TLONG|TULONG|TPOINT,
	SZERO,		TANY,
		0,	0,
		"ZQ", },

/* word reg <- reg */
{ ASSIGN,	FOREFF|INAREG|FORCC,
	SAREG,		TWORD,
	SAREG|SNAME|SOREG|SCON,	TWORD,
		0,	RDEST|RESCC,
		"	ld	AL,AR\n", },

/* word mem <- reg */
{ ASSIGN,	FOREFF|FORCC,
	SNAME|SOREG,	TWORD,
	SAREG,		TWORD,
		0,	RESCC,
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

/* pair reg <- pair reg or mem (long/ptr) */
{ ASSIGN,	FOREFF|INBREG,
	SBREG,		TLONG|TULONG|TPOINT,
	SBREG|SNAME|SOREG|SCON,	TLONG|TULONG|TPOINT,
		0,	RDEST,
		"	ldl	AL,AR\n", },

/* pair mem <- pair reg (long/ptr) */
{ ASSIGN,	FOREFF,
	SNAME|SOREG,	TLONG|TULONG|TPOINT,
	SBREG,		TLONG|TULONG|TPOINT,
		0,	0,
		"	ldl	AL,AR\n", },

/* pair mem <- const long: there is NO direct rule on purpose.  The
 * hardware has no "ldl mem,#imm" form (Coherent as mchld: only word/byte
 * have the LDI store path), so the constant is materialized into a pair
 * register (OPLTYPE ldl $imm) and stored via the mem <- pair rule above. */

/* byte/char reg <- reg or mem (dest reg -> low byte; src reg -> low byte) */
{ ASSIGN,	FOREFF|INAREG|FORCC,
	SAREG,		TCHAR|TUCHAR,
	SAREG|SNAME|SOREG|SCON,	TCHAR|TUCHAR,
		0,	RDEST|RESCC,
		"	ldb	ZG,ZJ\n", },

/* byte mem <- reg (src reg -> low byte) */
{ ASSIGN,	FOREFF|FORCC,
	SNAME|SOREG,	TCHAR|TUCHAR,
	SAREG,		TCHAR|TUCHAR,
		0,	RESCC,
		"	ldb	AL,ZJ\n", },

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
 * A2 = byte count; the source pointer (right) is a pair. */
{ STASG,	FOREFF|INAREG,
	SOREG|SNAME,	TANY,
	SBREG,		TPTRTO|TANY,
		NEEDS(NREG(A, 1), NREG(B, 1)),	RDEST,
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

/* load long/ptr through pair register */
{ UMUL,		INBREG,
	SANY,		TANY,
	SOREG,		TLONG|TULONG|TPOINT,
		XSL(B),	RESC1,
		"	ldl	A1,AL\n", },

/* load signed char through pair register */
{ UMUL,		INAREG,
	SANY,		TANY,
	SOREG,		TCHAR,
		XSL(A),	RESC1,
		"	ldb	ZH,AL\n	extsb	A1\n", },

/* load unsigned char through pair register */
{ UMUL,		INAREG,
	SANY,		TANY,
	SOREG,		TUCHAR,
		XSL(A),	RESC1,
		"	clr	A1\n	ldb	ZH,AL\n", },

/*
 * Logical/comparison operators.
 * OPLOG covers EQ, NE, LE, GE, LT, GT, ULE, UGE, ULT, UGT.
 */

/*
 * Compare vs zero.  We must use cp/cpl (a real subtraction), NOT test/testl:
 * TEST performs "dst OR 0" (Z8000 manual), so it sets S and Z but leaves the
 * P/V flag as parity rather than signed-overflow.  The signed conditions
 * lt/ge/gt/le are (S xor V), so after TEST they misfire at the 0 boundary
 * (e.g. "0 < 0" wrongly taken).  cp/cpl set S, V, C and Z correctly for all
 * signed and unsigned conditions.
 */
/*
 * cp/cpb have two hardware forms (Coherent as S_CP): "cp Rd,src" with
 * src = R/IM/IR/DA/X, and the immediate-compare "cp dst,#imm" with
 * dst = IR/DA/X.  There is NO mem-vs-reg compare and NO BA operand.
 * cpl has ONLY the register-dst form: "cpl RRd,src".
 */

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

/* compare char vs char (reg operands -> low byte) */
{ OPLOG,	FORCC,
	SAREG,			TCHAR|TUCHAR,
	SAREG|SNAME|SCON,	TCHAR|TUCHAR,
		0,	RESCC,
		"	cpb	ZG,ZJ\n", },

{ OPLOG,	FORCC,
	SAREG,	TCHAR|TUCHAR,
	SNBA,	TCHAR|TUCHAR,
		0,	RESCC,
		"	cpb	ZG,ZJ\n", },

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

/* load word constant/name/oreg into word register */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SAREG|SCON|SOREG|SNAME,	TWORD|TSHORT|TUSHORT,
		NAREG,	RESC1,
		"	ld	A1,AL\n", },

/* load long/ptr constant/name/oreg into pair register */
{ OPLTYPE,	INBREG,
	SANY,	TANY,
	SBREG|SCON|SOREG|SNAME,	TLONG|TULONG|TPOINT,
		NBREG,	RESC1,
		"	ldl	A1,AL\n", },

/* char already in a register, or a char constant: copy as a word */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SAREG|SCON,	TCHAR|TUCHAR,
		NAREG,	RESC1,
		"	ld	A1,AL\n", },

/* load signed char from mem into word register */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SOREG|SNAME,	TCHAR,
		NAREG,	RESC1,
		"	ldb	ZH,AL\n	extsb	A1\n", },

/* load unsigned char from mem into word register */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SOREG|SNAME,	TUCHAR,
		NAREG,	RESC1,
		"	clr	A1\n	ldb	ZH,AL\n", },

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
	SAREG,	TWORD|TCHAR|TUCHAR,
	SANY,	TANY,
		0,	RLEFT,
		"	neg	AL\n", },

{ UMINUS,	INBREG|FOREFF,
	SBREG,	TLONG|TULONG,
	SANY,	TANY,
		0,	RLEFT,
		"ZN", },

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

/* push word constant or memory */
{ FUNARG,	FOREFF,
	SCON|SNAME|SOREG,	TWORD|TSHORT|TUSHORT,
	SANY,			TWORD,
		NAREG,	RNULL,
		"	ld	A1,AL\n	push	(rr14),A1\n", },

/* push long/ptr pair register */
{ FUNARG,	FOREFF,
	SBREG,		TLONG|TULONG|TPOINT,
	SANY,		TLONG|TULONG|TPOINT,
		0,	RNULL,
		"	pushl	(rr14),AL\n", },

/* push long/ptr from memory or constant */
{ FUNARG,	FOREFF,
	SCON|SNAME|SOREG,	TLONG|TULONG|TPOINT,
	SANY,			TLONG|TULONG|TPOINT,
		NBREG,	RNULL,
		"	ldl	A1,AL\n	pushl	(rr14),A1\n", },

/* push char (promoted to word) */
{ FUNARG,	FOREFF,
	SAREG,		TCHAR|TUCHAR,
	SANY,		TCHAR|TUCHAR,
		0,	RNULL,
		"	push	(rr14),AL\n", },

/* push zero word */
{ FUNARG,	FOREFF,
	SZERO,	TANY,
	SANY,	TANY,
		0,	RNULL,
		"	push	(rr14),$0\n", },

/* struct argument (by-value struct copy onto stack) via ldirb.
 * A1 = scratch dest-address pair, A2 = byte count; n_left = source pair. */
{ STARG,	FOREFF,
	SBREG,		TPTRTO|TANY,
	SANY,		TSTRUCT,
		NEEDS(NREG(A, 1), NREG(B, 1)),	0,
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
