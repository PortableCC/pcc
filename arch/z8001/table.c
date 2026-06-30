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
		"	ld	U1,AL\n	ext0l	A1\n", },

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
		"	ld	U1,AL\n	ext0l	A1\n", },

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
		"	andb	AL,$0xff\n", },

/* char from memory -> int */
{ SCONV,	INAREG,
	SOREG|SNAME,	TCHAR,
	SANY,		TINT|TUNSIGNED,
		NAREG,	RESC1,
		"	ldb	A1,AL\n	extsb	A1\n", },

/* unsigned char from memory -> (u)int */
{ SCONV,	INAREG,
	SOREG|SNAME,	TUCHAR,
	SANY,		TINT|TUNSIGNED,
		NAREG,	RESC1,
		"	ldb	A1,AL\n", },

/* char -> long */
{ SCONV,	INBREG,
	SAREG,		TCHAR,
	SANY,		TLONG,
		XSL(B),	RESC1,
		"	extsb	AL\n	ld	U1,AL\n	ext0l	A1\n", },

/* unsigned char -> unsigned long */
{ SCONV,	INBREG,
	SAREG,		TUCHAR,
	SANY,		TULONG,
		XSL(B),	RESC1,
		"	andb	AL,$0xff\n	ld	U1,AL\n	clr	A1\n", },

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
	SAREG|SOREG|SNAME,	TWORD,
	SONE,			TANY,
		0,	RLEFT|RESCC,
		"	inc	AL,$1\n", },

/* dec word by 1 (represented as PLUS SMONE in PCC tree) */
{ PLUS,		FOREFF|INAREG|FORCC,
	SAREG|SOREG|SNAME,	TWORD,
	SMONE,			TANY,
		0,	RLEFT|RESCC,
		"	dec	AL,$1\n", },

/* add word reg + reg */
{ PLUS,		INAREG|FOREFF|FORCC,
	SAREG,		TWORD,
	SAREG|SNAME|SOREG|SCON,	TWORD,
		0,	RLEFT|RESCC,
		"	add	AL,AR\n", },

/* add word mem + reg/const (for side effects) */
{ PLUS,		FOREFF|FORCC,
	SNAME|SOREG,	TWORD,
	SAREG|SCON,	TWORD,
		0,	RLEFT|RESCC,
		"	add	AL,AR\n", },

/* add pair + pair (long) */
{ PLUS,		INBREG|FOREFF,
	SBREG,		TLONG|TULONG,
	SBREG|SOREG|SNAME|SCON,	TLONG|TULONG,
		0,	RLEFT,
		"	addl	AL,AR\n", },

/* pointer + int offset */
{ PLUS,		INBREG|FOREFF,
	SBREG,		TPOINT,
	SAREG|SCON,	TWORD,
		0,	RLEFT,
		"	addl	AL,AR\n", },

/*
 * MINUS - integer subtraction.
 */

/* dec word by 1 */
{ MINUS,	FOREFF|INAREG|FORCC,
	SAREG|SOREG|SNAME,	TWORD,
	SONE,			TANY,
		0,	RLEFT|RESCC,
		"	dec	AL,$1\n", },

/* inc word by 1 (MINUS SMONE) */
{ MINUS,	FOREFF|INAREG|FORCC,
	SAREG|SOREG|SNAME,	TWORD,
	SMONE,			TANY,
		0,	RLEFT|RESCC,
		"	inc	AL,$1\n", },

/* subtract word reg - reg */
{ MINUS,	INAREG|FOREFF|FORCC,
	SAREG,		TWORD,
	SAREG|SNAME|SOREG|SCON,	TWORD,
		0,	RLEFT|RESCC,
		"	sub	AL,AR\n", },

/* subtract word mem (side effect) */
{ MINUS,	FOREFF|FORCC,
	SNAME|SOREG,	TWORD,
	SAREG|SCON,	TWORD,
		0,	RLEFT|RESCC,
		"	sub	AL,AR\n", },

/* subtract pair (long) */
{ MINUS,	INBREG|FOREFF,
	SBREG,		TLONG|TULONG,
	SBREG|SOREG|SNAME|SCON,	TLONG|TULONG,
		0,	RLEFT,
		"	subl	AL,AR\n", },

/* pointer - word offset */
{ MINUS,	INBREG|FOREFF,
	SBREG,		TPOINT,
	SAREG|SCON,	TWORD,
		0,	RLEFT,
		"	subl	AL,AR\n", },

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
	SAREG|SNAME|SOREG|SCON,	TWORD,
		NEEDS(NLEFT(R1), NEVER(R0), NRES(R1)),	RLEFT,
		"	mult	rr0,AR\n", },

/* long multiply */
{ MUL,		INBREG,
	SBREG,		TLONG|TULONG,
	SBREG|SNAME|SOREG|SCON,	TLONG|TULONG,
		NEEDS(NREG(B, 1), NSL(B), NRES(RR0)),	RESC1,
		"	multl	AL,AR\n", },

/*
 * DIV - division.
 */

/*
 * word divide: divs rr0,src divides the 32-bit dividend in rr0 by the
 * word src, leaving the quotient in r1 (low) and remainder in r0 (high).
 * The dividend word is forced into r1 then sign/zero-extended into rr0.
 * The quotient (r1) is reclaimed as the int result via RLEFT.
 */
{ DIV,		INAREG,
	SAREG,		TINT,
	SAREG|SNAME|SOREG|SCON,	TINT,
		NEEDS(NLEFT(R1), NEVER(R0), NRES(R1)),	RLEFT,
		"	exts	rr0\n	divs	rr0,AR\n", },

/* unsigned word divide */
{ DIV,		INAREG,
	SAREG,		TUNSIGNED,
	SAREG|SNAME|SOREG|SCON,	TUNSIGNED,
		NEEDS(NLEFT(R1), NEVER(R0), NRES(R1)),	RLEFT,
		"	clr	r0\n	divu	rr0,AR\n", },

/* signed long divide */
{ DIV,		INBREG,
	SBREG,		TLONG,
	SBREG|SNAME|SOREG|SCON,	TLONG,
		NEEDS(NREG(B, 1), NSL(B), NRES(RR0)),	RESC1,
		"	divsl	AL,AR\n", },

/* unsigned long divide */
{ DIV,		INBREG,
	SBREG,		TULONG,
	SBREG|SNAME|SOREG|SCON,	TULONG,
		NEEDS(NREG(B, 1), NSL(B), NRES(RR0)),	RESC1,
		"	divul	AL,AR\n", },

/*
 * MOD - remainder.
 * divs/divu leaves the remainder in r0 (high word).  We copy it down to
 * r1 so the result lands in the same register that RLEFT reclaims.
 */
{ MOD,		INAREG,
	SAREG,		TINT,
	SAREG|SNAME|SOREG|SCON,	TINT,
		NEEDS(NLEFT(R1), NEVER(R0), NRES(R1)),	RLEFT,
		"	exts	rr0\n	divs	rr0,AR\n	ld	r1,r0\n", },

{ MOD,		INAREG,
	SAREG,		TUNSIGNED,
	SAREG|SNAME|SOREG|SCON,	TUNSIGNED,
		NEEDS(NLEFT(R1), NEVER(R0), NRES(R1)),	RLEFT,
		"	clr	r0\n	divu	rr0,AR\n	ld	r1,r0\n", },

/*
 * Shifts.
 */

/* logical shift left word */
{ LS,		INAREG|FOREFF,
	SAREG,		TWORD,
	SAREG|SCON,	TWORD,
		0,	RLEFT,
		"	sll	AL,AR\n", },

/* arithmetic shift right (signed) */
{ RS,		INAREG|FOREFF,
	SAREG,		TINT|TSHORT,
	SAREG|SCON,	TWORD,
		0,	RLEFT,
		"	sra	AL,AR\n", },

/* logical shift right (unsigned) */
{ RS,		INAREG|FOREFF,
	SAREG,		TUNSIGNED|TUSHORT,
	SAREG|SCON,	TWORD,
		0,	RLEFT,
		"	srl	AL,AR\n", },

/* shift left long pair */
{ LS,		INBREG|FOREFF,
	SBREG,		TLONG|TULONG,
	SAREG|SCON,	TWORD,
		0,	RLEFT,
		"	slll	AL,AR\n", },

/* arithmetic shift right long pair (signed) */
{ RS,		INBREG|FOREFF,
	SBREG,		TLONG,
	SAREG|SCON,	TWORD,
		0,	RLEFT,
		"	sral	AL,AR\n", },

/* logical shift right long pair (unsigned) */
{ RS,		INBREG|FOREFF,
	SBREG,		TULONG,
	SAREG|SCON,	TWORD,
		0,	RLEFT,
		"	srll	AL,AR\n", },

/*
 * AND - bitwise and.
 */

{ AND,		INAREG|FOREFF|FORCC,
	SAREG,		TWORD,
	SAREG|SNAME|SOREG|SCON,	TWORD,
		0,	RLEFT|RESCC,
		"	and	AL,AR\n", },

{ AND,		FOREFF|FORCC,
	SNAME|SOREG,	TWORD,
	SAREG|SCON,	TWORD,
		0,	RLEFT|RESCC,
		"	and	AL,AR\n", },

{ AND,		INBREG|FOREFF,
	SBREG,		TLONG|TULONG,
	SBREG|SNAME|SOREG|SCON,	TLONG|TULONG,
		0,	RLEFT,
		"	andl	AL,AR\n", },

/*
 * OR - bitwise or.
 */

{ OR,		INAREG|FOREFF|FORCC,
	SAREG,		TWORD,
	SAREG|SNAME|SOREG|SCON,	TWORD,
		0,	RLEFT|RESCC,
		"	or	AL,AR\n", },

{ OR,		FOREFF|FORCC,
	SNAME|SOREG,	TWORD,
	SAREG|SCON,	TWORD,
		0,	RLEFT|RESCC,
		"	or	AL,AR\n", },

{ OR,		INBREG|FOREFF,
	SBREG,		TLONG|TULONG,
	SBREG|SNAME|SOREG|SCON,	TLONG|TULONG,
		0,	RLEFT,
		"	orl	AL,AR\n", },

/*
 * ER - bitwise exclusive or.
 */

{ ER,		INAREG|FOREFF|FORCC,
	SAREG,		TWORD,
	SAREG|SNAME|SOREG|SCON,	TWORD,
		0,	RLEFT|RESCC,
		"	xor	AL,AR\n", },

{ ER,		FOREFF|FORCC,
	SNAME|SOREG,	TWORD,
	SAREG|SCON,	TWORD,
		0,	RLEFT|RESCC,
		"	xor	AL,AR\n", },

{ ER,		INBREG|FOREFF,
	SBREG,		TLONG|TULONG,
	SBREG|SNAME|SOREG|SCON,	TLONG|TULONG,
		0,	RLEFT,
		"	xorl	AL,AR\n", },

/*
 * ASSIGN - assignments.
 */

/* word reg <- zero */
{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TWORD,
	SZERO,		TANY,
		0,	RDEST,
		"	clr	AL\n", },

/* word mem <- zero */
{ ASSIGN,	FOREFF,
	SNAME|SOREG,	TWORD,
	SZERO,		TANY,
		0,	0,
		"	clr	AL\n", },

/* pair <- zero (long) */
{ ASSIGN,	FOREFF|INBREG,
	SBREG|SNAME|SOREG,	TLONG|TULONG|TPOINT,
	SZERO,			TANY,
		0,	RDEST,
		"	clrl	AL\n", },

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

/* word mem <- const */
{ ASSIGN,	FOREFF,
	SNAME|SOREG,	TWORD,
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

/* pair mem <- const long */
{ ASSIGN,	FOREFF,
	SNAME|SOREG,	TLONG|TULONG,
	SCON,		TANY,
		0,	0,
		"	ldl	AL,AR\n", },

/* byte/char reg <- reg or mem */
{ ASSIGN,	FOREFF|INAREG|FORCC,
	SAREG,		TCHAR|TUCHAR,
	SAREG|SNAME|SOREG|SCON,	TCHAR|TUCHAR,
		0,	RDEST|RESCC,
		"	ldb	AL,AR\n", },

/* byte mem <- reg */
{ ASSIGN,	FOREFF|FORCC,
	SNAME|SOREG,	TCHAR|TUCHAR,
	SAREG,		TCHAR|TUCHAR,
		0,	RESCC,
		"	ldb	AL,AR\n", },

/* byte mem <- const */
{ ASSIGN,	FOREFF,
	SNAME|SOREG,	TCHAR|TUCHAR,
	SCON,		TANY,
		0,	0,
		"	ldb	AL,AR\n", },

/* struct assignment */
{ STASG,	FOREFF|INAREG,
	SOREG|SNAME,	TANY,
	SAREG,		TPTRTO|TANY,
		NEEDS(NREG(B, 1), NSL(B)),	RDEST,
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
		"	ldb	A1,AL\n	extsb	A1\n", },

/* load unsigned char through pair register */
{ UMUL,		INAREG,
	SANY,		TANY,
	SOREG,		TUCHAR,
		XSL(A),	RESC1,
		"	ldb	A1,AL\n", },

/*
 * Logical/comparison operators.
 * OPLOG covers EQ, NE, LE, GE, LT, GT, ULE, UGE, ULT, UGT.
 */

/* compare word vs zero: use test */
{ OPLOG,	FORCC,
	SAREG|SNAME|SOREG,	TWORD,
	SZERO,	TANY,
		0,	RESCC,
		"	test	AL\n", },

/* compare pair vs zero: use testl */
{ OPLOG,	FORCC,
	SBREG|SNAME|SOREG,	TLONG|TULONG|TPOINT,
	SZERO,	TANY,
		0,	RESCC,
		"	testl	AL\n", },

/* compare word vs word */
{ OPLOG,	FORCC,
	SAREG|SNAME|SOREG,	TWORD,
	SAREG|SCON,		TWORD,
		0,	RESCC,
		"	cp	AL,AR\n", },

/* compare pair vs pair (long/ptr) */
{ OPLOG,	FORCC,
	SBREG|SNAME|SOREG,	TLONG|TULONG|TPOINT,
	SBREG|SCON,		TLONG|TULONG|TPOINT,
		0,	RESCC,
		"	cpl	AL,AR\n", },

/* compare char vs char */
{ OPLOG,	FORCC,
	SAREG|SNAME|SOREG,	TCHAR|TUCHAR,
	SAREG|SCON,		TCHAR|TUCHAR,
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

/* load signed char from mem into word register */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SOREG|SNAME,	TCHAR,
		NAREG,	RESC1,
		"	ldb	A1,AL\n	extsb	A1\n", },

/* load unsigned char from mem into word register */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SOREG|SNAME,	TUCHAR,
		NAREG,	RESC1,
		"	ldb	A1,AL\n", },

/* load address (lda) of SOREG/SNAME into pair register */
{ OPLTYPE,	INBREG,
	SANY,	TANY,
	SOREG|SNAME,	TPOINT|TLONG|TULONG,
		NBREG,	RESC1,
		"	lda	A1,AL\n", },

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
		"	negl	AL\n", },

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
		"	coml	AL\n", },

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

/* struct argument (by-value struct copy onto stack) */
{ STARG,	FOREFF,
	SBREG,		TPTRTO|TANY,
	SANY,		TSTRUCT,
		0,	0,
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
