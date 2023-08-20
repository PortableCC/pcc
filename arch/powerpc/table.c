/*	$Id$	*/
/*-
 * Copyright (c) 2007 Gregory McGarry <g.mcgarry@ieee.org>
 *
 * Permission to use, copy, modify, and distribute this software for any
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

/*
 * A template has five logical sections:
 *
 *	1) subtree (operator); goal to achieve (cookie)
 *	2) left node descendent of operator (node class; type)
 *	3) right node descendent of operator (node class; type)
 *	4) resource requirements (number of scratch registers);
 *	   subtree rewriting rule
 *	5) emitted instructions
 */

#include "pass2.h"

#define TUWORD	TUNSIGNED|TULONG
#define TSWORD	TINT|TLONG
#define TWORD	TUWORD|TSWORD

#if defined(ELFABI) || defined(AOUTABI)
#define HA16(x)	# x "@ha"
#define LO16(x)	# x "@l"
#elif defined(MACHOABI)
#define HA16(x)	"ha16(" # x ")"
#define LO16(x)	"lo16(" # x ")"
#else
#error undefined ABI
#endif

#define XSL(c)  NEEDS(NREG(c, 1), NSL(c))
#define	NLA0	NEEDS(NREG(A, 1), NSL(A), NEVER(R0))
#define NSCAA	NEEDS(NREG(A, 1), NSL(A), NLEFT(R3), NRES(R3))
#define NSCAB   NEEDS(NREG(B, 1), NLEFT(R3), NRES(R3R4))
#define NSCBA	NEEDS(NREG(A, 1), NLEFT(R3R4), NRES(R3))
#define NSCBB   NEEDS(NREG(B, 1), NLEFT(R3R4), NRES(R3R4))
#define NSCBC   NEEDS(NREG(C, 1), NLEFT(R3R4), NRES(F1), NEVER(F0))
#define NSCCB   NEEDS(NREG(B, 1), NLEFT(F1), NRES(R3R4), NEVER(F0))
#define NOL     NEEDS(NOLEFT(R0))
#define NOR     NEEDS(NORIGHT(R0))
#define NDIVA   NEEDS(NREG(A, 1), NLEFT(R3), NRIGHT(R4), NRES(R3))
#define NDIVB   NEEDS(NREG(B, 1), NLEFT(R3R4), NRIGHT(R5R6), NRES(R3R4))
#define NA      NEEDS(NREG(A, 1))
#define NB      NEEDS(NREG(B, 1))
#define NC      NEEDS(NREG(C, 1))
#define NA0     NEEDS(NREG(A, 1), NOLEFT(R0))
#define NAV0    NEEDS(NREG(A, 1), NEVER(R0))
#define NB0     NEEDS(NREG(B, 1), NOLEFT(R0))
#define NBV0    NEEDS(NREG(B, 1), NEVER(R0))


struct optab table[] = {
/* First entry must be an empty entry */
{ -1, FOREFF, SANY, TANY, SANY, TANY, 0, 0, "", }, 

/* PCONVs are not necessary */
{ PCONV,	INAREG,
	SAREG,	TWORD|TPOINT,
	SAREG,	TWORD|TPOINT,
		0,	RLEFT,
		COM "pointer conversion\n", },

/*
 * Conversions of integral types
 * SCONV are unary
 */

{ SCONV,	INAREG,
	SAREG,	TCHAR|TUCHAR,
	SAREG,	TCHAR|TUCHAR,
		0,	RLEFT,
		COM "convert between (u)char and (u)char\n", },

{ SCONV,	INAREG,
	SAREG,	TSHORT|TUSHORT,
	SAREG,	TSHORT|TUSHORT,
		0,	RLEFT,
		COM "convert between (u)short and (u)short\n", },

{ SCONV,	INAREG,
	SAREG,	TPOINT|TWORD,
	SAREG,	TWORD,
		0,	RLEFT,
		COM "convert a pointer/word to an int\n", },

{ SCONV,	INAREG,
	SAREG,	TPOINT,
	SAREG,	TPOINT,
		0,	RLEFT,
		COM "convert pointers\n", },

{ SCONV,	INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SBREG,	TLONGLONG|TULONGLONG,
		0,	RLEFT,
		COM "convert (u)longlong to (u)longlong\n", },

{ SCONV,	INAREG,
	SAREG,	TCHAR,
	SAREG,	TSHORT|TSWORD,
		XSL(A),	RESC1,
		"	extsb A1,AL" COM "convert char to short/int\n", },

{ SCONV,	INAREG,
	SAREG,	TUCHAR,
	SAREG,	TSHORT|TSWORD,
		0,	RLEFT,
		"	nop" COM "convert uchar to short/int\n", },

{ SCONV,	INAREG,
	SAREG,	TUCHAR,
	SAREG,	TUSHORT|TUWORD,
		0,	RLEFT,
		"	nop" COM "convert uchar to ushort/unsigned\n", },

/* XXX is this necessary? */
{ SCONV,	INAREG,
	SAREG,	TCHAR,
	SAREG,	TUSHORT|TUWORD,
		NLA0,	RESC1, //NSPECIAL|NAREG|NASL
		"	extsb A1,AL" COM "convert char to ushort/unsigned\n", },

{ SCONV,	INBREG | FEATURE_BIGENDIAN,
	SAREG,	TUCHAR|TUSHORT|TUNSIGNED,
	SBREG,	TLONGLONG|TULONGLONG,
		NEEDS(NREG(B, 1)), RESC1, // NBREG
		"	mr U1,AL" COM "convert uchar/ushort/uint to (u)longlong\n"
		"	li A1,0\n", },

{ SCONV,	INBREG,
	SAREG,	TUCHAR|TUSHORT|TUNSIGNED,
	SBREG,	TLONGLONG|TULONGLONG,
		NEEDS(NREG(B, 1)), RESC1, //NBREG
		"	mr A1,AL" COM "convert uchar/ushort/uint to (u)longlong\n"
		"	li U1,0\n", },

{ SCONV,	INBREG | FEATURE_BIGENDIAN,
	SAREG,	TCHAR|TSHORT|TSWORD,
	SBREG,	TULONGLONG|TLONGLONG,
		NEEDS(NREG(B, 1)), RESC1, // NBREG
		"	mr U1,AL" COM "convert char/short/int to ulonglong\n"
		"	srawi A1,AL,31\n", },

{ SCONV,	INBREG,
	SAREG,	TCHAR|TSHORT|TSWORD,
	SBREG,	TULONGLONG|TLONGLONG,
		NEEDS(NREG(B, 1)), RESC1, // NBREG
		"	mr A1,AL" COM "convert char/short/int to ulonglong\n"
		"	srawi U1,AL,31\n", },

{ SCONV,	INAREG,
	SAREG,	TSHORT|TUSHORT,
	SAREG,	TCHAR|TUCHAR,
		NLA0,	RESC1,	//NSPECIAL|NAREG|NASL
		"	andi. A1,AL,255" COM "convert (u)short to (u)char\n", },

/* extsh copies bit 16 of AL to upper 16 bits of A1 */
{ SCONV,	INAREG,
	SAREG,	TSHORT,
	SAREG,	TWORD,
		NEEDS(NREG(A, 1), NEVER(R0)),	RESC1,  // NAREG|NASL
		"	extsh A1,AL" COM "convert short to int\n", },

{ SCONV,	INAREG,
	SAREG,	TUSHORT,
	SAREG,	TWORD,
		NSCAA,	RESC1,
		COM "convert ushort to word\n", },

{ SCONV,	INAREG,
	SAREG,	TWORD,
	SAREG,	TCHAR|TUCHAR,
		NSCAA,	RESC1,
		"	andi. A1,AL,255" COM "convert (u)int to (u)char\n", },

{ SCONV,	INAREG,
	SAREG,	TWORD,
	SAREG,	TSHORT|TUSHORT,
		NSCAA,	RESC1,
		"	andi. A1,AL,65535" COM "convert (u)int to (u)short\n", },

{ SCONV,	INAREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SAREG,	TCHAR|TUCHAR,
		NSCBA,	RESC1,
		"	andi. A1,AL,255" COM "(u)longlong to (u)char\n", },

{ SCONV,	INAREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SAREG,	TSHORT|TUSHORT,
		NSCBA,	RESC1,
		"	andi. A1,AL,65535" COM "(u)longlong to (u)short\n", },

{ SCONV,	INAREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SAREG,	TWORD,
		NEEDS(NREG(A, 1)),	RESC1,
		"	mr A1,AL" COM "convert (u)longlong to (u)int/long\n", },

/* conversions on load from memory */

{ SCONV,	INAREG,
	SOREG,	TCHAR,
	SAREG,	TWORD,
		NLA0,	RESC1,
		"	lbz A1,AL" COM "convert char to int/long\n"
		"	extsb A1,A1\n", },

{ SCONV,	INAREG,
	SOREG,	TUCHAR,
	SAREG,	TWORD,
		NLA0,	RESC1,
		"	lbz A1,AL" COM "convert uchar to int/long\n", },

{ SCONV,	INAREG,
	SOREG,	TSHORT,
	SAREG,	TWORD,
		NLA0,	RESC1,
		"	lha A1,AL" COM "convert short to int/long\n", },

{ SCONV,	INAREG,
	SOREG,	TUSHORT,
	SAREG,	TWORD,
		NLA0,	RESC1,
		"	lhz A1,AL" COM "convert ushort to int/long\n", },

{ SCONV,	INAREG,
	SOREG,	TLONGLONG|TULONGLONG,
	SAREG,	TCHAR|TUCHAR,
		NLA0,	RESC1,
		"	lwz A1,AL" COM "(u)longlong to (u)char\n"
		"	andi. A1,A1,255\n", },

{ SCONV,	INAREG,
	SOREG,	TLONGLONG|TULONGLONG,
	SAREG,	TSHORT|TUSHORT,
		NLA0,	RESC1,
		"	lwz A1,AL" COM "(u)longlong to (u)short\n"
		"	andi. A1,A1,65535\n", },

{ SCONV,	INAREG,
	SOREG,	TLONGLONG|TULONGLONG,
	SAREG,	TWORD,
		NLA0,	RESC1,
		"	lwz A1,AL" COM "(u)longlong to (u)int\n", },

/*
 * floating-point conversions
 *
 * There doesn't appear to be an instruction to move values between
 * the floating-point registers and the general-purpose registers.
 * So values are bounced into memory...
 */

{ SCONV,	INCREG | FEATURE_HARDFLOAT,
	SCREG,	TFLOAT,
	SCREG,	TDOUBLE|TLDOUBLE,
		0,	RLEFT,
		COM "convert float to (l)double\n", },

/* soft-float */
{ SCONV,	INBREG,
	SAREG,	TFLOAT,
	SBREG,	TDOUBLE|TLDOUBLE,
		NSCAB,	RESC1,
		"ZF", },

{ SCONV,	INCREG | FEATURE_HARDFLOAT,
	SCREG,	TDOUBLE|TLDOUBLE,
	SCREG,	TFLOAT,
		NEEDS(NREG(C, 1)),	RESC1,
		"	frsp A1,AL" COM "convert (l)double to float\n", },

/* soft-float */
{ SCONV,	INAREG,
	SBREG,	TDOUBLE|TLDOUBLE,
	SAREG,	TFLOAT,
		NSCBA,	RESC1,
		"ZF", },

{ SCONV,	INCREG | FEATURE_HARDFLOAT,
	SCREG,	TDOUBLE|TLDOUBLE,
	SCREG,	TDOUBLE|TLDOUBLE,
		0,	RLEFT,
		COM "convert (l)double to (l)double\n", },

/* soft-float */
{ SCONV,	INBREG,
	SBREG,	TDOUBLE|TLDOUBLE,
	SBREG,	TDOUBLE|TLDOUBLE,
		0,	RLEFT,
		COM "convert (l)double to (l)double (soft-float)\n", },

{ SCONV,	INCREG | FEATURE_HARDFLOAT,
	SAREG,	TWORD,
	SCREG,	TFLOAT|TDOUBLE|TLDOUBLE,
		NEEDS(NREG(A, 1), NREG(C, 2)),	RESC3,
		"ZC", },

/* soft-float */
{ SCONV,	INAREG,
	SAREG,	TWORD,
	SAREG,	TFLOAT,
		NSCAA,	RESC1,
		"ZF", },

/* soft-float */
{ SCONV,	INBREG,
	SAREG,	TWORD,
	SBREG,	TDOUBLE|TLDOUBLE,
		NSCAB,	RESC1,
		"ZF", },

{ SCONV,	INAREG | FEATURE_HARDFLOAT,
	SOREG,	TFLOAT|TDOUBLE|TLDOUBLE,
	SAREG,	TWORD,
		NEEDS(NREG(A, 1), NREG(C, 2)),	RESC1,
		"ZC", },

/* soft-float */
{ SCONV,	INAREG,
	SAREG,	TFLOAT,
	SAREG,	TWORD,
		NSCAA,	RESC1,
		"ZF", },

/* soft-float */
{ SCONV,	INAREG,
	SBREG,	TDOUBLE|TLDOUBLE,
	SAREG,	TWORD,
		NSCAA,	RESC1,
		"ZF", },
	
{ SCONV,	INCREG | FEATURE_HARDFLOAT,
	SBREG,	TLONGLONG|TULONGLONG,
	SCREG,	TFLOAT|TDOUBLE|TLDOUBLE,
		NSCBC,	RESC1,
		"ZF", },

/* soft-float */
{ SCONV,	INAREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SAREG,	TFLOAT,
		NSCBA,	RESC1,
		"ZF", },

/* soft-float */
{ SCONV,	INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SBREG,	TDOUBLE|TLDOUBLE,
		NSCBB,	RESC1,
		"ZF", },

{ SCONV,	INBREG | FEATURE_HARDFLOAT,
	SCREG,	TFLOAT|TDOUBLE|TLDOUBLE,
	SBREG,	TLONGLONG|TULONGLONG,
		NSCCB,	RESC1,
		"ZF", },

/* soft-float */
{ SCONV,	INBREG,
	SAREG,	TFLOAT,
	SBREG,	TLONGLONG|TULONGLONG,
		NSCAB,	RESC1,
		"ZF", },

/* soft-float */
{ SCONV,	INBREG,
	SBREG,	TDOUBLE|TLDOUBLE,
	SBREG,	TLONGLONG|TULONGLONG,
		NSCBB,	RESC1,
		"ZF", },

/*
 * Subroutine calls.
 */

{ CALL,		FOREFF,
	SCON,	TANY,
	SANY,	TANY,
		0,	0,
		"	bl CL" COM "call (args, no result) to scon\n", },

{ UCALL,	FOREFF,
	SCON,	TANY,
	SANY,	TANY,
		0,	0,
		"	bl CL" COM "call (no args, no result) to scon\n", },

{ CALL,		INAREG,
	SCON,	TANY,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		XSL(A),	RESC1,	/* should be 0 */
		"	bl CL" COM "call (args, result) to scon\n", },

{ UCALL,	INAREG,
	SCON,	TANY,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		XSL(A),	RESC1,	/* should be 0 */
		"	bl CL" COM "call (no args, result) to scon\n", },

{ CALL,		INBREG,
	SCON,	TANY,
	SBREG,	TLONGLONG|TULONGLONG,
		XSL(B),	RESC1,	/* should be 0 */
		"	bl CL" COM "call (args, result) to scon\n", },

{ UCALL,	INBREG,
	SCON,	TANY,
	SBREG,	TLONGLONG|TULONGLONG,
		XSL(B),	RESC1,	/* should be 0 */
		"	bl CL" COM "call (no args, result) to scon\n", },

{ CALL,		INCREG | FEATURE_HARDFLOAT,
	SCON,	TANY,
	SCREG,	TFLOAT|TDOUBLE|TLDOUBLE,
		XSL(C),	RESC1,	/* should be 0 */
		"	bl CL" COM "call (args, result) to scon\n", },

{ UCALL,	INCREG | FEATURE_HARDFLOAT,
	SCON,	TANY,
	SCREG,	TFLOAT|TDOUBLE|TLDOUBLE,
		XSL(C),	RESC1,	/* should be 0 */
		"	bl CL" COM "call (no args, result) to scon\n", },
		
{ CALL,		INCREG | FEATURE_HARDFLOAT,
	SCREG,	TFLOAT|TDOUBLE|TLDOUBLE,
	SCREG,	TFLOAT|TDOUBLE|TLDOUBLE,
		XSL(C),	RESC1,
		"	bl CL" COM "call (args, result is fp) to fp\n", },

{ CALL,		INAREG,
	SCON,	TANY,
	SAREG,	TFLOAT,
		XSL(A),	RESC1,	/* should be 0 */
		"	bl CL" COM "call (args, result) to scon\n", },

{ UCALL,	INAREG,
	SCON,	TANY,
	SAREG,	TFLOAT,
		XSL(A),	RESC1,	/* should be 0 */
		"	bl CL" COM "call (no args, result) to scon\n", },

{ CALL,		INBREG,
	SCON,	TANY,
	SBREG,	TDOUBLE|TLDOUBLE,
		XSL(B),	RESC1,	/* should be 0 */
		"	bl CL" COM "call (args, result) to scon\n", },

{ UCALL,	INBREG,
	SCON,	TANY,
	SBREG,	TDOUBLE|TLDOUBLE,
		XSL(B),	RESC1,	/* should be 0 */
		"	bl CL" COM "call (no args, result) to scon\n", },



{ CALL,		FOREFF,
	SAREG,	TFTN,
	SANY,	TANY,
	NEEDS(NLEFT(R12)),	0,
		"	mtctr AL" COM "call (args, no result) to ctr\n"
		"	bctrl\n", },

{ UCALL,	FOREFF,
	SAREG,	TFTN,
	SANY,	TANY,
	NEEDS(NLEFT(R12)),	0,
		"	mtctr AL" COM "ucall (no args, no result) to ctr\n"
		"	bctrl\n", },

{ CALL,		INAREG,
	SAREG,	TFTN,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NEEDS(NREG(A, 1), NLEFT(R12)),	RESC1,
		"	mtctr AL" COM "call (args, result) to ctr\n"
		"	bctrl\n", },

{ UCALL,	INAREG,
	SAREG, TFTN,
	SAREG, TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NEEDS(NREG(A, 1), NLEFT(R12)),	RESC1,
		"	mtctr AL" COM "ucall (no args, result) to ctr\n"
		"	bctrl\n", },

	
{ CALL,		INCREG | FEATURE_HARDFLOAT,
	SAREG, TFTN,
	SCREG, TFLOAT|TDOUBLE|TLDOUBLE,
		XSL(C),	RESC1,
		"	mtctr AL" COM "call (args, result is fp) to fp\n"
		"	bctrl\n", },


/* struct return */
{ USTCALL,	FOREFF,
	SCON,	TANY,
	SANY,	TANY,
		0,	0,
		"	bl CL\n", },

{ USTCALL,	INAREG,
	SCON,	TANY,
	SANY,	TANY,
		XSL(A),	RESC1,	/* should be 0 */
		"	bl CL\n", },

{ USTCALL,	INAREG,
	SAREG,	TANY,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NEEDS(NREG(A, 1), NLEFT(R12)),	RESC1,
		"	mtctr AL"
		"	bctrl\n", },

{ STCALL,	FOREFF,
	SCON,	TANY,
	SANY,	TANY,
		0,	0,
		"	bl CL\n", },

{ STCALL,	INAREG,
	SCON,	TANY,
	SANY,	TANY,
		XSL(A),	RESC1,	/* should be 0 */
		"	bl CL\n", },

{ STCALL,	INAREG,
	SAREG,	TANY,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		XSL(A),	RESC1,
		"	mtctr AL"
		"	bctrl\n", },

/*
 * The next rules handle all binop-style operators.
 */

/* XXX AL cannot be R0 */
{ PLUS,		INAREG,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SSCON,	TANY,
		NLA0,	RESC1,
		"	addi A1,AL,AR" COM "addition of constant\n", },

/* XXX AL cannot be R0 */
{ PLUS,		INAREG,
	SAREG,	TWORD|TPOINT|TPTRTO|TCHAR|TUCHAR,
	SCON,	TANY,
		NLA0,	RESC1,
		"	addis A1, AL, " HA16(AR) COM "move label into register\n"
		"	addi A1, A1, " LO16(AR) "\n", },


/* XXX AL cannot be R0 */
{ PLUS,		INAREG|FORCC,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SSCON,	TANY,
		NLA0,	RESC1|RESCC,
		"	addic. A1,AL,AR" COM "addition of constant\n", },

{ PLUS,		INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SSCON,	TANY,
		XSL(B),	RESC1,
		"	addic A1,AL,AR" COM "64-bit addition of constant\n"
		"	addze U1,UL\n", },

{ PLUS,		INAREG,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NLA0,	RESC1,
		"	add A1,AL,AR\n", },

{ PLUS,		INAREG|FORCC,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NLA0,	RESC1|RESCC,
		"	add. A1,AL,AR\n", },

{ PLUS,		INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SBREG,	TLONGLONG|TULONGLONG,
		XSL(B),	RESC1,
		"	addc A1,AL,AR" COM "64-bit add\n"
		"	adde U1,UL,UR\n", },

{ PLUS,		INCREG | FEATURE_HARDFLOAT,
	SCREG,	TFLOAT,
	SCREG,	TFLOAT,
		NC,		RESC1,
		"	fadds A1,AL,AR" COM "float add\n", },

{ PLUS,		INAREG,
	SAREG,	TFLOAT,
	SAREG,	TFLOAT,
		NA0,	 RESC1,
		"ZF", },

{ PLUS,		INCREG | FEATURE_HARDFLOAT,
	SCREG,	TDOUBLE|TLDOUBLE,
	SCREG,	TDOUBLE|TLDOUBLE,
		XSL(C),	RESC1,
		"	fadd A1,AL,AR" COM "(l)double add\n", },

/* soft-float */
{ PLUS,		INBREG,
	SBREG,	TDOUBLE|TLDOUBLE,
	SBREG,	TDOUBLE|TLDOUBLE,
		NDIVB,	RESC1,
		"ZF", },

{ MINUS,	INAREG,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SSCON,	TANY,
		NLA0,	RESC1,
		"	addi A1,AL,-AR\n", },

{ MINUS,	INAREG|FORCC,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SSCON,	TANY,
		NLA0,	RESC1|RESCC,
		"	addic. A1,AL,-AR\n", },

{ MINUS,	INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SSCON,	TANY,
		XSL(B),	RESC1,
		"	addic A1,AL,-AR\n"
		"	addme U1,UL\n", },

{ MINUS,	INAREG,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NLA0,	RESC1,
		"	subf A1,AR,AL\n", },

{ MINUS,	INAREG|FORCC,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NLA0,	RESC1|RESCC,
		"	subf. A1,AR,AL\n", },

{ MINUS,	INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SBREG,	TLONGLONG|TULONGLONG,
		XSL(B),	RESC1,
		"	subfc A1,AR,AL" COM "64-bit subtraction\n"
		"	subfe U1,UR,UL\n", },

{ MINUS,	INCREG | FEATURE_HARDFLOAT,
	SCREG,	TFLOAT,
	SCREG,	TFLOAT,
		NC,	RESC1,
		"	fsubs A1,AL,AR\n", },

{ MINUS,	INAREG,
	SAREG,	TFLOAT,
	SAREG,	TFLOAT,
		NEEDS(NREG(A, 1), NLEFT(R3), NRIGHT(R4)),	RLEFT,
		"ZF", },

{ MINUS,		INCREG | FEATURE_HARDFLOAT,
	SCREG,	TDOUBLE|TLDOUBLE,
	SCREG,	TDOUBLE|TLDOUBLE,
		XSL(C),	RESC1,
		"	fsub A1,AL,AR" COM "(l)double sub\n", },

/* soft-float */
{ MINUS,		INBREG,
	SBREG,	TDOUBLE|TLDOUBLE,
	SBREG,	TDOUBLE|TLDOUBLE,
		NDIVB,	RESC1,
		"ZF", },


/*
 * The next rules handle all shift operators.
 */

{ LS,	INAREG,
	SAREG,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
		XSL(A),	RESC1,
		"	slw A1,AL,AR" COM "left shift\n", },

{ LS,	INAREG|FORCC,
	SAREG,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
		XSL(A),	RESC1,
		"	slw. A1,AL,AR" COM "left shift\n", },

{ LS,	INAREG,
	SAREG,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SCON,	TANY,
		XSL(A),	RESC1,
		"	slwi A1,AL,AR" COM "left shift by constant\n", },

{ LS,	INAREG|FORCC,
	SAREG,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SCON,	TANY,
		XSL(A),	RESC1,
		"	slwi. A1,AL,AR" COM "left shift by constant\n", },

{ LS,	INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SCON,	TANY,
		NB,	RESC1,
		"ZO", },

{ LS,	INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SAREG,	TANY,
		NEEDS(NREG(B, 1), NLEFT(R3R4), NRIGHT(R5), NRES(R3R4)),	RESC1,
		"ZE", },

{ RS,	INAREG,
	SAREG,	TUWORD|TUSHORT|TUCHAR,
	SAREG,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
		XSL(A),	RESC1,
		"	srw A1,AL,AR" COM "right shift\n", },

{ RS,	INAREG,
	SAREG,	TSWORD|TSHORT|TCHAR,
	SAREG,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
		XSL(A),	RESC1,
		"	sraw A1,AL,AR" COM "arithmetic right shift\n", },

{ RS,	INAREG|FORCC,
	SAREG,	TUWORD|TUSHORT|TUCHAR,
	SAREG,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
		XSL(A),	RESC1,
		"	srw. A1,AL,AR" COM "right shift\n", },

{ RS,	INAREG|FORCC,
	SAREG,	TSWORD|TSHORT|TCHAR,
	SAREG,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
		XSL(A),	RESC1,
		"	sraw. A1,AL,AR" COM "arithmetic right shift\n", },

{ RS,	INAREG,
	SAREG,	TUWORD|TUSHORT|TUCHAR,
	SCON,	TANY,
		XSL(A),	RESC1,
		"	srwi A1,AL,AR" COM "right shift by constant\n", },

{ RS,	INAREG,
	SAREG,	TSWORD|TSHORT|TCHAR,
	SCON,	TANY,
		XSL(A),	RESC1,
		"	srawi A1,AL,AR" COM "arithmetic right shift by constant\n", },

{ RS,	INAREG|FORCC,
	SAREG,	TUWORD|TUSHORT|TUCHAR,
	SCON,	TANY,
		XSL(A),	RESC1,
		"	srwi. A1,AL,AR" COM "right shift by constant\n", },

{ RS,	INAREG|FORCC,
	SAREG,	TSWORD|TSHORT|TCHAR,
	SCON,	TANY,
		XSL(A),	RESC1,
		"	srawi. A1,AL,AR" COM "right shift by constant\n", },

{ RS,	INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SCON,	TANY,
		NB,	RESC1,
		"ZO" },

{ RS,	INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SAREG,	TANY,
		NEEDS(NREG(B, 1), NLEFT(R3R4), NRIGHT(R5), NRES(R3R4)),	RESC1,
		"ZE", },

/*
 * The next rules takes care of assignments. "=".
 */
 

{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SSCON,		TANY,
		0,	RDEST,
		"	li AL,AR\n", },

{ ASSIGN,	FOREFF|INBREG,
	SBREG,		TLONGLONG|TULONGLONG,
	SSCON,		TANY,
		0,	RDEST,
		"	li AL,AR\n"
		"	li UL,UR\n", },

{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SCON,		TANY,
		NOL,	RDEST,
		"	lis AL," HA16(AR) "\n"
		"	addi AL,AL," LO16(AR) "\n", },

{ ASSIGN,	FOREFF|INBREG,
	SBREG,		TLONGLONG|TULONGLONG,
	SCON,		TANY,
		NOL,	RDEST,
		"	lis AL," HA16(AR) "\n"
		"	addi AL,AL," LO16(AR) "\n"
		"	lis UL," HA16(UR) "\n"
		"	addi UL,UL," LO16(UR) "\n", },

{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TWORD|TPOINT,
	SOREG,		TWORD|TPOINT,
		NOR,	RDEST,
		"	lwz AL,AR" COM "assign oreg to reg\n", },

{ ASSIGN,	FOREFF|INBREG,
	SBREG,		TLONGLONG|TULONGLONG,
	SOREG,		TLONGLONG|TULONGLONG,
		NOR,	RDEST,
		"	lwz AL,AR" COM "assign llong to reg\n"
		"	lwz UL,UR\n" },
#if 1
{ ASSIGN,	FOREFF|INAREG,
	SBREG,		TLONGLONG|TULONGLONG,
	SNAME,		TLONGLONG|TULONGLONG,
		NOL,	RDEST,
		"	lis AL," HA16(AR) COM "assign 64-bit sname to reg\n"
		"	lwz AL," LO16(AR) "(AL)\n"
		"	lis UL," HA16(UR) "\n"
		"	lwz UL," LO16(UR) "(UL)\n", },
#endif

{ ASSIGN,	FOREFF|INBREG,
	SBREG,		TLONGLONG|TULONGLONG,
	SOREG,		TSWORD,
		NOR,	RDEST,
		"	lwz AL,AR" COM "load int/pointer into llong\n"
		"	srawi UL,AR,31\n" },

{ ASSIGN,	FOREFF|INBREG,
	SBREG,		TLONGLONG|TULONGLONG,
	SOREG,		TUNSIGNED|TPOINT,
		NOR,	RDEST,
		"	lwz AL,AR" COM "load uint/pointer into (u)llong\n"
		"	li UL,0\n" },

{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TUCHAR,
	SOREG,		TUCHAR,
		NOR,	RDEST,
		"	lbz AL,AR\n", },

{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TCHAR,
	SOREG,		TCHAR,
		NOR,	RDEST,
		"	lbz AL,AR\n"
		"	extsb AL,AL\n", },
#if 1
{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TCHAR,
	SNAME,		TCHAR,
		NOL,	RDEST,
		"	lis AL," HA16(AR) COM "assign char sname to reg\n"
		"	lbz AL," LO16(AR) "(AL)\n"
		"	extsb AL,AL\n", },
#endif
{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TWORD|TPOINT,
	SOREG,		TSHORT,
		NOR,	RDEST,
		"	lha AL,AR\n", },

{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TWORD|TPOINT,
	SOREG,		TUSHORT,
		NOR,	RDEST,
		"	lhz AL,AR\n", },
#if 1
{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TWORD,
	SNAME,		TSHORT,
		NOL,	RDEST,
		"	lis AL," HA16(AR) "\n"
		"	lha AL," LO16(AR) "(AL)\n", },

{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TWORD,
	SNAME,		TUSHORT,
		NOL,	RDEST,
		"	lis AL," HA16(AR) "\n"
		"	lhz AL," LO16(AR) "(AL)\n", },
#endif
{ ASSIGN,	FOREFF|INAREG,
	SOREG,		TWORD|TPOINT,
	SAREG,		TWORD|TPOINT,
		NOL,	RDEST,
		"	stw AR,AL\n", },

{ ASSIGN,	FOREFF|INBREG,
	SOREG,		TLONGLONG|TULONGLONG,
	SBREG,		TLONGLONG|TULONGLONG,
		NOL,	RDEST,
		"	stw AR,AL" COM "store 64-bit value\n"
		"	stw UR,UL\n", },

{ ASSIGN,	FOREFF|INBREG,
	SNAME,		TLONGLONG|TULONGLONG,
	SBREG,		TLONGLONG|TULONGLONG,
		NEEDS(NREG(B, 1), NEVER(R0)),	RDEST,
		"	lis A1," HA16(AL) COM "assign reg to 64-bit sname\n"
		"	stw AR," LO16(AL) "(A1)\n"
		"	lis U1," HA16(UL) "\n"
		"	stw UR," LO16(UL) "(U1)\n", },

{ ASSIGN,	FOREFF|INAREG,
	SOREG,		TCHAR|TUCHAR,
	SAREG,		TCHAR|TUCHAR,
		NOL,	RDEST,
		"	stb AR,AL\n", },

{ ASSIGN,	FOREFF|INAREG,
	SOREG,		TSHORT|TUSHORT,
	SAREG,		TSHORT|TUSHORT,
		NOL,	RDEST,
		"	sth AR,AL\n", },

{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,		TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		0,	RDEST,
		"	mr AL,AR" COM "assign AR to AL\n", },

{ ASSIGN,      FOREFF|INBREG,
        SBREG,	TLONGLONG|TULONGLONG,
        SBREG,	TLONGLONG|TULONGLONG,
                0,  RDEST,
		"	mr AL,AR" COM "assign UR:AR to UL:AL\n"
                "	mr UL,UR\n", },


{ STASG,	INAREG|FOREFF,
	SOREG|SNAME,	TANY,
	SAREG,		TPTRTO|TANY,
		NEEDS(NEVER(R3), NRIGHT(R4), NEVER(R5)),	RDEST,
		"ZQ", },

{ ASSIGN,	FOREFF|INCREG | FEATURE_HARDFLOAT,
	SOREG,		TFLOAT,
	SCREG,		TFLOAT,
		0,	RDEST,
		"	stfs AR,AL" COM "store float\n", },

/* soft-float */
{ ASSIGN,	FOREFF|INAREG,
	SOREG,		TFLOAT,
	SAREG,		TFLOAT,
		0,	RDEST,
		"	stw AR,AL" COM "store float (soft-float)\n", },

{ ASSIGN,	FOREFF|INCREG | FEATURE_HARDFLOAT,
	SCREG,		TFLOAT,
	SOREG,		TFLOAT,
		0,	RDEST,
		"	lfs AL,AR" COM "load float\n", },

/* soft-float */
{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TFLOAT,
	SOREG,		TFLOAT,
		0,	RDEST,
		"	lwz AL,AR" COM "load float (soft-float)\n", },

{ ASSIGN,	FOREFF|INCREG | FEATURE_HARDFLOAT,
	SCREG,		TFLOAT,
	SCREG,		TFLOAT,
		0,	RDEST,
		"	fmr AL,AR" COM "assign AR to AL\n", },

/* soft-float */
{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TFLOAT,
	SAREG,		TFLOAT,
		0,	RDEST,
		"	mr AL,AR" COM "assign AR to AL\n", },

{ ASSIGN,	FOREFF|INCREG | FEATURE_HARDFLOAT,
	SOREG,		TDOUBLE|TLDOUBLE,
	SCREG,		TDOUBLE|TLDOUBLE,
		0,	RDEST,
		"	stfd AR,AL" COM "store (l)double\n", },

/* soft-float */
{ ASSIGN,	FOREFF|INBREG,
	SOREG,		TDOUBLE|TLDOUBLE,
	SBREG,		TDOUBLE|TLDOUBLE,
		0,	RDEST,
		"	stw AR,AL" COM "store (l)double (soft-float)\n"
		"	stw UR,UL\n", },

/* soft-float */
{ ASSIGN,	FOREFF|INBREG,
	SNAME,		TDOUBLE|TLDOUBLE,
	SBREG,		TDOUBLE|TLDOUBLE,
		NA0,	RDEST,
		"	lis A1," HA16(AL) "\n"
		"	stw AR," LO16(AL) "(A1)\n"
		"	lis A1," HA16(UL) "\n"
		"	stw UR," LO16(UL) "(A1)\n", },

{ ASSIGN,	FOREFF|INCREG | FEATURE_HARDFLOAT,
	SCREG,		TDOUBLE|TLDOUBLE,
	SOREG,		TDOUBLE|TLDOUBLE,
		0,	RDEST,
		"	lfd AL,AR" COM "load (l)double\n", },

/* soft-float */
{ ASSIGN,	FOREFF|INBREG,
	SBREG,		TDOUBLE|TLDOUBLE,
	SOREG,		TDOUBLE|TLDOUBLE,
		0,	RDEST,
		"	lwz AL,AR" COM "load (l)double (soft-float)\n"
		"	lwz UL,UR\n", },

{ ASSIGN,	FOREFF|INCREG | FEATURE_HARDFLOAT,
	SCREG,		TDOUBLE|TLDOUBLE,
	SCREG,		TDOUBLE|TLDOUBLE,
		0,	RDEST,
		"	fmr AL,AR" COM "assign AR to AL\n", },

/* soft-float */
{ ASSIGN,	FOREFF|INBREG,
	SBREG,		TDOUBLE|TLDOUBLE,
	SBREG,		TDOUBLE|TLDOUBLE,
		0,	RDEST,
		"	mr AL,AR" COM "assign AR to AL\n"
		"	mr UL,UR\n", },

/*
 * DIV/MOD/MUL 
 */

{ DIV,	INAREG,
	SAREG,	TUWORD|TPOINT|TUSHORT|TUCHAR,
	SAREG,	TUWORD|TPOINT|TUSHORT|TUCHAR,
		XSL(A),	RESC1,
		"	divwu A1,AL,AR\n", },

{ DIV,	INAREG|FORCC,
	SAREG,	TUWORD|TPOINT|TUSHORT|TUCHAR,
	SAREG,	TUWORD|TPOINT|TUSHORT|TUCHAR,
		XSL(A),	RESC1|RESCC,
		"	divwu. A1,AL,AR\n", },

{ DIV,	INAREG,
	SAREG,	TWORD|TSHORT|TCHAR,
	SAREG,	TWORD|TSHORT|TCHAR,
		XSL(A),	RESC1,
		"	divw A1,AL,AR\n", },

{ DIV,	INAREG|FORCC,
	SAREG,	TWORD|TSHORT|TCHAR,
	SAREG,	TWORD|TSHORT|TCHAR,
		XSL(A),	RESC1|RESCC,
		"	divw. A1,AL,AR\n", },

{ DIV,	INBREG,
	SBREG,		TLONGLONG|TULONGLONG,
	SBREG,		TLONGLONG|TULONGLONG,
		NDIVB,	RESC1,
		"ZE", },

{ DIV, INCREG | FEATURE_HARDFLOAT,
	SCREG,		TFLOAT,
	SCREG,		TFLOAT,
		XSL(C),	RESC1,
		"	fdivs A1,AL,AR" COM "float divide\n", },

/* soft-float */
{ DIV, INAREG,
	SAREG,		TFLOAT,
	SAREG,		TFLOAT,
		NDIVA,	RESC1,
		"ZF", },

{ DIV, INCREG | FEATURE_HARDFLOAT,
	SCREG,		TDOUBLE|TLDOUBLE,
	SCREG,		TDOUBLE|TLDOUBLE,
		XSL(C),	RESC1,
		"	fdiv A1,AL,AR" COM "(l)double divide\n", },

/* soft-float */
{ DIV, INBREG,
	SBREG,		TDOUBLE|TLDOUBLE,
	SBREG,		TDOUBLE|TLDOUBLE,
		NDIVB,	RESC1,
		"ZF", },

{ MOD,	INAREG,
	SAREG,	TUWORD|TPOINT|TUSHORT|TUCHAR,
	SAREG,	TUWORD|TPOINT|TUSHORT|TUCHAR,
		NA,	RESC1,
		"	divwu A1,AL,AR" COM "unsigned modulo\n"
		"	mullw A1,A1,AR\n"
		"	subf A1,A1,AL\n", },

{ MOD,	INAREG,
	SAREG,	TWORD|TSHORT|TCHAR,
	SAREG,	TWORD|TSHORT|TCHAR,
		NA,	RESC1,
		"	divw A1,AL,AR" COM "signed modulo\n"
		"	mullw A1,A1,AR\n"
		"	subf A1,A1,AL\n", },

{ MOD,	INBREG,
	SBREG,		TLONGLONG|TULONGLONG,
	SBREG,		TLONGLONG|TULONGLONG,
		NDIVB,	RESC1,
		"ZE", },

{ MUL,	INAREG,
	SAREG,		TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SSCON,		TANY,
		XSL(A),	RESC1,
		"	mulli A1,AL,AR\n", },

{ MUL,	INAREG|FORCC,
	SAREG,		TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SSCON,		TANY,
		XSL(A),	RESC1|RESCC,
		"	mulli. A1,AL,AR\n", },

{ MUL,	INAREG,
	SAREG,		TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,		TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		XSL(A),	RESC1,
		"	mullw A1,AL,AR\n", },

{ MUL,	INAREG|FORCC,
	SAREG,		TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,		TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		XSL(A),	RESC1|RESCC,
		"	mullw. A1,AL,AR\n", },

{ MUL,	INBREG,
	SAREG,		TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,		TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NB,	RESC1,
		"	mullw A1,AL,AR\n"
		"	mulhw U1,AL,AR\n", },

{ MUL,	INBREG,
	SBREG,		TLONGLONG|TULONGLONG,
	SBREG,		TLONGLONG|TULONGLONG,
		NB,	RESC1,
		"	mullw A1,AL,AR\n"
		"	mulhw U1,AL,AR\n", },

{ MUL, INCREG | FEATURE_HARDFLOAT,
	SCREG,		TFLOAT,
	SCREG,		TFLOAT,
		XSL(C),	RESC1,
		"	fmuls A1,AL,AR" COM "float multiply\n", },

/* soft-float */
{ MUL, INAREG,
	SAREG,		TFLOAT,
	SAREG,		TFLOAT,
		NDIVA,	RESC1,
		"ZF", },

{ MUL, INCREG | FEATURE_HARDFLOAT,
	SCREG,		TDOUBLE|TLDOUBLE,
	SCREG,		TDOUBLE|TLDOUBLE,
		XSL(C),	RESC1,
		"	fmul A1,AL,AR" COM "(l)double multiply\n", },

/* soft-float */
{ MUL, INBREG,
	SBREG,		TDOUBLE|TLDOUBLE,
	SBREG,		TDOUBLE|TLDOUBLE,
		NDIVB,	RESC1,
		"ZF", },

/*
 * Indirection operators.
 */

{ UMUL,	INAREG,
	SANY,		TANY,
	SOREG|SNAME,	TWORD|TPOINT,
		NA0,	RESC1,
		"	lwz A1,AL" COM "word load\n", },

{ UMUL,	INAREG,
	SANY,		TANY,
	SOREG|SNAME,	TCHAR,
		NA0,	RESC1,
		"	lbz A1,AL" COM "char load\n"
		"	extsb A1,A1\n", },

{ UMUL,	INAREG,
	SANY,		TANY,
	SOREG|SNAME,	TUCHAR,
		NA0,	RESC1,
		"	lbz A1,AL" COM "uchar load\n", },

{ UMUL,	INAREG,
	SANY,		TANY,
	SOREG|SNAME,	TSHORT,
		NA0,	RESC1,
		"	lha A1,AL" COM "short load\n", },

{ UMUL,	INAREG,
	SANY,		TANY,
	SOREG|SNAME,	TUSHORT,
		NA0,	RESC1,
		"	lhz A1,AL" COM "ushort load\n", },

{ UMUL, INBREG,
	SANY,		TANY,
	SOREG|SNAME,	TLONGLONG|TULONGLONG,
		NB,	RESC1,
		"	lwz A1,AL" COM "64-bit load\n"
		"	lwz U1,UL\n", },

{ UMUL, INCREG | FEATURE_HARDFLOAT,
	SANY,		TANY,
	SOREG|SNAME,	TFLOAT,
		NC,	RESC1,
		"	lfs A1,AL" COM "float load\n", },

{ UMUL, INAREG,
	SANY,		TANY,
	SOREG|SNAME,	TFLOAT,
		NA,	RESC1,
		"	lwz A1,AL" COM "float load (soft-float)\n", },

{ UMUL, INCREG | FEATURE_HARDFLOAT,
	SANY,		TANY,
	SOREG|SNAME,	TDOUBLE|TLDOUBLE,
		NC,	RESC1,
		"	lfd A1,AL" COM "(l)double load\n", },

{ UMUL, INBREG,
	SANY,		TANY,
	SOREG|SNAME,	TDOUBLE|TLDOUBLE,
		NB0,	RESC1,
		"	lwz A1,AL" COM "(l)double load (soft-float)\n"
		"	lwz U1,UL\n", },

#if 0
{ UMUL, INAREG,
	SANY,		TANY,
	SAREG,		TWORD|TPOINT,
		NA,	RESC1,
		"	lwz A1,(AL)" COM "word load\n", },
#endif

/*
 * Logical/branching operators
 */

/* compare with constant */
{ OPLOG,	FORCC,
	SAREG,	TSWORD|TSHORT|TCHAR,
	SSCON,	TANY,
		0, 	RESCC,
		"	cmpwi AL,AR\n", },

/* compare with constant */
{ OPLOG,	FORCC,
	SAREG,	TUWORD|TPOINT|TUSHORT|TUCHAR,
	SSCON,	TANY,
		0, 	RESCC,
		"	cmplwi AL,AR\n", },

/* compare with register */
{ OPLOG,	FORCC,
	SAREG,	TSWORD|TSHORT|TCHAR,
	SAREG,	TSWORD|TSHORT|TCHAR,
		0, 	RESCC,
		"	cmpw AL,AR\n", },

/* compare with register */
{ OPLOG,	FORCC,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		0, 	RESCC,
		"	cmplw AL,AR\n", },

/* compare with register */
{ OPLOG,	FORCC,
	SBREG,	TLONGLONG|TULONGLONG,
	SBREG,	TLONGLONG|TULONGLONG,
		0, 	RESCC,
		"ZD", },

/* compare with register */
{ OPLOG,	FORCC | FEATURE_HARDFLOAT,
	SCREG,	TFLOAT|TDOUBLE|TLDOUBLE,
	SCREG,	TFLOAT|TDOUBLE|TLDOUBLE,
		0,	RESCC,
		"	fcmpu 0,AL,AR\n", },

/* soft-float */
{ OPLOG,	FORCC,
	SAREG,	TFLOAT,
	SAREG,	TFLOAT,
		NDIVA,	RESCC,
		"ZF\n", },

/* soft-float */
{ OPLOG,	FORCC,
	SBREG,	TDOUBLE|TLDOUBLE,
	SBREG,	TDOUBLE|TLDOUBLE,
		NEEDS(NREG(B, 1), NLEFT(R3R4), NRIGHT(R5R6), NRES(R3)),	RESCC,
		"ZF", },

{ OPLOG,	FORCC,
	SANY,	TANY,
	SANY,	TANY,
		NEEDS(NREWRITE),	0,
		"diediedie!", },

/* AND/OR/ER */
{ AND,	INAREG,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NLA0,	RESC1|RESCC,
		"	and A1,AL,AR\n", },

{ AND,	INAREG|FORCC,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NLA0,	RESC1,
		"	and. A1,AL,AR\n", },

/* AR must be positive */
{ AND,	INAREG|FORCC,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SPCON,	TANY,
		NLA0,	RESC1|RESCC,
		"	andi. A1,AL,AR\n", },

{ AND,	INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SBREG,	TLONGLONG|TULONGLONG,
		XSL(B),	RESC1,
		"	and A1,AL,AR" COM "64-bit and\n"
		"	and U1,UL,UR\n" },

{ AND,	INBREG|FORCC,
	SBREG,	TLONGLONG|TULONGLONG,
	SPCON,	TANY,
		XSL(B),	RESC1|RESCC,
		"	andi. A1,AL,AR" COM "64-bit and with constant\n"
		"	li U1,0\n" },

{ OR,	INAREG,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NLA0,	RESC1,
		"	or A1,AL,AR\n", },

{ OR,	INAREG|FORCC,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NLA0,	RESC1|RESCC,
		"	or. A1,AL,AR\n", },

{ OR,	INAREG,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SPCON,	TANY,
		XSL(A),	RESC1,
		"	ori A1,AL,AR\n", },

{ OR,	INAREG|FORCC,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SPCON,	TANY,
		XSL(A),	RESC1|RESCC,
		"	ori. A1,AL,AR\n", },

{ OR,	INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SBREG,	TLONGLONG|TULONGLONG,
		XSL(B),	RESC1,
		"	or A1,AL,AR" COM "64-bit or\n"
		"	or U1,UL,UR\n" },

{ OR,	INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SPCON,	TANY,
		XSL(B),	RESC1,
		"	ori A1,AL,AR" COM "64-bit or with constant\n" },

{ OR,	INBREG|FORCC,
	SBREG,	TLONGLONG|TULONGLONG,
	SPCON,	TANY,
		XSL(B),	RESC1|RESCC,
		"	ori. A1,AL,AR" COM "64-bit or with constant\n" },

{ ER,	INAREG,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NLA0,	RESC1,
		"	xor A1,AL,AR\n", },

{ ER,	INAREG|FORCC,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NLA0,	RESC1|RESCC,
		"	xor. A1,AL,AR\n", },

{ ER,	INAREG,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SPCON,	TANY,
		NLA0,	RESC1,
		"	xori A1,AL,AR\n", },

{ ER,	INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SBREG,	TLONGLONG|TULONGLONG,
		XSL(B),	RESC1,
		"	xor A1,AL,AR" COM "64-bit xor\n"
		"	xor U1,UL,UR\n" },

{ ER,	INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SPCON,	TANY,
		XSL(B),	RESC1,
		"	xori A1,AL,AR" COM "64-bit xor with constant\n" },

/*
 * Jumps.
 */
{ GOTO, 	FOREFF,
	SCON,	TANY,
	SANY,	TANY,
		0,	RNOP,
		"	b LL\n", },

{ GOTO, 	FOREFF,
	SAREG,	TANY,
	SANY,	TANY,
		0,	RNOP,
		"	mtctr AL\n"
		"	bctr\n", },

/*
 * Convert LTYPE to reg.
 */

#if defined(ELFABI)
{ OPLTYPE,	INAREG | FEATURE_PIC,
	SANY,		TANY,
	SNAME,		TANY,
		NA,	RESC1,
		"	lwz A1,AL" COM "elfabi pic load\n", },
#endif

{ OPLTYPE,      INBREG,
        SANY,   	TANY,
        SOREG,		TLONGLONG|TULONGLONG,
                NB,  RESC1,
                "	lwz A1,AL" COM "load llong from memory\n"
		"	lwz U1,UL\n", },

{ OPLTYPE,      INBREG,
        SANY,   	TANY,
        SNAME,		TLONGLONG|TULONGLONG,
                NB,  RESC1,
		"	lis A1," HA16(AL) COM "load llong from sname\n"
		"	lwz A1," LO16(AL) "(A1)\n"
		"	lis U1," HA16(UL) "\n"
		"	lwz U1," LO16(UL) "(U1)\n", },

{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SOREG,		TWORD|TPOINT,
		NA,	RESC1,
		"	lwz A1,AL" COM "load word from memory\n", },

{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SNAME,		TWORD|TPOINT,
		NA0,	RESC1,
		"	lis A1," HA16(AL) COM "load word from sname\n"
		"	lwz A1," LO16(AL) "(A1)\n", },

{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SOREG,		TCHAR,
		NA,	RESC1,
		"	lbz A1,AL" COM "load char from memory\n"
		"	extsb A1,A1\n", },

{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SNAME,		TCHAR,
		NAV0,	RESC1,
		"	lis A1," HA16(AL) COM "load char from sname\n"
		"	lbz A1," LO16(AL) "(A1)\n"
		"	extsb A1,A1\n", },

{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SOREG,		TUCHAR,
		NA,	RESC1,
		"	lbz A1,AL" COM "load uchar from memory\n", },

{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SNAME,		TUCHAR,
		NAV0,	RESC1,
		"	lis A1," HA16(AL) COM "load uchar from sname\n"
		"	lbz A1," LO16(AL) "(A1)\n", },

/* load short from memory */
{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SOREG,		TSHORT,
		NA,	RESC1,
		"	lha A1,AL" COM "load short from memory\n", },

{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SOREG,		TUSHORT,
		NA,	RESC1,
		"	lhz A1,AL" COM "load ushort from memory\n", },

{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SNAME,		TSHORT,
		NAV0,	RESC1,
		"	lis A1," HA16(AL) COM "load short from sname\n"
		"	lha A1," LO16(AL) "(A1)\n", },

{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SNAME,		TUSHORT,
		NAV0,	RESC1,
		"	lis A1," HA16(AL) COM "load ushort from sname\n"
		"	lhz A1," LO16(AL) "(A1)\n", },

{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SSCON,		TANY,
		NA,	RESC1,
		"	li A1,AL" COM "load 16-bit constant\n", },

{ OPLTYPE,	INBREG,
	SANY,	TANY,
	SSCON,	TANY,
		NB,	RESC1,
		"	li A1,AL" COM "load 16-bit constant\n"
		"	li U1,UL\n", },

{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SCON,	TANY,
		NLA0,	RESC1,
		"	lis A1," HA16(AL) COM "reload constant into register\n"
		"	addi A1,A1," LO16(AL) "\n", },

{ OPLTYPE,	INBREG,
	SANY,	TANY,
	SCON,	TANY,
		NB,	RESC1,
		"	lis A1," HA16(AL) COM "load constant into register\n"
		"	addi A1,A1," LO16(AL) "\n"
		"	lis U1," HA16(UL) "\n"
		"	addi U1,U1," LO16(UL) "\n", },

{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SAREG,	TANY,
		NA,	RESC1,
		"	mr A1,AL" COM "load leaf AL into A1\n" },

{ OPLTYPE,      INBREG,
        SANY,   TANY,
        SBREG,	TANY,
                NB,  RESC1,
		"	mr A1,AL" COM "load UL:AL into U1:A1\n"
                "       mr U1,UL\n", },

{ OPLTYPE,      INCREG,
        SANY,   TANY,
        SCREG,	TFLOAT|TDOUBLE|TLDOUBLE,
                NC,  RESC1,
		"	fmr A1,AL" COM "load AL into A1\n", },

{ OPLTYPE,	INCREG | FEATURE_HARDFLOAT,
	SANY,		TANY,
	SOREG,		TFLOAT,
		NC,	RESC1,
		"	lfs A1,AL" COM "load float\n", },

/* soft-float */
{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SOREG,		TFLOAT,
		NA,	RESC1,
		"	lwz A1,AL" COM "load float (soft-float)\n", },

{ OPLTYPE,	INCREG | FEATURE_HARDFLOAT,
	SANY,		TANY,
	SNAME,		TFLOAT,
		NEEDS(NREG(A, 1), NREG(C, 1), NEVER(R0)),	RESC2,
		"	lis A1," HA16(AL) COM "load sname\n"
		"	lfs A2," LO16(AL) "(A1)\n", },


{ OPLTYPE,	INCREG | FEATURE_HARDFLOAT | FEATURE_PIC,
	SANY,		TANY,
	SNAME,		TFLOAT,
		NEEDS(NREG(A, 1), NREG(C, 1), NEVER(R0)),	RESC2,
		"	lis A1, AL, " HA16(AL) COM "load pic sname\n"
		"	lfs A2," LO16(AL) "(A1)\n", },


/* soft-float */
{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SNAME,		TFLOAT,
		NAV0,	RESC1,
		"	lis A1," HA16(AL) COM "load sname (soft-float)\n"
		"	lwz A1," LO16(AL) "(A1)\n", },

{ OPLTYPE,	INCREG | FEATURE_HARDFLOAT,
	SANY,		TANY,
	SOREG,		TDOUBLE|TLDOUBLE,
		NC,	RESC1,
		"	lfd A1,AL" COM "load (l)double\n", },

/* soft-float */
{ OPLTYPE,	INBREG,
	SANY,		TANY,
	SOREG,		TDOUBLE|TLDOUBLE,
		NB,	RESC1,
		"	lwz A1,AL" COM "load (l)double (soft-float)\n"
		"	lwz U1,UL\n", },
#if 1
{ OPLTYPE,	INCREG | FEATURE_HARDFLOAT,
	SANY,		TANY,
	SNAME,		TDOUBLE|TLDOUBLE,
		NEEDS(NREG(A, 1), NREG(C, 1), NEVER(R0)),	RESC2,
		"	addis A1, r31, " HA16(AL) COM "pic load sname\n"
		"	lfd A2," LO16(AL) "(A1)\n", },
#else
{ OPLTYPE,	INCREG | FEATURE_HARDFLOAT,
	SANY,		TANY,
	SNAME,		TDOUBLE|TLDOUBLE,
		NCREG|NAREG|NSPECIAL,	RESC2,
		"	lis A1," HA16(AL) COM "load sname\n"
		"	lfd A2," LO16(AL) "(A1)\n", },
#endif

{ OPLTYPE,	INBREG,
	SANY,		TANY,
	SNAME,		TDOUBLE|TLDOUBLE,
		NBV0,	RESC1,
		"	lis A1," HA16(AL) COM "load sname (soft-float)\n"
		"	lwz A1," LO16(AL) "(A1)\n"
		"	lis U1," HA16(UL) "\n"
		"	lwz U1," LO16(UL) "(U1)\n", },


/*
 * Negate a word.
 */

{ UMINUS,	INAREG,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SANY,	TANY,
		XSL(A),	RESC1,
		"	neg A1,AL\n", },

{ UMINUS,	INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SANY,	TANY,
		XSL(B),	RESC1,
		"	subfic A1,AL,0\n"
		"	subfze U1,UL\n", },

{ UMINUS,	INCREG | FEATURE_HARDFLOAT,
	SCREG,	TFLOAT|TDOUBLE|TLDOUBLE,
	SANY,	TANY,
		XSL(C),	RESC1,
		"	fneg A1,AL\n", },

{ UMINUS,	INAREG,
	SAREG,	TFLOAT,
	SANY,	TANY,
		XSL(A),	RESC1,
		"	xoris A1,AL,0x8000" COM "(soft-float)\n", },

{ UMINUS,	INBREG,
	SBREG,	TDOUBLE|TLDOUBLE,
	SANY,	TANY,
		XSL(B),	RESC1,
		"	xoris U1,UL,0x8000" COM "(soft-float)\n"
		"	mr A1,AL\n", },

{ COMPL,	INAREG,
	SAREG,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SANY,	TANY,
		XSL(A),	RESC1,
		"	not A1,AL\n", },

{ COMPL,	INBREG,
	SBREG,	TLONGLONG|TULONGLONG,
	SANY,	TANY,
		XSL(B),	RESC1,
		"	not A1,AL\n"
		"	not U1,UL\n", },

/*
 * Arguments to functions.
 */

#if 0
{ STARG,	FOREFF,
	SAREG|SOREG|SNAME|SCON,	TANY,
	SANY,	TSTRUCT,
		NSPECIAL|NAREG,	0,
		"ZF", },
#endif

# define DF(x) FORREW,SANY,TANY,SANY,TANY,NEEDS(NREWRITE),x,""

{ UMUL, DF( UMUL ), },

{ ASSIGN, DF(ASSIGN), },

{ STASG, DF(STASG), },

{ FLD, DF(FLD), },

{ OPLEAF, DF(NAME), },

/* { INIT, DF(INIT), }, */

{ OPUNARY, DF(UMINUS), },

{ OPANY, DF(BITYPE), },

{ FREE,	FREE,	FREE,	FREE,	FREE,	FREE,	0,	FREE,	"help; I'm in trouble\n" },
};

int tablesize = sizeof(table)/sizeof(table[0]);
