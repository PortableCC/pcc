/*	$Id$	*/
/*
 * Copyright (c) 2015 Anders Magnusson (ragge@ludd.luth.se).
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


# include "pass2.h"

#define TLL	TLONGLONG|TULONGLONG
#define TWORD	TCHAR|TUCHAR|TSHORT|TUSHORT|TINT|TUNSIGNED /* anything <= int */

struct optab table[] = {
/* First entry must be an empty entry */
{	-1, FOREFF, SANY, TANY, SANY, TANY, 0, 0, "	nop	", }, 

/* eliminate OREG, NAME and ICON nodes by preloading */

{	ICON,    INAREG, 
	SANY,    TANY, 
	SCON,    TWORD | TPOINT, 
	NAREG | NASL,     RESC1, 
    "	li A1, AR	" COM "sub for scon tword (right)\n", }, 

{	ICON,    INAREG, 
	SANY,    TANY, 
	SZERO,   TANY, 
	0,     0, 
    "" COM "passing on subbing a zero\n", }, 


{	FCON,    INBREG, 
	SANY,    TANY, 
	SCON,    TFLOAT, 
	NAREG | NBREG,     RESC2, 
    "	lla A1, AR	" COM "float fcon from scon\n" \
    "	fcvt.s.w A2, A1\n", }, 

{	OREG,    INAREG, 
	SANY,    TANY, 
	SOREG,    TWORD | TPOINT, 
	NAREG | NASR,     RESC1, 
    "	lw A1, AR	" COM "sub for soreg tword (right)\n", }, 

{	OREG,    INBREG, 
	SOREG,    TFLOAT, 
	SANY,    TANY, 
	NBREG | NBSL,     RESC1, 
    "	flw A1, AL	" COM "sub for soreg tfloat (left)\n", }, 
    
{	OREG,    INBREG, 
	SOREG,    TDOUBLE,
	SANY,    TANY,  
	NBREG | NBSL,     RESC1, 
    "	fld A1, AL	" COM "sub for soreg tdouble (left)\n", },
    
{	OREG,    INBREG, 
	SANY,    TANY, 
	SOREG,    TFLOAT, 
	NBREG | NBSL,     RESC1, 
    "	flw A1, AR	" COM "sub for soreg tfloat (right)\n", }, 

{	OREG,    INBREG, 
	SANY,    TANY, 
	SOREG,    TDOUBLE, 
	NBREG | NBSL,     RESC1, 
    "	fld A1, AR	" COM "sub for soreg tdouble (right)\n", },  

{	NAME,    INAREG, 
	SANY,    TANY, 
	SNAME,    TPOINT, 
	NAREG,     RESC1, 
	"	lla A1, AR	" COM "name pointer to nareg (right)\n", }, 
	
{	NAME,    INAREG, 
	SANY,    TANY, 
	SNAME,    TWORD, 
	NAREG,     RESC1, 
	"	lla A1, AR\n"
	"	lw A1, 0(A1)" COM "name word to nareg (right)\n", }, 

{	NAME,    INAREG, 
	SNAME,    TPOINT, 
	SANY,    TANY, 
	NAREG,     RESC1, 
	"	lla A1, AL	" COM "name pointer to nareg (left)\n", }, 
	
{	NAME,    INAREG, 
	SNAME,    TWORD, 
	SANY,    TANY, 
	NAREG,     RESC1, 
	"	lla A1, AL\n"
	"	lw A1, 0(A1)" COM "name word to nareg (left)\n", }, 

{	NAME,    INBREG, 
	SNAME,    TFLOAT, 
	SANY | SCON,    TANY, 
	NBREG | NBSL,     RESC1, 
    "	flw A1, AL	" COM "float fp from sname (left)\n", }, 

{	NAME,    INBREG, 
	SANY,    TANY, 
	SNAME | SCON,    TFLOAT, 
	NBREG | NBSL,     RESC1, 
    "	flw A1, AR	" COM "float fp from sname (right)\n", }, 

{	NAME,    INBREG, 
	SNAME,    TDOUBLE, 
	SANY | SCON,    TANY, 
	NBREG | NBSL,     RESC1, 
    "	fld A1, AL	" COM "double from sname (left)\n", }, 

{	NAME,    INBREG, 
	SANY,    TANY, 
	SNAME | SCON,    TDOUBLE, 
	NBREG | NBSL,     RESC1, 
    "	fld A1, AR	" COM "double from sname (right)\n", }, 

{	NAME,    INCREG, 
	SANY,    TANY, 
	SNAME,    TLL, 
	NCREG,     RESC1, 
	"	lla A1, AR\n"
	"	lw A1, 0(A1)\n"
	"	lw U1, 4(A1)" COM "line 3 of name pointer to ncreg (right)\n", }, 
    
{	ICON,    INCREG, 
	SANY,    TANY, 
	SCON,    TLL, 
	NCREG | NBSL,     RESC1, 
    "	li A1, AR	" COM "sub for scon tlonglong (right)\n" \
    "	li U1, UR\n", }, 


{	TEMP, 	INTEMP|INAREG, 
	SANY, 	TANY, 
	SANY, 	TANY, 
	0, 	RNOP, 
	"	nop	" COM "intemp|inareg\n", }, 

/* ixp 20 */
{	TEMP, 	INTEMP|INBREG, 
	SANY, 	TANY, 
	SANY, 	TANY, 
	NBREG, 	RLEFT, 
	"	nop	" COM "intemp|inbreg\n", }, 



/* PCONVs are usually not necessary */
{	PCONV, 	INAREG, 
	SAREG, 	TWORD|TPOINT, 
	SAREG, 	TWORD|TPOINT, 
	0, 	RLEFT, 
	"	nop	" COM "pconv\n", }, 

/*
 * A bunch conversions of integral<->integral types
 * Only to lower types needed, rest is done when loaded into register.
 */

/* First higher rank */
/* convert (u)char to larger type <= unsigned. */
{	SCONV, 	INAREG |INTEMP, 
	SAREG, 	TCHAR|TUCHAR|TSHORT|TUSHORT|TINT|TUNSIGNED, 
	SAREG, 	TCHAR|TUCHAR|TSHORT|TUSHORT|TINT|TUNSIGNED, 
	NASL, 	RLEFT, 
	"	nop	" COM "sconv char\n", }, 

/* convert (u)short to larger type <= unsigned. */
{	SCONV, 	INAREG, 
	SAREG, 	TSHORT|TUSHORT, 
	SAREG, 	TSHORT|TUSHORT|TINT|TUNSIGNED, 
	NASL, 	RLEFT, 
	"	nop	" COM "sconv short to larger\n", }, 

/* convert pointers to int. */
{	SCONV, 	INAREG, 
	SAREG, 	TSTRUCT|TPOINT|TPTRTO|TWORD, 
	SAREG, 	TWORD, 
	NAREG|NASL, 	RLEFT, 
	"	nop	" COM "sconv pointer to int\n", },  

/* convert (u)int to larger type <= unsigned. */
{	SCONV, 	INAREG, 
	SAREG, 	TINT|TUNSIGNED, 
	SAREG, 	TINT|TUNSIGNED, 
	NASL, 	RLEFT, 
	"	nop	" COM "sconv int to larger\n", }, 

/* convert any unsigned to (u)longlong */
{	SCONV, 	INCREG, 
	SAREG, 	TUCHAR|TUSHORT|TUNSIGNED, 
	SCREG, 	TLL, 
	NCREG, 	RESC1, 
	"	add A1, x0, AL\n"
	"	add U1, x0, x0\n", }, 

/* convert any signed to (u)longlong */
{	SCONV, 	INCREG, 
	SAREG, 	TCHAR|TSHORT|TINT, 
	SCREG, 	TLL, 
	NCREG, 	RESC1, 
	"	add A1, x0, AL\n"
	"	srai U1, AL, 31\n", }, 

/* (u)longlong to (u)longlong */
{	SCONV, 	INCREG, 
	SCREG, 	TLL, 
	SCREG, 	TLL, 
	0, 	RLEFT, 
	"	nop	" COM "sconv longlong to longlong\n", }, 

/* (u)longlong to (u)int */
{	SCONV, 	INAREG, 
	SCREG, 	TLL, 
	SAREG, 	TINT|TUNSIGNED, 
	NAREG, 	RESC1, 
	"	add A1, x0, AL\n", }, 

/* (u)longlong to ushort */
{	SCONV, 	INAREG, 
	SCREG, 	TLL, 
	SAREG, 	TUSHORT, 
	NAREG, 	RESC1, 
	"	slli A1, AL, 16\n"
	"	srli A1, A1, 16\n", }, 

/* (u)longlong to short */
{	SCONV, 	INAREG, 
	SCREG, 	TLL, 
	SAREG, 	TSHORT, 
	NAREG, 	RESC1, 
	"	slli A1, AL, 16\n"
	"	srai A1, A1, 16\n", }, 

/* (u)longlong to uchar */
{	SCONV, 	INAREG, 
	SCREG, 	TLL, 
	SAREG, 	TUCHAR, 
	NAREG, 	RESC1, 
	"	slli A1, AL, 24\n"
	"	srli A1, A1, 24\n", }, 

/* (u)longlong to char */
{	SCONV, 	INAREG, 
	SCREG, 	TLL, 
	SAREG, 	TCHAR, 
	NAREG, 	RESC1, 
	"	slli A1, AL, 24\n"
	"	srai A1, A1, 24\n", }, 

/* (u)int to ushort */
{	SCONV, 	INAREG, 
	SAREG, 	TINT|TUNSIGNED, 
	SAREG, 	TUSHORT, 
	0, 	RLEFT, 
	"	slli AL, AL, 16\n"
	"	srli AL, AL, 16\n", }, 

/* (u)int to short */
{	SCONV, 	INAREG, 
	SAREG, 	TINT|TUNSIGNED, 
	SAREG, 	TSHORT, 
	0, 	RLEFT, 
	"	slli AL, AL, 16\n"
	"	srai AL, AL, 16\n", }, 

/* (u)int to uchar */
{	SCONV, 	INAREG, 
	SAREG, 	TINT|TUNSIGNED|TSHORT|TUSHORT, 
	SAREG, 	TUCHAR, 
	0, 	RLEFT, 
	"	slli AL, AL, 24\n"
	"	srli AL, AL, 24\n", }, 

/* (u)int to uchar */
{	SCONV, 	INAREG, 
	SAREG, 	TINT|TUNSIGNED|TSHORT|TUSHORT, 
	SAREG, 	TCHAR, 
	0, 	RLEFT, 
	"	slli AL, AL, 24\n"
	"	srai AL, AL, 24\n", }, 

/* XXX add float casts */
/* single precision float to double */
{	SCONV, 	INBREG|INTEMP, 
	SANY, 	TFLOAT, 
	SBREG, 	TDOUBLE, 
	NBREG|NBSL, 	RLEFT, 
	"	fcvt.d.s A1, AL\n" , }, 

/* double precision float to single */	
{	SCONV, 	INBREG|INTEMP, 
	SANY, 	TDOUBLE, 
	SBREG, 	TFLOAT, 
	NBREG|NBSL, 	RLEFT, 
	"	fcvt.s.d A1, AL\n", }, 

/* word to double precision float */	
{	SCONV, 	INBREG|INTEMP, 
	SANY, 	TWORD, 
	SBREG, 	TDOUBLE, 
	NBREG, 	RESC1, 
	"	fcvt.d.w A1, AL" COM "aaa\n", }, 

/* word to single precision float */	
{	SCONV, 	INBREG|INTEMP, 
	SANY, 	TWORD,  
	SBREG, 	TFLOAT,
	NBREG|NBSL , 	RLEFT, 
	"	fcvt.s.w A1, AL" COM "bbb\n", },

/* single precision float to word */	
{	SCONV, 	INAREG|INTEMP,
	SANY, 	TFLOAT,  
	SAREG, 	TWORD, 
	NAREG | NASL, 	RLEFT, 
	"	fcvt.w.s A1, AL\n", }, 

/* double precision float to word */	
{	SCONV, 	INBREG|INTEMP,
	SANY, 	TDOUBLE,  
	SBREG, 	TWORD, 
	NAREG | NASL, 	RLEFT, 
	"	fcvt.w.d A1, AL\n", }, 

/*
 * Subroutine calls.
 * XXX "far" calls?
 */

/* Direct calls w/o return value */
{	UCALL, 	FOREFF, 
	SCON, 	TANY, 
	SANY, 	TANY, 
	0, 	0, 
	"	jal ra, CL" COM "ucall scon/sany\n", }, 

{	CALL, 	FOREFF, 
	SCON, 	TANY, 
	SANY, 	TANY, 
	0, 	0, 
	"	jal ra, CL	" COM "call scon/sany\n", }, 

/* Direct calls with return value in areg/breg/creg */
{	UCALL, 	INAREG, 
	SCON, 	TANY, 
	SAREG, 	TWORD|TPOINT, 
	NAREG|NASL, 	RESC1, 
	"	jal ra, CL" COM "ucall scon/sareg\n", }, 

{	CALL, 	INAREG, 
	SCON, 	TANY, 
	SAREG, 	TWORD|TPOINT, 
	NAREG|NASL, 	RESC1, 
	"	jal ra, CL	" COM "call scon/sareg\n", }, 

{	UCALL, 	INBREG | FEATURE_HARDFLOAT, 
	SCON, 	TANY, 
	SBREG, 	TANY, 
	NBREG, 	RESC1, 
	"	jal ra, CL	" COM "ucall scon/sbreg\n", }, 

{	CALL, 	INBREG | FEATURE_HARDFLOAT, 
	SCON, 	TANY, 
	SBREG, 	TANY, 
	NBREG, 	RESC1, 
	"	jal ra, CL	" COM "call scon/sbreg\n", }, 

{	UCALL, 	INCREG, 
	SCON, 	TANY, 
	SCREG, 	TANY, 
	NCREG, 	RESC1, 
	"	jal ra, CL	" COM "ucall scon/screg\n", }, 

{	CALL, 	INCREG, 
	SCON, 	TANY, 
	SCREG, 	TANY, 
	NCREG, 	RESC1, 
	"	jal ra, CL	" COM "call scon/screg\n", }, 

/* Indirect calls w/o return value */
{	UCALL, 	FOREFF, 
	SAREG, 	TANY, 
	SANY, 	TANY, 
	0, 	0, 
	"	jalr ra, AL	" COM "ucall sareg/sany\n", }, 

{	CALL, 	FOREFF, 
	SAREG, 	TANY, 
	SANY, 	TANY, 
	0, 	0, 
	"	jalr ra, AL	" COM "call sareg/sany\n", }, 

/* Indirect calls with return value in areg/breg/creg */
{	UCALL, 	INAREG, 
	SAREG, 	TANY, 
	SAREG, 	TWORD|TPOINT, 
	NAREG|NASL, 	RESC1, 
	"	jalr ra, AL	" COM "ucall sareg/sareg\n", }, 

{	CALL, 	INAREG, 
	SAREG, 	TANY, 
	SAREG, 	TWORD|TPOINT, 
	NAREG|NASL, 	RESC1, 
	"	jalr ra, AL	" COM "call sareg/sareg\n", }, 

{	UCALL, 	INBREG | FEATURE_HARDFLOAT, 
	SAREG, 	TANY, 
	SBREG, 	TANY, 
	NBREG, 	RESC1, 
	"	jalr ra, AL	" COM "ucall sareg/sbreg\n", }, 

{	CALL, 	INBREG | FEATURE_HARDFLOAT, 
	SAREG, 	TANY, 
	SBREG, 	TANY, 
	NBREG, 	RESC1, 
	"	jalr ra, AL	" COM "call sareg/sbreg\n", }, 

{	UCALL, 	INCREG, 
	SAREG, 	TANY, 
	SCREG, 	TANY, 
	NCREG, 	RESC1, 
	"	jalr ra, AL	" COM "ucall sareg/screg\n", }, 

{	CALL, 	INCREG, 
	SAREG, 	TANY, 
	SCREG, 	TANY, 
	NCREG, 	RESC1, 
	"	jalr ra, AL	" COM "call sareg/screg\n", }, 

/*
 * The next rules handle all simple binop-style operators.
 */

#if 0
{   OPSIMP,     INAREG,
    SAREG,     TINT | TUNSIGNED,
    SCON,     TINT | TUNSIGNED,
    NASL,     RLEFT,
    "   Ow AL,AL,CR	" COM "test rleft\n", },

{	OPSIMP,		INAREG,
	SAREG,	TINT | TUNSIGNED | TPOINT,
	SSCON,	TANY,
	NAREG|NASL,	RESC1,
	"	addi A1,AL,AR	" COM "addition of short\n", },

#else

{	OPSIMP, 	INAREG, 
	SAREG, 	TINT | TUNSIGNED | TPOINT, 
	SCON, 	TANY, 
	2*NAREG|NASL, 	RESC1, 
	"	ZP " COM "zp\n", }, 

#endif

{	OPSIMP, 	INAREG, 
	SAREG, 	TINT | TUNSIGNED | TPOINT, 
	SAREG, 	TINT | TUNSIGNED | TPOINT, 
	NAREG|NASL, 	RESC1, 
	"	Ow A1, AL, AR	" COM "opsimp\n", }, 

{	OPSIMP, 	INBREG, 
	SBREG, 	TFLOAT, 
	SBREG, 	TFLOAT, 
	NBREG|NBSL, 	RESC1, 
	"	Of A1, AL, AR\n", }, 

{	OPSIMP, 	INBREG, 
	SBREG, 	TDOUBLE, 
	SBREG, 	TDOUBLE, 
	NBREG|NBSL, 	RESC1, 
	"	Od A1, AL, AR\n", }, 

/* Special treatment for long long */
{	PLUS, 	INCREG, 
	SCREG, 	TLL, 
	SCREG, 	TLL, 
	NCREG, 	RESC1,
	"	add A1, AL, AR\n"
	"	sltu U1, A1, AL\n"
	"	add U1, UL, U1\n"
	"	add U1, U1, UR\n", }, 

{	MINUS, 	INCREG, 
	SCREG, 	TLL, 
	SCREG, 	TLL, 
	NCREG, 	RESC1, 
	"	sub A1, AL, AR\n	"
	"	sltu U1, AL, AR\n	"
	"	sub U1, UL, U1\n"
	"	sub U1, U1, UR\n", }, 
	
	
/*
 * The next rules handle all shift operators.
 */
/* (u)longlong shift is handles separate */
{	LS, 	INCREG, 
	SCREG, 	TLL, 
	SAREG, 	TCHAR|TUCHAR, 
	NSPECIAL, 	RLEFT, 
	"ZO", }, 

/* l = l << r */
{	LS, 	INAREG, 
	SAREG, 	TWORD, 
	SAREG, 	TWORD, 
	NAREG|NASL, 	RESC1, 
	"	sll A1, AL, AR\n", }, 

{	LS, 	INAREG, 
	SAREG, 	TWORD, 
	SCON, 	TWORD, 
	NAREG|NASL, 	RESC1, 
	"	slli A1, AL, AR\n", }, 

/* (u)longlong right shift is emulated */
{	RS, 	INCREG, 
	SCREG, 	TLL, 
	SAREG, 	TCHAR|TUCHAR, 
	NSPECIAL, 	RLEFT, 
	"ZO", }, 

{	RS, 	INAREG, 
	SAREG, 	TCHAR|TSHORT|TINT, 
	SAREG, 	TINT, 
	NAREG|NASL, 	RESC1, 
	"	sra A1, AL, AR\n", }, 

{	RS, 	INAREG, 
	SAREG, 	TCHAR|TSHORT|TINT, 
	SCON, 	TINT, 
	NAREG|NASL, 	RESC1, 
	"	srai A1, AL, AR\n", }, 

{	RS, 	INAREG, 
	SAREG, 	TUCHAR|TUSHORT|TUNSIGNED, 
	SAREG, 	TINT, 
	NAREG|NASL, 	RESC1, 
	"	srl A1, AL, AR", }, 
	
{	RS, 	INAREG, 
	SAREG, 	TUCHAR|TUSHORT|TUNSIGNED, 
	SCON, 	TINT, 
	NAREG|NASL, 	RESC1, 
	"	srli A1, AL, AR", }, 

/*
 * The next rules takes care of assignments. "=".
 */

{	ASSIGN, FOREFF|INAREG, 
	SAREG, 	TWORD|TPOINT, 
	SAREG, 	TWORD|TPOINT, 
	0, 	RDEST, 
	"	mv AL, AR	" COM "move between registers\n", }, 

{	ASSIGN, FOREFF|INAREG, 
	SNAME, 	TINT|TUNSIGNED|TPOINT, 
	SAREG, 	TINT|TUNSIGNED|TPOINT, 
	NAREG, 	RDEST, 
	"	lla A1, AL\n"
	"	sw AR, 0(A1)	" COM "assign sareg to sname\n", }, 

{	ASSIGN, FOREFF|INAREG, 
	SAREG, 	TINT|TUNSIGNED|TPOINT, 
	SNAME, 	TINT|TUNSIGNED|TPOINT, 
	NAREG, 	RDEST, 
	"	lla A1, AR\n"
	"	lw AL, 0(A1)	" COM "assign sname to sareg\n", }, 

{	ASSIGN, FOREFF|INAREG, 
	SOREG, 	TINT|TUNSIGNED|TPOINT, 
	SAREG, 	TINT|TUNSIGNED|TPOINT, 
	0, 	RDEST, 
	"	sw AR, AL	" COM "assign \n", }, 


{	ASSIGN, FOREFF|INAREG, 
	SOREG, 	TINT|TUNSIGNED|TPOINT, 
	SZERO, 	TINT|TUNSIGNED|TPOINT, 
	0, 	RDEST, 
	"	sw x0, AL	" COM "assign zero\n", }, 

{	ASSIGN, FOREFF|INAREG, 
	SOREG, 	TCHAR|TUCHAR, 
	SAREG, 	TCHAR|TUCHAR, 
	0, 	RDEST, 
	"	sb AR, AL	" COM "assign byte\n", }, 

{	ASSIGN, FOREFF|INAREG, 
	SOREG, 	TCHAR, 
	SZERO, 	TCHAR, 
	0, 	RDEST, 
	"	sb x0, AL	" COM "assign zero byte\n", }, 

{	ASSIGN, FOREFF|INAREG, 
	SOREG, 	TSHORT, 
	SAREG, 	TSHORT, 
	0, 	RDEST, 
	"	sh AR, AL	" COM "assign halfword\n", }, 

{	ASSIGN, FOREFF|INAREG, 
	SOREG, 	TSHORT, 
	SZERO, 	TSHORT, 
	0, 	RDEST, 
	"	sh x0, AL	" COM "assign zero halfword\n", }, 

{	ASSIGN, 	FOREFF|INAREG, 
	SAREG, 	TINT|TUNSIGNED|TPOINT, 
	SOREG, 	TINT|TUNSIGNED|TPOINT, 
	0, 	RDEST, 
	"	lw AL, AR	" COM "assign oreg to areg\n", }, 
	
{	ASSIGN, 	FOREFF|INAREG, 
	SAREG, 	TINT|TUNSIGNED|TPOINT, 
	SCON, 	TCHAR, 
	0, 	RDEST, 
	"	addi AL, x0, AR	" COM "assign scon byte to areg\n", }, 
	
{	ASSIGN, 	FOREFF|INAREG, 
	SAREG, 	TINT|TUNSIGNED|TPOINT, 
	SCON, 	TINT|TUNSIGNED, 
	0, 	RDEST, 
	"	li AL, AR	" COM "assign scon word to areg\n", }, 	
	
{	ASSIGN, 	FOREFF|INAREG, 
	SAREG, 	TINT|TUNSIGNED|TPOINT, 
	SCON, 	TPOINT, 
	0, 	RDEST, 
	"	lla AL, AR	" COM "assign label to areg\n", }, 

{	ASSIGN, 	FOREFF|INAREG, 
	SAREG, 	TINT|TUNSIGNED|TPOINT, 
	SCON, 	TWORD, 
	0, 	RDEST, 
	"	lla AL, AR	" COM "probably not right\n", },

#if 0
{	ASSIGN, 	FOREFF|INAREG, 
	SOREG, 	TINT|TUNSIGNED|TPOINT, 
	SCON, 	TINT|TUNSIGNED|TPOINT, 
	NAREG, 	RDEST, 
	"	li A1, AR\n	sw A1, AL	" COM "assign scon to soreg\n", }, 
#endif
	
{	ASSIGN, 	FOREFF|INBREG, 
	SBREG, 	TFLOAT, 
	SBREG, 	TFLOAT, 
	0, 	RDEST, 
	"	fmv.s AL, AR\n", }, 	
	
{	ASSIGN, 	FOREFF|INBREG, 
	SBREG, 	TDOUBLE, 
	SBREG, 	TDOUBLE, 
	0, 	RDEST, 
	"	fmv.d AL, AR\n", }, 			

{	ASSIGN, 	FOREFF|INBREG, 
	SBREG, 	TFLOAT, 
	SCON | SNAME, 	TFLOAT, 
	0, 	RDEST, 
	"	flw AL, AR\n", },

{	ASSIGN, 	FOREFF|INBREG, 
	SBREG, 	TDOUBLE, 
	SNAME, 	TDOUBLE, 
	0, 	RDEST, 
	"	fld AL, AR\n", }, 	

{	ASSIGN, 	FOREFF|INBREG, 
	SOREG, 	TFLOAT, 
	SBREG, 	TFLOAT, 
	0, 	RDEST, 
	"	fsw AR, AL\n", }, 	

{	ASSIGN, 	FOREFF|INBREG, 
	SOREG, 	TDOUBLE, 
	SBREG, 	TDOUBLE, 
	0, 	RDEST, 
	"	fsd AR, AL\n", }, 	

{	ASSIGN, 	FOREFF|INBREG, 
	SBREG, 	TFLOAT, 
	SOREG, 	TFLOAT, 
	0, 	RDEST, 
	"	flw AL, AR\n", }, 	

{	ASSIGN, 	FOREFF|INBREG, 
	SBREG, 	TDOUBLE, 
	SOREG, 	TDOUBLE, 
	0, 	RDEST, 
	"	fld AL, AR\n", }, 	

{	ASSIGN, 	FOREFF|INCREG, 
	SCREG, 	TLL,
	SCREG, 	TLL,  
	NCREG, 	RDEST, 
	"	mv AL, AR\n"
	"	mv UL, UR	" COM "line 2 of move between cregs\n", }, 	
	
{	ASSIGN, 	FOREFF|INCREG, 
	SOREG, 	TLL,
	SCREG, 	TLL,  
	0, 	RDEST, 
	"	sw AR, AL\n"
	"	sw UR, UL	" COM "line 2 of screg to soreg\n", }, 	

{	ASSIGN, 	FOREFF|INCREG, 
	SNAME, 	TLL, 
	SCREG, 	TLL, 
	NAREG, 	RDEST, 
	"	lla A1, AL\n"
	"	sw AR, 0(A1)\n"
	"	sw UR, 4(A1)	" COM "line 3 of assign screg to sname\n", }, 

{	ASSIGN, 	FOREFF|INCREG, 
	SCREG, 	TLL, 
	SCON, 	TLL, 
	0, 	RDEST, 
	"	li AL, AR\n"
	"	li UL, UR	" COM "scon to screg \n", }, 	
	
	
#if 0
{	ASSIGN, 	INFL|FOREFF, 
	SHFL, 	TFLOAT, 
	SHFL|SOREG|SNAME, 	TFLOAT, 
	0, 	RDEST, 
	"	flds AR\n", }, 
#endif

/* Leaf types */
{	OPLTYPE, 	INAREG|INTEMP, 
	SANY, 	TANY, 
	SOREG, 	TINT|TUNSIGNED|TPOINT, 
	NAREG, 	RESC1, 
	"	lw A1, AR	" COM "caught1\n", }, 

{	OPLTYPE, 	INAREG, 
	SANY, 	TANY, 
	SAREG, 	TINT|TUNSIGNED|TPOINT, 
	NAREG, 	RESC1, 
	"	mr A1, AR	" COM "caught3\n", },


/*
 * DIV/MOD/MUL 
 */

{	DIV,  INAREG,
	SAREG,	TANY,
	SAREG,	TANY,
	NAREG,	RESC1,
	"	div A1, AL, AR\n", },

{	MOD,	 INAREG,
	SAREG,	TANY,
	SAREG,	TANY,
	NAREG,	RESC1,
	"	div A1, AL, AR	" COM "mod\n"
	"	mul AR, A1, AR\n"
	"	sub A1, AL, AR\n", },

{	MUL, INAREG,
	SAREG,	TANY,
	SAREG,	TANY,
	NAREG,	RESC1,
	"	mul A1, AL, AR\n", },

{	DIV,  INBREG,
	SBREG,	TFLOAT,
	SBREG,	TFLOAT,
	NBREG | NBSL,	RESC1,
	"	fdiv.s A1, AL, AR\n", },
	
{	DIV,  INBREG,
	SBREG,	TDOUBLE,
	SBREG,	TDOUBLE,
	NBREG | NBSL,	RESC1,
	"	fdiv.d A1, AL, AR\n", },

{	MOD,	 INBREG,
	SBREG,	TFLOAT,
	SBREG,	TFLOAT,
	NBREG | NBSL,	RESC1,
	"	fdiv.s A1, AL, AR	" COM "mod\n"
	"	fmul.s AR, A1, AR\n"
	"	fsub.s A1, AL, AR\n", },

{	MOD,	 INBREG,
	SBREG,	TDOUBLE,
	SBREG,	TDOUBLE,
	NBREG | NBSL,	RESC1,
	"	fdiv.d A1, AL, AR	" COM "mod\n"
	"	fmul.d AR, A1, AR\n"
	"	fsub.d A1, AL, AR\n", },

{	MUL, INBREG,
	SBREG,	TFLOAT,
	SBREG,	TFLOAT,
	NBREG | NBSL,	RESC1,
	"	fmul.s A1, AL, AR\n", },
	
{	MUL, INBREG,
	SBREG,	TDOUBLE,
	SBREG,	TDOUBLE,
	NBREG | NBSL,	RESC1,
	"	fmul.d A1, AL, AR\n", },

{	DIV,  INCREG,
	SCREG,	TANY,
	SCREG,	TANY,
	NCREG | NCSL,	RESC1,
	"	div A1, AL, AR\n", },

{	MOD,	 INCREG,
	SCREG,	TANY,
	SCREG,	TANY,
	NCREG,	RESC1,
	"	div A1, AL, AR" COM "mod\n"
	"	mul AR, A1, AR\n"
	"	sub A1, AL, AR\n", },

{	MUL, INCREG,
	SCREG,	TLONGLONG,
	SCREG,	TLONGLONG,
	NCREG,	RESC1,
	"	mulh U1, AL, AR\n" \
	"	mul A1, AL, AR\n", },
	
{	MUL, INCREG,
	SCREG,	TULONGLONG,
	SCREG,	TULONGLONG,
	NCREG,	RESC1,
	"	mulhu U1, AL, AR\n" \
	"	mul A1, AL, AR\n", },
	
{	MUL, INCREG,
	SCREG,	TLONGLONG,
	SCREG,	TULONGLONG,
	NCREG,	RESC1,
	"	mulhsu U1, AL, AR\n" \
	"	mul A1, AL, AR\n", },
	
{	MUL, INCREG,
	SCREG,	TULONGLONG,
	SCREG,	TLONGLONG,
	NCREG,	RESC1,
	"	mulhsu U1, AR, AL\n" \
	"	mul A1, AR, AL\n", },

/*
 * Indirection operators.
 */

#if 0
{	UMUL, 	INAREG|INTEMP, 
	SANY, 	TPOINT|TWORD, 
	SANY, 	TPOINT|TWORD, 
	NAREG|NASL, 	RESC1, 
	"	lw A1, AL	" COM "umul sareg nareg\n", }, 
#endif

{	UMUL, 	INAREG, 
	SANY, 	TPOINT|TWORD, 
	SOREG, 	TPOINT|TWORD, 
	NAREG|NASL, 	RESC1, 
	"	lw A1, AL	" COM "umul soreg nareg\n", }, 


{	UMUL, 	INBREG, 
	SANY, 	TPOINT, 
	SOREG, 	TFLOAT, 
	NBREG, 	RESC1, 
	"	flw A1, AL	" COM "umul nbreg\n", }, 

{	UMUL, 	INBREG, 
	SANY, TPOINT , 
	SOREG, 	TDOUBLE | TLDOUBLE, 
	NBREG, 	RESC1, 
	"	fld A1, AL	" COM "umul double nbreg\n", }, 
	
{	UMUL, 	INCREG, 
	SANY, 	TANY, 
	SOREG, 	TLL, 
	NCREG, 	RESC1, 
	"	lw A1, AR\n"
	"	lw U1, UR		" COM "line 2 of creg umul\n", }, 


/*
 * Logical/branching operators
 */
{ OPLOG, FORCC, 
	SAREG, 	TWORD|TPOINT, 
	SAREG, 	TWORD|TPOINT, 
	0, 	RNOP, 
	"	ZA AL, AR, LC\n", }, 

/* Compare against zero - recommended special syntax */
{ OPLOG, FORCC, 
	SAREG, 	TWORD|TPOINT, 
	SZERO, 	TWORD|TPOINT, 
	0, 	RNOP, 
	"	ZB AL, LC\n", }, 

/* floating point comparison, require two instructions */
{ OPLOG, FORCC, 
	SBREG, 	TFLOAT|TDOUBLE,
	SBREG, 	TFLOAT|TDOUBLE,
	NAREG, 	RNOP, 
	"ZF" }, 

/* who needs OPLOG? */
{	OPLOG, 	FORCC, 
	SANY, 	TANY, 
	SANY, 	TANY, 
	REWRITE, 	0, 
	"diediedie!", }, 


/*
 * Jumps.
 */
{	GOTO, 	FOREFF, 
	SCON, 	TANY, 
	SANY, 	TANY, 
	0, 	RNOP, 
	"	jal x0, LL\n", }, 
/*
 * Convert LTYPE to reg.
 */
/*
 * Negate a word.
 */
/*
 * Negate a word.
 */

{	UMINUS,	INAREG,
	SAREG,	TWORD|TPOINT|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SANY,	TANY,
	NAREG|NASL,	RESC1,
	"	neg A1,AL\n", },
/*
{	UMINUS,	INBREG | FEATURE_HARDFLOAT,
	SBREG,	TFLOAT,
	SANY,	TANY,
	NCREG|NCSL,	RESC1,
	"	fneg.s A1,AL\n", },

{	UMINUS,	INBREG | FEATURE_HARDFLOAT,
	SBREG,	TDOUBLE|TLDOUBLE,
	SANY,	TANY,
	NCREG|NCSL,	RESC1,
	"	fneg.d A1,AL\n", },
*/

{	UMINUS,	INCREG,
	SCREG,	TLONGLONG|TULONGLONG,
	SANY,	TANY,
	NCREG|NCSL,	RESC1,
	"	neg A1,AL\n", },

{	COMPL,	INAREG,
	SAREG,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SANY,	TANY,
	NAREG|NASL,	RESC1,
	"	not A1,AL\n", },

{	COMPL,	INCREG,
	SCREG,	TLL,
	SANY,	TANY,
	NCREG|NCSL,	RESC1,
	"	not A1,AL\n"
	"	not U1,UL\n", },

{	STASG,        INAREG|FOREFF,
	SOREG|SNAME,    TANY,
	SAREG,          TPTRTO|TANY,
	2 * NCREG,       RDEST,
	"addi A1, x0, ZQ\n" COM "structs must be < 2^12 in size\n" \
	"beq A1, x0, done\n" \
	"lw U1, 0(AR)" COM "derefence the right node\n" \
    "mr U2, AL" COM "copy the destination address to a register\n" \
	"andi A2, A1, 1" COM "check for odd size\n" \
	"beq, A2, x0, two_byte\n" \
	"lb A2, U1" COM "move a single byte\n" \
	"sb A2, U2\n" \
	"addi U1, U1, 1" COM "increment source\n" \
	"addi U2, U2, 1" COM "increment destination\n" \
	"subi A1, A1, 1\n" \
	"beq A1, x0, done\n" \
	".two_byte:\n" \
	"andi A2, A1, 2" COM "check for divisible by 4\n" \
	"beq A2, x0, four_byte\n" \
	"lh A2, U1" COM "move two bytes\n" \
	"sh A2, U2\n" \
	"addi U1, U1, 2" COM "increment source\n" \
	"addi U2, U2, 2" COM "increment destination\n" \
	"subi A1, A1, 2\n" \
	"beq A1, x0, done\n" \
	".four_byte:\n" \
	"lw A2, 0(U1)" COM "move four bytes\n" \
	"sw A2, U2\n" \
	"addi U1, U1, 4" COM "increment source\n" \
	"addi U2, U2, 4" COM "increment destination\n" \
	"subi A1, A1, 4\n" \
	"be A1, x0, done" \
	"j four_bytes" COM "loop until no more bytes\n" \
	".done:\n" \
	"subi U2, U2, ZQ\n" COM "structs must be < 2^12 in size\n", },

	
#if 0
/*
 *  Function arguments
 */

{ FUNARG,       FOREFF,
	SANY,  TANY,
	SANY,   TANY,
	0,      0,
	"	subi sp, sp, AL\n", },
#endif

# define DF(x) FORREW, SANY, TANY, SANY, TANY, REWRITE, x, ""

{	UMUL, DF( UMUL ), }, 

{	ASSIGN, DF(ASSIGN), }, 

{	FLD, DF(FLD), }, 

{	OPLEAF, DF(NAME), }, 

/* {	INIT, DF(INIT), }, */

{	OPUNARY, DF(UMINUS), }, 

{	OPANY, DF(BITYPE), }, 

{	FREE, 	FREE, 	FREE, 	FREE, 	FREE, 	FREE, 	FREE, 	FREE, 	"help; I'm in trouble\n" }, 
};

int tablesize = sizeof(table)/sizeof(table[0]);
