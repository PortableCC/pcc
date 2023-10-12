/*	$Id$	*/
/*
 * Copyright (c) 2003 Anders Magnusson (ragge@ludd.luth.se).
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
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission
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

#ifdef NEWSHAPES
struct shape *shareglst[] = { &shareg, 0 };
struct shape *shbreglst[] = { &shbreg, 0 };
struct shape *shcreglst[] = { &shcreg, 0 };
struct shape *shdreglst[] = { &shdreg, 0 };
struct shape shpcon = { SPECON, SPCON, 0 };
struct shape shlwxor = { SPECON, SMILWXOR, 0 };
struct shape shhwxor = { SPECON, SMIHWXOR, MAX_INT };

struct shape *shaon[] = { &shareg, &shoreg, &shname, 0 };
struct shape *shbon[] = { &shbreg, &shoreg, &shname, 0 };
struct shape *shccon[] = { &shcreg, &shoreg, &shname, 0 };
struct shape *shdonlst[] = { &shdreg, &shoreg, &shname, 0 };
struct shape *shon[] = { &shoreg, &shname, 0 };
struct shape *shan[] = { &shareg, &shname, 0 };
struct shape *shcc[] = { &shcreg, &shicon, 0 };
struct shape *shonelst[] = { &shone, 0 };
struct shape *shconlst[] = { &shicon, 0 };
struct shape *shpconlst[] = { &shpcon, 0 };
struct shape *shzerolst[] = { &shzero, 0 };
struct shape *shlwxorlst[] = { &shlwxor, 0 };
struct shape *shhwxorlst[] = { &shhwxor, 0 };
struct shape *shanoclst[] = { &shareg, &shoreg, &shname, &shicon, 0 };
struct shape *shbnoclst[] = { &shbreg, &shoreg, &shname, &shicon, 0 };
struct shape *shcnoclst[] = { &shcreg, &shoreg, &shname, &shicon, 0 };
struct shape *shoreglst[] = { &shoreg, 0 };
struct shape *shaclst[] = { &shareg, &shicon, 0 };
struct shape *shbclst[] = { &shbreg, &shicon, 0 };
struct shape *shnoclst[] = { &shoreg, &shname, &shicon, 0 };

#define SO_N	shon
#define SC_C	shcc
#define SA_N	shan
#define SA_C	shaclst
#define SA_O_N	shaon
#define SB_O_N	shbon
#define SB_C	shbclst
#define SC_O_N	shccon
#define SA_O_N_C	shanoclst
#define SB_O_N_C	shbnoclst
#define SC_O_N_C	shcnoclst
#define SO_N_C	shnoclst
#define SD_O_N	shdonlst
#undef	SOREG
#define	SOREG	shoreglst
#undef	SMIXOR
#define	SMIXOR	SZERO
#undef	SMIHWXOR
#define	SMIHWXOR shhwxorlst
#undef	SMILWXOR
#define	SMILWXOR shlwxorlst
#undef	SANY
#define	SANY	0
#undef	SPCON
#define	SPCON	shpconlst
#undef	SZERO
#define	SZERO	shzerolst
#undef	SONE
#define	SONE	shonelst
#undef	SCON
#define	SCON	shconlst
#undef	SDREG
#define	SDREG	shdreglst
#define	SHFL	shdreglst
#undef	SCREG
#define	SCREG	shcreglst
#define	SHLL	shcreglst
#undef	SBREG
#define	SBREG	shbreglst
#define	SHCH	shbreglst
#undef	SAREG
#define	SAREG	shareglst
#define	SHINT	shareglst
#undef	SANY
#define	SANY	0	/* match any shape */
#else
#define	 SHINT	SAREG	/* short and int */
#define	 SHCH	SBREG	/* shape for char */
#define	 SHLL	SCREG	/* shape for long long */
#define	 SHFL	SDREG	/* shape for float/double */
#define	SB_C	SBREG|SCON
#define	SC_C	SCREG|SCON
#define	SA_N	SAREG|SNAME
#define	SA_C	SAREG|SCON
#define	SA_O_N	SAREG|SOREG|SNAME
#define	SB_O_N	SBREG|SOREG|SNAME
#define	SC_O_N	SCREG|SOREG|SNAME
#define	SD_O_N	SDREG|SOREG|SNAME
#define	SO_N	SOREG|SNAME
#define SA_O_N_C SAREG|SOREG|SNAME|SCON
#define SB_O_N_C SBREG|SOREG|SNAME|SCON
#define SC_O_N_C SCREG|SOREG|SNAME|SCON
#define SO_N_C	SOREG|SNAME|SCON
#endif

# define TLL TLONGLONG|TULONGLONG
# define ANYSIGNED TINT|TLONG|TSHORT|TCHAR
# define ANYUSIGNED TUNSIGNED|TULONG|TUSHORT|TUCHAR
# define ANYFIXED ANYSIGNED|ANYUSIGNED
# define TUWORD TUNSIGNED|TULONG
# define TSWORD TINT|TLONG
# define TWORD TUWORD|TSWORD
#define	TAREG	TINT|TSHORT|TCHAR|TUNSIGNED|TUSHORT|TUCHAR
#define	 ININT	INAREG
#ifndef NOBREGS
#define	 INCH	INBREG
#endif
#define	 INLL	INCREG
#define	 INFL	INDREG	/* shape for float/double */

#define	XSL(c)	NEEDS(NREG(c, 1), NSL(c))

struct optab table[] = {
/* First entry must be an empty entry */
{ -1, FOREFF, SANY, TANY, SANY, TANY, 0, 0, "", },

/* PCONVs are usually not necessary */
{ PCONV,	INAREG,
	SAREG,	TWORD|TPOINT,
	SAREG,	TWORD|TPOINT,
		0,	RLEFT,
		"", },

/*
 * A bunch conversions of integral<->integral types
 * There are lots of them, first in table conversions to itself
 * and then conversions from each type to the others.
 */

/* itself to itself, including pointers */

#ifdef NOBREGS
/* convert (u)char to (u)char. */
{ SCONV,	INAREG,
	SAREG,	TCHAR|TUCHAR,
	SAREG,	TCHAR|TUCHAR,
		0,	RLEFT,
		"", },
#else
/* convert (u)char to (u)char. */
{ SCONV,	INCH,
	SHCH,	TCHAR|TUCHAR,
	SHCH,	TCHAR|TUCHAR,
		0,	RLEFT,
		"", },
#endif

/* convert pointers to int. */
{ SCONV,	ININT,
	SHINT,	TPOINT|TWORD,
	SANY,	TWORD,
		0,	RLEFT,
		"", },

/* convert (u)longlong to (u)longlong. */
{ SCONV,	INLL,
	SHLL,	TLL,
	SHLL,	TLL,
		0,	RLEFT,
		"", },

/* convert between float/double/long double. */
{ SCONV,	INFL,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
		0,	RLEFT,
		"ZI", },

/* convert pointers to pointers. */
{ SCONV,	ININT,
	SHINT,	TPOINT,
	SANY,	TPOINT,
		0,	RLEFT,
		"", },

/* char to something */

#ifdef NOBREGS
/* convert char to (unsigned) short. */
/* Done when reg is loaded */
{ SCONV,	INAREG,
	SAREG,	TCHAR|TUCHAR,
	SAREG,	TSHORT|TUSHORT,
		0,	RLEFT,
		"", },

/* convert char to (unsigned) short. */
{ SCONV,	INAREG,
	SO_N,	TCHAR,
	SAREG,	TSHORT|TUSHORT,
		XSL(A),	RESC1,
		"	movsbl AL,A1\n", },

/* convert unsigned char to (u)short. */
{ SCONV,	INAREG,
	SO_N,	TUCHAR,
	SAREG,	TSHORT|TUSHORT,
		NEEDS(NREG(A, 1), NSL(A)),	RESC1,
		"	movzbl AL,A1\n", },
#else
/* convert char to (unsigned) short. */
{ SCONV,	ININT,
	SB_O_N,	TCHAR,
	SAREG,	TSHORT|TUSHORT,
		XSL(A),	RESC1,
		"	movsbw AL,A1\n", },

/* convert unsigned char to (u)short. */
{ SCONV,	ININT,
	SB_O_N,	TUCHAR,
	SAREG,	TSHORT|TUSHORT,
		NEEDS(NREG(A, 1), NSL(A)),	RESC1,
		"	movzbw AL,A1\n", },
#endif

/* convert signed char to int (or pointer). */
#ifdef NOBREGS
{ SCONV,	ININT,
	SAREG,	TCHAR|TUCHAR,
	SAREG,	TWORD|TPOINT,
		0,	RLEFT,
		"", },

{ SCONV,	ININT,
	SO_N,	TCHAR,
	SAREG,	TWORD|TPOINT,
		NEEDS(NREG(A, 1), NSL(A)),	RESC1,
		"	movsbl AL,A1\n", },

/* convert unsigned char to (u)int. */
{ SCONV,	ININT,
	SO_N,	TUCHAR,
	SAREG,	TWORD,
		NEEDS(NREG(A, 1), NSL(A)),	RESC1,
		"	movzbl AL,A1\n", },

/* convert char to (u)long long */
{ SCONV,	INLL,
	SAREG,	TCHAR,
	SANY,	TLL,
		NEEDS(NREG(C, 1), NSL(C),
		    NRES(EAXEDX), NLEFT(EAX)),	RESC1,
		"	cltd\n", },

/* convert unsigned char (in mem) to (u)long long */
{ SCONV,	INLL,
	SO_N,	TUCHAR,
	SANY,	TLL,
		NEEDS(NREG(C, 1), NSL(C)),	RESC1,
		"	movzbl AL,A1\n	xorl U1,U1\n", },

/* convert unsigned char to (u)long long */
{ SCONV,	INLL,
	SAREG,	TUCHAR,
	SANY,	TLL,
		NEEDS(NREG(C, 1), NSL(C)),	RESC1,
		"	movl AL,A1\n	xorl U1,U1\n", },

/* convert (u)char (in register) to double */
{ SCONV,	INFL,
	SAREG,	TCHAR|TUCHAR,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
		NEEDS(NREG(D, 1), NTEMP(1)),	RESC1,
		"	movl AL,A2\n 	fildl A2\n", },
#else
{ SCONV,	ININT,
	SB_O_N,	TCHAR,
	SAREG,	TWORD|TPOINT,
		NEEDS(NREG(A, 1), NSL(A)),	RESC1,
		"	movsbl AL,A1\n", },

/* convert unsigned char to (u)int. */
{ SCONV,	ININT,
	SB_O_N,	TUCHAR,
	SAREG,	TWORD,
		NEEDS(NREG(A, 1), NSL(A)),	RESC1,
		"	movzbl AL,A1\n", },

/* convert char to (u)long long */
{ SCONV,	INLL,
	SB_O_N,	TCHAR,
	SANY,	TLL,
		NEEDS(NREG(C, 1), NSL(C), NRES(EAXEDX), 
		    NEVER(EAX), NEVER(EDX)),	RESC1,
		"	movsbl AL,%eax\n	cltd\n", },

/* convert unsigned char to (u)long long */
{ SCONV,	INLL,
	SB_O_N,	TUCHAR,
	SANY,			TLL,
		NEEDS(NREG(C, 1), NSL(C)),	RESC1,
		"	movzbl AL,A1\n	xorl U1,U1\n", },

/* convert char (in register) to double XXX - use NTEMP */
{ SCONV,	INFL,
	SB_O_N,	TCHAR,
	SHFL,			TLDOUBLE|TDOUBLE|TFLOAT,
		NEEDS(NREG(A, 1), NSL(A), NREG(D, 1)),	RESC2,
		"	movsbl AL,A1\n	pushl A1\n"
		"	fildl (%esp)\n	addl $4,%esp\n", },

/* convert (u)char (in register) to double XXX - use NTEMP */
{ SCONV,	INFL,
	SB_O_N,	TUCHAR,
	SHFL,			TLDOUBLE|TDOUBLE|TFLOAT,
		NEEDS(NREG(A, 1), NSL(A), NREG(D, 1)),	RESC2,
		"	movzbl AL,A1\n	pushl A1\n"
		"	fildl (%esp)\n	addl $4,%esp\n", },
#endif

/* short to something */

/* convert (u)short to (u)short. */
{ SCONV,	INAREG,
	SAREG,	TSHORT|TUSHORT,
	SAREG,	TSHORT|TUSHORT,
		0,	RLEFT,
		"", },

#ifdef NOBREGS
/* convert short (in memory) to char */
{ SCONV,	INAREG,
	SO_N,	TSHORT|TUSHORT,
	SAREG,		TCHAR|TUCHAR,
		XSL(A),		RESC1,
		"	movzbl AL,A1\n", },

/* convert short (in reg) to char. */
{ SCONV,	INAREG,
	SAREG,	TSHORT|TUSHORT,
	SAREG,	TCHAR|TUCHAR,
		NEEDS(NOLEFT(ESI), NOLEFT(EDI)),    RLEFT,
		"	movsbl AL,AL\n", },

/* convert short to (u)int. */
{ SCONV,	ININT,
	SO_N,	TSHORT,
	SAREG,	TWORD,
		NEEDS(NREG(A, 1), NSL(A)),	RESC1,
		"	movswl AL,A1\n", },

/* convert unsigned short to (u)int. */
{ SCONV,	ININT,
	SO_N,	TUSHORT,
	SAREG,	TWORD,
		NEEDS(NREG(A, 1), NSL(A)),	RESC1,
		"	movzwl AL,A1\n", },

/* convert unsigned short to (u)int (in reg) */
{ SCONV,	INAREG,
	SAREG,	TSHORT|TUSHORT,
	SAREG,	TWORD,
		0,	RLEFT,
		"", },
#else
/* convert short (in memory) to char */
{ SCONV,	INCH,
	SO_N,	TSHORT|TUSHORT,
	SHCH,		TCHAR|TUCHAR,
		NEEDS(NREG(B, 1), NSL(B)),	RESC1,
		"	movb AL,A1\n", },

/* convert short (in reg) to char. */
{ SCONV,	INCH,
	SA_O_N,	TSHORT|TUSHORT,
	SHCH,			TCHAR|TUCHAR,
		NEEDS(NREG(B, 1), NSL(B),
		    NOLEFT(ESI), NOLEFT(EDI)),    RESC1,
		"ZM", },
/* convert short to (u)int. */
{ SCONV,	ININT,
	SA_O_N,	TSHORT,
	SAREG,	TWORD,
		NEEDS(NREG(A, 1), NSL(A)),	RESC1,
		"	movswl AL,A1\n", },

/* convert unsigned short to (u)int. */
{ SCONV,	ININT,
	SA_O_N,	TUSHORT,
	SAREG,	TWORD,
		NEEDS(NREG(A, 1), NSL(A)),	RESC1,
		"	movzwl AL,A1\n", },
#endif


/* convert short to (u)long long */
{ SCONV,	INLL,
	SA_O_N,	TSHORT,
	SHLL,			TLL,
		NEEDS(NREG(C, 1), NSL(C), NRES(EAXEDX), 
		    NEVER(EAX), NEVER(EDX)),	RESC1,
		"	movswl AL,%eax\n	cltd\n", },

/* convert unsigned short to (u)long long */
{ SCONV,	INLL,
	SA_O_N,	TUSHORT,
	SHLL,			TLL,
		NEEDS(NREG(C, 1), NSL(C)),	RESC1,
		"	movzwl AL,A1\n	xorl U1,U1\n", },

/* convert short (in memory) to float/double */
{ SCONV,	INFL,
	SO_N,	TSHORT,
	SDREG,	TLDOUBLE|TDOUBLE|TFLOAT,
		NEEDS(NREG(D, 1)),	RESC1,
		"	fild AL\n", },

/* convert short (in register) to float/double */
{ SCONV,	INFL,
	SAREG,	TSHORT,
	SDREG,	TLDOUBLE|TDOUBLE|TFLOAT,
		NEEDS(NREG(D, 1), NTEMP(1)), RESC1,
		"	pushw AL\n	fild (%esp)\n	addl $2,%esp\n", },

/* convert unsigned short to double XXX - use NTEMP */
{ SCONV,	INFL,
	SA_O_N,	TUSHORT,
	SHFL,			TLDOUBLE|TDOUBLE|TFLOAT,
		NEEDS(NREG(A, 1), NSL(A), 
		    NREG(D, 1), NTEMP(1)),	RESC2,
		"	movzwl AL,A1\n	movl A1,A3\n"
		"	fildl A3\n", },

/* int to something */

/* convert int to char. This is done when register is loaded */
#ifdef NOBREGS
{ SCONV,	INAREG,
	SAREG,	TWORD|TPOINT,
	SAREG,	TCHAR|TUCHAR,
#if 0
		NEEDS(NOLEFT(ESI), NOLEFT(EDI)),	RLEFT,
		"	movsbl ZT,AL\n", },
#else
		0,	RLEFT,
		"", },
#endif
#else
{ SCONV,	INCH,
	SAREG,	TWORD|TPOINT,
	SANY,	TCHAR|TUCHAR,
		NEEDS(NREG(B, 1), NSL(B),
		    NOLEFT(ESI), NOLEFT(EDI)),	RESC1,
		"ZM", },
#endif

/* convert int to short. Nothing to do */
{ SCONV,	INAREG,
	SAREG,	TWORD|TPOINT,
	SANY,	TSHORT|TUSHORT,
		0,	RLEFT,
		"", },

/* convert signed int to (u)long long */
{ SCONV,	INLL,
	SHINT,	TSWORD,
	SHLL,	TLL,
		NEEDS(NREG(C, 1), NSL(C), NLEFT(EAX),
		    NEVER(EAX), NEVER(EDX), NRES(EAXEDX)),	RESC1,
		"	cltd\n", },

/* convert unsigned int to (u)long long */
{ SCONV,	INLL,
	SA_O_N,	TUWORD|TPOINT,
	SHLL,	TLL,
		NEEDS(NREG(C, 1), NSL(C)),	RESC1,
		"	movl AL,A1\n	xorl U1,U1\n", },

/* convert signed int (in memory) to double */
{ SCONV,	INFL,
	SO_N,	TSWORD,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
		NEEDS(NREG(D, 1)),	RESC1,
		"	fildl AL\n", },

/* convert signed int (in register) to double */
{ SCONV,	INFL,
	SAREG,	TSWORD,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
		NEEDS(NREG(D, 1), NTEMP(1)),	RESC1,
		"	movl AL,A2\n	fildl A2\n", },

/* convert unsigned int (reg&mem) to double */
{ SCONV,       INFL,
	SA_O_N,	TUWORD,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
		NEEDS(NREG(D, 1), NTEMP(1)),	RESC1,
		"	pushl $0\n"
		"	pushl AL\n"
		"	fildq (%esp)\n"
		"	addl $8,%esp\n", },

/* long long to something */

#ifdef NOBREGS
/* convert (u)long long to (u)char (mem->reg) */
{ SCONV,	INAREG,
	SO_N,	TLL,
	SANY,	TUCHAR,
		XSL(A),	RESC1,
		"	movzbl AL,A1\n", },

{ SCONV,	INAREG,
	SO_N,	TLL,
	SANY,	TCHAR,
		XSL(A),	RESC1,
		"	movsbl AL,A1\n", },

/* convert (u)long long to (u)char (reg->reg, hopefully nothing) */
{ SCONV,	INAREG,
	SHLL,	TLL,
	SANY,	TCHAR|TUCHAR,
		NEEDS(NREG(A, 1), NSL(A), NTEMP(1)),	RESC1,
		"ZS", },
#else
/* convert (u)long long to (u)char (mem->reg) */
{ SCONV,	INCH,
	SO_N,	TLL,
	SANY,	TCHAR|TUCHAR,
		NEEDS(NREG(B, 1), NSL(B)),	RESC1,
		"	movb AL,A1\n", },

/* convert (u)long long to (u)char (reg->reg, hopefully nothing) */
{ SCONV,	INCH,
	SHLL,	TLL,
	SANY,	TCHAR|TUCHAR,
		NEEDS(NREG(B, 1), NSL(B), NTEMP(1)),	RESC1,
		"ZS", },
#endif

/* convert (u)long long to (u)short (mem->reg) */
{ SCONV,	INAREG,
	SO_N,	TLL,
	SAREG,	TSHORT|TUSHORT,
		NEEDS(NREG(A, 1), NSL(A)),	RESC1,
		"	movw AL,A1\n", },

/* convert (u)long long to (u)short (reg->reg, hopefully nothing) */
{ SCONV,	INAREG,
	SC_O_N,	TLL,
	SAREG,	TSHORT|TUSHORT,
		NEEDS(NREG(A, 1), NSL(A), NTEMP(1)),	RESC1,
		"ZS", },

/* convert long long to int (mem->reg) */
{ SCONV,	INAREG,
	SO_N,	TLL,
	SAREG,	TWORD|TPOINT,
		NEEDS(NREG(A, 1), NSL(A)),    RESC1,
		"	movl AL,A1\n", },

/* convert long long to int (reg->reg, hopefully nothing) */
{ SCONV,	INAREG,
	SC_O_N,	TLL,
	SAREG,	TWORD|TPOINT,
		NEEDS(NREG(A, 1), NSL(A), NTEMP(1)),	RESC1,
		"ZS", },

/* convert long long (in memory) to floating */
{ SCONV,	INFL,
	SO_N,	TLONGLONG,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
		NEEDS(NREG(D, 1)),	RESC1,
		"	fildq AL\n", },

/* convert long long (in register) to floating */
{ SCONV,	INFL,
	SHLL,	TLONGLONG,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
		NEEDS(NREG(D, 1), NTEMP(1)),	RESC1,
		"	pushl UL\n	pushl AL\n"
		"	fildq (%esp)\n	addl $8,%esp\n", },

/* convert unsigned long long to floating */
{ SCONV,	INFL,
	SCREG,	TULONGLONG,
	SDREG,	TLDOUBLE|TDOUBLE|TFLOAT,
		NEEDS(NREG(D, 1), NTEMP(1)),	RESC1,
		"ZJ", },

/* float to something */

#if 0 /* go via int by adding an extra sconv in clocal() */
/* convert float/double to (u) char. XXX should use NTEMP here */
{ SCONV,	INCH,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
	SHCH,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NEEDS(NREG(B, 1)),	RESC1,
		"	subl $4,%esp\n	fistpl (%esp)\n	popl A1\n", },

/* convert float/double to (u) int/short/char. XXX should use NTEMP here */
{ SCONV,	INCH,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
	SHCH,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
		NEEDS(NREG(C, 1)),	RESC1,
		"	subl $4,%esp\n	fistpl (%esp)\n	popl A1\n", },
#endif

/* convert float/double to int. XXX should use NTEMP here */
{ SCONV,	INAREG,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
	SAREG,	TSWORD,
		NEEDS(NREG(A, 1), NTEMP(3)),	RESC1,
		"	fnstcw A2\n"
		"	fnstcw 4+A2\n"
		"	movb $12,1+A2\n"
		"	fldcw A2\n"
		"	fistpl 8+A2\n"
		"	movl 8+A2,A1\n"
		"	fldcw 4+A2\n", },

/* convert float/double to unsigned int. */
{ SCONV,       INAREG,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
	SAREG,	TUWORD,
		NEEDS(NREG(A, 1), NTEMP(4)),	RESC1,
		"	fnstcw A2\n"
		"	fnstcw 4+A2\n"
		"	movb $12,1+A2\n"
		"	fldcw A2\n"
		"	fistpq 8+A2\n"
		"	movl 8+A2,A1\n"
		"	fldcw 4+A2\n", },

/* convert float/double (in register) to long long */
{ SCONV,	INLL,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
	SHLL,	TLONGLONG,
		NEEDS(NREG(C, 1), NTEMP(4)),	RESC1,
		"	fnstcw A2\n"
		"	fnstcw 4+A2\n"
		"	movb $12,1+A2\n"
		"	fldcw A2\n"
		"	fistpq 8+A2\n"
		"	movl 8+A2,A1\n"
		"	movl 12+A2,U1\n"
		"	fldcw 4+A2\n", },

/* convert float/double (in register) to unsigned long long */
{ SCONV,	INLL,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
	SHLL,	TULONGLONG,
		NEEDS(NREG(C, 1), NTEMP(4)),	RESC1,
		"	fnstcw A2\n"
		"	fnstcw 4+A2\n"
		"	movb $7,1+A2\n"	/* 64-bit, round down  */
		"	fldcw A2\n"
		"	movl $0x5f000000, 8+A2\n"	/* (float)(1<<63) */
		"	fsubs 8+A2\n"	/* keep in range of fistpq */
		"	fistpq 8+A2\n"
		"	xorb $0x80,15+A2\n"	/* addq $1>>63 to 8(%esp) */
		"	movl 8+A2,A1\n"
		"	movl 12+A2,U1\n"
		"	fldcw 4+A2\n", },

/* slut sconv */

/*
 * Subroutine calls.
 */

{ UCALL,	FOREFF,
	SCON,	TANY,
	SANY,	TANY,
		0,	0,
		"	call CL\nZC", },

{ UCALL,	INAREG|FOREFF,
	SCON,	TANY,
	SAREG,	TSHORT|TUSHORT|TWORD|TPOINT,
		NEEDS(NREG(A, 1), NSL(A)),	RESC1,	/* should be 0 */
		"	call CL\nZC", },

{ UCALL,	INBREG,
	SCON,	TANY,
	SBREG,	TCHAR|TUCHAR,
		NEEDS(NREG(B, 1)),	RESC1,	/* should be 0 */
		"	call CL\nZC", },

{ UCALL,	INCREG,
	SCON,	TANY,
	SCREG,	TANY,
		NEEDS(NREG(C, 1), NSL(C)),	RESC1,	/* should be 0 */
		"	call CL\nZC", },

{ UCALL,	INDREG,
	SCON,	TANY,
	SDREG,	TANY,
		NEEDS(NREG(D, 1), NSL(D)),	RESC1,	/* should be 0 */
		"	call CL\nZC", },

{ UCALL,	FOREFF,
	SAREG,	TANY,
	SANY,	TANY,
		0,	0,
		"	call *AL\nZC", },

{ UCALL,	INAREG,
	SAREG,	TANY,
	SANY,	TANY,
		XSL(A),	RESC1,	/* should be 0 */
		"	call *AL\nZC", },

{ UCALL,	INBREG,
	SAREG,	TANY,
	SANY,	TANY,
		XSL(B),	RESC1,	/* should be 0 */
		"	call *AL\nZC", },

{ UCALL,	INCREG,
	SAREG,	TANY,
	SANY,	TANY,
		XSL(C),	RESC1,	/* should be 0 */
		"	call *AL\nZC", },

{ UCALL,	INDREG,
	SAREG,	TANY,
	SANY,	TANY,
		XSL(D),	RESC1,	/* should be 0 */
		"	call *AL\nZC", },

{ USTCALL,	FOREFF,
	SCON,	TANY,
	SANY,	TANY,
		XSL(A),	0,
		"	call CL\nZC", },

{ USTCALL,	INAREG,
	SCON,	TANY,
	SANY,	TANY,
		XSL(A),	RESC1,	/* should be 0 */
		"	call CL\nZC", },

{ USTCALL,	INAREG,
	SA_N,	TANY,
	SANY,	TANY,
		XSL(A),	RESC1,	/* should be 0 */
		"	call *AL\nZC", },

/*
 * The next rules handle all binop-style operators.
 */
/* Special treatment for long long */
{ PLUS,		INLL|FOREFF,
	SHLL,		TLL,
	SC_O_N,	TLL,
		0,	RLEFT,
		"	addl AR,AL\n	adcl UR,UL\n", },

{ PLUS,		INLL|FOREFF,
	SC_O_N,	TLL,
	SC_C,		TLL,
		0,	RLEFT,
		"	addl AR,AL\n	adcl UR,UL\n", },

/* Special treatment for long long  XXX - fix commutative check */
{ PLUS,		INLL|FOREFF,
	SC_O_N,	TLL,
	SHLL,			TLL,
		0,	RRIGHT,
		"	addl AL,AR\n	adcl UL,UR\n", },

{ PLUS,		INFL,
	SHFL,		TDOUBLE,
	SO_N,	TDOUBLE,
		0,	RLEFT,
		"	faddl AR\n", },

{ PLUS,		INFL|FOREFF,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
		0,	RLEFT,
		"	faddp\n", },

#ifdef NOBREGS
{ PLUS,		INAREG|FOREFF,
	SA_O_N,	TAREG|TPOINT,
	SONE,	TANY,
		0,	RLEFT,
		"	incl AL\n", },

{ PLUS,		FOREFF,
	SO_N,	TSHORT|TUSHORT,
	SONE,	TANY,
		0,	RLEFT,
		"	incw AL\n", },

{ PLUS,		FOREFF,
	SO_N,	TCHAR|TUCHAR,
	SONE,	TANY,
		0,	RLEFT,
		"	incb AL\n", },
#else
{ PLUS,		INAREG|FOREFF,
	SA_O_N,	TWORD|TPOINT,
	SONE,	TANY,
		0,	RLEFT,
		"	incl AL\n", },

{ PLUS,		INAREG|FOREFF,
	SA_O_N,	TSHORT|TUSHORT,
	SONE,	TANY,
		0,	RLEFT,
		"	incw AL\n", },

{ PLUS,		INCH|FOREFF,
	SB_O_N,	TCHAR|TUCHAR,
	SONE,	TANY,
		0,	RLEFT,
		"	incb AL\n", },
#endif

{ PLUS,		INAREG,
	SAREG,	TAREG,
	SAREG,	TAREG,
		NEEDS(NREG(A,1),NSL(A),NSR(A)),	RESC1,
		"	leal (AL,AR),A1\n", },

#ifdef NOBREGS
{ MINUS,	INAREG|FOREFF,
	SA_O_N,	TAREG|TPOINT,
	SONE,			TANY,
		0,	RLEFT,
		"	decl AL\n", },

{ MINUS,	FOREFF,
	SO_N,	TSHORT|TUSHORT,
	SONE,			TANY,
		0,	RLEFT,
		"	decw AL\n", },

{ MINUS,	FOREFF,
	SO_N,	TCHAR|TUCHAR,
	SONE,	TANY,
		0,	RLEFT,
		"	decb AL\n", },
#else
{ MINUS,	INAREG|FOREFF,
	SA_O_N,	TWORD|TPOINT,
	SONE,			TANY,
		0,	RLEFT,
		"	decl AL\n", },

{ MINUS,	INAREG|FOREFF,
	SA_O_N,	TSHORT|TUSHORT,
	SONE,			TANY,
		0,	RLEFT,
		"	decw AL\n", },

{ MINUS,	INCH|FOREFF,
	SB_O_N,	TCHAR|TUCHAR,
	SONE,	TANY,
		0,	RLEFT,
		"	decb AL\n", },
#endif

/* address as register offset, negative */
{ MINUS,	INLL|FOREFF,
	SHLL,	TLL,
	SC_O_N,	TLL,
		0,	RLEFT,
		"	subl AR,AL\n	sbbl UR,UL\n", },

{ MINUS,	INLL|FOREFF,
	SC_O_N,	TLL,
	SC_C,	TLL,
		0,	RLEFT,
		"	subl AR,AL\n	sbbl UR,UL\n", },

{ MINUS,	INFL,
	SHFL,	TDOUBLE,
	SO_N,	TDOUBLE,
		0,	RLEFT,
		"	fsubl AR\n", },

{ MINUS,	INFL|FOREFF,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
		0,	RLEFT,
		"	fsubZAp\n", },

/* Simple r/m->reg ops */
/* m/r |= r */
{ OPSIMP,	INAREG|FOREFF|FORCC,
	SA_O_N,	TWORD|TPOINT,
	SAREG,			TWORD|TPOINT,
		0,	RLEFT|RESCC,
		"	Ol AR,AL\n", },

/* r |= r/m */
{ OPSIMP,	INAREG|FOREFF|FORCC,
	SAREG,			TWORD|TPOINT,
	SA_O_N,	TWORD|TPOINT,
		0,	RLEFT|RESCC,
		"	Ol AR,AL\n", },

#ifdef NOBREGS
/* m/r |= r */
{ OPSIMP,	INAREG|FOREFF|FORCC,
	SO_N,	TSHORT|TUSHORT,
	SAREG,		TSHORT|TUSHORT,
		0,	RLEFT|RESCC,
		"	Ow AR,AL\n", },

/* r |= r/m */
{ OPSIMP,	INAREG|FOREFF|FORCC,
	SAREG,		TSHORT|TUSHORT,
	SA_O_N,	TSHORT|TUSHORT,
		0,	RLEFT|RESCC,
		"	Ow AR,AL\n", },

/* m/r |= r */
{ OPSIMP,	INAREG|FOREFF|FORCC,
	SAREG,	TCHAR|TUCHAR,
	SAREG,	TCHAR|TUCHAR,
		0,	RLEFT|RESCC,
		"	Ol AR,AL\n", },

{ OPSIMP,	FOREFF|FORCC,
	SO_N,	TCHAR|TUCHAR,
	SCON,	TANY,
		0,	RLEFT|RESCC,
		"	Ob AR,AL\n", },

{ OPSIMP,	INAREG|FOREFF|FORCC,
	SAREG,	TSHORT|TUSHORT,
	SCON,	TANY,
		0,	RLEFT|RESCC,
		"	Ol AR,AL\n", },
#else
/* m/r |= r */
{ OPSIMP,	INAREG|FOREFF|FORCC,
	SA_O_N,	TSHORT|TUSHORT,
	SHINT,		TSHORT|TUSHORT,
		0,	RLEFT|RESCC,
		"	Ow AR,AL\n", },

/* r |= r/m */
{ OPSIMP,	INAREG|FOREFF|FORCC,
	SHINT,		TSHORT|TUSHORT,
	SA_O_N,	TSHORT|TUSHORT,
		0,	RLEFT|RESCC,
		"	Ow AR,AL\n", },

/* m/r |= r */
{ OPSIMP,	INCH|FOREFF|FORCC,
	SHCH,		TCHAR|TUCHAR,
	SB_O_N,	TCHAR|TUCHAR,
		0,	RLEFT|RESCC,
		"	Ob AR,AL\n", },

/* r |= r/m */
{ OPSIMP,	INCH|FOREFF|FORCC,
	SHCH,		TCHAR|TUCHAR,
	SB_O_N,	TCHAR|TUCHAR,
		0,	RLEFT|RESCC,
		"	Ob AR,AL\n", },

{ OPSIMP,	INCH|FOREFF|FORCC,
	SB_O_N,	TCHAR|TUCHAR,
	SCON,	TANY,
		0,	RLEFT|RESCC,
		"	Ob AR,AL\n", },

{ OPSIMP,	INAREG|FOREFF|FORCC,
	SA_O_N,	TSHORT|TUSHORT,
	SCON,	TANY,
		0,	RLEFT|RESCC,
		"	Ow AR,AL\n", },
#endif

/* m/r |= const */
{ OPSIMP,	INAREG|FOREFF|FORCC,
	SA_O_N,	TWORD|TPOINT,
	SCON,	TWORD|TPOINT,
		0,	RLEFT|RESCC,
		"	Ol AR,AL\n", },

/* r |= r/m */
{ OPSIMP,	INLL|FOREFF,
	SHLL,	TLL,
	SC_O_N,	TLL,
		0,	RLEFT,
		"	Ol AR,AL\n	Ol UR,UL\n", },

/* m/r |= r/const */
{ OPSIMP,	INLL|FOREFF,
	SC_O_N,	TLL,
	SC_C,	TLL,
		0,	RLEFT,
		"	Ol AR,AL\n	Ol UR,UL\n", },

/* Try use-reg instructions first */
{ PLUS,		INAREG,
	SAREG,	TWORD|TPOINT,
	SCON,	TANY,
		XSL(A),	RESC1,
		"	leal CR(AL),A1\n", },

{ MINUS,	INAREG,
	SAREG,	TWORD|TPOINT,
	SPCON,	TANY,
		XSL(A),	RESC1,
		"	leal -CR(AL),A1\n", },


/*
 * The next rules handle all shift operators.
 */
#ifdef NOBREGS
/* (u)longlong left shift is emulated */
{ LS,	INCREG,
	SCREG,	TLL,
	SAREG,	TAREG,
		NEEDS(NLEFT(EAXEDX), NRIGHT(ECX), NRES(EAXEDX)),	RLEFT,
		"ZO", },
/* r/m <<= r */
{ LS,	INAREG|FOREFF,
	SA_O_N,	TWORD,
	SAREG,			TAREG,
		NEEDS(NOLEFT(ECX), NRIGHT(ECX)),	RLEFT,
		"	sall ZT,AL\n", },

/* r/m <<= const */
{ LS,	INAREG|FOREFF,
	SA_O_N,	TWORD,
	SCON,	TANY,
		0,	RLEFT,
		"	sall AR,AL\n", },

/* r/m <<= r */
{ LS,	FOREFF,
	SO_N,	TSHORT|TUSHORT,
	SAREG,		TAREG,
		NEEDS(NOLEFT(ECX), NRIGHT(ECX)),	RLEFT,
		"	shlw ZT,AL\n", },

/* r/m <<= r */
{ LS,	FOREFF,
	SO_N,	TCHAR|TUCHAR,
	SAREG,		TAREG,
		NEEDS(NOLEFT(ECX), NRIGHT(ECX)),	RLEFT,
		"	shlb ZT,AL\n", },

/* r/m <<= const */
{ LS,	INAREG|FOREFF,
	SAREG,	TAREG,
	SCON,	TANY,
		0,	RLEFT,
		"	shll AR,AL\n", },

{ LS,	INAREG|FOREFF,
	SAREG,	TAREG,
	SAREG,	TAREG,
		NEEDS(NOLEFT(ECX), NRIGHT(ECX)),	RLEFT,
		"	shll ZT,AL\n", },
#else
/* (u)longlong left shift is emulated */
{ LS,	INCREG,
	SCREG,	TLL,
	SHCH,	TCHAR|TUCHAR,
		NEEDS(NLEFT(EAXEDX), NRIGHT(CL),NRES(EAXEDX)),	RLEFT,
		"ZO", },
/* r/m <<= r */
{ LS,	INAREG|FOREFF,
	SA_O_N,	TWORD,
	SHCH,		TCHAR|TUCHAR,
		NEEDS(NOLEFT(ECX), NRIGHT(CL)),	RLEFT,
		"	sall AR,AL\n", },
/* r/m <<= const */
{ LS,	INAREG|FOREFF,
	SA_O_N,	TWORD,
	SCON,	TANY,
		0,	RLEFT,
		"	sall AR,AL\n", },
/* r/m <<= r */
{ LS,	INAREG|FOREFF,
	SA_O_N,	TSHORT|TUSHORT,
	SHCH,			TCHAR|TUCHAR,
		NEEDS(NOLEFT(ECX), NRIGHT(CL)),	RLEFT,
		"	shlw AR,AL\n", },
/* r/m <<= const */
{ LS,	INAREG|FOREFF,
	SA_O_N,	TSHORT|TUSHORT,
	SCON,	TANY,
		0,	RLEFT,
		"	shlw AR,AL\n", },
{ LS,	INCH|FOREFF,
	SB_O_N,	TCHAR|TUCHAR,
	SHCH,			TCHAR|TUCHAR,
		NEEDS(NOLEFT(ECX), NRIGHT(CL)),	RLEFT,
		"	salb AR,AL\n", },

{ LS,	INCH|FOREFF,
	SB_O_N,	TCHAR|TUCHAR,
	SCON,			TANY,
		0,	RLEFT,
		"	salb AR,AL\n", },
#endif

#ifdef NOBREGS
/* (u)longlong right shift is emulated */
{ RS,	INCREG,
	SCREG,	TLL,
	SAREG,	TAREG,
		NEEDS(NLEFT(EAXEDX), NRIGHT(ECX),NRES(EAXEDX)),	RLEFT,
		"ZO", },

/* right-shift word in memory or reg */
{ RS,	INAREG|FOREFF,
	SA_O_N,	TWORD,
	SAREG,			TAREG,
		NEEDS(NOLEFT(ECX), NRIGHT(ECX)),	RLEFT,
		"	sZUrl ZT,AL\n", },

/* as above but using a constant */
{ RS,	INAREG|FOREFF,
	SA_O_N,	TWORD,
	SCON,			TAREG,
		0,		RLEFT,
		"	sZUrl AR,AL\n", },

/* short in memory */
{ RS,	FOREFF,
	SO_N,	TSHORT|TUSHORT,
	SAREG,		TAREG,
		NEEDS(NOLEFT(ECX), NRIGHT(ECX)),	RLEFT,
		"	sZUrw ZT,AL\n", },

{ RS,	FOREFF,
	SO_N,	TSHORT|TUSHORT,
	SCON,		TAREG,
		0,	RLEFT,
		"	sZUrw AR,AL\n", },

{ RS,	FOREFF,
	SO_N,	TCHAR|TUCHAR,
	SAREG,		TAREG,
		NEEDS(NOLEFT(ECX), NRIGHT(ECX)),	RLEFT,
		"	sZUrl ZT,AL\n", },
#else
/* (u)longlong right shift is emulated */
{ RS,	INCREG,
	SCREG,	TLL,
	SHCH,	TCHAR|TUCHAR,
		NEEDS(NLEFT(EAXEDX), NRIGHT(CL),NRES(EAXEDX)),	RLEFT,
		"ZO", },

{ RS,	INAREG|FOREFF,
	SA_O_N,	TSWORD,
	SHCH,			TCHAR|TUCHAR,
		NEEDS(NOLEFT(ECX), NRIGHT(CL)),	RLEFT,
		"	sarl AR,AL\n", },

{ RS,	INAREG|FOREFF,
	SA_O_N,	TSWORD,
	SCON,			TANY,
		0,		RLEFT,
		"	sarl AR,AL\n", },

{ RS,	INAREG|FOREFF,
	SA_O_N,	TUWORD,
	SHCH,			TCHAR|TUCHAR,
		NEEDS(NOLEFT(ECX), NRIGHT(CL)),	RLEFT,
		"	shrl AR,AL\n", },

{ RS,	INAREG|FOREFF,
	SA_O_N,	TUWORD,
	SCON,			TANY,
		0,		RLEFT,
		"	shrl AR,AL\n", },

{ RS,	INAREG|FOREFF,
	SA_O_N,	TSHORT,
	SHCH,			TCHAR|TUCHAR,
		NEEDS(NOLEFT(ECX), NRIGHT(CL)),	RLEFT,
		"	sarw AR,AL\n", },

{ RS,	INAREG|FOREFF,
	SA_O_N,	TSHORT,
	SCON,			TANY,
		0,		RLEFT,
		"	sarw AR,AL\n", },
{ RS,	INAREG|FOREFF,
	SA_O_N,	TUSHORT,
	SHCH,			TCHAR|TUCHAR,
		NEEDS(NOLEFT(ECX), NRIGHT(CL)),	RLEFT,
		"	shrw AR,AL\n", },

{ RS,	INAREG|FOREFF,
	SA_O_N,	TUSHORT,
	SCON,			TANY,
		0,		RLEFT,
		"	shrw AR,AL\n", },
{ RS,	INCH|FOREFF,
	SB_O_N,	TCHAR,
	SHCH,			TCHAR|TUCHAR,
		NEEDS(NOLEFT(ECX), NRIGHT(CL)),	RLEFT,
		"	sarb AR,AL\n", },

{ RS,	INCH|FOREFF,
	SB_O_N,	TCHAR,
	SCON,			TANY,
		0,		RLEFT,
		"	sarb AR,AL\n", },
{ RS,	INCH|FOREFF,
	SB_O_N,	TUCHAR,
	SHCH,			TCHAR|TUCHAR,
		NEEDS(NOLEFT(ECX), NRIGHT(CL)),	RLEFT,
		"	shrb AR,AL\n", },

{ RS,	INCH|FOREFF,
	SB_O_N,	TUCHAR,
	SCON,			TANY,
		0,		RLEFT,
		"	shrb AR,AL\n", },
#endif

/*
 * The next rules takes care of assignments. "=".
 */
{ ASSIGN,	FORCC|FOREFF|INLL,
	SHLL,		TLL,
	SZERO,		TANY,
		0,	RDEST,
		"	xorl AL,AL\n	xorl UL,UL\n", },

{ ASSIGN,	FORCC|FOREFF|INLL,
	SHLL,		TLL,
	SMILWXOR,	TANY,
		0,	RDEST,
		"	xorl AL,AL\n	movl UR,UL\n", },

{ ASSIGN,	FORCC|FOREFF|INLL,
	SHLL,		TLL,
	SMIHWXOR,	TANY,
		0,	RDEST,
		"	movl AR,AL\n	xorl UL,UL\n", },

{ ASSIGN,	FOREFF|INLL,
	SHLL,		TLL,
	SCON,		TANY,
		0,	RDEST,
		"	movl AR,AL\n	movl UR,UL\n", },

{ ASSIGN,	FOREFF,
	SC_O_N,	TLL,
	SCON,		TANY,
		0,	0,
		"	movl AR,AL\n	movl UR,UL\n", },

{ ASSIGN,	FOREFF,
	SO_N,	TLL,
	SZERO,		TANY,
		0,	0,
		"	andl $0,AL\n	andl $0,UL\n", },

{ ASSIGN,	FORCC|FOREFF|INAREG,
	SAREG,	TWORD|TPOINT,
	SZERO,		TANY,
		0,	RDEST,
		"	xorl AL,AL\n", },

{ ASSIGN,	FOREFF,
	SO_N,	TWORD|TPOINT,
	SZERO,		TANY,
		0,	0,
		"	andl $0,AL\n", },

{ ASSIGN,	FOREFF,
	SA_O_N,	TWORD|TPOINT,
	SCON,		TANY,
		0,	0,
		"	movl AR,AL\n", },

{ ASSIGN,	FOREFF|INAREG,
	SAREG,	TWORD|TPOINT,
	SCON,		TANY,
		0,	RDEST,
		"	movl AR,AL\n", },

{ ASSIGN,	FORCC|FOREFF|INAREG,
	SAREG,	TSHORT|TUSHORT,
	SMIXOR,		TANY,
		0,	RDEST,
		"	xorw AL,AL\n", },

{ ASSIGN,	FOREFF,
	SA_O_N,	TSHORT|TUSHORT,
	SCON,		TANY,
		0,	0,
		"	movw AR,AL\n", },

{ ASSIGN,	FOREFF|INAREG,
	SAREG,	TSHORT|TUSHORT,
	SCON,		TANY,
		0,	RDEST,
		"	movw AR,AL\n", },

#ifdef NOBREGS
{ ASSIGN,	INAREG|FOREFF,
	SAREG,			TUCHAR,
	SO_N,	TUCHAR,
		0,	RDEST,
		"	movzbl AR,AL\n", },

{ ASSIGN,	INAREG|FOREFF,
	SAREG,			TCHAR,
	SO_N,	TCHAR,
		0,	RDEST,
		"	movsbl AR,AL\n", },

{ ASSIGN,	INAREG|FOREFF,
	SO_N,	TCHAR|TUCHAR,
	SAREG,		TCHAR|TUCHAR,
		NEEDS(NORIGHT(ESI), NORIGHT(EDI)),	RDEST,
		"	movb ZT,AL\n", },
#else
{ ASSIGN,	FOREFF,
	SB_O_N,	TCHAR|TUCHAR,
	SCON,		TANY,
		0,	0,
		"	movb AR,AL\n", },

{ ASSIGN,	FOREFF|INCH,
	SHCH,		TCHAR|TUCHAR,
	SCON,		TANY,
		0,	RDEST,
		"	movb AR,AL\n", },
#endif

{ ASSIGN,	FOREFF|INLL,
	SO_N,	TLL,
	SHLL,		TLL,
		0,	RDEST,
		"	movl AR,AL\n	movl UR,UL\n", },

{ ASSIGN,	FOREFF|INLL,
	SHLL,	TLL,
	SHLL,	TLL,
		0,	RDEST,
		"ZH", },

{ ASSIGN,	FOREFF|INAREG,
	SA_O_N,	TWORD|TPOINT,
	SAREG,		TWORD|TPOINT,
		0,	RDEST,
		"	movl AR,AL\n", },

{ ASSIGN,	FOREFF|INAREG,
	SAREG,			TWORD|TPOINT,
	SA_O_N,	TWORD|TPOINT,
		0,	RDEST,
		"	movl AR,AL\n", },

{ ASSIGN,	FOREFF|INAREG,
	SA_O_N,	TSHORT|TUSHORT,
	SAREG,		TSHORT|TUSHORT,
		0,	RDEST,
		"	movw AR,AL\n", },

#ifdef NOBREGS
{ ASSIGN,	FOREFF|INAREG,
	SO_N,	TCHAR|TUCHAR,
	SAREG,		TCHAR|TUCHAR|TWORD,
		NEEDS(NORIGHT(ESI), NORIGHT(EDI)),	RDEST,
		"	movb ZT,AL\n", },

{ ASSIGN,	FOREFF|INAREG,
	SAREG,	TUCHAR,
	SAREG,	TCHAR|TUCHAR|TWORD,
		NEEDS(NORIGHT(ESI), NORIGHT(EDI)),	RDEST,
		"	movzbl ZT,AL\n", },

{ ASSIGN,	FOREFF|INAREG,
	SAREG,	TCHAR,
	SAREG,	TCHAR|TUCHAR|TWORD,
		NEEDS(NORIGHT(ESI), NORIGHT(EDI)),	RDEST,
		"	movsbl ZT,AL\n", },
#else
{ ASSIGN,	FOREFF|INCH,
	SB_O_N,	TCHAR|TUCHAR,
	SHCH,		TCHAR|TUCHAR|TWORD,
		0,	RDEST,
		"	movb AR,AL\n", },
#endif

{ ASSIGN,	INDREG|FOREFF,
	SHFL,	TFLOAT|TDOUBLE|TLDOUBLE,
	SHFL,	TFLOAT|TDOUBLE|TLDOUBLE,
		0,	RDEST,
		"", }, /* This will always be in the correct register */

/* order of table entries is very important here! */
{ ASSIGN,	INFL,
	SO_N,	TLDOUBLE,
	SHFL,	TFLOAT|TDOUBLE|TLDOUBLE,
		0,	RDEST,
		"	fstpt AL\n	fldt AL\n", }, /* XXX */

{ ASSIGN,	FOREFF,
	SO_N,	TLDOUBLE,
	SHFL,	TFLOAT|TDOUBLE|TLDOUBLE,
		0,	0,
		"	fstpt AL\n", },

{ ASSIGN,	INFL,
	SO_N,	TDOUBLE,
	SHFL,	TFLOAT|TDOUBLE|TLDOUBLE,
		0,	RDEST,
		"	fstl AL\n", },

{ ASSIGN,	FOREFF,
	SO_N,	TDOUBLE,
	SHFL,	TFLOAT|TDOUBLE|TLDOUBLE,
		0,	0,
		"	fstpl AL\n", },

{ ASSIGN,	INFL,
	SO_N,	TFLOAT,
	SHFL,	TFLOAT|TDOUBLE|TLDOUBLE,
		0,	RDEST,
		"	fsts AL\n", },

{ ASSIGN,	FOREFF,
	SO_N,	TFLOAT,
	SHFL,	TFLOAT|TDOUBLE|TLDOUBLE,
		0,	0,
		"	fstps AL\n", },
/* end very important order */

{ ASSIGN,	INFL|FOREFF,
	SHFL,		TLDOUBLE,
	SD_O_N,	TLDOUBLE,
		0,	RDEST,
		"	fldt AR\n", },

{ ASSIGN,	INFL|FOREFF,
	SHFL,		TDOUBLE,
	SD_O_N,	TDOUBLE,
		0,	RDEST,
		"	fldl AR\n", },

{ ASSIGN,	INFL|FOREFF,
	SHFL,		TFLOAT,
	SD_O_N,	TFLOAT,
		0,	RDEST,
		"	flds AR\n", },

#if 0
{ STASG,	FOREFF,
	SNAME,	TANY,
	SHSTR,	TPTRTO|TANY,
		NEEDS(NREG(A,1)),	RDEST,
		"ZR", },

{ STASG,	FOREFF,
	SOREG,	TANY,
	SHSTR,	TPTRTO|TANY,
		NEEDS(NREG(A,2)),	RDEST,
		"ZV", },
#endif

{ STASG,	INAREG|FOREFF,
	SO_N,	TANY,
	SAREG,		TPTRTO|TANY,
		NEEDS(NEVER(EDI), NEVER(ESI), NRIGHT(ESI), NOLEFT(ESI),
		    NOLEFT(ECX), NORIGHT(ECX), NEVER(ECX), NREG(A,1)),	RDEST,
		"F	movl %esi,A1\nZQF	movl A1,%esi\n", },

/*
 * DIV/MOD/MUL 
 */
/* long long div is emulated */
{ DIV,	INCREG,
	SC_O_N_C, TLL,
	SC_O_N_C, TLL,
		NEEDS(NREG(C,1), NSL(C), NSR(C), NEVER(EAX), 
		    NEVER(EDX), NEVER(ECX), NRES(EAXEDX)), RESC1,
		"ZO", },

{ DIV,	INAREG,
	SAREG,			TSWORD,
	SA_O_N,	TWORD,
		NEEDS(NEVER(EAX), NEVER(EDX), NLEFT(EAX), 
		    NRES(EAX), NORIGHT(EAX), NORIGHT(EDX)), RDEST,
		"	cltd\n	idivl AR\n", },

{ DIV,	INAREG,
	SAREG,			TUWORD|TPOINT,
	SA_O_N,	TUWORD|TPOINT,
		NEEDS(NEVER(EAX), NEVER(EDX), NLEFT(EAX), 
		    NRES(EAX), NORIGHT(EAX), NORIGHT(EDX)), RDEST,
		"	xorl %edx,%edx\n	divl AR\n", },

{ DIV,	INAREG,
	SAREG,			TUSHORT,
	SA_O_N,	TUSHORT,
		NEEDS(NEVER(EAX), NEVER(EDX), NLEFT(EAX), 
		    NRES(EAX), NORIGHT(EAX), NORIGHT(EDX)), RDEST,
		"	xorl %edx,%edx\n	divw AR\n", },

#ifdef NOBREGS
{ DIV,	INAREG,
	SAREG,	TUCHAR,
	SAREG,	TUCHAR,
		NEEDS(NEVER(EAX), NEVER(EDX), NLEFT(EAX), 
		    NRES(EAX), NORIGHT(EAX), NORIGHT(EDX)), RDEST,
		"	xorl %edx,%edx\n	divl AR\n", },
#else
{ DIV,	INCH,
	SHCH,			TUCHAR,
	SB_O_N,	TUCHAR,
		NEEDS(NEVER(AL), NEVER(AH), NLEFT(AL), 
		    NRES(AL), NORIGHT(AL), NORIGHT(AH)), RDEST,
		"	xorb %ah,%ah\n	divb AR\n", },
#endif

{ DIV,	INFL,
	SHFL,		TDOUBLE,
	SO_N,	TDOUBLE,
		0,	RLEFT,
		"	fdivl AR\n", },

{ DIV,	INFL,
	SHFL,		TLDOUBLE|TDOUBLE|TFLOAT,
	SHFL,		TLDOUBLE|TDOUBLE|TFLOAT,
		0,	RLEFT,
		"	fdivZAp\n", },

/* (u)longlong mod is emulated */
{ MOD,	INCREG,
	SC_O_N_C, TLL,
	SC_O_N_C, TLL,
		NEEDS(NREG(C,1), NSL(C), NSR(C), NEVER(EAX), 
		    NEVER(EDX), NEVER(ECX), NRES(EAXEDX)), RESC1,
		"ZO", },

{ MOD,	INAREG,
	SAREG,			TSWORD,
	SA_O_N,	TSWORD,
		NEEDS(NREG(A,1), NEVER(EAX), NEVER(EDX), NLEFT(EAX), 
		    NRES(EDX), NORIGHT(EAX), NORIGHT(EDX)), RESC1,
		"	cltd\n	idivl AR\n", },

{ MOD,	INAREG,
	SAREG,			TWORD|TPOINT,
	SA_O_N,	TUWORD|TPOINT,
		NEEDS(NREG(A,1), NEVER(EAX), NEVER(EDX), NLEFT(EAX), 
		    NRES(EDX), NORIGHT(EAX), NORIGHT(EDX)), RESC1,
		"	xorl %edx,%edx\n	divl AR\n", },

{ MOD,	INAREG,
	SAREG,			TUSHORT,
	SA_O_N,	TUSHORT,
		NEEDS(NREG(A,1), NEVER(EAX), NEVER(EDX), NLEFT(EAX), 
		    NRES(EDX), NORIGHT(EAX), NORIGHT(EDX)), RESC1,
		"	xorl %edx,%edx\n	divw AR\n", },

#ifdef NOBREGS
{ MOD,	INAREG,
	SAREG,	TUCHAR,
	SAREG,	TUCHAR,
		NEEDS(NREG(A,1), NEVER(EAX), NEVER(EDX), NLEFT(EAX), 
		    NRES(EDX), NORIGHT(EAX), NORIGHT(EDX)), RESC1,
		"	xorl %edx,%edx\n	divl AR\n", },
#else
{ MOD,	INCH,
	SHCH,			TUCHAR,
	SB_O_N,	TUCHAR,
		NEEDS(NREG(B,1), NEVER(AL), NEVER(AH), NLEFT(AL), 
		    NRES(AH), NORIGHT(AL), NORIGHT(AH)), RESC1,
		"	xorb %ah,%ah\n	divb AR\n", },
#endif

/* (u)longlong mul is emulated */
{ MUL,	INCREG,
	SCREG,	TLL,
	SCREG,	TLL,
		NEEDS(NEVER(ESI), NRIGHT(ECXESI), NLEFT(EAXEDX), 
		    NRES(EAXEDX)), RDEST,
		"ZO", },

{ MUL,	INAREG,
	SAREG,				TWORD|TPOINT,
	SA_O_N_C,		TWORD|TPOINT,
		0,	RLEFT,
		"	imull AR,AL\n", },

{ MUL,	INAREG,
	SAREG,			TSHORT|TUSHORT,
	SA_O_N,	TSHORT|TUSHORT,
		0,	RLEFT,
		"	imulw AR,AL\n", },

#ifdef NOBREGS
{ MUL,	INAREG,
	SAREG,		TCHAR|TUCHAR,
	SAREG|SCON,	TCHAR|TUCHAR,
		0,	RLEFT,
		"	imull AR,AL\n", },
#else
{ MUL,	INCH,
	SHCH,			TCHAR|TUCHAR,
	SB_O_N,	TCHAR|TUCHAR,
		NEEDS(NLEFT(AL), NEVER(AL), NEVER(AH), 
		    NRES(AL)), RDEST,
		"	imulb AR\n", },
#endif

{ MUL,	INFL,
	SHFL,		TDOUBLE,
	SO_N,	TDOUBLE,
		0,	RLEFT,
		"	fmull AR\n", },

{ MUL,	INFL,
	SHFL,		TLDOUBLE|TDOUBLE|TFLOAT,
	SHFL,		TLDOUBLE|TDOUBLE|TFLOAT,
		0,	RLEFT,
		"	fmulp\n", },

/*
 * Indirection operators.
 */
{ UMUL,	INLL,
	SANY,	TANY,
	SOREG,	TLL,
		NEEDS(NREG(C, 1)),	RESC1,
		"	movl UL,U1\n	movl AL,A1\n", },

{ UMUL,	INAREG,
	SANY,	TPOINT|TWORD,
	SOREG,	TPOINT|TWORD,
		XSL(A),	RESC1,
		"	movl AL,A1\n", },

#ifdef NOBREGS
{ UMUL,	INAREG,
	SANY,	TANY,
	SOREG,	TCHAR,
		XSL(A),	RESC1,
		"	movsbl AL,A1\n", },
{ UMUL,	INAREG,
	SANY,	TANY,
	SOREG,	TUCHAR,
		XSL(A),	RESC1,
		"	movzbl AL,A1\n", },
#else
{ UMUL,	INCH,
	SANY,	TANY,
	SOREG,	TCHAR|TUCHAR,
		XSL(B),	RESC1,
		"	movb AL,A1\n", },
#endif

{ UMUL,	INAREG,
	SANY,	TANY,
	SOREG,	TSHORT|TUSHORT,
		XSL(A),	RESC1,
		"	movw AL,A1\n", },

{ UMUL,	INFL,
	SANY,	TANY,
	SOREG,	TLDOUBLE,
		XSL(D),	RESC1,
		"	fldt AL\n", },

{ UMUL,	INFL,
	SANY,	TANY,
	SOREG,	TDOUBLE,
		XSL(D),	RESC1,
		"	fldl AL\n", },

{ UMUL,	INFL,
	SANY,	TANY,
	SOREG,	TFLOAT,
		XSL(D),	RESC1,
		"	flds AL\n", },

/*
 * Logical/branching operators
 */

/* Comparisions, take care of everything */
{ OPLOG,	FORCC,
	SC_O_N,	TLL,
	SHLL,			TLL,
		0,	0,
		"ZD", },

{ OPLOG,	FORCC,
	SA_O_N,	TWORD|TPOINT,
	SA_C,	TWORD|TPOINT,
		0, 	RESCC,
		"	cmpl AR,AL\n", },

#if 0
{ OPLOG,	FORCC,
	SA_C,	TWORD|TPOINT,
	SA_O_N,	TWORD|TPOINT,
		0, 	RESCC,
		"	cmpl AR,AL\n", },
#endif

{ OPLOG,	FORCC,
	SA_O_N,	TSHORT|TUSHORT,
	SA_C,	TANY,
		0, 	RESCC,
		"	cmpw AR,AL\n", },

{ OPLOG,	FORCC,
	SB_O_N,	TCHAR|TUCHAR,
	SB_C,	TANY,
		0, 	RESCC,
		"	cmpb AR,AL\n", },

{ OPLOG,	FORCC,
	SDREG,	TLDOUBLE|TDOUBLE|TFLOAT,
	SDREG,	TLDOUBLE|TDOUBLE|TFLOAT,
		NEEDS(NEVER(EAX)), 	RNOP,
		"ZG", },

{ OPLOG,	FORCC,
	SANY,	TANY,
	SANY,	TANY,
		NEEDS(NREWRITE),	0,
		"diediedie!", },

/* AND/OR/ER/NOT */
{ AND,	INAREG|FOREFF,
	SA_O_N,	TWORD,
	SA_C,		TWORD,
		0,	RLEFT,
		"	andl AR,AL\n", },

{ AND,	INCREG|FOREFF,
	SCREG,			TLL,
	SC_O_N,	TLL,
		0,	RLEFT,
		"	andl AR,AL\n	andl UR,UL\n", },

{ AND,	INAREG|FOREFF,
	SAREG,			TWORD,
	SA_O_N,	TWORD,
		0,	RLEFT,
		"	andl AR,AL\n", },

{ AND,	INAREG|FOREFF,  
	SA_O_N,	TSHORT|TUSHORT,
	SA_C,		TSHORT|TUSHORT,
		0,	RLEFT,
		"	andw AR,AL\n", },

{ AND,	INAREG|FOREFF,  
	SAREG,			TSHORT|TUSHORT,
	SA_O_N,	TSHORT|TUSHORT,
		0,	RLEFT,
		"	andw AR,AL\n", },

{ AND,	INBREG|FOREFF,
	SB_O_N,	TCHAR|TUCHAR,
	SB_C,		TCHAR|TUCHAR,
		0,	RLEFT,
		"	andb AR,AL\n", },

{ AND,	INBREG|FOREFF,
	SBREG,			TCHAR|TUCHAR,
	SB_O_N,	TCHAR|TUCHAR,
		0,	RLEFT,
		"	andb AR,AL\n", },
/* AND/OR/ER/NOT */

/*
 * Jumps.
 */
{ GOTO, 	FOREFF,
	SCON,	TANY,
	SANY,	TANY,
		0,	RNOP,
		"	jmp LL\n", },

#if defined(GCC_COMPAT) || defined(LANG_F77)
{ GOTO, 	FOREFF,
	SAREG,	TANY,
	SANY,	TANY,
		0,	RNOP,
		"	jmp *AL\n", },
#endif

/*
 * Convert LTYPE to reg.
 */
{ OPLTYPE,	FORCC|INLL,
	SCREG,	TLL,
	SMIXOR,	TANY,
		NEEDS(NREG(C,1)),	RESC1,
		"	xorl U1,U1\n	xorl A1,A1\n", },

{ OPLTYPE,	FORCC|INLL,
	SCREG,	TLL,
	SMILWXOR,	TANY,
		NEEDS(NREG(C,1)),	RESC1,
		"	movl UL,U1\n	xorl A1,A1\n", },

{ OPLTYPE,	FORCC|INLL,
	SCREG,	TLL,
	SMIHWXOR,	TANY,
		NEEDS(NREG(C,1)),	RESC1,
		"	xorl U1,U1\n	movl AL,A1\n", },

{ OPLTYPE,	INLL,
	SANY,	TANY,
	SCREG,	TLL,
		NEEDS(NREG(C,1)),	RESC1,
		"ZK", },

{ OPLTYPE,	INLL,
	SANY,	TANY,
	SO_N_C,	TLL,
		NEEDS(NREG(C,1)),	RESC1,
		"	movl UL,U1\n	movl AL,A1\n", },

{ OPLTYPE,	FORCC|INAREG,
	SAREG,	TWORD|TPOINT,
	SMIXOR,	TANY,
		XSL(A),	RESC1,
		"	xorl A1,A1\n", },

{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SA_O_N_C,	TWORD|TPOINT,
		XSL(A),	RESC1,
		"	movl AL,A1\n", },

#ifdef NOBREGS
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SCON,	TCHAR|TUCHAR,
		XSL(A),	RESC1,
		"	movl AL,A1\n", },

{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SO_N,	TUCHAR,
		XSL(A),	RESC1,
		"	movzbl AL,A1\n", },

{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SO_N,	TCHAR,
		XSL(A),	RESC1,
		"	movsbl AL,A1\n", },

{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SAREG,	TCHAR|TUCHAR,
		XSL(A),	RESC1,
		"	movl AL,A1\n", },
#else
{ OPLTYPE,	INBREG,
	SANY,	TANY,
	SB_O_N_C,	TCHAR|TUCHAR,
		XSL(B),	RESC1,
		"	movb AL,A1\n", },
#endif

{ OPLTYPE,	FORCC|INAREG,
	SAREG,	TSHORT|TUSHORT,
	SMIXOR,	TANY,
		XSL(A),	RESC1,
		"	xorw A1,A1\n", },

{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SA_O_N_C,	TSHORT|TUSHORT,
		XSL(A),	RESC1,
		"	movw AL,A1\n", },

{ OPLTYPE,	INDREG,
	SANY,		TLDOUBLE,
	SO_N,	TLDOUBLE,
		XSL(D),	RESC1,
		"	fldt AL\n", },

{ OPLTYPE,	INDREG,
	SANY,		TDOUBLE,
	SO_N,	TDOUBLE,
		XSL(D),	RESC1,
		"	fldl AL\n", },

{ OPLTYPE,	INDREG,
	SANY,		TFLOAT,
	SO_N,	TFLOAT,
		XSL(D),	RESC1,
		"	flds AL\n", },

/* Only used in ?: constructs. The stack already contains correct value */
{ OPLTYPE,	INDREG,
	SANY,	TFLOAT|TDOUBLE|TLDOUBLE,
	SDREG,	TFLOAT|TDOUBLE|TLDOUBLE,
		XSL(D),	RESC1,
		"", },

/*
 * Negate a word.
 */

{ UMINUS,	INCREG|FOREFF,
	SCREG,	TLL,
	SCREG,	TLL,
		0,	RLEFT,
		"	negl AL\n	adcl $0,UL\n	negl UL\n", },

{ UMINUS,	INAREG|FOREFF,
	SAREG,	TWORD|TPOINT,
	SAREG,	TWORD|TPOINT,
		0,	RLEFT,
		"	negl AL\n", },

{ UMINUS,	INAREG|FOREFF,
	SAREG,	TSHORT|TUSHORT,
	SAREG,	TSHORT|TUSHORT,
		0,	RLEFT,
		"	negw AL\n", },

{ UMINUS,	INBREG|FOREFF,
	SBREG,	TCHAR|TUCHAR,
	SBREG,	TCHAR|TUCHAR,
		0,	RLEFT,
		"	negb AL\n", },

{ UMINUS,	INFL|FOREFF,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
	SHFL,	TLDOUBLE|TDOUBLE|TFLOAT,
		0,	RLEFT,
		"	fchs\n", },

{ COMPL,	INCREG,
	SCREG,	TLL,
	SANY,	TANY,
		0,	RLEFT,
		"	notl AL\n	notl UL\n", },

{ COMPL,	INAREG,
	SAREG,	TWORD,
	SANY,	TANY,
		0,	RLEFT,
		"	notl AL\n", },

{ COMPL,	INAREG,
	SAREG,	TSHORT|TUSHORT,
	SANY,	TANY,
		0,	RLEFT,
		"	notw AL\n", },

{ COMPL,	INBREG,
	SBREG,	TCHAR|TUCHAR,
	SANY,	TANY,
		0,	RLEFT,
		"	notb AL\n", },

/*
 * Arguments to functions.
 */
{ FUNARG,	FOREFF,
	SC_O_N_C,	TLL,
	SANY,	TLL,
		0,	RNULL,
		"	pushl UL\n	pushl AL\n", },

{ FUNARG,	FOREFF,
	SA_O_N_C,	TWORD|TPOINT,
	SANY,	TWORD|TPOINT,
		0,	RNULL,
		"	pushl AL\n", },

{ FUNARG,	FOREFF,
	SCON,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
	SANY,	TWORD|TSHORT|TUSHORT|TCHAR|TUCHAR,
		0,	RNULL,
		"	pushl AL\n", },

{ FUNARG,	FOREFF,
	SA_O_N,	TSHORT,
	SANY,	TSHORT,
		XSL(A),	0,
		"	movswl AL,ZN\n	pushl ZN\n", },

{ FUNARG,	FOREFF,
	SA_O_N,	TUSHORT,
	SANY,	TUSHORT,
		XSL(A),	0,
		"	movzwl AL,ZN\n	pushl ZN\n", },

#ifdef NOBREGS
{ FUNARG,	FOREFF,
	SA_O_N,	TUCHAR|TCHAR,
	SANY,			TUCHAR|TCHAR,
		XSL(A),	0,
		"	pushl AL\n", },
#else
{ FUNARG,	FOREFF,
	SB_O_N,	TCHAR,
	SANY,			TCHAR,
		XSL(A),	0,
		"	movsbl AL,A1\n	pushl A1\n", },

{ FUNARG,	FOREFF,
	SB_O_N,	TUCHAR,
	SANY,	TUCHAR,
		XSL(A),	0,
		"	movzbl AL,A1\n	pushl A1\n", },
#endif

{ FUNARG,	FOREFF,
	SO_N,	TDOUBLE,
	SANY,	TDOUBLE,
		0,	0,
		"	pushl UL\n	pushl AL\n", },

{ FUNARG,	FOREFF,
	SDREG,	TDOUBLE,
	SANY,		TDOUBLE,
		0,	0,
		"	subl $8,%esp\n	fstpl (%esp)\n", },

{ FUNARG,	FOREFF,
	SO_N,	TFLOAT,
	SANY,		TFLOAT,
		0,	0,
		"	pushl AL\n", },

{ FUNARG,	FOREFF,
	SDREG,	TFLOAT,
	SANY,		TFLOAT,
		0,	0,
		"	subl $4,%esp\n	fstps (%esp)\n", },

{ FUNARG,	FOREFF,
	SDREG,	TLDOUBLE,
	SANY,		TLDOUBLE,
		0,	0,
		"	subl $12,%esp\n	fstpt (%esp)\n", },

{ STARG,	FOREFF,
	SAREG,	TPTRTO|TSTRUCT,
	SANY,	TSTRUCT,
		NEEDS(NEVER(EDI), NLEFT(ESI), NEVER(ECX)),	0,
		"ZF", },

# define DF(x) FORREW,SANY,TANY,SANY,TANY,NEEDS(NREWRITE),x,""

{ UMUL, DF( UMUL ), },

{ ASSIGN, DF(ASSIGN), },

{ STASG, DF(STASG), },

{ FLD, DF(FLD), },

{ OPLEAF, DF(NAME), },

/* { INIT, DF(INIT), }, */

{ OPUNARY, DF(UMINUS), },

{ OPANY, DF(BITYPE), },

{ FREE,	FREE,	0,	FREE,	0,	FREE,	0,	FREE,	"help; I'm in trouble\n" },
};

int tablesize = sizeof(table)/sizeof(table[0]);
