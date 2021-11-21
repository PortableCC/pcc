/*	$Id$	*/
/*
 * Copyright (c) 2006 Anders Magnusson (ragge@ludd.luth.se).
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
 * Machine-dependent defines for Data General Nova.
 */

/*
 * Convert (multi-)character constant to integer.
 */
#define makecc(val,i)	lastcon = (lastcon<<8)|(val);

/*
 * Storage space requirements
 */
#define SZCHAR		8
#define SZBOOL		8
#define SZINT		16
#define SZFLOAT		32
#define SZDOUBLE	64
#define SZLDOUBLE	64
#define SZLONG		32
#define SZSHORT		16
#define SZLONGLONG	64
#define SZPOINT(t)	16	/* Actually 15 */

/*
 * Alignment constraints
 */
#define ALCHAR		8
#define ALBOOL		8
#define ALINT		16
#define ALFLOAT		16
#define ALDOUBLE	16
#define ALLDOUBLE	16
#define ALLONG		16
#define ALLONGLONG	16
#define ALSHORT		16
#define ALPOINT		16
#define ALSTRUCT	16
#define ALSTACK		16 

/*
 * Min/max values.
 */
#define	MIN_CHAR	-128
#define	MAX_CHAR	127
#define	MAX_UCHAR	255
#define	MIN_SHORT	-32768
#define	MAX_SHORT	32767
#define	MAX_USHORT	65535
#define	MIN_INT		MIN_SHORT
#define	MAX_INT		MAX_SHORT
#define	MAX_UNSIGNED	MAX_USHORT
#define	MIN_LONG	0x80000000L
#define	MAX_LONG	0x7fffffffL
#define	MAX_ULONG	0xffffffffUL
#define	MIN_LONGLONG	0x8000000000000000LL
#define	MAX_LONGLONG	0x7fffffffffffffffLL
#define	MAX_ULONGLONG	0xffffffffffffffffULL

/* Default char is unsigned */
#define	CHAR_UNSIGNED
#define WORD_ADDRESSED
#undef STACK_DOWN	/* nova stack grows upward */
#define	STACK_TYPE	INT	/* type for accessing stack */
#define	BOOL_TYPE	UCHAR
#define	MYALIGN		/* provide private alignment function */
#undef	FIELDOPS	/* no bit-field instructions */
#define TARGET_ENDIAN	TARGET_LE /* XXX should be both */
#define	AUTOINIT	16	/* first var one word above offset */
#define	ARGINIT		16	/* start args one word below fp */
#define FINDMOPS		/* can in/decrement memory directly. */
#define NEWNEED			/* new-style needs definitions */

/*
 * Use large-enough types.
 */
typedef	long CONSZ;
typedef	unsigned long U_CONSZ;
typedef long OFFSZ;

#define CONFMT	"0%lo"		/* format for printing constants */
#define LABFMT	"L%d"		/* format for printing labels */
#define	STABLBL	"LL%d"		/* format for stab (debugging) labels */

/* Definitions mostly used in pass2 */

#define BYTEOFF(x)	((x)&01)
#define wdal(k)		(BYTEOFF(k)==0)

#define	szty(t)	((t) == DOUBLE || (t) == LDOUBLE || \
	(t) == LONGLONG || (t) == ULONGLONG ? 4 : \
	((t) == LONG || (t) == ULONG || (t) == FLOAT) ? 2 : 1)

/*
 * The Nova has three register classes.
 * Register 6 and 7 are FP and SP (in zero page or HW regs).
 *
 * The classes used on Nova are:
 *	A - AC0-AC3 (AC3 not available)		: reg 0-3
 *	B - LC0 (long, AC0-1 concatenated)	: reg 4
 *	C - FP0 (floating point)		: 5
 */
#define	AC0	0
#define	AC1	1
#define	AC2	2
#define	AC3	3
#define	LC0	4
#define	FP0	5
#define	FP	6
#define	SP	7

#define	MAXREGS	8	/* 0-5 */

#define	RSTATUS	\
	SAREG|TEMPREG, SAREG|TEMPREG, SAREG|TEMPREG, 0,	\
	SBREG|TEMPREG, 0, SCREG|TEMPREG, 0, 0
	

#define	ROVERLAP \
	{ LC0, -1 }, { LC0, -1 }, { -1 }, { -1 },	\
	{ 0, 1, -1 }, { -1 }, { -1 }, { -1 },

/* Return a register class based on the type of the node */
/* Used in tshape, avoid matching fp/sp as reg */
#define PCLASS(p) \
	(p->n_type == LONG || p->n_type == ULONG ? SBREG : SAREG) /* XXX FP */

#define	NUMCLASS 	3	/* highest number of reg classes used */

int COLORMAP(int c, int *r);
#define	GCLASS(x) (x < 4 ? CLASSA : x == LC0 ? CLASSB : CLASSC)
#define DECRA(x,y)	(((x) >> (y*6)) & 63)	/* decode encoded regs */
#define	ENCRD(x)	(x)		/* Encode dest reg in n_reg */
#define ENCRA1(x)	((x) << 6)	/* A1 */
#define ENCRA2(x)	((x) << 12)	/* A2 */
#define ENCRA(x,y)	((x) << (6+y*6))	/* encode regs in int */
#define	RETREG(t)	(t==LONG || t==ULONG ? LC0 : ISPTR(t) ? AC2 : AC0)

#define FPREG	AC3	/* frame pointer, kept in AC3 */
#define STKREG	SP	/* stack pointer */

#ifdef os_none
#define	MYINSTRING
#endif

/*
 * special shapes for sp/fp.
 */
#define	SLDFPSP		(MAXSPECIAL+1)	/* load fp or sp */

/* floating point definitions */
#define	FDFLOAT
#define	DEFAULT_FPI_DEFS { &fpi_ffloat, &fpi_dfloat, &fpi_dfloat }
