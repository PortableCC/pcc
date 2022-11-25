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

/*
 * Machine-dependent defines for both passes.
 */

/*
 * Convert (multi-)character constant to integer.
 */
#define makecc(val,i)	lastcon = (lastcon<<8)|((val<<24)>>24);

/*
 * Storage space requirements
 */
#define SZCHAR		8
#define SZBOOL		8
#define SZSHORT		16
#define SZINT		32
#define SZLONG		SZINT
#define SZPOINT(t)		SZLONG
#define SZLONGLONG	64
#define SZFLOAT		32
#define SZDOUBLE	64
#define SZLDOUBLE	128

/*
 * Alignment constraints
 */
#define ALCHAR		8
#define ALBOOL		8
#define ALSHORT		16
#define ALINT		32
#define ALLONG		64 /* allong */
#define ALPOINT	32	/* alpoint */
#define ALLONGLONG	64
#define ALFLOAT		32
#define ALDOUBLE	64
#define ALLDOUBLE	128
/* #undef ALSTRUCT	riscv struct alignment is member defined */
#define ALSTACK		64
#define ALMAX		128 

/*
 * Min/max values.
 */
#define	MIN_CHAR	-128
#define	MAX_CHAR	127
#define	MAX_UCHAR	255
#define	MIN_SHORT	-32768
#define	MAX_SHORT	32767
#define	MAX_USHORT	65535
#define	MIN_INT		(-0x7fffffff-1)
#define	MAX_INT		0x7fffffff
#define	MAX_UNSIGNED	0xffffffffU
#define	MIN_LONG	MIN_INT
#define	MAX_LONG	MAX_INT
#define	MAX_ULONG	MAX_UNSIGNED
#define	MIN_LONGLONG	0x8000000000000000LL
#define	MAX_LONGLONG	0x7fffffffffffffffLL
#define	MAX_ULONGLONG	0xffffffffffffffffULL

/* Default char is signed */
#define	CHAR_UNSIGNED
#define	BOOL_TYPE	UCHAR	/* what used to store _Bool */

/*
 * Use large-enough types.
 */
typedef	long long CONSZ;
typedef	unsigned long long U_CONSZ;
typedef long long OFFSZ;

#define CONFMT	"%lld"		/* format for printing constants */
#define LABFMT	".L%d"		/* format for printing labels */
#define	STABLBL	".LL%d"		/* format for stab (debugging) labels */

#define ARGINIT		0	/* # bits above fp where arguments start */
#define AUTOINIT	0	/* # bits below fp where automatics start */
#define BACKAUTO 		/* stack grows negatively for automatics */
#define BACKTEMP 		/* stack grows negatively for temporaries */

#undef	FIELDOPS		/* no bit-field instructions */
#define	TARGET_ENDIAN TARGET_LE	/* little-endian only */

#undef FINDMOPS			/* no modify memory ops */

#define	CC_DIV_0	/* division by zero is safe in the compiler */

/* Definitions mostly used in pass2 */

#define BYTEOFF(x)	((x)&07)
#define wdal(k)		(BYTEOFF(k)==0)

#define STOARG(p)
#define STOFARG(p)
#define STOSTARG(p)
#define genfcall(a,b)	gencall(a,b)

/* How many integer registers are needed? (used for stack allocation) */
#define	szty(t)	(t == LDOUBLE ? 2 : 1)

#define USE_T0_AS_TEMP
//#define SAVE_RA_FOR_LAST 

/*
 * The classes used on riscv32 are:
 *	A - integer registers
 *	B - floating point registers
 *	C - concatenated (long long) registers.
 */
#define		ZERO	000
#ifdef SAVE_RA_FOR_LAST
#define		T6	1
#else
#define		RA	1
#endif
#define		SP	2
#define		GP	3
#define		TP	4
#define		T0	5
#define		T1	6
#define		T2	7

#define		S0	8
#define		FP	S0
#define		S1	9

#define		A0	10
#define		A1	11
#define		A2	12
#define		A3	13
#define		A4	14
#define		A5	15
#define		A6	16
#define		A7	17

#define		S2	18
#define		S3	19
#define		S4	20
#define		S5	21
#define		S6	22
#define		S7	23
#define		S8	24
#define		S9	25
#define		S10	26
#define		S11	27

#define		T3	28
#define		T4	29
#define		T5	30

#ifdef SAVE_RA_FOR_LAST
#define		RA	31
#else
#define		T6	31
#endif

#define 	FT0 	32
#define 	FT1 	33
#define 	FT2 	34
#define 	FT3 	35
#define 	FT4 	36
#define 	FT5 	37
#define 	FT6 	38
#define 	FT7 	39

#define		FS0		40
#define		FS1		41

#define		FA0		42
#define		FV0		FA0
#define		FA1		43
#define		FA2		44
#define		FA3		45
#define		FA4		46
#define		FA5		47
#define		FA6		48
#define		FA7		49

#define 	FS2		50
#define 	FS3		51
#define 	FS4		52
#define 	FS5		53
#define 	FS6		54
#define 	FS7		55
#define 	FS8		56
#define 	FS9		57
#define 	FS10	58
#define 	FS11	59

#define 	FT8 	60
#define 	FT9 	61
#define 	FT10 	62
#define 	FT11 	63


#define		DA0	64	/* a0/a1 */
#define		DV0	DA0
#define		DA1	65	/* a2/a3 */
#define		DA2	66	/* a4/a5 */
#define		DA3	67	/* a6/a7 */
#define		DT0	68	/* t0/t1 */
#define		DT1	69	/* t2/t3 */
#define		DT2	70	/* t4/t5 */
#define		DS0	71	/* s0/s1  - not used */
#define		DS1	72	/* s2/s3 */
#define		DS2	73	/* s4/s5 */
#define		DS3	74	/* s6/s7 */
#define		DS4	75	/* s8/s9 */
#define		DS5	76	/* s10/s11 */

#define		MAXREGS	77	/* 77 registers */

#define		NARGREGS	8  /* max of eight arguments passed in registers */

#define		PERMTYPE(x) ((x) < 32 ? INT : ((x) < 64 ? FLOAT : LONGLONG))

#define	RETREG(x)	(x == FLOAT || x == DOUBLE || x == LDOUBLE ? FA0 : \
			 x == LONGLONG || x == ULONGLONG ? DA0 : A0)

#define FPREG	FP	/* frame pointer */
#define STKREG	SP	/* stack pointer */

#if 0
#ifdef SAVE_RA_FOR_LAST
#define LINE1	/* x0, t6, sp, gp, tp */	0, SAREG|TEMPREG, 0, 0, 0,
#define LINE2	/* t3, t4, t5, ra */		SAREG|TEMPREG, SAREG|TEMPREG, SAREG|TEMPREG, SAREG|PERMREG, 
#else
#define LINE1	/* x0, ra, sp, gp, tp */	0, SAREG|PREMREG, 0, 0, 0,
#define LINE2 	/* t3, t4, t5, t6 */ SAREG|TEMPREG, SAREG|TEMPREG, SAREG|TEMPREG, SAREG|TEMPREG,
#endif
#endif

#define		RSTATUS	\
/* x0, ra, sp, gp, tp */0, SAREG|PREMREG, 0, 0, 0,	\
/* t0, t1, t2 */	SAREG|TEMPREG, SAREG|TEMPREG, SAREG|TEMPREG, \
/* fp, s1 */		0, SAREG|PERMREG, \
\
/* a0, a1, a2, a3 */	SAREG|TEMPREG, SAREG|TEMPREG, SAREG|TEMPREG, SAREG|TEMPREG,	\
/* a4, a5, a6, a7 */	SAREG|TEMPREG, SAREG|TEMPREG, SAREG|TEMPREG, SAREG|TEMPREG,	\
/* s2, s3, s4, s5 */	SAREG|PERMREG, SAREG|PERMREG, SAREG|PERMREG, SAREG|PERMREG,	\
/* s6, s7, s8, s9 */	SAREG|PERMREG, SAREG|PERMREG, SAREG|PERMREG, SAREG|PERMREG,	\
/* s10, s11 */		SAREG|PERMREG, SAREG|PERMREG,  \
/* t3, t4, t5, t6 */ 	SAREG|TEMPREG, SAREG|TEMPREG, SAREG|TEMPREG, SAREG|TEMPREG, \
\
/* ft0, ft1, ft2, ft3 */SBREG|TEMPREG, SBREG|TEMPREG, SBREG|TEMPREG, SBREG|TEMPREG,	\
/* ft4, ft5, ft6, ft7 */SBREG|TEMPREG, SBREG|TEMPREG, SBREG|TEMPREG, SBREG|TEMPREG,	\
/* fs0, fs1 */		SBREG|PERMREG, SBREG|PERMREG, \
/* fa0, fa1, fa2, fa3 */SBREG|TEMPREG, SBREG|TEMPREG, SBREG|TEMPREG, SBREG|TEMPREG,	\
/* fa4, fa5, fa6, fa7 */SBREG|TEMPREG, SBREG|TEMPREG, SBREG|TEMPREG, SBREG|TEMPREG,	\
/* fs2, fs3, fs4, fs5 */SBREG|PERMREG, SBREG|PERMREG, SBREG|PERMREG, SBREG|PERMREG, 	\
/* fs6, fs7, fs8, fs9 */SBREG|PERMREG, SBREG|PERMREG, SBREG|PERMREG, SBREG|PERMREG, 	\
/* fs10, fs11 */	SBREG|PERMREG, SBREG|PERMREG,	\
/* ft8, ft9, ft10, ft11 bug in mkext */	SBREG|TEMPREG, SBREG|TEMPREG, SBREG|TEMPREG, 0, \
\
/* a0a1, a2a3 */	SCREG, SCREG, \
/* a4a5, a6a7 */ 	SCREG, SCREG, \
/* s0s1, s2s3, */	0, SCREG, \
/* s4s5, s6s7*/		SCREG, SCREG, \
/* s8s9, s10s11 */	SCREG, SCREG, \
\
/*  t0t1, t2t3, t4t5 */	SCREG, SCREG, SCREG				

		
#define	ROVERLAP \
/* x0, ra, sp, gp, tp */	{ -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
/* t0, t1, t2 */		{DT0,  -1 }, { DT0,  -1 }, { DT1, -1 }, \
/* fp, s1 */			{ -1 }, {-1}, \
\
/* a0, a1, a2, a3 */ 	{ DA0, -1 }, { DA0, -1 }, { DA1, -1 }, { DA1, -1 }, \
/* a4, a5, a6, a7 */	{ DA2, -1 }, { DA2, -1 }, { DA3, -1 }, { DA3, -1 }, \
/* s2, s3, s4, s5 */	{ DS1, -1 }, { DS1, -1 }, { DS2, -1 }, { DS2, -1 }, \
/* s6, s7, s8, s9 */	{ DS3, -1 }, { DS3, -1 }, { DS4, -1 }, { DS4, -1 }, \
/* s10, s11 */		{ DS5, -1 }, { DS5, -1 }, \
/* t3, t4, t5, t6 */	{ DT1, -1 }, { DT2, -1 }, { DT2, -1 }, { -1 }, \
\
	{ -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
	{ -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
	{ -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
	{ -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 },	\
\
/* a0a1, a2a3 */		{ A0, A1, -1 }, { A2, A3, -1 }, 	\
/* a4a5, a6a7 */		{ A4, A5, -1 },{ A6, A7, -1 }, \
/* s0s1, s2s3, */		{ -1 }, { S2, S3, -1 }, \
/* s4s5, s6s7, */		{ S4, S5, -1 }, { S6, S7, -1 }, \
/* s8s9, s10, s11 */		{S8, S9, -1}, { S10, S11, -1 }, \
/* t0t1, t2t3, t4t5 */		{ T0, T1, -1 }, { T2, T3, -1 }, { T2, T3, -1 }
	
/* Return a register class based on the type of the node */
#define PCLASS(p) (p->n_type == FLOAT || p->n_type == DOUBLE ? SBREG : \
	p->n_type == LONGLONG || p->n_type == ULONGLONG ? SCREG : SAREG)

#define	GCLASS(x) (x < 32 ? CLASSA : x < 64 ? CLASSB : CLASSC)
#define DECRA(x,y)	(((x) >> (y*8)) & 255)	/* decode encoded regs */
#define	ENCRD(x)	(x)		/* Encode dest reg in n_reg */
#define ENCRA1(x)	((x) << 8)	/* A1 */
#define ENCRA2(x)	((x) << 16)	/* A2 */
#define ENCRA(x,y)	((x) << (8+y*8))	/* encode regs in int */

#define		NUMCLASS 	3	/* highest number of reg classes used */

int COLORMAP(int c, int *r);

#define	SHSTR		(MAXSPECIAL+1)	/* short struct */
#define	SFUNCALL	(MAXSPECIAL+2)	/* struct assign after function call */
#define SPCON		(MAXSPECIAL+3)  /* positive constant */

int features(int f);
#define FEATURE_BIGENDIAN	0x00010000
#define FEATURE_PIC		0x00020000
#define FEATURE_HARDFLOAT	0x00040000

struct stub {
	struct { struct stub *q_forw, *q_back; } link;
	char *name;
};
extern struct stub stublist;
extern struct stub nlplist;

#define COM     "       ; "

/*
 * Extended assembler macros.
 */
int xasmconstregs(char *);
#if 0
void targarg(char *w, void *arg, int n);
#define	XASM_TARGARG(w, ary)	\
	(w[1] == 'b' || w[1] == 'h' || w[1] == 'w' || w[1] == 'k' || \
	 w[1] == 'q' ? w++, targarg(w, ary, n), 1 : 0)
#endif

#if 0
int numconv(void *ip, void *p, void *q);
#define	XASM_NUMCONV(ip, p, q)	numconv(ip, p, q)
#endif

#define	XASMCONSTREGS(x)	xasmconstregs(x)

#define	HAVE_WEAKREF
#define TARGET_FLT_EVAL_METHOD	0	/* all as their type */
/*
 * builtins.
 */
#define TARGET_VALIST
#define TARGET_STDARGS
#define TARGET_BUILTINS							\
	{ "__builtin_stdarg_start", riscv_builtin_stdarg_start, 	\
						0, 2, 0, VOID },	\
	{ "__builtin_va_start", riscv_builtin_stdarg_start,		\
						0, 2, 0, VOID },	\
	{ "__builtin_va_arg", riscv_builtin_va_arg, BTNORVAL|BTNOPROTO, \
							2, 0, 0 },	\
	{ "__builtin_va_end", riscv_builtin_va_end, 0, 1, 0, VOID },	\
	{ "__builtin_va_copy", riscv_builtin_va_copy, 0, 2, 0, VOID }

#ifdef LANG_CXX
#define P1ND struct node
#else
#define P1ND struct p1node
#endif
struct node;
struct bitable;
P1ND *riscv_builtin_stdarg_start(const struct bitable *, P1ND *a);
P1ND *riscv_builtin_va_arg(const struct bitable *, P1ND *a);
P1ND *riscv_builtin_va_end(const struct bitable *, P1ND *a);
P1ND *riscv_builtin_va_copy(const struct bitable *, P1ND *a);
#undef P1ND

extern int msettings;
#define	RV_M		0001
#define	RV_A		0002
#define	RV_F		0004
#define	RV_D		0010
#define	RV_Q		0020
#define	RV_C		0040
#define	RV_64		0100
#define	RV_E		0200

#define	RVHASM()	(msettings & RV_M)
#define	RVHASA()	(msettings & RV_A)
#define	RVHASF()	(msettings & RV_F)
#define	RVHASD()	(msettings & RV_D)
#define	RVHASQ()	(msettings & RV_Q)
#define	RVHASC()	(msettings & RV_C)
#define	RVIS64()	(msettings & RV_64)
#define	RVISE()		(msettings & RV_E)

#define	XLEN	(RVIS64() ? 64 : 32)
#define	XLENTYP	szlong

int szlong, szpoint, allong, alpoint;

/* floating point definitions */
#define USE_IEEEFP_32
#define FLT_PREFIX      IEEEFP_32
#define USE_IEEEFP_64
#define DBL_PREFIX      IEEEFP_64
#define LDBL_PREFIX     IEEEFP_64

#define DEFAULT_FPI_DEFS { &fpi_binary32, &fpi_binary64, &fpi_binary64 }
