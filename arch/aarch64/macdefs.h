/*	$Id$	*/
 /*
 * Copyright (c) 2020 Puresoftware Ltd.
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
 * Machine-dependent defines for both passes.
 */

/*
 * Convert (multi-)character constant to integer.
 */
#define makecc(val,i)	lastcon = (lastcon<<8)|((val<<24)>>24);

/*
 * Storage space requirements
 */
#define SZCHAR          8
#define SZBOOL          32
#define SZINT           32
#define SZFLOAT         32
#define SZDOUBLE        64
#define SZLDOUBLE       64
#define SZLONG          64
#define SZSHORT         16
#define SZLONGLONG      64
#define SZPOINT(t)      64

/*
 * Alignment constraints
 */
#define ALCHAR          8
#define ALBOOL          32
#define ALINT           32
#define ALFLOAT         32
#define ALDOUBLE        32
#define ALLDOUBLE       32
#define ALLONG          32
#define ALLONGLONG      32
#define ALSHORT         16
#define ALPOINT         32
#define ALSTRUCT        32
#define ALSTACK         32

/*
 * Min/max values.
 */
#define	MIN_CHAR	-128
#define	MAX_CHAR	127
#define	MAX_UCHAR	255
#define	MIN_SHORT	-32768
#define	MAX_SHORT	32767
#define	MAX_USHORT	65535
#define	MIN_INT		-1
#define	MAX_INT		0x7fffffff
#define	MAX_UNSIGNED	0xffffffff
#define	MIN_LONG	0x8000000000000000L
#define	MAX_LONG	0x7fffffffffffffffL
#define	MAX_ULONG	0xffffffffffffffffUL
#define	MIN_LONGLONG	0x8000000000000000LL
#define	MAX_LONGLONG	0x7fffffffffffffffLL
#define	MAX_ULONGLONG	0xffffffffffffffffULL

#define	BOOL_TYPE	INT	/* what used to store _Bool */

/*
 * Use large-enough types.
 */
typedef	long long CONSZ;
typedef	unsigned long long U_CONSZ;
typedef long long OFFSZ;

#define CONFMT	"#%lld"		/* format for printing constants */
#define LABFMT	".L%d"		/* format for printing labels */
#define	STABLBL	"LL%d"		/* format for stab (debugging) labels */
#define STAB_LINE_ABSOLUTE	/* S_LINE fields use absolute addresses */

#undef	FIELDOPS		/* no bit-field instructions */

/* Definitions mostly used in pass2 */

#define BYTEOFF(x)	((x)&03)
#define wdal(k)		(BYTEOFF(k)==0)

#define STOARG(p)
#define STOFARG(p)
#define STOSTARG(p)

#define	szty(t)	(((t) == DOUBLE || (t) == LDOUBLE || \
	(t) == LONG || (t) == ULONG || (t) == LONGLONG || (t) == ULONGLONG) ? 2 : 1)

#define R0	0
#define R1	1
#define R2	2
#define R3	3
#define R4	4
#define R5	5
#define R6	6
#define R7	7
#define R8	8
#define R9	9
#define R10	10
#define R11	11
#define R12	12
#define	R13	13
#define R14	14
#define R15	15
#define R16	16
#define R17	17
#define R18	18
#define R19	19
#define R20	20
#define R21	21
#define R22	22
#define R23	23
#define R24	24
#define R25	25
#define R26	26
#define R27	27
#define R28	28
#define R29	29
#define R30	30
#define R31	31   //SP register

#define FP	R29
#define IP	R16
#define SP	R31
#define LR	R30

#define NUMCLASS 3
#define	MAXREGS  34	

#define RSTATUS \
	SAREG|TEMPREG, SAREG|TEMPREG, SAREG|TEMPREG, SAREG|TEMPREG,	\
	SAREG|PERMREG, SAREG|PERMREG, SAREG|PERMREG, SAREG|PERMREG,	\
	SAREG|PERMREG, SAREG|PERMREG, SAREG|PERMREG,			\
	0, 0, 0, 0, 0,							\
        SBREG|TEMPREG, SBREG|TEMPREG, SBREG|TEMPREG, SBREG,		\
        SBREG, SBREG, SBREG, SBREG, SBREG, SBREG,			\
	SCREG, SCREG, SCREG, SCREG,					\
	SCREG, SCREG, SCREG, SCREG,					\

/* no overlapping registers at all */
#define ROVERLAP \
        { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
        { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
        { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
        { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
        { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 },

#define ARGINIT		(16*8)	/* # bits above fp where arguments start */
#define AUTOINIT	(32*8)	/* # bits above fp where automatics start */

#undef	FIELDOPS		/* no bit-field instructions */
#define TARGET_ENDIAN TARGET_LE

/* XXX - to die */
#define FPREG   FP	/* frame pointer */
#define SPREG   SP      /* Stack pointer */

/* Return a register class based on the type of the node */
#define PCLASS(p)	(1 << gclass((p)->n_type))

#define GCLASS(x)	(x < 16 ? CLASSA : x < 26 ? CLASSB : CLASSC)
#define DECRA(x,y)      (((x) >> (y*6)) & 63)   /* decode encoded regs */
#define ENCRD(x)        (x)             /* Encode dest reg in n_reg */
#define ENCRA1(x)       ((x) << 6)      /* A1 */
#define ENCRA2(x)       ((x) << 12)     /* A2 */
#define ENCRA(x,y)      ((x) << (6+y*6))        /* encode regs in int */
#define RETREG(x)	retreg(x)

int COLORMAP(int c, int *r);
int retreg(int ty);
int features(int f);

#define FEATURE_BIGENDIAN	0x00010000
#define FEATURE_HALFWORDS	0x00020000	/* ldrsh/ldrh, ldrsb */
#define FEATURE_EXTEND		0x00040000	/* sxth, sxtb, uxth, uxtb */
#define FEATURE_MUL		0x00080000
#define FEATURE_MULL		0x00100000
#define FEATURE_DIV		0x00200000
#define FEATURE_FPA		0x10000000
#define FEATURE_VFP		0x20000000
#define FEATURE_HARDFLOAT	(FEATURE_FPA|FEATURE_VFP)

#undef NODE
#ifdef LANG_CXX
#define NODE struct node
#else
#define NODE struct p1node
#endif
struct node;
struct bitable;
NODE *arm_builtin_stdarg_start(const struct bitable *bt, NODE *a);
NODE *arm_builtin_va_arg(const struct bitable *bt, NODE *a);
NODE *arm_builtin_va_end(const struct bitable *bt, NODE *a);
NODE *arm_builtin_va_copy(const struct bitable *bt, NODE *a);
#undef NODE

#define COM     "\t// "
#define NARGREGS	4

/* floating point definitions */
#define USE_IEEEFP_32
#define FLT_PREFIX	IEEEFP_32
#define USE_IEEEFP_64
#define DBL_PREFIX	IEEEFP_64
#define LDBL_PREFIX	IEEEFP_64
#define DEFAULT_FPI_DEFS { &fpi_binary32, &fpi_binary64, &fpi_binary64 }
