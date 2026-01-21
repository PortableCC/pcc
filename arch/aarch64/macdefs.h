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
#define SZBOOL          8 /* XXX - investigate */
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
#define ALBOOL          8
#define ALINT           32
#define ALFLOAT         32
#define ALDOUBLE        64
#define ALLDOUBLE       64
#define ALLONG          64
#define ALLONGLONG      64
#define ALSHORT         16
#define ALPOINT         64
#define ALSTRUCT        32
#define ALSTACK         128

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
#define	MAX_UNSIGNED	0xffffffff
#define	MIN_LONG	0x8000000000000000L
#define	MAX_LONG	0x7fffffffffffffffL
#define	MAX_ULONG	0xffffffffffffffffUL
#define	MIN_LONGLONG	0x8000000000000000LL
#define	MAX_LONGLONG	0x7fffffffffffffffLL
#define	MAX_ULONGLONG	0xffffffffffffffffULL

#define	BOOL_TYPE	UCHAR	/* what used to store _Bool */

/*
 * Use large-enough types.
 */
typedef	long long CONSZ;
typedef	unsigned long long U_CONSZ;
typedef long long OFFSZ;

#define CONFMT	"%lld"		/* format for printing constants */
#define LABFMT	".L%d"		/* format for printing labels */
#define	STABLBL	"LL%d"		/* format for stab (debugging) labels */
#define STAB_LINE_ABSOLUTE	/* S_LINE fields use absolute addresses */

/* Definitions mostly used in pass2 */

#define BYTEOFF(x)	((x)&03)
#define wdal(k)		(BYTEOFF(k)==0)

#define STOARG(p)
#define STOFARG(p)
#define STOSTARG(p)

#define szty(t) (t < LONG || t == FLOAT ? 1 : t == LDOUBLE ? 4 : 2)

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

#define V0	32
#define V1	33
#define V2	34
#define V3	35
#define V4	36
#define V5	37
#define V6	38
#define V7	39
#define V8	40
#define V9	41
#define V10	42
#define V11	43
#define V12	44
#define V13	45
#define V14	46
#define V15	47
#define V16	48
#define V17	49
#define V18	50
#define V19	51
#define V20	52
#define V21	53
#define V22	54
#define V23	55
#define V24	56
#define V25	57
#define V26	58
#define V27	59
#define V28	60
#define V29	61
#define V30	62
#define V31	63

#define NUMCLASS 3
#define	MAXREGS  64

#define RSTATUS \
/* x0  */ SAREG|TEMPREG, \
/* x1  */ SAREG|TEMPREG, \
/* x2  */ SAREG|TEMPREG, \
/* x3  */ SAREG|TEMPREG, \
/* x4  */ SAREG|TEMPREG, \
/* x5  */ SAREG|TEMPREG, \
/* x6  */ SAREG|TEMPREG, \
/* x7  */ SAREG|TEMPREG, \
/* x8  */ SAREG|TEMPREG, \
/* x9  */ SAREG|TEMPREG, \
/* x10 */ SAREG|TEMPREG, \
/* x11 */ SAREG|TEMPREG, \
/* x12 */ SAREG|TEMPREG, \
/* x13 */ SAREG|TEMPREG, \
/* x14 */ SAREG|TEMPREG, \
/* x15 */ SAREG|TEMPREG, \
/* x16 */ 0,            /* IP0 scratch (not allocatable) */ \
/* x17 */ 0,            /* IP1 scratch */ \
/* x18 */ 0,            /* platform register */ \
/* x19 */ SAREG|PERMREG, \
/* x20 */ SAREG|PERMREG, \
/* x21 */ SAREG|PERMREG, \
/* x22 */ SAREG|PERMREG, \
/* x23 */ SAREG|PERMREG, \
/* x24 */ SAREG|PERMREG, \
/* x25 */ SAREG|PERMREG, \
/* x26 */ SAREG|PERMREG, \
/* x27 */ SAREG|PERMREG, \
/* x28 */ SAREG|PERMREG, \
/* x29 */ 0,            /* FP (frame pointer) */ \
/* x30 */ 0,            /* LR */ \
/* x31 */ 0,            /* SP/WZR */ \
        \
	/* class B empty for now */ \
        \
/* v0  */ SCREG|TEMPREG, \
/* v1  */ SCREG|TEMPREG, \
/* v2  */ SCREG|TEMPREG, \
/* v3  */ SCREG|TEMPREG, \
/* v4  */ SCREG|TEMPREG, \
/* v5  */ SCREG|TEMPREG, \
/* v6  */ SCREG|TEMPREG, \
/* v7  */ SCREG|TEMPREG, \
/* v8  */ SCREG|PERMREG, /* callee-saved */ \
/* v9  */ SCREG|PERMREG, /* callee-saved */ \
/* v10 */ SCREG|PERMREG, /* callee-saved */ \
/* v11 */ SCREG|PERMREG, /* callee-saved */ \
/* v12 */ SCREG|PERMREG, /* callee-saved */ \
/* v13 */ SCREG|PERMREG, /* callee-saved */ \
/* v14 */ SCREG|PERMREG, /* callee-saved */ \
/* v15 */ SCREG|PERMREG, /* callee-saved */ \
/* v16 */ SCREG|TEMPREG, \
/* v17 */ SCREG|TEMPREG, \
/* v18 */ SCREG|TEMPREG, \
/* v19 */ SCREG|TEMPREG, \
/* v20 */ SCREG|TEMPREG, \
/* v21 */ SCREG|TEMPREG, \
/* v22 */ SCREG|TEMPREG, \
/* v23 */ SCREG|TEMPREG, \
/* v24 */ SCREG|TEMPREG, \
/* v25 */ SCREG|TEMPREG, \
/* v26 */ SCREG|TEMPREG, \
/* v27 */ SCREG|TEMPREG, \
/* v28 */ SCREG|TEMPREG, \
/* v29 */ SCREG|TEMPREG, \
/* v30 */ SCREG|TEMPREG, \
/* v31 */ 0            /* unusable due to class size limit */


/* no overlapping registers at all */
#define ROVERLAP \
        { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
        { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
        { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
        { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
        { -1 }, { -1 }, { -1 }, { -1 }, \
	\
        /* class B empty for now */ \
	\
        { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
        { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
        { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
        { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, { -1 }, \
        { -1 }, { -1 }, { -1 }, { -1 }


#define STACK_DOWN              /* stack grows negatively for temporaries */

#define ARGINIT		(16*8)	/* # bits above fp where arguments start */
#define AUTOINIT	0	/* # bits above fp where automatics start */

#undef	FIELDOPS		/* no bit-field instructions */
#define TARGET_ENDIAN TARGET_LE

/* XXX - to die */
#define FPREG   FP	/* frame pointer */
#define SPREG   SP      /* Stack pointer */

/* Return a register class based on the type of the node */
#define PCLASS(p)	(1 << gclass((p)->n_type))

#define GCLASS(x)	(x < 32 ? CLASSA : CLASSC )
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
#define NARGREGS	8

/* floating point definitions */
#define USE_IEEEFP_32
#define FLT_PREFIX	IEEEFP_32
#define USE_IEEEFP_64
#define DBL_PREFIX	IEEEFP_64
#define LDBL_PREFIX	IEEEFP_64
#define DEFAULT_FPI_DEFS { &fpi_binary32, &fpi_binary64, &fpi_binary64 }
