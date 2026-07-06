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
 * Machine-dependent defines for both passes.
 * Target: Zilog Z8001 (segmented) running Coherent on Commodore 900.
 *
 * Key facts:
 *   - 16-bit int, 32-bit long, 32-bit pointer (segmented: 7-bit segment + 16-bit offset)
 *   - Big-endian
 *   - Pure stack-based calling convention (no argument registers)
 *   - r13 = frame pointer, r14:r15 (rr14) = stack pointer
 *   - Segmented call pushes 4-byte return address (CS + PC)
 */

/*
 * Convert (multi-)character constant to integer.
 * Big-endian: first character in high byte.
 */
#define makecc(val,i)	lastcon = i ? (lastcon << 8) | val : val

#define ARGINIT		32	/* bits above frame base to first argument (4-byte return address) */
#define AUTOINIT	0	/* bits below frame base to first automatic (no initial reservation) */

/*
 * Storage space requirements (in bits).
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
#define SZPOINT(t)	32	/* segmented pointer: 16-bit segment word + 16-bit offset word */

/*
 * Alignment constraints (in bits).
 *
 * The Coherent ABI is word-aligned THROUGHOUT, longs and pointers
 * included (PDP-11 heritage, K&R compiler).  Proof: struct stat has
 * seven 16-bit members before st_size (long), placing it at offset 14.
 * Anything above 16 here also breaks our own calling convention:
 * FUNARG pushes arguments contiguously while pass 1 would lay out the
 * callee's incoming arg offsets with alignment padding (seen as the
 * mixed(int, long, int) failure: caller put the long at +6, callee
 * read it at +8).  Register pairs need no memory alignment.
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
#define ALSTRUCT	16	/* struct: strictest member, minimum word */
#define ALSTACK		16	/* stack pointer kept word-aligned */

/*
 * Min/max values.
 */
#define	MIN_CHAR	-128
#define	MAX_CHAR	127
#define	MAX_UCHAR	255
#define	MIN_SHORT	-32768
#define	MAX_SHORT	32767
#define	MAX_USHORT	65535
#define	MIN_INT		(-0x7fff-1)
#define	MAX_INT		0x7fff
#define	MAX_UNSIGNED	0xffff
#define	MIN_LONG	(-0x7fffffffL-1)
#define	MAX_LONG	0x7fffffffL
#define	MAX_ULONG	0xffffffffUL
#define	MIN_LONGLONG	(-0x7fffffffffffffffLL-1)
#define	MAX_LONGLONG	0x7fffffffffffffffLL
#define	MAX_ULONGLONG	0xffffffffffffffffULL

/* char is signed by default (ldb + extsb pattern in reference output) */
#undef	CHAR_UNSIGNED
#define	BOOL_TYPE	CHAR

/*
 * Use large-enough types for constants and offsets.
 */
typedef	long long CONSZ;
typedef	unsigned long long U_CONSZ;
typedef long long OFFSZ;

#define CONFMT		"%lld"		/* format for printing constants (decimal) */
#define LABFMT		"L%d"		/* format for printing internal labels */

#define STACK_DOWN			/* stack grows toward lower addresses */

#undef	FIELDOPS			/* no hardware bit-field instructions; use shift+mask */
#define TARGET_ENDIAN	TARGET_BE	/* big-endian */

#define	FINDMOPS			/* Z8001 ALU ops can target memory directly */
#define	MYALIGN				/* backend provides defalign() */

/* Coherent's assembler has no .file directive; suppress it. */
#define	MYDOTFILE
#define	printdotfile(x)

/* Coherent's assembler has no .ascii; emit strings as .byte lists. */
#define	MYINSTRING

/* Definitions mostly used in pass2 */

#define BYTEOFF(x)	((x) & 01)	/* nonzero if offset x is byte-aligned */
#define wdal(k)		(BYTEOFF(k) == 0)

#define STOARG(p)
#define STOFARG(p)
#define STOSTARG(p)

/*
 * szty(t): number of 16-bit register units occupied by type t.
 *   char/short/int  -> 1
 *   long/float/ptr  -> 2  (register pair)
 *   double/longlong -> 4  (register quad)
 *
 * A float value in registers is the raw 32-bit IEEE bit pattern in a
 * pair; all float ARITHMETIC is done in double via the runtime helpers
 * (K&R style, matching the native compiler, which has no float helpers
 * at all - see fixfloatops() in local2.c).
 */
/* STRTY/UNIONTY count as 2: a struct value is only ever "in registers"
 * as the pointer holding its address (hidden-pointer return ABI), so
 * PCLASS/RETREG must see it as a pair. */
#define szty(t) ((t) == DOUBLE || (t) == LDOUBLE || \
		 (t) == LONGLONG || (t) == ULONGLONG ? 4 : \
		 (t) == LONG || (t) == ULONG || \
		 (t) == FLOAT || ISPTR(t) || \
		 (t) == STRTY || (t) == UNIONTY ? 2 : 1)

/*
 * Register definitions.
 *
 * Physical registers r0-r15 occupy PCC indices 0-15.
 * Register pairs rr0, rr2, rr4, rr6, rr8, rr10 occupy indices 16-21.
 * r13 (frame pointer) and r14/r15 (stack pointer) are reserved.
 *
 * Register classes:
 *   A (SAREG) - 16-bit word registers: r0-r12
 *   B (SBREG) - 32-bit register pairs: rr0,rr2,rr4,rr6,rr8,rr10
 *   C (SCREG) - 64-bit register quads: rq0,rq4,rq8 (doubles; native
 *               soft-FP convention keeps a double value in rq0)
 *   D (SDREG) - 8-bit byte registers rl0-rl7 (the low bytes of r0-r7)
 *
 * Class D exists because Z8001 byte instructions (ldb/cpb/...) can only
 * name the halves of r0-r7; r8-r12 have no byte-addressable halves.
 * Making char values their own class (the arch/i86 model) lets the
 * allocator enforce that structurally, through ROVERLAP/aliasmap,
 * instead of via per-rule NOLEFT/NORIGHT/NEVER word-register constraints
 * - NEVER in particular is clobber semantics (addalledges), which gave
 * r8-r12 interference edges to EVERY value live near a char access and
 * starved cross-call values out of rr8/rr10.  Only the LOW halves exist
 * as registers here (no rh0-rh7): a char held in a word register lives
 * in its low byte everywhere in this ABI (big-endian argument slots,
 * memory loads, extsb), so high-byte registers would break that
 * convention at every conversion or store.
 */
#define	R0	0	/* scratch, low half of rr0, return word (int) */
#define	R1	1	/* scratch, high half of rr0, return value (int) */
#define	R2	2	/* scratch, low half of rr2 */
#define	R3	3	/* scratch, high half of rr2 */
#define	R4	4	/* scratch, low half of rr4 */
#define	R5	5	/* scratch, high half of rr4 */
#define	R6	6	/* callee-saved, low half of rr6 */
#define	R7	7	/* callee-saved, high half of rr6 */
#define	R8	8	/* callee-saved, low half of rr8 */
#define	R9	9	/* callee-saved, high half of rr8 */
#define	R10	10	/* callee-saved, low half of rr10 */
#define	R11	11	/* callee-saved, high half of rr10 */
#define	R12	12	/* callee-saved (no pair: rr12 includes r13=FP) */
#define	R13	13	/* frame pointer - reserved */
#define	R14	14	/* stack pointer high - reserved */
#define	R15	15	/* stack pointer low  - reserved */

#define	RR0	16	/* r0:r1  - scratch pair, return value (long/ptr) */
#define	RR2	17	/* r2:r3  - scratch pair */
#define	RR4	18	/* r4:r5  - scratch pair */
#define	RR6	19	/* r6:r7  - callee-saved pair */
#define	RR8	20	/* r8:r9  - callee-saved pair */
#define	RR10	21	/* r10:r11 - callee-saved pair */

#define	RQ0	22	/* r0-r3   - scratch quad, return value (double) */
#define	RQ4	23	/* r4-r7   - scratch quad (r6/r7 saved when used) */
#define	RQ8	24	/* r8-r11  - callee-saved quad */

#define	RL0	25	/* low byte of r0 - scratch */
#define	RL1	26	/* low byte of r1 - scratch, return value (char) */
#define	RL2	27	/* low byte of r2 - scratch */
#define	RL3	28	/* low byte of r3 - scratch */
#define	RL4	29	/* low byte of r4 - scratch */
#define	RL5	30	/* low byte of r5 - scratch */
#define	RL6	31	/* low byte of r6 - callee-saved (via word r6) */
#define	RL7	32	/* low byte of r7 - callee-saved (via word r7) */

#define	MAXREGS	33

/*
 * RSTATUS: register class membership and caller/callee-saved flags.
 * r13, r14, r15 are reserved (0) and never allocated.
 */
#define	RSTATUS	\
	SAREG|TEMPREG,	/* r0  */ \
	SAREG|TEMPREG,	/* r1  */ \
	SAREG|TEMPREG,	/* r2  */ \
	SAREG|TEMPREG,	/* r3  */ \
	SAREG|TEMPREG,	/* r4  */ \
	SAREG|TEMPREG,	/* r5  */ \
	SAREG|PERMREG,	/* r6  */ \
	SAREG|PERMREG,	/* r7  */ \
	SAREG|PERMREG,	/* r8  */ \
	SAREG|PERMREG,	/* r9  */ \
	SAREG|PERMREG,	/* r10 */ \
	SAREG|PERMREG,	/* r11 */ \
	SAREG|PERMREG,	/* r12 */ \
	0,		/* r13 - frame pointer */ \
	0,		/* r14 - SP high       */ \
	0,		/* r15 - SP low        */ \
	SBREG,		/* rr0  - valid color (RETREG) but cleared from clregs
			   in bjobcode so never allocated (RR0 can't be a base) */ \
	SBREG,		/* rr2  */ \
	SBREG,		/* rr4  */ \
	SBREG,		/* rr6  - preserved via its words r6/r7  */ \
	SBREG,		/* rr8  - preserved via its words r8/r9  */ \
	SBREG,		/* rr10 - preserved via its words r10/r11 */ \
	SCREG,		/* rq0  - caller-saved, double RETREG */ \
	SCREG,		/* rq4  - r6/r7 half saved by prologue when used */ \
	SCREG,		/* rq8  - preserved via its words r8-r11 */ \
	SDREG,		/* rl0  - caller-saved via its word r0 */ \
	SDREG,		/* rl1  - caller-saved, char RETREG */ \
	SDREG,		/* rl2  - caller-saved via its word r2 */ \
	SDREG,		/* rl3  - caller-saved via its word r3 */ \
	SDREG,		/* rl4  - caller-saved via its word r4 */ \
	SDREG,		/* rl5  - caller-saved via its word r5 */ \
	SDREG,		/* rl6  - preserved via its word r6 */ \
	SDREG,		/* rl7  - preserved via its word r7 */
/*
 * The byte registers carry no TEMPREG either: a char live across a call
 * conflicts with the precolored r0-r5 edges added there, and aliasmap
 * turns those into rl0-rl5 exclusions in class D automatically.
 *
 * Only the word registers r0-r5 carry TEMPREG.  tempregs[] is consumed in
 * exactly one place (regs.c call handling: addalledges of every listed
 * register at each call site), and marking the caller-saved pairs/quads
 * there as well is both redundant and costly:
 *  - redundant because AssignColors excludes overlapped colors through
 *    aliasmap(): a pair/quad temp live across a call already conflicts
 *    with precolored r0-r5, which maps to rr0/rr2/rr4 in class B and
 *    rq0/rq4 in class C;
 *  - costly because listing rq4 (r4-r7) makes every call exclude the
 *    callee-saved words r6/r7 (and pair rr6) from values that live
 *    across it, so cross-call words lost r6/r7 and cross-call pairs
 *    lost rr6 for no reason.  Found compiling wc.c: every register
 *    local spilled to the frame.
 */

/*
 * ROVERLAP: which other registers each register aliases.
 * A pair RRn aliases the two word registers Rn and R(n+1); a quad RQn
 * aliases four words and two pairs; a byte register RLn aliases its
 * containing word Rn and, transitively, that word's pair and quad.
 */
#define	ROVERLAP \
	{ RL0,  RR0,  RQ0, -1 },	/* r0  */ \
	{ RL1,  RR0,  RQ0, -1 },	/* r1  */ \
	{ RL2,  RR2,  RQ0, -1 },	/* r2  */ \
	{ RL3,  RR2,  RQ0, -1 },	/* r3  */ \
	{ RL4,  RR4,  RQ4, -1 },	/* r4  */ \
	{ RL5,  RR4,  RQ4, -1 },	/* r5  */ \
	{ RL6,  RR6,  RQ4, -1 },	/* r6  */ \
	{ RL7,  RR6,  RQ4, -1 },	/* r7  */ \
	{ RR8,  RQ8, -1 },	/* r8  */ \
	{ RR8,  RQ8, -1 },	/* r9  */ \
	{ RR10, RQ8, -1 },	/* r10 */ \
	{ RR10, RQ8, -1 },	/* r11 */ \
	{ -1 },			/* r12 - no pair */ \
	{ -1 },			/* r13 - reserved */ \
	{ -1 },			/* r14 - reserved */ \
	{ -1 },			/* r15 - reserved */ \
	{ R0,  R1,  RL0, RL1, RQ0, -1 },	/* rr0  */ \
	{ R2,  R3,  RL2, RL3, RQ0, -1 },	/* rr2  */ \
	{ R4,  R5,  RL4, RL5, RQ4, -1 },	/* rr4  */ \
	{ R6,  R7,  RL6, RL7, RQ4, -1 },	/* rr6  */ \
	{ R8,  R9,  RQ8, -1 },	/* rr8  */ \
	{ R10, R11, RQ8, -1 },	/* rr10 */ \
	{ R0, R1, R2, R3, RL0, RL1, RL2, RL3, RR0, RR2, -1 },	/* rq0 */ \
	{ R4, R5, R6, R7, RL4, RL5, RL6, RL7, RR4, RR6, -1 },	/* rq4 */ \
	{ R8, R9, R10, R11, RR8, RR10, -1 },	/* rq8 */ \
	{ R0, RR0, RQ0, -1 },	/* rl0 */ \
	{ R1, RR0, RQ0, -1 },	/* rl1 */ \
	{ R2, RR2, RQ0, -1 },	/* rl2 */ \
	{ R3, RR2, RQ0, -1 },	/* rl3 */ \
	{ R4, RR4, RQ4, -1 },	/* rl4 */ \
	{ R5, RR4, RQ4, -1 },	/* rl5 */ \
	{ R6, RR6, RQ4, -1 },	/* rl6 */ \
	{ R7, RR6, RQ4, -1 },	/* rl7 */

/* Return the register class for a node's type */
#define PCLASS(p) ((p)->n_type == CHAR || (p)->n_type == UCHAR ? SDREG : \
		   szty((p)->n_type) == 4 ? SCREG : \
		   szty((p)->n_type) == 2 ? SBREG : SAREG)

#define	NUMCLASS	4	/* classes: A (word), B (pair), C (quad), D (byte) */

int COLORMAP(int c, int *r);
#define	GCLASS(x)	((x) < 16 ? CLASSA : (x) < 22 ? CLASSB : \
			 (x) < 25 ? CLASSC : CLASSD)
/* 6-bit register fields: MAXREGS is 33, three regs packed in n_reg */
#define DECRA(x,y)	(((x) >> ((y)*6)) & 63)	/* decode register from n_reg */
#define	ENCRD(x)	(x)			/* encode dest register */
#define ENCRA1(x)	((x) << 6)
#define ENCRA2(x)	((x) << 12)
#define ENCRA(x,y)	((x) << (6+(y)*6))	/* encode source register */

/*
 * Return register for each type (matches the native Coherent compiler:
 * factor.s reads int results from r1, long results from rr0, and double
 * results from rq0; the FP runtime's ifix returns int in r1 too):
 *   char            -> rl1 (the low byte of r1; the class-D view of the
 *                      native word convention - a caller wanting an int
 *                      re-extends, one reading a char takes rl1 as is)
 *   int/short       -> r1
 *   long/ptr/float  -> rr0 (r0:r1)
 *   double          -> rq0 (r0-r3)
 */
#define	RETREG(x)	((x) == CHAR || (x) == UCHAR ? RL1 : \
			 szty(x) == 4 ? RQ0 : szty(x) == 2 ? RR0 : R1)

#define FPREG	R13	/* frame pointer */
#define STKREG	R15	/* stack pointer (low word of rr14) */

/*
 * Special shapes.  The Z8001 based address mode rrN(disp) (BA) is only
 * legal in the ld/ldl/ldb/lda family; every other instruction taking a
 * memory operand accepts only IR "(rrN)", DA "name" and X "L<n>+off(r13)"
 * modes (Coherent as machine.c: S_RSRC/S_DEC/S_CLR/S_CP/S_PUSH all lack
 * BAOK).  So plain SOREG must not appear in non-load rules; these shapes
 * take its place there.
 */
/*
 * Target pass2 attribute: each STCALL/USTCALL carries the offset of its
 * OWN struct-return buffer in the caller's frame (assigned by myreader()
 * in local2.c, consumed by the ZR escape).  One shared buffer is not
 * enough: pass 2 pre-evaluates call-containing arguments into pointer
 * temps before pushing any argument, so with two struct-returning calls
 * in one argument list both results are live at the same time.
 */
#define	ATTR_P2_TARGET	ATTR_P2_STBUF

#define	SNBA	(MAXSPECIAL+1)	/* OREG encodable in a non-load insn:
				   frame (X mode) or pair base with zero
				   displacement (IR mode) */
#define	SFRAME	(MAXSPECIAL+2)	/* frame (r13-based) OREG only: for rules
				   that access both pair halves at off and
				   off+2 (ZL/ZQ), where a pair-base OREG
				   would need BA for the second half */
#define	SR13	(MAXSPECIAL+3)	/* REG node that is exactly r13: the frame
				   pointer as a bare word register, produced
				   only by the reader lowering &frameobj to
				   PLUS/MINUS(REG r13, ICON off) */

/*
 * sizeof and pointer-difference results are plain 16-bit integers, NOT
 * pointer-sized: the Coherent libc is K&R and unprototyped, and its
 * functions declare sizes and counts as int/unsigned words -
 * qsort(base, nel, width, compar) "unsigned nel, width", malloc(size)
 * "unsigned int size", fread "int size, nitems".  The native compiler
 * pushes them as words (ls.s qsort call: "push (rr14),$38").  With the
 * pcc default (INTPTR = LONG, since pointers are 32-bit), every
 * malloc(n*sizeof(x)) would push 4 bytes where libc reads 2.
 */
#define	SIZET		UNSIGNED
#define	PTRDIFFT	INT

/*
 * Never fold x+0/x-0 to a bare frame-pointer REG: a segmented address
 * needs the lda+mask pair materialization (ZF), and r13 alone is a
 * word with no segment.  Hit by &arr[N] where the array end lands at
 * frame offset exactly 0 (tee.c "fpp >= &fp[NUFILE]" emitted the
 * illegal "cpl rr8,r13").
 */
#define	OPTIM_KEEPZERO(p)	(p->n_left->n_op == REG && \
				 p->n_left->n_rval == FPREG)

/* Soft-float: big-endian IEEE binary32 and binary64 */
#define	USE_IEEEFP_32
#define	FLT_PREFIX	IEEEFP_32
#define	USE_IEEEFP_64
#define	DBL_PREFIX	IEEEFP_64
#define	LDBL_PREFIX	IEEEFP_64
#define	DEFAULT_FPI_DEFS { &fpi_binary32, &fpi_binary64, &fpi_binary64 }
