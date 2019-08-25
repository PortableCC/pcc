/*	$Id$	*/

/*
 * Copyright (c) 2008 Anders Magnusson. All rights reserved.
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

#include "manifest.h"
#include "softfloat.h"

#include <stdint.h>
#include <stdlib.h>
#include <string.h>

#ifndef PCC_DEBUG
#define assert(e) ((void)0)
#else
#define assert(e) (!(e)?cerror("assertion failed " #e " at softfloat:%d",__LINE__):(void)0)
#endif

#define SFDEBUG
#ifdef SFDEBUG
int sfdebug=0;
#define	SD(x)	if (sfdebug) printf x
#else
#define SD(x)
#endif
#define sfp2ld(x) (x)->debugfp

/*
 * Description of a floating point format.
 */
typedef struct FPI {
	int nbits;	/* size of mantissa */
	int storage;	/* size of fp word */
	int bias;	/* exponent bias */
	int minexp;	/* min exponent (except zero/subnormal) */
	int maxexp;	/* max exponent (except INF) */
	int min10exp;	/* min base10 exponent (except zero/subnormal) */
	int max10exp;	/* max base10 exponent (except INF) */
	int dig;	/* max number of decimal digits in mant */
	int expadj;	/* adjust for fraction point position */

	/* fp-specific routines */
	void (*make)	/* make this type in sfp */
	    (SFP, int typ, int sign, int exp, MINT *mant);
	int (*unmake)	/* growel out this type from sfp */
	    (SFP, int *sign, int *exp, MINT *mant);
	int (*classify)(SFP sfp);
} FPI;

FPI *fpis[3] = DEFAULT_FPI_DEFS; /* FLOAT, DOUBLE, LDOUBLE, respectively */
#define	LDBLPTR	fpis[SF_LDOUBLE]

#define MKSF(t)		((t)-FLOAT)
#define SF_FLOAT	(0)
#define SF_DOUBLE	(1)
#define SF_LDOUBLE	(2)

#define	SOFT_INFINITE	1
#define	SOFT_NAN	2
#define	SOFT_ZERO	3
#define	SOFT_NORMAL	4
#define	SOFT_SUBNORMAL	5
#ifdef SFDEBUG
static char *sftyp[] = { "0", "Inf", "Nan", "Zero", "Normal", "Subnormal" };
#endif

#define MINTZ(x) ((x)->len == 0 || ((x)->len == 1 && (x)->val[0] == 0))

void madd(MINT *a, MINT *b, MINT *c);
void msub(MINT *a, MINT *b, MINT *c);
void mult(MINT *a, MINT *b, MINT *c);
void mdiv(MINT *a, MINT *b, MINT *c, MINT *r);
void minit(MINT *m, int v);
void mshl(MINT *m, int nbits);
static void mshr(MINT *m, int nbits, int sticky);
static void chomp(MINT *a);
void mdump(char *c, MINT *a);
static int geq(MINT *l, MINT *r);
static int topbit(MINT *a);
static void grsround(MINT *a, FPI *);
static void mcopy(MINT *b, MINT *a);
static void mexpand(MINT *a, int minsz);
static int mknormal(FPI *, int *e, MINT *m);

/*
 * Floating point emulation, to not depend on the characteristics (and bugs)
 * of the host floating-point implementation when compiling.
 */

#ifdef FDFLOAT
static void
ffloat_make(SFP sfp, int typ, int sign, int exp, MINT *m)
{
	sfp->fp[0] = (sign << 15);

	SD(("ffloat_make: typ %s sign %d exp %d M 0x%04x%04x %04x%04x\n",
	   sftyp[typ], sign, exp, m->val[3], m->val[2], m->val[1], m->val[0]));
	if (typ == SOFT_NORMAL)
		typ = mknormal(&fpi_ffloat, &exp, m);

	SD(("ffloat_make2: typ %s sign %d exp %d M 0x%04x%04x %04x%04x\n",
	    sftyp[typ], sign, exp, m->val[3], m->val[2], m->val[1], m->val[0]));
	switch (typ) {
	case SOFT_ZERO:
		break;
	case SOFT_INFINITE:
		sfp->fp[0] |= 0xffff7fff; /* highest possible number */
		break;
	case SOFT_NAN:
		sfp->fp[0] |= 0x00008000; /* signal */
		break;
	case SOFT_NORMAL:
		exp += (fpi_ffloat.bias-1);
		sfp->fp[0] |= (exp & 0xff) << 7;
		sfp->fp[0] += m->val[1] + ((uint32_t)m->val[0] << 16);
		break;
	case SOFT_SUBNORMAL:
		break; /* no subnormal */
	}
	SD(("ffloat_make3: fp %08x\n", sfp->fp[0]));
}

static int
ffloat_unmake(SFP sfp, int *sign, int *exp, MINT *m)
{
	*sign = (sfp->fp[0] >> 15) & 1;
	*exp = ((sfp->fp[0] >> 7) & 0xff) - fpi_ffloat.bias;
	minit(m, sfp->fp[0] >> 16);
	m->val[1] = (sfp->fp[0] & 0x7f) | (1 << 7);
	m->len = 2;
	return (sfp->fp[0] == 0xffff7fff ? SOFT_INFINITE : SOFT_NORMAL);
}

FPI fpi_ffloat = { 
	.nbits = FFLOAT_MANT_DIG,  
	.storage = 32,
        .bias = 128,
	.minexp = FFLOAT_MIN_EXP-1,
	.maxexp = FFLOAT_MAX_EXP-1,
	.min10exp = FFLOAT_MIN_10_EXP-1,
	.max10exp = FFLOAT_MAX_10_EXP-1,
	.dig = FFLOAT_DIG,
	.expadj = 0,

	.make = ffloat_make,
	.unmake = ffloat_unmake,
};

static int
dfloat_classify(SFP sfp)
{
	uint32_t val = sfp->fp[0] & 0xffff7fff;

	if (val == 0xffff7fff && sfp->fp[1] == 0xffffffff)
		return SOFT_INFINITE;
	if ((val & 0x00007f80) == 0)
		return SOFT_ZERO;
	return SOFT_NORMAL;
}

static void
dfloat_make(SFP sfp, int typ, int sign, int exp, MINT *m)
{
	sfp->fp[0] = (sign << 15);

	SD(("dfloat_make: typ %s sign %d exp %d M 0x%04x%04x %04x%04x\n",
	   sftyp[typ], sign, exp, m->val[3], m->val[2], m->val[1], m->val[0]));
	if (typ == SOFT_NORMAL)
		typ = mknormal(&fpi_dfloat, &exp, m);

	SD(("dfloat_make2: typ %s sign %d exp %d M 0x%04x%04x %04x%04x\n",
	    sftyp[typ], sign, exp, m->val[3], m->val[2], m->val[1], m->val[0]));
	switch (typ) {
	case SOFT_ZERO:
		sfp->fp[0] = sfp->fp[1] = 0;
		break;
	case SOFT_INFINITE:
		sfp->fp[0] |= 0xffff7fff; /* highest possible number */
		sfp->fp[1] = 0xffffffff; /* highest possible number */
		break;
	case SOFT_NAN:
		sfp->fp[0] |= 0x00008000; /* signal */
		sfp->fp[1] = 0;
		break;
	case SOFT_NORMAL:
		exp += (fpi_dfloat.bias-1);
		sfp->fp[0] |= (exp & 0xff) << 7;
		sfp->fp[0] += m->val[3] + ((uint32_t)m->val[2] << 16);
		sfp->fp[1] = m->val[1] + ((uint32_t)m->val[0] << 16);
		break;
	case SOFT_SUBNORMAL:
		break; /* no subnormal */
	}
	SD(("dfloat_make3: fp %08x %08x\n", sfp->fp[0], sfp->fp[1]));
	
}

static int
dfloat_unmake(SFP sfp, int *sign, int *exp, MINT *m)
{
	int t = dfloat_classify(sfp);

	SD(("dfloat_unmake1: fp %08x %08x\n", sfp->fp[0], sfp->fp[1]));
	*sign = (sfp->fp[0] >> 15) & 1;
	*exp = ((sfp->fp[0] >> 7) & 0xff) - fpi_dfloat.bias;
	minit(m, sfp->fp[1] >> 16);
	m->val[1] = sfp->fp[1];
	m->val[2] = (sfp->fp[0] >> 16);
	m->val[3] = (sfp->fp[0] & 0x7f) | (1 << 7);
	m->len = 4;
	SD(("dfloat_unmake2: typ %s sign %d exp %d M 0x%04x%04x %04x%04x\n",
	    sftyp[t], *sign, *exp, m->val[3], m->val[2], m->val[1], m->val[0]));
	return t;
}

FPI fpi_dfloat = { 
	.nbits = DFLOAT_MANT_DIG,  
	.storage = 64,
        .bias = 128,
	.minexp = DFLOAT_MIN_EXP-1,
	.maxexp = DFLOAT_MAX_EXP-1,
	.min10exp = DFLOAT_MIN_10_EXP-1,
	.max10exp = DFLOAT_MAX_10_EXP-1,
	.dig = DFLOAT_DIG,
	.expadj = 0,

	.make = dfloat_make,
	.unmake = dfloat_unmake,
	.classify = dfloat_classify,
};
#endif

/* IEEE binary formats, and their interchange format encodings */
#ifdef notdef
FPI fpi_binary16 = { 11, 1-15-11+1,
                        30-15-11+1, 1, 0,
        0, 1, 1, 0,  16,   15+11-1 };
#endif
#ifdef notyet
FPI fpi_binary128 = { 113,   1-16383-113+1,
                         32766-16383-113+1, 1, 0,
        0, 1, 1, 0,   128,     16383+113-1 };
#endif

#ifdef USE_IEEEFP_32
#define	IEEEFP_32_ISINF(x)	(((x)->fp[0] & 0x7fffffff) == 0x7f800000)
#define	IEEEFP_32_ISZERO(x)	(((x)->fp[0] & 0x7fffffff) == 0)
#define	IEEEFP_32_ISNAN(x)	(((x)->fp[0] & 0x7fffffff) == 0x7fc00000)

static int
ieee32_classify(SFP sfp)
{
	uint32_t val = sfp->fp[0] & 0x7fffffff;

	if (val == 0x7f800000)
		return SOFT_INFINITE;
	if (val == 0x7fc00000)
		return SOFT_NAN;
	if (val == 0)
		return SOFT_ZERO;
	if (val & 0x7f800000)
		return SOFT_NORMAL;
	return SOFT_SUBNORMAL;
}

static void
ieee32_make(SFP sfp, int typ, int sign, int exp, MINT *m)
{
	sfp->fp[0] = (sign << 31);

	SD(("ieee32_make: typ %s sign %d exp %d M 0x%04x%04x %04x%04x\n",
	   sftyp[typ], sign, exp, m->val[3], m->val[2], m->val[1], m->val[0]));
	if (typ == SOFT_NORMAL)
		typ = mknormal(&fpi_binary32, &exp, m);

	SD(("ieee32_make2: typ %s sign %d exp %d M 0x%04x%04x %04x%04x\n",
	    sftyp[typ], sign, exp, m->val[3], m->val[2], m->val[1], m->val[0]));
	switch (typ) {
	case SOFT_ZERO:
		break;
	case SOFT_INFINITE:
		sfp->fp[0] |= 0x7f800000;
		break;
	case SOFT_NAN:
		sfp->fp[0] |= 0x7fc00000;
		break;
	case SOFT_NORMAL:
		exp += (fpi_binary32.bias-1);
		sfp->fp[0] |= (uint32_t)(exp & 0xff) << 23;
		sfp->fp[0] += (((uint32_t)m->val[1] << 16) | m->val[0]);
		break;
	case SOFT_SUBNORMAL:
		sfp->fp[0] |= ((uint32_t)m->val[1] << 16) | m->val[0];
		break;
	}
	SD(("ieee32_make3: fp %08x\n", sfp->fp[0]));
	
}

static int
ieee32_unmake(SFP sfp, int *sign, int *exp, MINT *m)
{
	int t, v = ieee32_classify(sfp);

	*sign = (sfp->fp[0] >> 31) & 1;
	*exp = ((sfp->fp[0] >> 23) & 0xff) - fpi_binary32.bias;
	minit(m, sfp->fp[0]);
	m->val[1] = ((sfp->fp[0] >> 16) & 0x7f);
	m->len = 2;
	if (v == SOFT_SUBNORMAL) {
		v = SOFT_NORMAL;
		chomp(m);
		t = topbit(m);
		*exp = fpi_binary32.minexp - (fpi_binary32.nbits - t) + 1;
	} else if (v == SOFT_NORMAL)
		m->val[1] |= (1 << 7);
	return v;
}

FPI fpi_binary32 = { 
	.nbits = IEEEFP_32_MANT_DIG,  
	.storage = 32,
        .bias = 127,
	.minexp = IEEEFP_32_MIN_EXP-1,
	.maxexp = IEEEFP_32_MAX_EXP-1,
	.min10exp = IEEEFP_32_MIN_10_EXP-1,
	.max10exp = IEEEFP_32_MAX_10_EXP-1,
	.dig = IEEEFP_32_DIG,
	.expadj = 1,

	.make = ieee32_make,
	.unmake = ieee32_unmake,
	.classify = ieee32_classify,
};
#endif

#ifdef USE_IEEEFP_64
#define	IEEEFP_64_ISINF(x) ((((x)->fp[1] & 0x7fffffff) == 0x7ff00000) && \
	    (x)->fp[0] == 0)
#define	IEEEFP_64_ISZERO(x) ((((x)->fp[1] & 0x7fffffff) == 0) && (x)->fp[0] == 0)
#define	IEEEFP_64_ISNAN(x) ((((x)->fp[1] & 0x7fffffff) == 0x7ff80000) && \
	    (x)->fp[0] == 0)

static int
ieee64_classify(SFP sfp)
{
	int e = sfp->fp[1] & 0x7ff00000;

	if (IEEEFP_64_ISINF(sfp))
		return SOFT_INFINITE;
	if (IEEEFP_64_ISNAN(sfp))
		return SOFT_NAN;
	if (IEEEFP_64_ISZERO(sfp))
		return SOFT_ZERO;
	if (e)
		return SOFT_NORMAL;
	return SOFT_SUBNORMAL;
}

static int
ieee64_unmake(SFP sfp, int *sign, int *exp, MINT *m)
{
	int t, v = ieee64_classify(sfp);

	*sign = (sfp->fp[1] >> 31) & 1;
	*exp = ((sfp->fp[1] >> 20) & 0x7ff) - fpi_binary64.bias;
	minit(m, sfp->fp[0]);
	m->val[1] = (sfp->fp[0] >> 16);
	m->val[2] = sfp->fp[1];
	m->val[3] = ((sfp->fp[1] >> 16) & 0x0f);
	m->len = 4;
	if (v == SOFT_SUBNORMAL) {
		v = SOFT_NORMAL;
		chomp(m);
		t = topbit(m);
		*exp = fpi_binary64.minexp - (fpi_binary64.nbits - t) + 1;
	} else if (v == SOFT_NORMAL)
		m->val[3] |= (1 << 4);
	return v;
}

static void
ieee64_make(SFP sfp, int typ, int sign, int exp, MINT *m)
{
	sfp->fp[0] = 0;
	sfp->fp[1] = (sign << 31);

	SD(("ieee64_make: typ %s sign %d exp %d M 0x%04x%04x %04x%04x\n",
	   sftyp[typ], sign, exp, m->val[3], m->val[2], m->val[1], m->val[0]));

	if (typ == SOFT_NORMAL)
		typ = mknormal(&fpi_binary64, &exp, m);

	SD(("ieee64_make2: typ %s sign %d exp %d M 0x%04x%04x %04x%04x\n",
	    sftyp[typ], sign, exp, m->val[3], m->val[2], m->val[1], m->val[0]));
	switch (typ) {
	case SOFT_ZERO:
		break;
	case SOFT_INFINITE:
		sfp->fp[1] |= 0x7ff00000;
		break;
	case SOFT_NAN:
		sfp->fp[1] |= 0x7ff80000;
		break;
	case SOFT_NORMAL:
		exp += (fpi_binary64.bias-1);
		sfp->fp[0] = ((uint32_t)m->val[1] << 16) | m->val[0];
		sfp->fp[1] |= ((uint32_t)m->val[3] << 16) | m->val[2];
		sfp->fp[1] += (uint32_t)(exp & 0x7ff) << 20;
		break;
	case SOFT_SUBNORMAL:
		sfp->fp[0] = ((uint32_t)m->val[1] << 16) | m->val[0];
		sfp->fp[1] |= ((uint32_t)m->val[3] << 16) | m->val[2];
		break;
	}
	SD(("ieee64_make3: fp %08x %08x\n", sfp->fp[1], sfp->fp[0]));
}

FPI fpi_binary64 = {
	.nbits = IEEEFP_64_MANT_DIG,
	.storage = 64,
	.bias = 1023,
	.minexp = IEEEFP_64_MIN_EXP-1,
	.maxexp = IEEEFP_64_MAX_EXP-1,
	.min10exp = IEEEFP_64_MIN_10_EXP-1,
	.max10exp = IEEEFP_64_MAX_10_EXP-1,
	.dig = IEEEFP_64_DIG,
	.expadj = 1,

	.make = ieee64_make,
	.unmake = ieee64_unmake,
	.classify = ieee64_classify,
};      
#endif

#ifdef USE_IEEEFP_X80
#define	IEEEFP_X80_ISINF(x) ((((x)->fp[2] & 0x7fff) == 0x7fff) && \
	((x)->fp[1] == 0x80000000) && (x)->fp[0] == 0)
#define	IEEEFP_X80_ISZERO(x) ((((x)->fp[2] & 0x7fff) == 0) && \
	((x)->fp[1] | (x)->fp[0]) == 0)
#define	IEEEFP_X80_ISNAN(x) ((((x)->fp[2] & 0x7fff) == 0x7fff) && \
	(((x)->fp[1] != 0x80000000) || (x)->fp[0] == 0))

static int
ieeex80_classify(SFP sfp)
{
	short val = sfp->fp[2] & 0x7fff;

	if (IEEEFP_X80_ISINF(sfp))
		return SOFT_INFINITE;
	if (IEEEFP_X80_ISNAN(sfp))
		return SOFT_NAN;
	if (IEEEFP_X80_ISZERO(sfp))
		return SOFT_ZERO;
	if (val)
		return SOFT_NORMAL;
	return SOFT_SUBNORMAL;
}

static void
ieeex80_make(SFP sfp, int typ, int sign, int exp, MINT *m)
{
	sfp->fp[0] = sfp->fp[1] = 0;
	sfp->fp[2] = (sign << 15);

	SD(("ieeex80_make: typ %s sign %d exp %d M 0x%04x%04x %04x%04x\n",
	   sftyp[typ], sign, exp, m->val[3], m->val[2], m->val[1], m->val[0]));

	m->sign = 0;
	if (typ == SOFT_NORMAL)
		typ = mknormal(&fpi_binaryx80, &exp, m);

	SD(("ieeex80_make2: typ %s sign %d exp %d M 0x%04x%04x %04x%04x\n",
	    sftyp[typ], sign, exp, m->val[3], m->val[2], m->val[1], m->val[0]));
	switch (typ) {
	case SOFT_ZERO:
		break;
	case SOFT_INFINITE:
		sfp->fp[1] = 0x80000000;
		sfp->fp[2] |= 0x7fff;
		break;
	case SOFT_NAN:
		sfp->fp[1] = 0xc0000000;
		sfp->fp[2] |= 0x7fff;
		break;
	case SOFT_NORMAL:
		exp += fpi_binaryx80.bias;
		sfp->fp[0] = ((uint32_t)m->val[1] << 16) | m->val[0];
		sfp->fp[1] = ((uint32_t)m->val[3] << 16) | m->val[2];
		sfp->fp[2] |= (uint32_t)(exp & 0x7fff);
		if (m->len ==5 && m->val[4])
			sfp->fp[2]++;
		break;
	case SOFT_SUBNORMAL:
		sfp->fp[0] = ((uint32_t)m->val[1] << 16) | m->val[0];
		sfp->fp[1] = ((uint32_t)m->val[3] << 16) | m->val[2];
		break;
	}
	SD(("ieeex80_make3: fp %04x %08x %08x\n", sfp->fp[2], sfp->fp[1], sfp->fp[0]));
}


static int
ieeex80_unmake(SFP sfp, int *sign, int *exp, MINT *m)
{
	int t, v = ieeex80_classify(sfp);

	SD(("ieeex80_unmake: %s %04x %08x %08x\n", 
	    sftyp[v], sfp->fp[2], sfp->fp[1], sfp->fp[0]));
	*sign = (sfp->fp[2] >> 15) & 1;
	*exp = (sfp->fp[2] & 0x7fff) - fpi_binaryx80.bias;
	minit(m, sfp->fp[0]);
	m->val[1] = (sfp->fp[0] >> 16);
	m->val[2] = sfp->fp[1];
	m->val[3] = (sfp->fp[1] >> 16);
	m->len = 4;
	if (v == SOFT_SUBNORMAL) {
		v = SOFT_NORMAL;
		chomp(m);
		t = topbit(m);
		*exp = fpi_binaryx80.minexp - (fpi_binaryx80.nbits - t) + 1;
	}
	SD(("ieeex80_unmake2: sign %d exp %d m %04x%04x %04x%04x\n",
	    *sign, *exp, m->val[3], m->val[2], m->val[1], m->val[0]));
	return v;
}

/* IEEE double extended in its usual form, for example Intel 387 */
FPI fpi_binaryx80 = {
	.nbits = IEEEFP_X80_MANT_DIG,
	.storage = 80,
	.bias = 16383,
	.minexp = IEEEFP_X80_MIN_EXP-1,
	.maxexp = IEEEFP_X80_MAX_EXP-1,
	.min10exp = IEEEFP_X80_MIN_10_EXP-1,
	.max10exp = IEEEFP_X80_MAX_10_EXP-1,
	.dig = IEEEFP_X80_DIG,
	.expadj = 1,

	.make = ieeex80_make,
	.unmake = ieeex80_unmake,
	.classify = ieeex80_classify,
};      
#endif

#ifdef USE_IEEEFP_X80
#define	SZLD 10 /* less than SZLDOUBLE, avoid cmp junk */
#else
#define SZLD sizeof(long double)
#endif

#define FPI_FLOAT	C(FLT_PREFIX,_FPI)
#define FPI_DOUBLE	C(DBL_PREFIX,_FPI)
#define FPI_LDOUBLE	C(LDBL_PREFIX,_FPI)

/*
 * IEEE specials:
 * Zero:	Exponent 0, mantissa 0
 * Denormal:	Exponent 0, mantissa != 0
 * Infinity:	Exponent all 1, mantissa 0
 * QNAN:	Exponent all 1, mantissa MSB 1 (indeterminate)
 * SNAN:	Exponent all 1, mantissa MSB 0 (invalid)
 */

/*
 * Create correct floating point values for f.
 * Exponent is not biased, and if it is negative it is a subnormal number.
 * Return may be any class.
 */
#define	RNDBIT 10
static int
mknormal(FPI *f, int *exp, MINT *m)
{
	MINT a, c;
	int t = topbit(m);
	int e = *exp;
	int bno = f->nbits-1;
	int sav, issub = 0;

	MINTDECL(a);
	MINTDECL(c);

	SD(("mknormal: t %d bno %d exp %d m %04x%04x %04x%04x\n",
	    t, bno, e, m->val[3], m->val[2], m->val[1], m->val[0]));
	/* first make distance between in and out number RNDBIT bits */
	if (t - bno < RNDBIT)
		mshl(m, RNDBIT - (t - bno));
	if (t - bno > RNDBIT)
		mshr(m, (t - bno) - RNDBIT, 1);

	minit(&a, 1 << (RNDBIT-1));

	SD(("mknormal2: a0 %x m %04x%04x %04x%04x\n",
	    a.val[0], m->val[3], m->val[2], m->val[1], m->val[0]));
	if (e < f->minexp) {
		mshr(m, -(e-f->minexp), 1);
		SD(("mknormal3: shr %d m %04x%04x %04x%04x\n", e-f->minexp,
		    m->val[3], m->val[2], m->val[1], m->val[0]));
		issub = 1;
	} else if (e >= f->maxexp) {
		SD(("mknormal4: e %d m %04x%04x %04x%04x\n",
		    e, m->val[3], m->val[2], m->val[1], m->val[0]));
		if (e > f->maxexp)
			return SOFT_INFINITE;
		madd(m, &a, &c);
		if (topbit(&c) == topbit(m)+1)
			return SOFT_INFINITE;
	}
	sav = m->val[0] & ((a.val[0] << 1)-1);
	mshr(m, RNDBIT, 0);
	SD(("mknormal5: m %04x%04x %04x%04x\n",
	    m->val[3], m->val[2], m->val[1], m->val[0]));
	if ((sav & a.val[0])) {
		if ((sav & (a.val[0]-1)) || (m->val[0] & 1)) {
			a.val[0] = 1;
			madd(m, &a, &c);
			mcopy(&c, m);
		}
	}
	SD(("mknormal6: m %04x%04x %04x%04x\n",
	    m->val[3], m->val[2], m->val[1], m->val[0]));
	if (MINTZ(m))
		return SOFT_ZERO;
	return issub ? SOFT_SUBNORMAL : SOFT_NORMAL;
}

/*
 * Round using "nearest-to-even".
 */
static void
grsround(MINT *m, FPI *f)
{
	int t = topbit(m);
	int bno = f->nbits-1;
	MINT a, c;
	int sav;

	MINTDECL(a);
	MINTDECL(c);
	minit(&a, 1 << (RNDBIT-1));

	if (t - bno < RNDBIT)
		mshl(m, RNDBIT - (t - bno));
	if (t - bno > RNDBIT)
		mshr(m, (t - bno) - RNDBIT, 1);

	sav = m->val[0] & ((a.val[0] << 1)-1);
	mshr(m, RNDBIT, 0);
	if ((sav & a.val[0])) {
		if ((sav & (a.val[0]-1)) || (m->val[0] & 1)) {
			a.val[0] = 1;
			madd(m, &a, &c);
			mcopy(&c, m);
		}
	}
}

/*
 * Return highest set bit in a.  
 * Bit numbering starts with 0.
 */
static int
topbit(MINT *a)
{
	uint16_t val;
	int res;

	chomp(a);
	res = (a->len-1) * 16;
	val = a->val[a->len-1];
	val >>= 1;
	while (val)
		val >>= 1, res++;
	return res;
}

static void
mcopy(MINT *b, MINT *a)
{
	int i;

	if (a->allo < b->len)
		mexpand(a, b->len);
	a->len = b->len;
	a->sign = b->sign;
	for (i = 0; i < a->len; i++)
		a->val[i] = b->val[i];
}

/*
 * Conversions.
 */

/*
 * Convert from integer type f to floating-point type t.
 * Rounds correctly to the target type.
 */
void
soft_int2fp(SFP rv, CONSZ l, TWORD f, TWORD t)
{
	MINT m;
	int c, s, e;
#ifdef DEBUGFP
	CONSZ debl = l;
#endif

	MINTDECL(m);

	e = s = 0;
	c = SOFT_NORMAL;
	if (!ISUNSIGNED(f) && l < 0) {
		if (l ^ 0x8000000000000000ULL)
			l = -l;
		s = 1;
	} else if (l == 0)
		c = SOFT_ZERO;

	m.val[0] = l;
	m.val[1] = l >> 16;
	m.val[2] = l >> 32;
	m.val[3] = l >> 48;
	m.len = 4;

	e = topbit(&m) + 1 - LDBLPTR->expadj;

	LDBLPTR->make(rv, c, s, e, &m);
	if (t == FLOAT || t == DOUBLE)
		soft_fp2fp(rv, t);

#ifdef DEBUGFP
	{ long double dl;
		dl = ISUNSIGNED(f) ? (long double)(U_CONSZ)(debl) :
		    (long double)(CONSZ)(debl);
		dl = t == FLOAT ? (float)dl : t == DOUBLE ? (double)dl : dl;
		if (dl != rv->debugfp)
			fpwarn("soft_int2fp", rv->debugfp, dl);
	}
#endif
}

/*
 * Explicit cast into some floating-point format.
 */
void
soft_fp2fp(SFP sfp, TWORD t)
{
	SF rv, rv2;
	MINT m;
	int e, s, c;

	MINTDECL(m);

	c = LDBLPTR->unmake(sfp, &s, &e, &m);
	fpis[MKSF(t)]->make(&rv2, c, s, e, &m);
	c = fpis[MKSF(t)]->unmake(&rv2, &s, &e, &m);
	LDBLPTR->make(&rv, c, s, e, &m);

#ifdef DEBUGFP
	{ long double l = (t == DOUBLE ? (double)sfp->debugfp :
	    (t == FLOAT ? (float)sfp->debugfp : sfp->debugfp));
	if (memcmp(&l, &rv.debugfp, SZLD))
		fpwarn("soft_fp2fp", rv.debugfp, l);
	}
#endif
	*sfp = rv;
}

/*
 * Convert a fp number to a CONSZ. Always chop toward zero.
 */
CONSZ
soft_fp2int(SFP sfp, TWORD t)
{
	U_CONSZ rv;
	MINT m;
	int c, s, e;

	MINTDECL(m);

	c = LDBLPTR->unmake(sfp, &s, &e, &m);
	if (c != SOFT_NORMAL)
		return 0;

	rv = m.val[0];
	if (m.len > 1)
		rv |= ((CONSZ)m.val[1] << 16);
	if (m.len > 2)
		rv |= ((CONSZ)m.val[2] << 32);
	if (m.len > 3)
		rv |= ((CONSZ)m.val[3] << 48);

	e = e - LDBLPTR->nbits + LDBLPTR->expadj;
	while (e > 0)
		rv <<= 1, e--;
	while (e < 0)
		rv >>= 1, e++;
	if (s)
		rv = -rv;

#ifdef DEBUGFP
	{ uint64_t u = (uint64_t)sfp->debugfp;
	  int64_t ss = (int64_t)sfp->debugfp;
		if (ISUNSIGNED(t)) {
			if (u != (U_CONSZ)rv)
				fpwarn("soft_fp2int:u", 0.0, sfp->debugfp);
		} else {
			if (ss != (int64_t)rv)
				fpwarn("soft_fp2int:s", 0.0, sfp->debugfp);
		}
	}
#endif
	return rv;
}


/*
 * Operations.
 */

/*
 * Negate a softfloat.
 */
void
soft_neg(SFP sfp)
{
	MINT m;
	int c, s, e;

	MINTDECL(m);
	c = LDBLPTR->unmake(sfp, &s, &e, &m);
	s = !s;
	LDBLPTR->make(sfp, c, s, e, &m);
}

void
soft_plus(SFP x1p, SFP x2p, TWORD t)
{
	MINT a, m1, m2;
	SF rv;
	int d, c1, c2, s1, s2, e1, e2, ediff, mtop;

	MINTDECL(a);
	MINTDECL(m1);
	MINTDECL(m2);

	c1 = LDBLPTR->unmake(x1p, &s1, &e1, &m1);
	c2 = LDBLPTR->unmake(x2p, &s2, &e2, &m2);
	SD(("soft_plus: c1 %s c2 %s s1 %d s2 %d e1 %d e2 %d\n", 
	    sftyp[c1], sftyp[c2], s1, s2, e1, e2));

	ediff = e1 - e2;
	if (c1 == SOFT_INFINITE && c2 == SOFT_INFINITE) {
		if (s1 != s2)
			c1 = SOFT_NAN, s1 ^= s2;
	} else if (c1 == SOFT_NAN || c1 == SOFT_INFINITE) {
		;
	} else if (c2 == SOFT_NAN || c2 == SOFT_INFINITE) {
		c1 = c2;
		s1 = s2;
	} else {
		if (ediff > LDBLPTR->nbits+1)
			return; /* result x1 */
		if (ediff < -(LDBLPTR->nbits+1)) {
			*x1p = *x2p;
			return; /* result x2 */
		}
		if ((d = topbit(&m1)) < LDBLPTR->nbits-1)
			mshl(&m1, LDBLPTR->nbits-1 - d);
		if ((d = topbit(&m2)) < LDBLPTR->nbits-1)
			mshl(&m2, LDBLPTR->nbits-1 - d);

		if (e1 > e2)
			mshl(&m1, ediff), mtop = LDBLPTR->nbits-1+ediff;
		else
			mshl(&m2, -ediff), mtop = LDBLPTR->nbits-1-ediff;
		m1.sign = s1;
		m2.sign = s2;
		madd(&m1, &m2, &a);
		d = topbit(&a) - mtop;
		e1 += d, e2 += d;
		s1 = a.sign;
	}
	LDBLPTR->make(&rv, c1, s1, ediff > 0 ? e1 : e2, &a);

#ifdef DEBUGFP
	{ long double ldd = sfp2ld(x1p) + sfp2ld(x2p);
	  long double sp = sfp2ld(&rv);
	if (memcmp(&ldd, &sp, SZLD))
	  fpwarn("soft_plus", sfp2ld(&rv), ldd);
	}
#endif
	*x1p = rv;
}

void
soft_minus(SFP x1, SFP x2, TWORD t)
{
	soft_neg(x2);
	return soft_plus(x1, x2, t);
}

#if defined(mach_i386) || defined(mach_amd64)
#define	MULSIGN	1	/* 0 * INF == -NAN on x87 */
#else
#define	MULSIGN 0
#endif
/*
 * Multiply two softfloats.
 */
void
soft_mul(SFP x1p, SFP x2p, TWORD t)
{
	MINT a, m1, m2;
	int ee, c1, c2, s1, s2, e1, e2, d;
	SF rv;

	MINTDECL(a);
	MINTDECL(m1);
	MINTDECL(m2);

	c1 = LDBLPTR->unmake(x1p, &s1, &e1, &m1);
	c2 = LDBLPTR->unmake(x2p, &s2, &e2, &m2);
	SD(("soft_mul: s1 %d s2 %d e1 %d e2 %d\n", s1, s2, e1, e2));

	if (c1 == SOFT_NAN || c2 == SOFT_NAN) {
		c1 = SOFT_NAN;
		s1 = 0;
	} else if (c1 == SOFT_INFINITE && c2 == SOFT_INFINITE) {
		c1 = SOFT_INFINITE;
		s1 = s1 == s2;
	} else if (c1 == SOFT_INFINITE && c2 == SOFT_ZERO) {
		c1 = SOFT_NAN;
		s1 = MULSIGN;
	} else if (c2 == SOFT_INFINITE && c1 == SOFT_ZERO) {
		c1 = SOFT_NAN;
		s1 = MULSIGN;
	} else if (c1 == SOFT_INFINITE || c2 == SOFT_INFINITE) {
		c1 = SOFT_INFINITE;
		s1 = s1 == s2;
	} else {
		if ((d = topbit(&m1)) < LDBLPTR->nbits-1)
			mshl(&m1, LDBLPTR->nbits-1 - d);
		if ((d = topbit(&m2)) < LDBLPTR->nbits-1)
			mshl(&m2, LDBLPTR->nbits-1 - d);
		mult(&m1, &m2, &a);
		ee = topbit(&a) - (2 * (LDBLPTR->nbits-1));
		e1 += (e2 + ee) -1 + LDBLPTR->expadj;
		s1 = s1 != s2;
	}
	LDBLPTR->make(&rv, c1, s1, e1, &a);
#ifdef DEBUGFP
	{ long double ldd = sfp2ld(x1p) * sfp2ld(x2p);
	  long double sp = sfp2ld(&rv);
	if (memcmp(&ldd, &sp, SZLD))
	  fpwarn("soft_mul", sfp2ld(&rv), ldd);
	}
#endif
        *x1p = rv;
}

void
soft_div(SFP x1p, SFP x2p, TWORD t)
{
	MINT m1, m2, q, r, e, f;
	int sh, c1, c2, s1, s2, e1, e2, d;
	SF rv;

	MINTDECL(m1);
	MINTDECL(m2);
	MINTDECL(q);
	MINTDECL(r);
	MINTDECL(e);
	MINTDECL(f);

	c1 = LDBLPTR->unmake(x1p, &s1, &e1, &m1);
	c2 = LDBLPTR->unmake(x2p, &s2, &e2, &m2);

	SD(("soft_div: c1 %s c2 %s s1 %d s2 %d e1 %d e2 %d\n", 
	    sftyp[c1], sftyp[c2], s1, s2, e1, e2));
	if (c1 == SOFT_NAN || c2 == SOFT_NAN) {
		c1 = SOFT_NAN, s1 = 1;
	} else if (c1 == SOFT_INFINITE) {
		if (c2 == SOFT_INFINITE) {
			c1 = SOFT_NAN, s1 = 1;
		} else
			c1 = SOFT_INFINITE, s1 = s1 != s2;
	} else if (c1 == SOFT_ZERO) {
		if (c2 == SOFT_ZERO)
			c1 = SOFT_NAN, s1 = 1;
		else
			c1 = SOFT_ZERO, s1 = s1 != s2;
	} else if (c2 == SOFT_ZERO) {
		c1 = SOFT_INFINITE, s1 = s1 != s2;
	} else if (c2 == SOFT_INFINITE) {
		c1 = SOFT_ZERO, s1 = s1 == s2;
	} else {
		if ((d = topbit(&m1)) < LDBLPTR->nbits-1)
			mshl(&m1, LDBLPTR->nbits-1 - d);
		if ((d = topbit(&m2)) < LDBLPTR->nbits-1)
			mshl(&m2, LDBLPTR->nbits-1 - d);
		/* get quot and remainder of divided mantissa */
		mshl(&m1, LDBLPTR->nbits);
		mdiv(&m1, &m2, &q, &r);
		sh = topbit(&q) - LDBLPTR->nbits;
		if (sh < -1) {
			int s = -1 - sh;
			mshl(&q, s);
			e1 += s;
		}

		/* divide remainder as well, for use in rounding */
		mshl(&r, LDBLPTR->nbits);
		mdiv(&r, &m2, &e, &f);

		/* create double bit number of the two quotients */
		mshl(&q, LDBLPTR->nbits);
		madd(&q, &e, &f);

		grsround(&f, LDBLPTR);
		s1 = s1 != s2;
		e1 = (e1 - e2 + sh) + 1 - LDBLPTR->expadj;
	}
	SD(("soft_div2: c1 %d s1 %d e1 %d\n", c1, s1, e1));
	LDBLPTR->make(&rv, c1, s1, e1, &f);

#ifdef DEBUGFP
	{ long double ldd = sfp2ld(x1p) / sfp2ld(x2p);
	  long double sp = sfp2ld(&rv);
	if (memcmp(&ldd, &sp, SZLD))
		fpwarn("soft_div", sfp2ld(&rv), ldd);
	}
#endif
	*x1p = rv;
}

/*
 * Classifications and comparisons.
 */

/*
 * Return true if fp number is zero. Easy.
 */
int
soft_isz(SFP sfp)
{
	int r = LDBLPTR->classify(sfp) == SOFT_ZERO;
#ifdef DEBUGFP
	if ((sfp->debugfp == 0.0 && r == 0) || (sfp->debugfp != 0.0 && r == 1))
		fpwarn("soft_isz", sfp->debugfp, (long double)r);
#endif
	return r;
}

#define	SFLEFTLESS	1	
#define	SFLEFTEQ	2	
#define	SFLEFTGTR	3

/*
 * compare classes if both not normal.
 * classes here are: SOFT_INFINITE, SOFT_ZERO, SOFT_NORMAL.
 */
static int
soft_clcmp(int c1, int c2, int s1, int s2)
{
	if (c1 == SOFT_INFINITE && c2 == SOFT_INFINITE)
		return s1 == s2 ? SFLEFTEQ : s1 ? SFLEFTLESS : SFLEFTGTR;
	if (c1 == SOFT_ZERO && c2 == SOFT_ZERO)
		return SFLEFTEQ;

	if (c1 == SOFT_INFINITE)
		return s1 ? SFLEFTLESS : SFLEFTGTR;

	if (c1 == SOFT_ZERO)
		return s1 ? SFLEFTGTR : SFLEFTLESS;

	if (c1 == SOFT_NORMAL) {
		if (c2 == SOFT_INFINITE)
			return s2 ? SFLEFTGTR : SFLEFTLESS;
		return s1 ? SFLEFTLESS : SFLEFTGTR;

	}
	return 0;
}

int
soft_cmp(SFP v1p, SFP v2p, int v)
{
	MINT m1, m2;
	int c1, c2, s1, s2, e1, e2;
	int xrv, yrv, i;

	MINTDECL(m1);
	MINTDECL(m2);

	c1 = LDBLPTR->unmake(v1p, &s1, &e1, &m1);
	c2 = LDBLPTR->unmake(v2p, &s2, &e2, &m2);

	SD(("soft_cmp: v1 %s v1s %d v2 %s v2s %d\n",
            sftyp[c1], s1, sftyp[c2], s2));

	if (c1 != SOFT_NORMAL || c2 != SOFT_NORMAL) {
		if (c1 == SOFT_NAN || c2 == SOFT_NAN)
			return 0; /* never anything */
		xrv = soft_clcmp(c1, c2, s1, s2);
	} else {
		/* both are NORMAL */
		if (s1 > s2) {
			xrv = SFLEFTLESS;
		} else if (s1 < s2) {
			xrv = SFLEFTGTR;
		} else if (e1 > e2) {
			xrv = SFLEFTGTR;
		} else if (e1 < e2) {
			xrv = SFLEFTLESS;
		} else {
			for (i = m1.len-1; i >= 0; i--) {
				if (m1.val[i] > m2.val[i]) {
					xrv = s1 ? SFLEFTLESS : SFLEFTGTR;
					break;
				} else if (m1.val[i] < m2.val[i]) {
					xrv = s1 ? SFLEFTGTR : SFLEFTLESS;
					break;
				}
			}
			if (i < 0)
				xrv = SFLEFTEQ;
		}
	}

	yrv = 0;
	SD(("soft_cmp2: xrv %d\n", xrv));
	switch (v) {
	case GT: yrv = xrv == SFLEFTGTR; break;
	case LT: yrv = xrv == SFLEFTLESS; break;
	case GE: yrv = xrv == SFLEFTGTR || xrv == SFLEFTEQ; break;
	case LE: yrv = xrv == SFLEFTLESS || xrv == SFLEFTEQ; break;
	case EQ: yrv = xrv == SFLEFTEQ; break;
	case NE: yrv = xrv != SFLEFTEQ; break;
	}

	return yrv;
}

static void
mshr(MINT *a, int nbits, int sticky)
{
	int i, j, k;

	for (j = 0; j < nbits; j++) {
		k = a->val[0] & 1;
		for (i = 0; i < a->len-1; i++)
			a->val[i] = (a->val[i] >> 1) |	(a->val[i+1] << 15);
		a->val[i] >>= 1;
		if (sticky)
			a->val[0] |= k;
	}
	chomp(a);
}

/*
 * Round q(uot) using "half-to-even".
 * Destroys r(emainder).
 */
static void
mround(MINT *d, MINT *q, MINT *r)
{
	MINT a, b;

	MINTDECL(a);
	MINTDECL(b);

	mshl(r, 1);
	chomp(r);
	chomp(d);
	if (geq(r, d)) {
		if (memcmp(r->val, d->val, d->len * 2) || (q->val[0] & 1)) {
			minit(&a, 1);
			madd(&a, q, &b);
			mcopy(&b, q);
		}
	}
}

/*
 * - [0-9]+[Ee][+-]?[0-9]+				222e-33
 * - [0-9]*.[0-9]+([Ee][+-]?[0-9]+)?			.222e-33
 * - [0-9]+.[0-9]*([Ee][+-]?[0-9]+)?			222.e-33
 * Convert a decimal floating point number to a numerator and a denominator.
 * Return overflow, inexact, or 0.
 */
static int
decbig(char *str, MINT *mmant, MINT *mexp)
{
	MINT ten, b, ind, *cur;
	int exp10 = 0, gotdot = 0;
	int ch, i;

	MINTDECL(ten);
	MINTDECL(b);
	MINTDECL(ind);

	minit(&ten, 10);

	while ((ch = *str++)) {
		switch (ch) {
		case '0' ... '9':
			mult(mmant, &ten, &b);
			minit(&ind, ch - '0');
			madd(&b, &ind, mmant);
			if (gotdot)
				exp10--;
			continue;
	
		case '.':
			gotdot = 1;
			continue;

		case 0:
			break;

		case 'e':
		case 'E':
			exp10 += atoi(str);
			break;

		case 'i':
		case 'I':
		case 'l':
		case 'L':
		case 'f':
		case 'F':
			break;

		default:
			cerror("decbig %d", ch);
			break;
		}
		break;
	}
	if (MINTZ(mmant))
		return SOFT_ZERO;
	if (exp10 < 0) {
		if (exp10 < LDBLPTR->min10exp - LDBLPTR->dig - 5)
			return SOFT_ZERO;
		cur = mexp;
		exp10 = -exp10;
	} else if (exp10 > 0) {
		if (exp10 > LDBLPTR->max10exp)
			return SOFT_INFINITE;
		cur = mmant;
	}
	for (i = 0; i < exp10; i++) {
		mult(cur, &ten, &b);
		mcopy(&b, cur);
	}
	return SOFT_NORMAL;
}

/*
 * - 0[xX][a-fA-F0-9]+.[Pp][+-]?[0-9]+			0x.FFp+33
 * - 0[xX][a-fA-F0-9]*.[a-fA-F0-9]+[Pp][+-]?[0-9]+	0x1.FFp+33
 * - 0[xX][a-fA-F0-9]+[Pp][+-]?[0-9]+			0x1FFp+33
 * Convert a hex floating point number to a numerator and a denominator.
 * Return overflow, inexact, or 0.
 */
static int
hexbig(char *str, MINT *mmant, MINT *mexp)
{
	int exp2 = 0, gotdot = 0;
	int ch, e3 = 0;

	while ((ch = *str++)) {
		switch (ch) {
		case 'a' ... 'f':
			ch -= ('a' - 'A');
			/* FALLTHROUGH */
		case 'A' ... 'F':
			ch -= ('A' - '9' - 1);
			/* FALLTHROUGH */
		case '0' ... '9':
			mshl(mmant, 4);
			mmant->val[0] |= (ch - '0');
			if (gotdot)
				e3 -= 4;
			continue;
	
		case '.':
			gotdot = 1;
			continue;

		case 'p':
		case 'P':
			if (MINTZ(mmant))
				return SOFT_ZERO;
			exp2 = atoi(str) + e3;
			if (exp2 < 0) {
				if (exp2 < LDBLPTR->minexp - LDBLPTR->nbits + e3)
					return SOFT_ZERO;
				mshl(mexp, -exp2);
			} else if (exp2 > 0) {
				if (exp2 > LDBLPTR->maxexp)
					return SOFT_INFINITE;
				mshl(mmant, exp2);
			}
			return SOFT_NORMAL;

		default:
			break;
		}
		break;
	}
	cerror("hexbig %c", str[-1]);
	return SOFT_NORMAL;
}

static int
str2num(char *str, int *exp, MINT *m, struct FPI *fpi)
{
	MINT d, mm, me;
	int t, u, rv;

	MINTDECL(d);
	MINTDECL(mm);
	MINTDECL(me);

	minit(&mm, 0);
	minit(&me, 1);

	if (*str == '0' && (str[1] == 'x' || str[1] == 'X')) {
		rv = hexbig(str+2, &mm, &me);
	} else {
		rv = decbig(str, &mm, &me);
	}
	if (rv != SOFT_NORMAL)
		return rv;
	if (MINTZ(&mm))
		return SOFT_ZERO;

	/* 3. Scale into floating point mantissa len */
	t = topbit(&mm);
	u = topbit(&me);
	if ((t-u) < fpi->nbits) {
		int scale = fpi->nbits - (t-u) - 1;
		int sub = 0;

		/* check if we end up in subnormal range */
		/* must do that before division */
		if (fpi->nbits - scale - 1 <= -(fpi->bias-1)) {
			int recount = fpi->nbits - scale - 1;
			recount = -recount - (fpi->bias - 2);
			sub = 1;
			scale -= recount;
		}

		mshl(&mm, scale);	/* scale up numerator */
		mdiv(&mm, &me, m, &d);

		while (topbit(m) < fpi->nbits-1) {
			mshl(&mm, 1);
			mdiv(&mm, &me, m, &d);
			scale++;
		}
		mround(&me, m, &d);	/* round correctly */
		t = topbit(m);
		if (sub && t == fpi->nbits-1)
			sub = 0;
		if (topbit(m) == fpi->nbits) {
			mshr(m, 1, 0);
			scale--;
			if (sub)
				sub = 0;
		}

		if (sub)
			*exp = -fpi->bias;
		else
			*exp = fpi->nbits - scale - fpi->expadj;
	} else {
		int scale = (t-u) - fpi->nbits + 1;
		mshl(&me, scale);
		mdiv(&mm, &me, m, &d);
		if (topbit(m) < fpi->nbits-1) {
			mshr(&me, 1, 0);
			mdiv(&mm, &me, m, &d);
			scale--;
		}
		mround(&me, m, &d);
		if (topbit(m) == fpi->nbits) {
			mshr(m, 1, 0);
			scale++;
		}

		*exp = fpi->nbits + scale - fpi->expadj;
		if (*exp > fpi->maxexp)
			return SOFT_INFINITE;
	}
	return SOFT_NORMAL;
}

/*
 * Conversions from decimal and hexadecimal strings.
 * Rounds correctly to the target type (subject to FLT_EVAL_METHOD.)
 * dt is resulting type.
 */
void
strtosf(SFP sfp, char *str, TWORD tw)
{
	MINT m;
	int e;
	int rv;

	MINTDECL(m);

	rv = str2num(str, &e, &m, fpis[/*MKSF(tw)*/ 2]);
	SD(("strtosf: rv %d, expt %d, m %04x%04x, %04x%04x\n",
	    rv, e, m.val[3], m.val[2], m.val[1], m.val[0]));


	LDBLPTR->make(sfp, rv, 0, e, &m);
//	soft_fp2fp(sfp, tw);

#ifdef DEBUGFP
	{
		long double ld = strtold(str, NULL);
//		ld = tw == DOUBLE ? (double)ld : tw == FLOAT ? (float)ld : ld;
		if (ld != sfp2ld(sfp))
			fpwarn("strtosf", sfp2ld(sfp), ld);
	}
#endif
}

/*
 * return INF/NAN.
 */
void
soft_huge_val(SFP sfp)
{
	MINT a;

	LDBLPTR->make(sfp, SOFT_INFINITE, 0, 0, &a);

#ifdef DEBUGFP
	if (sfp->debugfp != __builtin_huge_vall())
		fpwarn("soft_huge_val", sfp->debugfp, __builtin_huge_vall());
#endif
}

void
soft_nan(SFP sfp, char *c)
{
	MINT a;

	LDBLPTR->make(sfp, SOFT_NAN, 0, 0, &a);
}

/*
 * Convert internally stored floating point to fp type in TWORD.
 * Save as a static array of uint32_t.
 */
uint32_t * soft_toush(SFP sfp, TWORD t, int *nbits)
{
	static SF sf;
	MINT mant;
	int exp, sign, typ;

	MINTDECL(mant);

	SD(("soft_toush: sfp %Lf %La t %d\n", sfp->debugfp, sfp->debugfp, t));
	SD(("soft_toushLD: %x %x %x\n", sfp->fp[2], sfp->fp[1], sfp->fp[0]));
#ifdef SFDEBUG
	if (sfdebug) {
	double d = sfp->debugfp;
	printf("soft_toush-D: d %08x %08x\n", *(((int *)&d)+1), *(int *)&d);
	}
#endif

	typ = fpis[SF_LDOUBLE]->unmake(sfp, &sign, &exp, &mant);
	SD(("soft_toush2: typ %s sign %d exp %d mant %04x%04x %04x%04x\n",
	    sftyp[typ], sign, exp, mant.val[3], mant.val[2],
	    mant.val[1], mant.val[0]));
	fpis[MKSF(t)]->make(&sf, typ, sign, exp, &mant);

#ifdef DEBUGFP
	if (0) { float ldf; double ldd; long double ldt;
	ldt = (t == FLOAT ? (float)sfp2ld(sfp) :
	    t == DOUBLE ? (double)sfp2ld(sfp) : (long double)sfp2ld(sfp));
	ldf = ldt;
	ldd = ldt;
	if (t == FLOAT && memcmp(&ldf, &sf.debugfp, sizeof(float)))
		fpwarn("soft_toush2", (long double)*(float*)&sf.debugfp, ldt);
	if (t == DOUBLE && memcmp(&ldd, &sf.debugfp, sizeof(double)))
		fpwarn("soft_toush3", (long double)*(double*)&sf.debugfp, ldt);
	if (t == LDOUBLE && memcmp(&ldt, &sf.debugfp, SZLD))
		fpwarn("soft_toush4", (long double)sf.debugfp, ldt);
	}
#endif
	*nbits = fpis[MKSF(t)]->storage;
	return sf.fp;
}

#ifdef DEBUGFP
void
fpwarn(const char *s, long double soft, long double hard)
{
	extern int nerrors, lineno;

	union { long double ld; int i[3]; } X;
	fprintf(stderr, "WARNING: In function %s: soft=%La hard=%La\n",
	    s, soft, hard);
	fprintf(stderr, "WARNING: soft=%Lf hard=%Lf\n", soft, hard);
	X.ld=soft;
	fprintf(stderr, "WARNING: s[0]=%x s[1]=%x s[2]=%x ",
	    X.i[0], X.i[1], X.i[2]);
	X.ld=hard;
	fprintf(stderr, "h[0]=%x h[1]=%x h[2]=%x\n", X.i[0], X.i[1], X.i[2]);
	fprintf(stderr, "WARNING: lineno %d\n", lineno);
	nerrors++;
}
#endif

/*
 * Veeeeery simple arbitrary precision code.
 * Interface similar to old libmp package.
 */
void
minit(MINT *m, int v)
{
	m->sign = 0;
	m->len = 1;
	m->val[0] = v;
}

static void
chomp(MINT *a)
{
	while (a->len > 0 && a->val[a->len-1] == 0)
		a->len--;
}

static void
neg2com(MINT *a)
{
	uint32_t sum;
	int i;

	sum = 1;
	for (i = 0; i < a->len; i++) {
		a->val[i] = ~a->val[i];
		sum = a->val[i] + sum;
		a->val[i] = sum;
		sum >>= 16;
	}
}

static void
mexpand(MINT *a, int minsz)
{
	int newsz = minsz == 0 ? a->allo * 2 : minsz;
	void *stmtalloc(int);

	if (minsz == 0)
		newsz = a->allo * 2;
	else if (minsz > a->allo)
		newsz = minsz;
	else
		return;

	a->val = memcpy(stmtalloc(newsz * 2), a->val, a->allo * 2);
	a->allo = newsz;
}

void
mshl(MINT *a, int nbits)
{
	int i, j;

	if (a->len == 0)
		return; /* nothing to do */
	/* XXXXXXX must improve speed significantly */
	for (j = 0; j < nbits; j++) {
		if (a->val[a->len-1] & 0x8000) {
			if (a->len >= a->allo)
				mexpand(a, 0);
			a->val[a->len++] = 0;
		}
		for (i = a->len-1; i > 0; i--)
			a->val[i] = (a->val[i] << 1) | (a->val[i-1] >> 15);
		a->val[i] = (a->val[i] << 1);
	}
}

void
mdump(char *c, MINT *a)
{
	int i;

	printf("%s: ", c);
	printf("len %d sign %d: ", a->len, (unsigned)a->sign);
	for (i = a->len-1; i >= 0; i--)
		printf("%04x ", a->val[i]);
	printf("\n");
}


/*
 * add (and sub) uses 2-complement (for simplicity).
 */
void
madd(MINT *a, MINT *b, MINT *c)
{
	int32_t sum;
	int mx, i;

	chomp(a);
	chomp(b);
	/* ensure both numbers are the same size + 1 (for two-complement) */
	mx = (b->len > a->len ? b->len : a->len) + 1;
	mexpand(a, mx);
	for (i = a->len; i < mx; i++)
		a->val[i] = 0;
	mexpand(b, mx);
	for (i = b->len; i < mx; i++)
		b->val[i] = 0;
	a->len = b->len = mx;

	minit(c, 0);
	mexpand(c, mx);

	if (a->sign)
		neg2com(a);
	if (b->sign)
		neg2com(b);

#ifdef SFDEBUG
	if (sfdebug) {
		printf("madd1: len %d m", a->len);
		for (i = a->len-1; i >= 0; i--)
			printf(" %04x", a->val[i]);
		printf("\nmadd1: len %d m", b->len);
		for (i = b->len-1; i >= 0; i--)
			printf(" %04x", b->val[i]);
		printf("\n");
	}
#endif
	sum = 0;
	for (i = 0; i < a->len; i++) {
		sum = a->val[i] + b->val[i] + sum;
		c->val[i] = sum;
		sum >>= 16;
	}
	c->len = a->len;
#ifdef SFDEBUG
	if (sfdebug) {
		printf("madd2: len %d m", c->len);
		for (i = c->len-1; i >= 0; i--)
			printf(" %04x", c->val[i]);
		printf("\n");
	}
#endif

	if (c->val[c->len-1] & 0x8000) {
		neg2com(c);
		c->sign = 1;
	} else
		c->sign = 0;
#ifdef SFDEBUG
	if (sfdebug) {
		printf("madd3: len %d m", c->len);
		for (i = c->len-1; i >= 0; i--)
			printf(" %04x", c->val[i]);
		printf("\n");
	}
#endif
	chomp(c);
}

void
msub(MINT *a, MINT *b, MINT *c)
{
	b->sign = !b->sign;
	madd(a, b, c);
}

void
mult(MINT *a, MINT *b, MINT *c)
{
	MINT *sw;
	uint32_t sum;
	int i, j;

	chomp(a);
	chomp(b);
	minit(c, 0);
	i = a->len + b->len;
	mexpand(c, i);
	c->len = i;
	for (i = 0; i < c->len; i++)
		c->val[i] = 0;

	if (b->len > a->len)
		sw = a, a = b, b = sw;

	for(i = 0; i < b->len; i++) {
		sum = 0;
		for(j = 0; j < a->len; j++) {
			sum = c->val[j+i] +
			    (uint32_t)a->val[j] * b->val[i] + sum;
			c->val[j+i] = sum;
			sum >>= 16;
		}
		c->val[j+i] = sum;
	}
	c->sign = (a->sign == b->sign) == 0;
}


static int
geq(MINT *l, MINT *r)
{
	int i;

	if (l->len > r->len)
		return 1;
	if (l->len < r->len)
		return 0;
	for (i = l->len-1; i >= 0; i--) {
		if (r->val[i] > l->val[i])
			return 0;
		if (r->val[i] < l->val[i])
			return 1;
	}
	return 1;
}

void
mdiv(MINT *n, MINT *d, MINT *q, MINT *r)
{
	MINT a, b;
	int i;

	MINTDECL(a);
	MINTDECL(b);

	minit(q, 0);
	minit(r, 0);
	chomp(n);
	chomp(d);
	mexpand(q, n->len);
	mexpand(r, n->len);
	for (i = 0; i < n->len; i++)
		q->val[i] = 0;
	q->len = n->len;

	for (i = n->len * 16 - 1; i >= 0; i--) {
		mshl(r, 1);
		if (r->len == 0)
			r->val[r->len++] = 0;
		r->val[0] |= (n->val[i/16] >> (i % 16)) & 1;
		if (geq(r, d)) {
			mcopy(d, &b);
			msub(r, &b, &a);
			mcopy(&a, r);
			q->val[i/16] |= (1 << (i % 16));
		}
	}
	chomp(q);
}

