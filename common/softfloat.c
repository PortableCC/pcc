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

#ifndef PCC_DEBUG
#define assert(e) ((void)0)
#else
#define assert(e) (!(e)?cerror("assertion failed " #e " at softfloat:%d",__LINE__):(void)0)
#endif
/*
 * Floating point emulation, to not depend on the characteristics (and bugs)
 * of the host floating-point implementation when compiling.
 *
 * Assumes that:
 *	- long long is (at least) 64 bits
 *	- long is at least 32 bits.
 *	- short is at least 16 bits.
 */
#define NEW_STRTOLD

#ifdef FDFLOAT

/*
 * Supports F- and D-float, used in DEC machines.
 *
 * XXX - assumes that:
 *	- long long is (at least) 64 bits
 *	- int is at least 32 bits.
 *	- short is 16 bits.
 */

/*
 * Useful macros to manipulate the float.
 */
#define DSIGN(w)	(((w).fd1 >> 15) & 1)
#define DSIGNSET(w,s)	((w).fd1 = (s << 15) | ((w).fd1 & 077777))
#define DEXP(w)		(((w).fd1 >> 7) & 0377)
#define DEXPSET(w,e)	((w).fd1 = (((e) & 0377) << 7) | ((w).fd1 & 0100177))
#define DMANTH(w)	((w).fd1 & 0177)
#define DMANTHSET(w,m)	((w).fd1 = ((m) & 0177) | ((w).fd1 & 0177600))

typedef unsigned int lword;
typedef unsigned long long dword;

#define MAXMANT 0x100000000000000LL

/*
 * Returns a zero dfloat.
 */
static SF
nulldf(void)
{
	SF rv;

	rv.fd1 = rv.fd2 = rv.fd3 = rv.fd4 = 0;
	return rv;
}

/*
 * Convert a (u)longlong to dfloat.
 * XXX - fails on too large (> 55 bits) numbers.
 */
SF
soft_cast(CONSZ ll, TWORD t)
{
	int i;
	SF rv;

	rv = nulldf();
	if (ll == 0)
		return rv;  /* fp is zero */
	if (ll < 0)
		DSIGNSET(rv,1), ll = -ll;
	for (i = 0; ll > 0; i++, ll <<= 1)
		;
	DEXPSET(rv, 192-i);
	DMANTHSET(rv, ll >> 56);
	rv.fd2 = ll >> 40;
	rv.fd3 = ll >> 24;
	rv.fd4 = ll >> 8;
	return rv;
}

/*
 * multiply two dfloat. Use chop, not round.
 */
SF
soft_mul(SF p1, SF p2)
{
	SF rv;
	lword a1[2], a2[2], res[4];
	dword sum;

	res[0] = res[1] = res[2] = res[3] = 0;

	/* move mantissa into lwords */
	a1[0] = p1.fd4 | (p1.fd3 << 16);
	a1[1] = p1.fd2 | DMANTH(p1) << 16 | 0x800000;

	a2[0] = p2.fd4 | (p2.fd3 << 16);
	a2[1] = p2.fd2 | DMANTH(p2) << 16 | 0x800000;

#define MULONE(x,y,r) sum += (dword)a1[x] * (dword)a2[y]; sum += res[r]; \
	res[r] = sum; sum >>= 32;

	sum = 0;
	MULONE(0, 0, 0);
	MULONE(1, 0, 1);
	res[2] = sum;
	sum = 0;
	MULONE(0, 1, 1);
	MULONE(1, 1, 2);
	res[3] = sum;

	rv.fd1 = 0;
	DSIGNSET(rv, DSIGN(p1) ^ DSIGN(p2));
	DEXPSET(rv, DEXP(p1) + DEXP(p2) - 128);
	if (res[3] & 0x8000) {
		res[3] = (res[3] << 8) | (res[2] >> 24);
		res[2] = (res[2] << 8) | (res[1] >> 24);
	} else {
		DEXPSET(rv, DEXP(rv) - 1);
		res[3] = (res[3] << 9) | (res[2] >> 23);
		res[2] = (res[2] << 9) | (res[1] >> 23);
	}
	DMANTHSET(rv, res[3] >> 16);
	rv.fd2 = res[3];
	rv.fd3 = res[2] >> 16;
	rv.fd4 = res[2];
	return rv;
}

SF
soft_div(SF t, SF n)
{
	SF rv;
	dword T, N, K;
	int c;

#define SHL(x,b) ((dword)(x) << b)
	T = SHL(1,55) | SHL(DMANTH(t), 48) |
	    SHL(t.fd2, 32) | SHL(t.fd3, 16) | t.fd4;
	N = SHL(1,55) | SHL(DMANTH(n), 48) |
	    SHL(n.fd2, 32) | SHL(n.fd3, 16) | n.fd4;

	c = T > N;
	for (K = 0; (K & 0x80000000000000ULL) == 0; ) {
		if (T >= N) {
			T -= N;
			K |= 1;
		}
		T <<= 1;
		K <<= 1;
	}
	rv.fd1 = 0;
	DSIGNSET(rv, DSIGN(t) ^ DSIGN(n));
	DEXPSET(rv, DEXP(t) - DEXP(n) + 128 + c);
	DMANTHSET(rv, K >> 48);
	rv.fd2 = K >> 32;
	rv.fd3 = K >> 16;
	rv.fd4 = K;
	return rv;
}

/*
 * Negate a float number. Easy.
 */
SF
soft_neg(SF sf)
{
	int sign = DSIGN(sf) == 0;
	DSIGNSET(sf, sign);
	return sf;
}

/*
 * Return true if fp number is zero.
 */
int
soft_isz(SF sf)
{
	return (DEXP(sf) == 0);
}

int
soft_cmp_eq(SF x1, SF x2)
{
	cerror("soft_cmp_eq");
	return 0;
}

int
soft_cmp_ne(SF x1, SF x2)
{
	cerror("soft_cmp_ne");
	return 0;
}

int
soft_cmp_le(SF x1, SF x2)
{
	cerror("soft_cmp_le");
	return 0;
}

int
soft_cmp_lt(SF x1, SF x2)
{
	cerror("soft_cmp_lt");
	return 0;
}

int
soft_cmp_ge(SF x1, SF x2)
{
	cerror("soft_cmp_ge");
	return 0;
}

int
soft_cmp_gt(SF x1, SF x2)
{
	cerror("soft_cmp_gt");
	return 0;
}

/*
 * Convert a fp number to a CONSZ.
 */
CONSZ
soft_val(SF sf)
{
	CONSZ mant;
	int exp = DEXP(sf) - 128;

	mant = SHL(1,55) | SHL(DMANTH(sf), 48) |
            SHL(sf.fd2, 32) | SHL(sf.fd3, 16) | sf.fd4;

	while (exp < 0)
		mant >>= 1, exp++;
	while (exp > 0)
		mant <<= 1, exp--;
	return mant;
}

SF
soft_plus(SF x1, SF x2)
{
	cerror("soft_plus");
	return x1;
}

SF
soft_minus(SF x1, SF x2)
{
	cerror("soft_minus");
	return x1;
}

/*
 * Convert a hex constant to floating point number.
 */
NODE *
fhexcon(char *s)
{
	cerror("fhexcon");
	return NULL;
}

/*
 * Convert a floating-point constant to D-float and store it in a NODE.
 */
NODE *
floatcon(char *s)
{
	NODE *p;
	dword mant;
	SF fl, flexp, exp5;
	int exp, negexp, bexp;

	exp = 0;
	mant = 0;
#define ADDTO(sum, val) sum = sum * 10 + val - '0'
	for (; *s >= '0' && *s <= '9'; s++) {
		if (mant<MAXMANT)
			ADDTO(mant, *s);
		else
			exp++;
	}
	if (*s == '.') {
		for (s++; *s >= '0' && *s <= '9'; s++) {
			if (mant<MAXMANT) {
				ADDTO(mant, *s);
				exp--;
			}
		}
	}

	if ((*s == 'E') || (*s == 'e')) {
		int eexp = 0, sign = 0;
		s++;
		if (*s == '+')
			s++;
		else if (*s=='-')
			sign = 1, s++;

		for (; *s >= '0' && *s <= '9'; s++)
			ADDTO(eexp, *s);
		if (sign)
			eexp = -eexp;
		exp = exp + eexp;
	}

	negexp = 1;
	if (exp<0) {
		negexp = -1;
		exp = -exp;
	}


	flexp = soft_cast(1, INT);
	exp5 = soft_cast(5, INT);
	bexp = exp;
	fl = soft_cast(mant, INT);

	for (; exp; exp >>= 1) {
		if (exp&01)
			flexp = soft_mul(flexp, exp5);
		exp5 = soft_mul(exp5, exp5);
	}
	if (negexp<0)
		fl = soft_div(fl, flexp);
	else
		fl = soft_mul(fl, flexp);

	DEXPSET(fl, DEXP(fl) + negexp*bexp);
	p = block(FCON, NIL, NIL, DOUBLE, 0, 0); /* XXX type */
	p->n_dcon = fl;
	return p;
}
#else

/*
 * Use parametric floating-point representation, as used in the package gdtoa
 * published by David M. Gay and generally available as gdtoa.tgz at
 * http://www.netlib.org/fp/ ; see also strtodg.c introduction.
 *
 * Arithmetic characteristics are described in struct FPI (explained below);
 * the actual numbers are represented (stored) in struct SF.
 * Floating-point numbers have fpi->nbits bits.
 * These numbers are regarded as integers multiplied by 2^e
 * (i.e., 2 to the power of the exponent e), where e is stored in
 * *exp by strtodg.  The minimum and maximum exponent values fpi->emin
 * and fpi->emax for normalized floating-point numbers reflect this
 * arrangement.  For example, the IEEE 754 standard for binary arithmetic
 * specifies doubles (also known as binary64) as having 53 bits, with
 * normalized values of the form 1.xxxxx... times 2^(b-1023), with 52 bits
 * (the x's) and the biased exponent b represented explicitly;
 * b is an unsigned integer in the range 1 <= b <= 2046 for normalized
 * finite doubles, b = 0 for denormals, and b = 2047 for Infinities and NaNs.
 * To turn an IEEE double into the representation used here, we multiply
 * 1.xxxx... by 2^52 (to make it an integer) and reduce the exponent
 * e = (b-1023) by 52:
 *	fpi->emin = 1 - 1023 - 52
 *	fpi->emax = 1046 - 1023 - 52
 * For fpi_binary64 initialization, we actually write -53+1 rather than -52,
 * to emphasize that there are 53 bits including one implicit bit at the
 * left of the binary point.
 * Field fpi->rounding indicates the desired rounding direction, with
 * possible values
 *	FPI_Round_zero = toward 0,
 *	FPI_Round_near = unbiased rounding -- the IEEE default,
 *	FPI_Round_up = toward +Infinity, and
 *	FPI_Round_down = toward -Infinity
 *	FPI_Round_near_from0 = to nearest, ties always away from 0
 * given in pass1.h.
 *
 * Field fpi->sudden_underflow indicates whether computations should return
 * denormals or flush them to zero.  Normal floating-point numbers have
 * bit fpi->nbits in the significand on.  Denormals have it off, with
 * exponent = fpi->emin.
 *
 * Fields fpi->explicit_one, fpi->storage, and fpi->exp_bias are only
 * relevant when the numbers are finally packed into interchange format.
 * If bit 1 is the lowest in the significand, bit fpi->storage has the sign.
 *
 * Some architectures do not use IEEE arithmetic but can nevertheless use
 * the same parametrization. They should provide their own FPI objects.
 * Fields fpi->has_inf_nan and fpi->has_neg_zero cover the non-IEEE cases
 * of lacking respectively the use of infinities and NaN, and negative zero.
 * Field fpi->has_radix_16 is for architectures (IBM, DG Nova) with base 16.
 *
 * In this implementation, the bits are stored in one large integer
 * (unsigned long long); this limits the number of bits to 64.
 * Because of the storage representation (but not the implementation),
 * exponents are restricted to 15 bits.
 *
 * Furthermore, this implementation assumes that:
 *	- integers are (obviously) stored as 2's complement
 *	- long long is (at least) 64 bits
 *	- CONSZ is (at least) 64 bits
 * There are possible issues if int is 16 bits, with divisions.
 *
 * As a result, this is also a slightly restricted software implementation of
 * IEEE 754:1985 standard. Missing parts, useless in a compiler, are:
 * - no soft_unpack(), to convert from external binary{32,64} formats
 * - no precision control (not required, dropped in :2008)
 * - no soft_sqrt() operation
 * - no soft_remainder() operation
 * - no soft_rint(), _ceil, or _floor rounding operations
 * - no binary-to-decimal conversion (can use D. Gay's dgtoa.c)
 * - signaling NaNs (SF_NoNumber; should cause SFEXCP_Invalid on every op)
 * - XXX fenv-support is pending
 * - no soft_scalb(), _logb, or _nextafter optional functions
 * It should be easy to expand it into a complete implementation.
 *
 * The operations are rounded according to the indicated type.
 * If because of FLT_EVAL_METHOD, the precision has to be greater,
 * this should be handled by the calling code.
 */

/*
 * API restrictions:
 *	- type information should be between FLOAT and LDOUBLE
 */

#ifndef Long
#define Long int
#endif
#ifndef ULong
typedef unsigned Long ULong;
#endif
#ifndef ULLong
typedef unsigned long long ULLong;
#endif

static uint64_t sfrshift(uint64_t mant, int bits);

extern int strtodg (const char*, char**, FPI*, Long*, ULong*);

/* IEEE binary formats, and their interchange format encodings */
#ifdef notdef
FPI fpi_binary16 = { 11, 1-15-11+1,
                        30-15-11+1, 1, 0,
        0, 1, 1, 0,  16,   15+11-1 };
#endif
#ifndef notyet
FPI fpi_binary128 = { 113,   1-16383-113+1,
                         32766-16383-113+1, 1, 0,
        0, 1, 1, 0,   128,     16383+113-1 };
#endif

#ifdef USE_IEEEFP_32
#define IEEEFP_32_FPI	fpi_binary32
FPI fpi_binary32 = { 24,  1-127-24+1,
                        254-127-24+1, 1, 0,
        0, 1, 1, 0,  32,    127+24-1, .bias = 127, .maxexp = 128 };
#define IEEEFP_32_ZERO(x,s)	((x)->fp[0] = (s << 31))
#define IEEEFP_32_NAN(x,sign)	((x)->fp[0] = 0x7fc00000 | (sign << 31))
#define IEEEFP_32_INF(x,sign)	((x)->fp[0] = 0x7f800000 | (sign << 31))
#define	IEEEFP_32_ISINF(x)	(((x)->fp[0] & 0x7fffffff) == 0x7f800000)
#define	IEEEFP_32_ISZERO(x)	(((x)->fp[0] & 0x7fffffff) == 0)
#define	IEEEFP_32_ISNAN(x)	(((x)->fp[0] & 0x7fffffff) == 0x7fc00000)
#define IEEEFP_32_BIAS	127
#define	IEEEFP_32_TOOLARGE(exp, mant)	ieeefp_32_toolarge(exp, mant)
#define	IEEEFP_32_TOOSMALL(exp, mant)	ieeefp_32_toosmall(exp, mant)
#define IEEEFP_32_MAKE(x, sign, exp, mant)	\
	((x)->fp[0] = (sign << 31) | (((exp & 0xff) << 23) + sfrshift(mant, 41)))
static int
ieeefp_32_toolarge(int exp, uint64_t mant)
{
	if (exp >= IEEEFP_32_MAX_EXP + IEEEFP_32_BIAS)
		return 1;
	if ((exp == IEEEFP_32_MAX_EXP + IEEEFP_32_BIAS - 1) &&
	    (sfrshift(mant, 41) > 0x7fffff))
		return 1;
	return 0;
}
static int
ieeefp_32_toosmall(int exp, uint64_t mant)
{
	if ( exp >= 0 )
		return 0;
	mant = sfrshift(mant, -exp);
	mant |= (mant & 0xffffffffff ? 0x10000000000 : 0);
	if (mant & 0xfffffe0000000000)
		return 1;
	return 0;
}
#else
#error need float definition
#endif

#ifdef USE_IEEEFP_64
#define IEEEFP_64_FPI	fpi_binary64
FPI fpi_binary64 = { 53,   1-1023-53+1,
                        2046-1023-53+1, 1, 0,
        0, 1, 1, 0,  64,     1023+53-1, .bias = 1023, .maxexp = 1024 };
//static SF ieee64_zero = { { { 0, 0, 0 } } };
#define IEEEFP_64_ZERO(x,s)	((x)->fp[0] = 0, (x)->fp[1] = (s << 31))
#define IEEEFP_64_NAN(x,sign)	\
	((x)->fp[0] = 0, (x)->fp[1] = 0x7ff80000 | (sign << 31))
#define IEEEFP_64_INF(x,sign)	\
	((x)->fp[0] = 0, (x)->fp[1] = 0x7ff00000 | (sign << 31))
#define	IEEEFP_64_NEG(x)	(x)->fp[1] ^= 0x80000000
#define	IEEEFP_64_ISINF(x) ((((x)->fp[1] & 0x7fffffff) == 0x7ff00000) && \
	    (x)->fp[0] == 0)
#define	IEEEFP_64_ISINFNAN(x) (((x)->fp[1] & 0x7ff00000) == 0x7ff00000)
#define	IEEEFP_64_ISZERO(x) ((((x)->fp[1] & 0x7fffffff) == 0) && (x)->fp[0] == 0)
#define	IEEEFP_64_ISNAN(x) ((((x)->fp[1] & 0x7fffffff) == 0x7ff80000) && \
	    (x)->fp[0] == 0)
#define IEEEFP_64_BIAS	1023
#define	IEEEFP_64_TOOLARGE(exp, mant)	ieeefp_64_toolarge(exp, mant)
#define	IEEEFP_64_MAXMINT	2048+64+16 /* exponent + subnormal + guard */
#define IEEEFP_64_MAKE(x, sign, exp, mant)		\
	{ uint64_t xmant = sfrshift(mant, 12);		\
	((x)->fp[0] = xmant, (x)->fp[1] = ((sign << 31) | 	\
	    ((exp & 0x7ff) << 20)) + (xmant >> 32)); }
static int
ieeefp_64_toolarge(int exp, uint64_t mant)
{
	if (exp >= IEEEFP_64_MAX_EXP + IEEEFP_64_BIAS)
		return 1;
	if ((exp == IEEEFP_64_MAX_EXP + IEEEFP_64_BIAS - 1) &&
	    (sfrshift(mant, 12) > 0xfffffffffffff))
		return 1;
	return 0;
}
#else
#error need double definition
#endif

#ifdef USE_IEEEFP_X80
#define IEEEFP_X80_FPI	fpi_binaryx80
/* IEEE double extended in its usual form, for example Intel 387 */
FPI fpi_binaryx80 = { 64,   1-16383-64+1,
                        32766-16383-64+1, 1, 0,
        1, 1, 1, 0,   80,     16383+64-1, .bias = 16383, .maxexp = 16384 };
#define IEEEFP_X80_NAN(x,s)	\
	((x)->fp[0] = 0, (x)->fp[1] = 0xc0000000, (x)->fp[2] = 0x7fff | ((s) << 15))
#define IEEEFP_X80_INF(x,s)	\
	((x)->fp[0] = 0, (x)->fp[1] = 0x80000000, (x)->fp[2] = 0x7fff | ((s) << 15))
#define IEEEFP_X80_ZERO(x,s)	\
	((x)->fp[0] = (x)->fp[1] = 0, (x)->fp[2] = (s << 15))
#define	IEEEFP_X80_NEG(x)	(x)->fp[2] ^= 0x8000
#define	IEEEFP_X80_ISINF(x) ((((x)->fp[2] & 0x7fff) == 0x7fff) && \
	((x)->fp[1] == 0x80000000) && (x)->fp[0] == 0)
#define	IEEEFP_X80_ISINFNAN(x) (((x)->fp[2] & 0x7fff) == 0x7fff)
#define	IEEEFP_X80_ISZERO(x) ((((x)->fp[2] & 0x7fff) == 0) && \
	((x)->fp[1] | (x)->fp[0]) == 0)
#define	IEEEFP_X80_ISNAN(x) ((((x)->fp[2] & 0x7fff) == 0x7fff) && \
	(((x)->fp[1] != 0x80000000) || (x)->fp[0] == 0))
#define IEEEFP_X80_BIAS	16383
#define	IEEEFP_X80_MAXMINT	32768+64+16 /* exponent + subnormal + guard */
#define IEEEFP_X80_MAKE(x, sign, exp, mant)	\
	((x)->fp[0] = mant >> 1, (x)->fp[1] = (mant >> 33) | \
	    (exp ? (1 << 31) : 0), \
	    (x)->fp[2] = (exp & 0x7fff) | (sign << 15))
#define IEEEFP_X80_MAKE2(x, sign, exp, mant)	\
	((x)->fp[0] = mant[0], (x)->fp[1] = mant[1], \
	    (x)->fp[2] = (exp & 0x7fff) | (sign << 15))
#endif

#ifdef USE_IEEEFP_X80
#define	SZLD 10 /* less than SZLDOUBLE, avoid cmp junk */
#else
#define SZLD sizeof(long double)
#endif

#define	SOFT_INFINITE	1
#define	SOFT_NAN	2
#define	SOFT_ZERO	3
#define	SOFT_NORMAL	4
#define	SOFT_SUBNORMAL	5
int soft_classify(SFP sf, TWORD type);

#define FPI_FLOAT	C(FLT_PREFIX,_FPI)
#define FPI_DOUBLE	C(DBL_PREFIX,_FPI)
#define FPI_LDOUBLE	C(LDBL_PREFIX,_FPI)

#define	LDOUBLE_NAN	C(LDBL_PREFIX,_NAN)
#define	LDOUBLE_INF	C(LDBL_PREFIX,_INF)
#define	LDOUBLE_ZERO	C(LDBL_PREFIX,_ZERO)
#define	LDOUBLE_NEG	C(LDBL_PREFIX,_NEG)
#define	LDOUBLE_ISINF	C(LDBL_PREFIX,_ISINF)
#define	LDOUBLE_ISNAN	C(LDBL_PREFIX,_ISNAN)
#define	LDOUBLE_ISINFNAN	C(LDBL_PREFIX,_ISINFNAN)
#define	LDOUBLE_ISZERO	C(LDBL_PREFIX,_ISZERO)
#define	LDOUBLE_BIAS	C(LDBL_PREFIX,_BIAS)
#define	LDOUBLE_MAKE	C(LDBL_PREFIX,_MAKE)
#define	LDOUBLE_MAKE2	C(LDBL_PREFIX,_MAKE2)
#define	LDOUBLE_MAXMINT	C(LDBL_PREFIX,_MAXMINT)
#define	LDOUBLE_SIGN	C(LDBL_PREFIX,_SIGN)

#define	DOUBLE_NAN	C(DBL_PREFIX,_NAN)
#define	DOUBLE_INF	C(DBL_PREFIX,_INF)
#define	DOUBLE_ZERO	C(DBL_PREFIX,_ZERO)
#define	DOUBLE_NEG	C(DBL_PREFIX,_NEG)
#define	DOUBLE_ISINF	C(DBL_PREFIX,_ISINF)
#define	DOUBLE_ISNAN	C(DBL_PREFIX,_ISNAN)
#define	DOUBLE_ISZERO	C(DBL_PREFIX,_ISZERO)
#define	DOUBLE_BIAS	C(DBL_PREFIX,_BIAS)
#define	DOUBLE_TOOLARGE	C(DBL_PREFIX,_TOOLARGE)
#define	DOUBLE_TOOSMALL	C(DBL_PREFIX,_TOOSMALL)
#define	DOUBLE_MAKE	C(DBL_PREFIX,_MAKE)
#define	DOUBLE_MAXMINT	C(DBL_PREFIX,_MAXMINT)

#define	FLOAT_NAN	C(FLT_PREFIX,_NAN)
#define	FLOAT_INF	C(FLT_PREFIX,_INF)
#define	FLOAT_ZERO	C(FLT_PREFIX,_ZERO)
#define	FLOAT_NEG	C(FLT_PREFIX,_NEG)
#define	FLOAT_ISINF	C(FLT_PREFIX,_ISINF)
#define	FLOAT_ISNAN	C(FLT_PREFIX,_ISNAN)
#define	FLOAT_ISZERO	C(FLT_PREFIX,_ISZERO)
#define	FLOAT_BIAS	C(FLT_PREFIX,_BIAS)
#define	FLOAT_TOOLARGE	C(FLT_PREFIX,_TOOLARGE)
#define	FLOAT_TOOSMALL	C(FLT_PREFIX,_TOOSMALL)
#define	FLOAT_MAKE	C(FLT_PREFIX,_MAKE)


FPI * fpis[3] = {
	&FPI_FLOAT,
	&FPI_DOUBLE,
	&FPI_LDOUBLE
};

#define	MAXMINT	(LDOUBLE_MAXMINT/16) /* nbits per uint16 */
/* MP package */
typedef struct mint {
	unsigned int len:15, sign:1; /* sign 1 if minus */
	uint16_t val[MAXMINT];
} MINT;

#define MINTZ(x) ((x)->len == 0 || ((x)->len == 1 && (x)->val[0] == 0))

void madd(MINT *a, MINT *b, MINT *c);
void msub(MINT *a, MINT *b, MINT *c);
void mult(MINT *a, MINT *b, MINT *c);
void mdiv(MINT *a, MINT *b, MINT *c, MINT *r);
void minit(MINT *m, int v);
void mshl(MINT *m, int nbits);
static void chomp(MINT *a);
void mdump(char *c, MINT *a);
static int geq(MINT *l, MINT *r);


/*
 * IEEE specials:
 * Zero:	Exponent 0, mantissa 0
 * Denormal:	Exponent 0, mantissa != 0
 * Infinity:	Exponent all 1, mantissa 0
 * QNAN:	Exponent all 1, mantissa MSB 1 (indeterminate)
 * SNAN:	Exponent all 1, mantissa MSB 0 (invalid)
 */

#define	LX(x,n)	((uint64_t)(x)->fp[n] << n*32)

#ifdef USE_IEEEFP_X80
/*
 * Get long double mantissa without hidden bit.
 * Hidden bit is expected to be at position 65.
 */
static uint64_t
ldouble_mant(SFP sfp)
{
	uint64_t rv;

	rv = (LX(sfp,0) | LX(sfp,1)) << 1; /* XXX */
	return rv;
}

#define	ldouble_exp(x)	((x)->fp[2] & 0x7FFF)
#define	ldouble_sign(x)	(((x)->fp[2] >> 15) & 1)
#elif defined(USE_IEEEFP_64)
#define	ldouble_mant double_mant
#define	ldouble_exp double_exp
#define	ldouble_sign double_sign
#endif

#define	double_mant(x)	(((uint64_t)(x)->fp[1] << 44) | ((uint64_t)(x)->fp[0] << 12))
#define	double_exp(x)	(((x)->fp[1] >> 20) & 0x7fff)
#define	double_sign(x)	(((x)->fp[1] >> 31) & 1)

#define	float_mant(x)	((uint64_t)((x)->fp[0] & 0x7fffff) << 41)
#define	float_exp(x)	(((x)->fp[0] >> 23) & 0xff)
#define	float_sign(x)	(((x)->fp[0] >> 31) & 1)

static void
mant2mint(MINT *a, SFP sfp)
{
	uint64_t rv = (LX(sfp,0) | LX(sfp,1));

	minit(a, 0);
	a->val[0] = rv;
	a->val[1] = rv >> 16;
	a->val[2] = rv >> 32;
	a->val[3] = rv >> 48;
	a->len = 4;
}

/*
 * convert a long double to MINT.
 * Known here to only be valid numbers.
 */
static void
ldbl2mint(MINT *a, SFP sfp)
{
	int exp = ldouble_exp(sfp);

	mant2mint(a, sfp);
	mshl(a, exp + 16); /* 16 == guard bits, 64 bit mant is in len */
	a->sign = ldouble_sign(sfp);
}

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

static int
getbit(MINT *a, int h)
{
	if (h < 0 || h/16 >= a->len)
		return 0;
	return (a->val[h/16] & (1 << (h%16))) != 0;
}

static void
mcopy(MINT *b, MINT *a)
{
	int i;

	a->len = b->len;
	a->sign = b->sign;
	for (i = 0; i < a->len; i++)
		a->val[i] = b->val[i];
}

/*
 * Round the MINT number.
 */
static void
grsround(MINT *a)
{
	int h = topbit(a);
	int doadd, i;

	h -= 63; /* points to lsb */
	/* if guard AND either lsb, round or sticky set, add to lsb */
//printf("grs: h %d a %x\n", h, a->val[1]);
	doadd = 0;
	if (getbit(a, h-1)) { /* guard bit set */
//printf("grs: getbit!\n");
		if (getbit(a, h) || getbit(a, h-2) || getbit(a, h-3)) {
			doadd = 1;
		} else {
			/* find out whether sticky should be set */
			for (i = (h/16)-1; i >= 0; i--) {
				if (a->val[i]) {
					doadd = 1;
					break;
				}
			}
			if (doadd == 0) {
				for (i = 0; i < (h%16)-2; i++) {
					if (getbit(a, i)) {
						doadd = 1;
						break;
					}
				}
			}
		}
	}
	if (doadd && h >= 0) {
		MINT d, e;
		minit(&d, 0);
		mcopy(a, &e);
		d.len = (h/16)+1;
		d.val[(h/16)] = 1 << (h % 16);
		madd(&d, &e, a);
	}
//printf("grs2: h %d a %x\n", h, a->val[1]);
}

/*
 * fillin SF with the mantissa.  Expect to already be rounded.
 * return number of times a is left-shifted.
 */
static int
mint2mant(MINT *a, uint64_t *r)
{
	int e = 0;
	uint64_t mant;
	int len = a->len-1;

	while ((a->val[len] & 0x8000) == 0)
		mshl(a, 1), e++;
	mant = (uint64_t)a->val[len] << 48;
	if (len > 0) mant |= (uint64_t)a->val[len-1] << 32;
	if (len > 1) mant |= (uint64_t)a->val[len-2] << 16;
	if (len > 2) mant |= (uint64_t)a->val[len-3];
	*r = mant;
	return e;
}

static void
mint2ldbl(SFP sfp, MINT *a)
{
	uint64_t mant;
	int exp;

	chomp(a);
	grsround(a);
	exp = -mint2mant(a, &mant);

	exp += (a->len-1) * 16;
	exp -= 64; /* bits in mantissa */
	mant <<= 1;
	LDOUBLE_MAKE(sfp, a->sign, exp, mant);
}

/*
 * Convert a extended float (x80) number to float (32-bit). 
 * Store as float.
 */
static void
floatx80_to_float32(SFP a)
{
	int exp, sign;
	uint64_t mant;

	mant = ldouble_mant(a);
	exp = ldouble_exp(a);
	sign = ldouble_sign(a);
//printf("x80: sign %d exp %x mant %llx\n", sign, exp, mant);
//printf("x80s: 0 %x 1 %x 2 %x\n", a.fp[0], a.fp[1], a.fp[2]);

	if (LDOUBLE_ISINF(a)) {
		FLOAT_INF(a, sign);
//printf("1\n");
	} else if (LDOUBLE_ISNAN(a)) {
		FLOAT_NAN(a, sign);
		a->fp[0] |= mant >> 41;
//printf("2\n");
	} else if (LDOUBLE_ISZERO(a)) {
//printf("3\n");
		FLOAT_ZERO(a, sign);
	} else {
//printf("4\n");
		exp = exp - LDOUBLE_BIAS + FLOAT_BIAS;
//printf("4: ecp %x\n", exp);
		if (FLOAT_TOOLARGE(exp, mant)) {
			FLOAT_INF(a, sign);
		} else if (FLOAT_TOOSMALL(exp, mant)) {
			FLOAT_ZERO(a, sign);
		} else {
			FLOAT_MAKE(a, sign, exp, mant);
		}
	}
}

/*
 * Convert a extended float (x80) number to double (64-bit). 
 * Store as double.
 */
static void
floatx80_to_float64(SFP a)
{
	SF rv;
	int exp, sign;
	uint64_t mant;

	mant = ldouble_mant(a);
	exp = ldouble_exp(a);
	sign = ldouble_sign(a);
//printf("x80: sign %d exp %x mant %llx\n", sign, exp, mant);
//printf("x80s: 0 %x 1 %x 2 %x\n", a.fp[0], a.fp[1], a.fp[2]);

	if (LDOUBLE_ISINF(a)) {
		DOUBLE_INF(&rv, sign);
//printf("1\n");
	} else if (LDOUBLE_ISNAN(a)) {
		DOUBLE_NAN(&rv, sign);
		rv.fp[1] |= (mant >> 44);
		rv.fp[0] = mant >> 12;
//printf("2\n");
	} else if (LDOUBLE_ISZERO(a)) {
//printf("3\n");
		DOUBLE_ZERO(&rv, sign);
	} else {
//printf("4\n");
		exp = exp - LDOUBLE_BIAS + DOUBLE_BIAS;
//printf("4: exp %d mant %llx sign %d\n", exp, mant, sign);
		if (DOUBLE_TOOLARGE(exp, mant)) {
			DOUBLE_INF(&rv, sign);
		} else {
			if (exp < 0) {
//printf("done1: sign %d exp %d mant %llx\n", sign, exp, mant);
				mant = (mant >> 1) | (1ULL << 63) | (mant & 1);
//printf("done2: sign %d exp %d mant %llx\n", sign, exp, mant);
				if (exp < 0)
					mant = sfrshift(mant, -exp);
//printf("done3: sign %d exp %d mant %llx\n", sign, exp, mant);
				exp = 0;
			}
//printf("done: sign %d exp %d mant %llx\n", sign, exp, mant);
			DOUBLE_MAKE(&rv, sign, exp, mant);
		}
//printf("X: %x %x %x\n", rv.fp[0], rv.fp[1], rv.fp[2]);
	}
#ifdef DEBUGFP
	{ 	double d = a->debugfp;
//printf("d: %llx\n", *(long long *)&d);
		if (memcmp(&rv, &d, sizeof(double)))
			fpwarn("floatx80_to_float64",
			    (long double)*(double*)&rv.debugfp, (long double)d);
	}
#endif
	*a = rv;
}

/*
 * Opposite to above; move a 64-bit float into an 80-bit value.
 */
static void
float64_to_floatx80(SFP a)
{
	SF rv;
	int exp, sign;
	uint64_t mant;

	sign = double_sign(a);
	switch (soft_classify(a, DOUBLE)) {
	case SOFT_ZERO:
		LDOUBLE_ZERO(&rv, sign);
		break;
	case SOFT_INFINITE:
		LDOUBLE_INF(&rv, sign);
		break;
	case SOFT_NAN:
		LDOUBLE_NAN(&rv, sign);
		break;
	default:
		mant = double_mant(a);
		exp = double_exp(a);
		exp = exp - DOUBLE_BIAS + LDOUBLE_BIAS;
		LDOUBLE_MAKE(&rv, sign, exp, mant);
		break;
	}
	*a = rv;
}

/*
 * Opposite to above; move a 32-bit float into an 80-bit value.
 */
static void
float32_to_floatx80(SFP a)
{
	int exp, sign;
	uint64_t mant;

	sign = float_sign(a);
//printf("float32_to_floatx80: classify %d\n", soft_classify(&a, FLOAT));
	switch (soft_classify(a, FLOAT)) {
	case SOFT_ZERO:
		LDOUBLE_ZERO(a, sign);
		break;
	case SOFT_INFINITE:
		LDOUBLE_INF(a, sign);
		break;
	case SOFT_NAN:
		LDOUBLE_NAN(a, sign);
		break;
	default:
		mant = float_mant(a);
		exp = float_exp(a);
//printf("exp %x\n", exp);
		exp = exp - FLOAT_BIAS + LDOUBLE_BIAS;
//printf("exp %x sign %d mant %llx\n", exp, sign, mant);
		LDOUBLE_MAKE(a, sign, exp, mant);
		break;
	}
}

/*
 * Constant rounding control mode (cf. TS 18661 clause 11).
 * Default is to have no effect. Set through #pragma STDC FENV_ROUND
 */
int sf_constrounding = FPI_RoundNotSet;
/*
 * Exceptions raised by functions which do not return a SF; behave like errno
 */
int sf_exceptions = 0;

/* 
 * Shift right, rounding to even.
 */
static uint64_t
sfrshift(uint64_t b, int count)
{
	uint64_t z;

	z = b >> (count - 3);
	if (b & ((1 << (count - 3)) - 1))
		z |= 1;	/* sticky */
	if (z & 4) {
		if ((z & 3) || (z & 8))
			z += 8;
	}
	return z >> 3;
}


/*
 * Conversions.
 */

/*
 * Convert from integer type f to floating-point type t.
 * Rounds correctly to the target type.
 * XXXX - routine must be cleaned from x80 dependencies!
 */
void
soft_int2fp(SFP rv, CONSZ l, TWORD f, TWORD t)
{
	int64_t ll = l;
	uint64_t mant;
	int sign = 0, exp;

	if (!ISUNSIGNED(f) && ll < 0) {
		ll = -ll;
		sign = 1;
	}

	if (ll == 0) {
		LDOUBLE_ZERO(rv, 0);
	} else if ((l ^ 0x8000000000000000ULL) == 0) {
		/* max negative long long */
		uint32_t m[2];
		m[0] = 0; m[1] = 0x80000000;
		LDOUBLE_MAKE2(rv, 1, (LDOUBLE_BIAS + 63), m);
	} else {
		exp = LDOUBLE_BIAS + 64;
		while (ll > 0)
			ll <<= 1, exp--;
		ll <<= 1, exp--;
		mant = ll;

		LDOUBLE_MAKE(rv, sign, exp, mant);
		if (t == FLOAT || t == DOUBLE)
			soft_fp2fp(rv, t);
	}
#ifdef DEBUGFP
	{ long double dl;
		dl = ISUNSIGNED(f) ? (long double)(U_CONSZ)(l) :
		    (long double)(CONSZ)(l);
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
#ifdef DEBUGFP
//	SF rvsave = *sfp;
#endif
	SF rv;

	if (t == DOUBLE) {
		rv = *sfp;
		floatx80_to_float64(&rv);
		float64_to_floatx80(&rv);
	} else if (t == FLOAT) {
		rv = *sfp;
		floatx80_to_float32(&rv);
//printf("soft_fp2fp: %f\n", (double)*(float *)&rv.debugfp);
		float32_to_floatx80(&rv);
//printf("soft_fp2fpX: %Lf\n", rv.debugfp);
	} else
		rv = *sfp;
//printf("soft_fp2fp: t %d\n", t);
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
	uint64_t mant;
	int exp;

	if (soft_classify(sfp, LDOUBLE) != SOFT_NORMAL)
		return 0;
	
	exp = ldouble_exp(sfp) - LDOUBLE_BIAS - 64 + 1;
	mant = ldouble_mant(sfp);
	mant = (mant >> 1) | (1LL << 63);
	while (exp > 0)
		mant <<= 1, exp--;
	while (exp < 0)
		mant >>= 1, exp++;

	if (ldouble_sign(sfp))
		mant = -(int64_t)mant;
#ifdef DEBUGFP
	{ uint64_t u = (uint64_t)sfp->debugfp;
	  int64_t s = (int64_t)sfp->debugfp;
		if (ISUNSIGNED(t)) {
			if (u != mant)
				fpwarn("soft_fp2int:u", 0.0, sfp->debugfp);
		} else {
			if (s != (int64_t)mant)
				fpwarn("soft_fp2int:s", 0.0, sfp->debugfp);
		}
	}
#endif
	return mant;
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
	LDOUBLE_NEG(sfp);
}

void
soft_plus(SFP x1p, SFP x2p, TWORD t)
{
	MINT a, b, c;
	SF rv;

	if (LDOUBLE_ISINF(x1p) && LDOUBLE_ISINF(x2p)) {
		if (ldouble_sign(x1p) == ldouble_sign(x2p))
			return;
		LDOUBLE_NAN(x1p,0);
		return;
	}
	if (LDOUBLE_ISNAN(x1p) || LDOUBLE_ISINF(x1p))
		return;
	if (LDOUBLE_ISNAN(x2p) || LDOUBLE_ISNAN(x2p)) {
		*x1p = *x2p;
		return;
	}

	ldbl2mint(&a, x1p);
	ldbl2mint(&b, x2p);
	madd(&a, &b, &c);
	mint2ldbl(&rv, &c);
#ifdef DEBUGFP
	if (x1p->debugfp + x2p->debugfp != rv.debugfp)
		fpwarn("soft_plus", rv.debugfp, x1p->debugfp + x2p->debugfp);
#endif
	*x1p = rv;
}

void
soft_minus(SFP x1, SFP x2, TWORD t)
{
	LDOUBLE_NEG(x2);
	return soft_plus(x1, x2, t);
}

/*
 * Multiply two softfloats.
 */
void
soft_mul(SFP x1p, SFP x2p, TWORD t)
{
	MINT a, b, c;
	uint64_t mant;
	int exp1, exp2, sign, sh;
	int s1 = ldouble_sign(x1p);
	int s2 = ldouble_sign(x2p);
	SF rv;

	if (LDOUBLE_ISINFNAN(x1p) || LDOUBLE_ISINFNAN(x2p)) {
		if (LDOUBLE_ISNAN(x1p) || LDOUBLE_ISNAN(x2p)) {
			LDOUBLE_NAN(x1p, 0);
		} else if (LDOUBLE_ISINF(x1p) && LDOUBLE_ISINF(x2p)) {
			LDOUBLE_INF(x1p, s1 == s2);
		} else if (LDOUBLE_ISINF(x1p) && LDOUBLE_ISZERO(x2p)) {
			LDOUBLE_NAN(x1p, 0);
		} else if (LDOUBLE_ISINF(x2p) && LDOUBLE_ISZERO(x1p)) {
			LDOUBLE_NAN(x1p, 0);
		} else /* if (LDOUBLE_ISINF(x1p) || LDOUBLE_ISINF(x2p)) */ {
			LDOUBLE_INF(x1p, s1 == s2);
		}
		return;
	}
	mant2mint(&a, x1p);
	mant2mint(&b, x2p);
//mdump("x1: ", &a);
//mdump("x2: ", &b);
	mult(&a, &b, &c);
//mdump("res: ", &c);
	grsround(&c);
	sh = 1 - mint2mant(&c, &mant);

	exp1 = ldouble_exp(x1p) - LDOUBLE_BIAS;
	exp2 = ldouble_exp(x2p) - LDOUBLE_BIAS;
//printf("exp1 %d exp2 %d\n", exp1, exp2);

	sign = s1 != s2;
	LDOUBLE_MAKE(&rv, sign, (exp1 + exp2 + sh + LDOUBLE_BIAS), (mant << 1));
#ifdef DEBUGFP
	if (x1p->debugfp * x2p->debugfp != rv.debugfp)
		fpwarn("soft_mul", rv.debugfp, x1p->debugfp * x2p->debugfp);
#endif
        *x1p = rv;
}

void
soft_div(SFP x1p, SFP x2p, TWORD t)
{
	MINT a, b, c, d, e, f;
	uint64_t mant;
	int exp1, exp2, sign, sh;
	int s1 = ldouble_sign(x1p);
	int s2 = ldouble_sign(x2p);
	SF rv;

	if (LDOUBLE_ISINFNAN(x1p) || LDOUBLE_ISINFNAN(x2p)) {
		if (LDOUBLE_ISNAN(x1p) || LDOUBLE_ISNAN(x2p)) {
			LDOUBLE_NAN(&rv, 1);
		} else if (LDOUBLE_ISINF(x1p) && LDOUBLE_ISINF(x2p)) {
			LDOUBLE_NAN(&rv, 0);
		} else if (LDOUBLE_ISINF(x1p) && LDOUBLE_ISZERO(x2p)) {
			LDOUBLE_NAN(&rv, 0);
		} else if (LDOUBLE_ISINF(x2p)) {
			LDOUBLE_ZERO(&rv, 0);
		} else if (LDOUBLE_ISZERO(x2p)) {
			LDOUBLE_INF(&rv, 0);
		} else /* if (LDOUBLE_ISINF(x1p)) */ {
			LDOUBLE_INF(&rv, s1);
		}
	} else if (LDOUBLE_ISZERO(x2p)) {
		if (LDOUBLE_ISZERO(x1p)) {
			LDOUBLE_NAN(&rv, s1 == s2);
		} else {
			LDOUBLE_INF(&rv, s1 != s2);
		}
	} else {

		/* get quot and remainder of divided mantissa */
		mant2mint(&a, x1p);
		mshl(&a, 64);
		mant2mint(&b, x2p);
		mdiv(&a, &b, &c, &d);
		sh = topbit(&c) - 64; /* MANT_BITS */

		/* divide remainder as well, for use in rounding */
		mshl(&d, 64);
		mant2mint(&b, x2p);
		mdiv(&d, &b, &e, &f);

		/* create 128-bit number of the two quotients */
		mshl(&c, 64);
		madd(&c, &e, &f);

		/* do correct rounding */
		grsround(&f);
		mint2mant(&f, &mant);

		exp1 = ldouble_exp(x1p) - LDOUBLE_BIAS;
		exp2 = ldouble_exp(x2p) - LDOUBLE_BIAS;

		sign = s1 != s2;
		LDOUBLE_MAKE(&rv, sign,
		    (exp1 - exp2 + sh + LDOUBLE_BIAS), (mant << 1));
	}
#ifdef DEBUGFP
	{ long double ldd = x1p->debugfp / x2p->debugfp;
	if (memcmp(&ldd, &rv.debugfp, SZLD))
		fpwarn("soft_div", rv.debugfp, ldd);
	}
#endif
//long double ldou = x1p->debugfp / x2p->debugfp;
//printf("x1: %llx %x\n", *(long long *)&x1.debugfp, ((int *)&x1.debugfp)[2]);
//printf("x2: %llx %x\n", *(long long *)&x2.debugfp, ((int *)&x2.debugfp)[2]);
//printf("rv: %llx %x\n", *(long long *)&rv.debugfp, ((int *)&rv.debugfp)[2]);
//printf("rv: %llx %x\n", *(long long *)&ldou, ((int *)&ldou)[2]);
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
	int r = LDOUBLE_ISZERO(sfp);
#ifdef DEBUGFP
	if ((sfp->debugfp == 0.0 && r == 0) || (sfp->debugfp != 0.0 && r == 1))
		fpwarn("soft_isz", sfp->debugfp, (long double)r);
#endif
	return r;
}

/*
 * Do classification as in C99 7.12.3, for internal use.
 * No subnormal yet.
 */
int
soft_classify(SFP sfp, TWORD t)
{
	int rv = 0;

	switch (t) {
	case FLOAT:
		if (FLOAT_ISINF(sfp))
			rv = SOFT_INFINITE;
		else if (FLOAT_ISNAN(sfp))
			rv = SOFT_NAN;
		else if (FLOAT_ISZERO(sfp))
			rv = SOFT_ZERO;
		else
			rv = SOFT_NORMAL;
		break;

	case DOUBLE:	
		if (DOUBLE_ISINF(sfp))
			rv = SOFT_INFINITE;
		else if (DOUBLE_ISNAN(sfp))
			rv = SOFT_NAN;
		else if (DOUBLE_ISZERO(sfp))
			rv = SOFT_ZERO;
		else
			rv = SOFT_NORMAL;
		break;

	case LDOUBLE:
		if (LDOUBLE_ISINF(sfp))
			rv = SOFT_INFINITE;
		else if (LDOUBLE_ISNAN(sfp))
			rv = SOFT_NAN;
		else if (LDOUBLE_ISZERO(sfp))
			rv = SOFT_ZERO;
		else
			rv = SOFT_NORMAL;
		break;
	}
	return rv;
}

static int
soft_cmp_eq(SFP x1, SFP x2)
{
	int s1, s2, e1, e2;
	uint64_t m1, m2;

	s1 = ldouble_sign(x1);
	s2 = ldouble_sign(x2);
	e1 = ldouble_exp(x1);
	e2 = ldouble_exp(x2);
	m1 = ldouble_mant(x1);
	m2 = ldouble_mant(x2);

	if (e1 == 0 && e2 == 0 && m1 == 0 && m2 == 0)
		return 1; /* special case: +0 == -0 (discard sign) */
	if (s1 != s2)
		return 0;
	if (e1 == e2 && m1 == m2)
		return 1;
	return 0;
}

/*
 * Is x1 greater/less than x2?
 */
static int
soft_cmp_gl(SFP x1, SFP x2, int isless)
{
	uint64_t mant1, mant2;
	int s2, rv;

	/* Both zero -> not greater */
	if (LDOUBLE_ISZERO(x1) && LDOUBLE_ISZERO(x2))
		return 0;

	/* one negative -> return x2 sign */
	if (ldouble_sign(x1) + (s2 = ldouble_sign(x2)) == 1)
		return isless ? !s2 : s2;

	/* check exponent */
	if (ldouble_exp(x1) > ldouble_exp(x2)) {
		rv = isless ? 0 : 1;
	} else if (ldouble_exp(x1) < ldouble_exp(x2)) {
		rv = isless ? 1 : 0;
	} else {

		/* exponent equal, check mantissa */
		mant1 = ldouble_mant(x1);
		mant2 = ldouble_mant(x2);
		if (mant1 == mant2)
			return 0; /* same number */
		if (mant1 > mant2) {
			rv = isless ? 0 : 1;
		} else /* if (mant1 < mant2) */
			rv = isless ? 1 : 0;
	}

	/* if both negative, invert rv */
	if (s2)
		rv ^= 1;
	return rv;
}

int
soft_cmp(SFP v1p, SFP v2p, int v)
{
	int rv = 0;

	if (LDOUBLE_ISNAN(v1p) || LDOUBLE_ISNAN(v2p))
		return 0; /* never equal */

	switch (v) {
	case GT:
	case LT:
		rv = soft_cmp_gl(v1p, v2p, v == LT);
		break;
	case GE:
	case LE:
		if ((rv = soft_cmp_eq(v1p, v2p)))
			break;
		rv = soft_cmp_gl(v1p, v2p, v == LE);
		break;
	case EQ:
		rv = soft_cmp_eq(v1p, v2p);
		break;
	case NE:
		rv = !soft_cmp_eq(v1p, v2p);
		break;
	}
	return rv;
}

#endif /* FDFLOAT */

#ifndef NEW_STRTOLD
static void
vals2fp(SF *sf, int k, int exp, uint32_t *mant)
{
	int sign = (k & SF_Neg) != 0;
	uint64_t m;

	switch (k & SF_kmask) {
	case SF_Zero:
		LDOUBLE_ZERO(sf, sign);
		break; /* already 0 */

	case SF_Normal:
		m = (((uint64_t)mant[1] << 32) | mant[0]) << 1;
//printf("vals2fp m %llx\n", m);
		exp += FPI_LDOUBLE.exp_bias;
		LDOUBLE_MAKE(sf, sign, exp, m);
//printf("vals2fp: %llx %llx\n", *(long long *)&sf->debugfp, m);
#ifdef DEBUGFP
		if (mant[0] != sf->fp[0] || mant[1] != sf->fp[1])
			fpwarn("vals2fp", sf->debugfp, sf->debugfp);
#endif
		break;
	case SF_Denormal:
		m = (((uint64_t)mant[1] << 32) | mant[0]) << 1;
		LDOUBLE_MAKE(sf, sign, 0, m);
		break;
	default:
		fprintf(stderr, "vals2fp: unhandled %x\n", k);
		break;
	}

	if (k & (SFEXCP_ALLmask & ~(SFEXCP_Inexlo|SFEXCP_Inexhi)))
		fprintf(stderr, "vals2fp: unhandled2 %x\n", k);
}
#endif

#ifdef NEW_STRTOLD

static void
mshr(MINT *a, int nbits)
{
	int i, j;

	for (j = 0; j < nbits; j++) {
		for (i = 0; i < a->len; i++)
			a->val[i] = (a->val[i] >> 1) |	(a->val[i+1] << 15);
		a->val[i] >>= 1;
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
 * Sanity check mantissa and exponent.
 * we decide that exponent more than 5 digits is too large.
 */
static int
mesanity(MINT *m, char *s)
{	
	int i, neg = 0;
	
	if (MINTZ(m))
		return SOFT_ZERO; 
	if ((*s == '-') || (*s == '+')) {
		neg = (*s == '-');
		s++;
	}
	for (i = 0; s[i] >= '0' && s[i] <= '9'; i++)
		;
	if (i > 4)
		return (neg ? SOFT_ZERO : SOFT_INFINITE);
	return 0;
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
	if ((ch = mesanity(mmant, str)))
		return ch;
	if (exp10 < 0) {
		cur = mexp;
		exp10 = -exp10;
	} else
		cur = mmant;
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
	int ch;

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
				exp2 -= 4;
			continue;
	
		case '.':
			gotdot = 1;
			continue;

		case 'p':
		case 'P':
			if ((ch = mesanity(mmant, str)))
				return ch;
			exp2 += atoi(str);
			if (exp2 < 0)
				mshl(mexp, -exp2);
			else
				mshl(mmant, exp2);
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
str2num(char *str, int *exp, uint32_t *mant, struct FPI *fpi)
{
	MINT c, d, mm, me;
	int t, u, i, rv;

	minit(&mm, 0);
	minit(&me, 1);

	if (*str == '0' && (str[1] == 'x' || str[1] == 'X')) {
		rv = hexbig(str+2, &mm, &me);
	} else {
		rv = decbig(str, &mm, &me);
	}
//printf("rv1 %d\n", rv);
	if (rv != SOFT_NORMAL)
		return rv;
//printf("rv2\n");

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
		mdiv(&mm, &me, &c, &d);

		if (topbit(&c) < fpi->nbits-1) {
			mshl(&mm, 1);
			mdiv(&mm, &me, &c, &d);
			scale++;
		}
		mround(&me, &c, &d);	/* round correctly */
		t = topbit(&c);
		if (sub && t == fpi->nbits-1)
			sub = 0;
		if (topbit(&c) == fpi->nbits) {
			mshr(&c, 1);
			scale--;
		}

		if (sub)
			*exp = -fpi->bias;
		else
			*exp = fpi->nbits - scale - 1;
	} else {
		int scale = (t-u) - fpi->nbits + 1;
		mshl(&me, scale);
		mdiv(&mm, &me, &c, &d);
		if (topbit(&c) < fpi->nbits-1) {
			mshr(&me, 1);
			mdiv(&mm, &me, &c, &d);
			scale--;
		}
		mround(&me, &c, &d);
		if (topbit(&c) == fpi->nbits) {
			mshr(&c, 1);
			scale++;
		}

		*exp = fpi->nbits + scale - 1;
		if (*exp >= fpi->maxexp) {
			*exp = fpi->maxexp;
			minit(&c, 1);
			mshl(&c, fpi->nbits-1);
		}
	}
	for (i = 0; i < fpi->nbits; i += 32)
		mant[i/32] = ((uint32_t)c.val[i/16+1] << 16) | c.val[i/16];
	*exp += fpi->bias;
//printf("mant0 %08x mant1 %08x exp %d\n", mant[0], mant[1], *exp);
	return SOFT_NORMAL;
}

#endif

/*
 * Conversions from decimal and hexadecimal strings.
 * Rounds correctly to the target type (subject to FLT_EVAL_METHOD.)
 * dt is resulting type.
 */
void
strtosf(SFP sfp, char *str, TWORD tw)
{
	ULong bits[2] = { 0, 0 };
	Long expt;

//printf("strtosf %s\n", str);
#ifdef NEW_STRTOLD
	int rv;

	/* XXX obey floating point number ending */
	rv = str2num(str, &expt, bits, fpis[2]);
//printf("strtosf: rv %d, expt %d, bits[0] %08x, bits[1] %08x\n", rv, expt, bits[0], bits[1]);
	switch (rv) {
	case SOFT_NORMAL:
		LDOUBLE_MAKE2(sfp, 0, expt, bits);
		break;
	case SOFT_ZERO:
		LDOUBLE_ZERO(sfp, 0);
		break;
	}
#else
	char *eptr;
	int k;
	k = strtodg(str, &eptr, &FPI_LDOUBLE, &expt, bits);

	if (k & SFEXCP_Overflow)
		werror("Overflow in floating-point constant");
	if (k & SFEXCP_Inexact && (str[1] == 'x' || str[1] == 'X'))
		werror("Hexadecimal floating-point constant not exactly");
	vals2fp(sfp, k, expt, bits);
//printf("strtosf: %llx\n", *(long long *)&sf.debugfp);
#endif

#ifdef DEBUGFP
	{
		long double ld = strtold(str, NULL);
		if (ld != sfp->debugfp)
			fpwarn("strtosf", sfp->debugfp, ld);
	}
#endif
}

/*
 * return INF/NAN.
 */
void
soft_huge_val(SFP sfp)
{
	LDOUBLE_INF(sfp, 0);

#ifdef DEBUGFP
	if (sfp->debugfp != __builtin_huge_vall())
		fpwarn("soft_huge_val", sfp->debugfp, __builtin_huge_vall());
#endif
}

void
soft_nan(SFP sfp, char *c)
{
	LDOUBLE_NAN(sfp, 0);
}

/*
 * Convert internally stored floating point to fp type in TWORD.
 * Save as a static array of uint32_t.
 */
uint32_t *
soft_toush(SFP sfp, TWORD t, int *nbits)
{
	static SF sf;

//printf("soft_toush: osf %Lf %La t %d\n", osf.debugfp, osf.debugfp, t);
//printf("soft_toushLD: %x %x %x\n", osf.fp[2], osf.fp[1], osf.fp[0]);
//float d = osf.debugfp; printf("soft_toush-D: d %x %x\n", *(((int *)&d)+1), *(int *)&d);

	memset(&sf, 0, sizeof(SF));
	if (t == LDOUBLE) {
		sf = *sfp;
	} else if (t == DOUBLE) {
		sf = *sfp;
		floatx80_to_float64(&sf);
//printf("soft_toushD: sf %f\n", *(double *)&sf.debugfp);
//printf("soft_toushD2: %x %x\n", sf.fp[1], sf.fp[0]);
	} else /* if (t == FLOAT) */ {
		sf = *sfp;
		floatx80_to_float32(&sf);
//printf("soft_toushD: sf %f\n", (double)*(float *)&sf.debugfp);
//printf("soft_toushD2: %x\n", sf.fp[0]);
	}
#ifdef DEBUGFP
	{ float ldf; double ldd; long double ldt;
	ldt = (t == FLOAT ? (float)sfp->debugfp :
	    t == DOUBLE ? (double)sfp->debugfp : (long double)sfp->debugfp);
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
	*nbits = fpis[t-FLOAT]->storage;
	return sf.fp;
}

#ifdef DEBUGFP
void
fpwarn(const char *s, long double soft, long double hard)
{
	extern int nerrors;

	union { long double ld; int i[3]; } X;
	fprintf(stderr, "WARNING: In function %s: soft=%La hard=%La\n",
	    s, soft, hard);
	fprintf(stderr, "WARNING: soft=%Lf hard=%Lf\n", soft, hard);
	X.ld=soft;
	fprintf(stderr, "WARNING: s[0]=%x s[1]=%x s[2]=%x ",
	    X.i[0], X.i[1], X.i[2]);
	X.ld=hard;
	fprintf(stderr, "h[0]=%x h[1]=%x h[2]=%x\n", X.i[0], X.i[1], X.i[2]);
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
	memset(m->val, 0, MAXMINT);
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

void
mshl(MINT *a, int nbits)
{
	int i, j;

	/* XXXXXXX must improve speed significantly */
	for (j = 0; j < nbits; j++) {
		if (a->val[a->len-1] & 0x8000) {
#ifdef DEBUGFP
			if (a->len >= MAXMINT)
				fpwarn("mshl: shifting out", 0, 0);
#endif
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
	printf("len %d sign %d:\n", a->len, (unsigned)a->sign);
	for (i = 0; i < a->len; i++)
		printf("%05d: %04x\n", i, a->val[i]);
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
	for (i = a->len; i < mx; i++)
		a->val[i] = 0;
	for (i = b->len; i < mx; i++)
		b->val[i] = 0;
	a->len = b->len = mx;

	if (a->sign)
		neg2com(a);
	if (b->sign)
		neg2com(b);

	sum = 0;
	for (i = 0; i < a->len; i++) {
		sum = a->val[i] + b->val[i] + sum;
		c->val[i] = sum;
		sum >>= 16;
	}
	c->len = a->len;

	if (c->val[c->len-1] & 0x8000) {
		neg2com(c);
		c->sign = 1;
	} else
		c->sign = 0;
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
	c->len = a->len + b->len;
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

	minit(q, 0);
	minit(r, 0);
	chomp(n);
	chomp(d);
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

