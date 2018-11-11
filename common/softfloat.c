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

#if 0
/*
 * Do a "Round to nearest, tie even" on mantissa.
 * Mantissa has no hidden bit, and length nbits.
 * The rounded result have resbits length.
 */
static uint64_t
sfroundmant(uint64_t mant, int nbits, int resbits)
{
	int grs, sticky = nbits - resbits - 3;

	if (mant & (sticky - 1))
		mant |= (1 << sticky);
	mant >>= sticky;

	grs = (mant & 7);
	if (grs > 4 || ((grs == 4) && (mant & 8)) /* round up */
		mant += 8;
	mant >>= 3;
	return mant;
}
#endif

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

#define ONEZEROES(n)	(1ull << (n))
#define ONES(n) 	(ONEZEROES(n) | (ONEZEROES(n)-1))

#define WORKBITS	64
#define NORMALMANT	ONEZEROES(WORKBITS-1)

#define SFNORMALIZE(sf)					\
	while ((sf).significand < NORMALMANT)		\
		(sf).significand <<= 1, (sf).exponent--;\
	if (((sf).kind & SF_kmask) == SF_Denormal)	\
		(sf).kind -= SF_Denormal - SF_Normal;

#define SFNEG(sf)	((sf).kind ^= SF_Neg, sf)
#define SFCOPYSIGN(sf, src)	\
	((sf).kind ^= ((sf).kind & SF_Neg) ^ ((src).kind & SF_Neg), (sf))
#define SFISZ(sf)	(((sf).kind & SF_kmask) == SF_Zero)
#define SFISINF(sf)	(((sf).kind & SF_kmask) == SF_Infinite)
#define SFISNAN(sf)	(((sf).kind & SF_kmask) >= SF_NaN)

typedef struct DULLong {
	ULLong hi, lo;
} DULLong;

static DULLong rshiftdro(ULLong, ULLong, int);
static uint64_t sfrshift(uint64_t mant, int bits);
static DULLong lshiftd(ULLong, ULLong, int);
static SF sfround(SF, ULLong, TWORD);
#define SFROUND(sf,t)	(sfround(sf, 0, t))
static SF sfadd(SF, SF, TWORD);
static SF sfsub(SF, SF, TWORD);

#ifndef NO_COMPLEX
static SF finitemma(SF, SF, int, SF, SF, ULLong *);
static SF sfddiv(SF, ULLong, SF, ULLong, TWORD);
#endif

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
        0, 1, 1, 0,  32,    127+24-1 };
#define IEEEFP_32_ZERO(sf,s)	(sf.fp[0] = (s << 31))
#define IEEEFP_32_NAN(sf,sign)	(sf.fp[0] = 0x7fc00000 | (sign << 31))
#define IEEEFP_32_INF(sf,sign)	(sf.fp[0] = 0x7f800000 | (sign << 31))
#define	IEEEFP_32_ISINF(x)	((x.fp[0] & 0x7fffffff) == 0x7f800000)
#define	IEEEFP_32_ISZERO(x)	((x.fp[0] & 0x7fffffff) == 0)
#define	IEEEFP_32_ISNAN(x)	((x.fp[0] & 0x7fffffff) == 0x7fc00000)
#define IEEEFP_32_BIAS	127
#define	IEEEFP_32_TOOLARGE(exp, mant)	ieeefp_32_toolarge(exp, mant)
#define	IEEEFP_32_TOOSMALL(exp, mant)	ieeefp_32_toosmall(exp, mant)
#define IEEEFP_32_MAKE(rv, sign, exp, mant)	\
	(rv.fp[0] = (sign << 31) | ((exp & 0xff) << 23) | sfrshift(mant, 41))
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
        0, 1, 1, 0,  64,     1023+53-1 };
//static SF ieee64_zero = { { { 0, 0, 0 } } };
#define IEEEFP_64_ZERO(sf,s)	(sf.fp[0] = 0, sf.fp[1] = (s << 31))
#define IEEEFP_64_NAN(sf,sign)	\
	(sf.fp[0] = 0, sf.fp[1] = 0x7ff80000 | (sign << 31))
#define IEEEFP_64_INF(sf,sign)	\
	(sf.fp[0] = 0, sf.fp[1] = 0x7ff00000 | (sign << 31))
#define	IEEEFP_64_ISINF(x) (((x.fp[1] & 0x7fffffff) == 0x7ff00000) && \
	    x.fp[0] == 0)
#define	IEEEFP_64_ISZERO(x) (((x.fp[1] & 0x7fffffff) == 0) && x.fp[0] == 0)
#define	IEEEFP_64_ISNAN(x) (((x.fp[1] & 0x7fffffff) == 0x7ff80000) && \
	    x.fp[0] == 0)
#define IEEEFP_64_BIAS	1023
#define	IEEEFP_64_TOOLARGE(exp, mant)	ieeefp_64_toolarge(exp, mant)
#define	IEEEFP_64_TOOSMALL(exp, mant)	ieeefp_64_toosmall(exp, mant)
#define IEEEFP_64_MAKE(rv, sign, exp, mant)		\
	{ uint64_t xmant = sfrshift(mant, 12);		\
	(rv.fp[0] = xmant, rv.fp[1] = ((sign << 31) | 	\
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
static int
ieeefp_64_toosmall(int exp, uint64_t mant)
{
	if ( exp >= 0 )
		return 0;
	mant = sfrshift(mant, -exp);
	mant |= (mant & 0x7ff ? 0x800 : 0);
	if (mant & 0xfffffffffffff000)
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
        1, 1, 1, 0,   80,     16383+64-1 };
#define IEEEFP_X80_NAN(sf,sign)	\
	(sf.fp[0] = 0, sf.fp[1] = 0xc0000000, sf.fp[2] = 0x7fff | (sign << 15))
#define IEEEFP_X80_INF(sf,sign)	\
	(sf.fp[0] = 0, sf.fp[1] = 0x80000000, sf.fp[2] = 0x7fff | (sign << 15))
#define IEEEFP_X80_ZERO(sf,s)	(sf.fp[0] = sf.fp[1] = 0, sf.fp[2] = (s << 15))
#define	IEEEFP_X80_ISZ(sf) \
	((sf.fp[0] | sf.fp[1] | (sf.fp[2] & 0x7fff)) == 0)
#define	IEEEFP_X80_NEG(sf)	sf.fp[2] ^= 0x8000
#define	IEEEFP_X80_ISINF(x) (((x.fp[2] & 0x7fff) == 0x7fff) && \
	(x.fp[1] == 0x80000000) && x.fp[0] == 0)
#define	IEEEFP_X80_ISZERO(x) (((x.fp[2] & 0x7fff) == 0) && \
	(x.fp[1] | x.fp[0]) == 0)
#define	IEEEFP_X80_ISNAN(x) (((x.fp[2] & 0x7fff) == 0x7fff) && \
	((x.fp[1] != 0x80000000) || x.fp[0] == 0))
#define IEEEFP_X80_BIAS	16383
#define	IEEEFP_X80_MAXMINT	32768+64+16 /* exponent + subnormal + guard */
#define IEEEFP_X80_MAKE(rv, sign, exp, mant)	\
	(rv.fp[0] = mant >> 1, rv.fp[1] = (mant >> 33) | (1 << 31), \
	    rv.fp[2] = (exp & 0x7fff) | (sign << 15))
#else
#error need long double definition
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
int soft_classify(SF sf, TWORD type);

#define FPI_FLOAT	C(FLT_PREFIX,_FPI)
#define FPI_DOUBLE	C(DBL_PREFIX,_FPI)
#define FPI_LDOUBLE	C(LDBL_PREFIX,_FPI)

#define	LDOUBLE_NAN	C(LDBL_PREFIX,_NAN)
#define	LDOUBLE_INF	C(LDBL_PREFIX,_INF)
#define	LDOUBLE_ZERO	C(LDBL_PREFIX,_ZERO)
#define	LDOUBLE_NEG	C(LDBL_PREFIX,_NEG)
#define	LDOUBLE_ISZ	C(LDBL_PREFIX,_ISZ)
#define	LDOUBLE_ISINF	C(LDBL_PREFIX,_ISINF)
#define	LDOUBLE_ISNAN	C(LDBL_PREFIX,_ISNAN)
#define	LDOUBLE_ISZERO	C(LDBL_PREFIX,_ISZERO)
#define	LDOUBLE_BIAS	C(LDBL_PREFIX,_BIAS)
#define	LDOUBLE_MAKE	C(LDBL_PREFIX,_MAKE)
#define	LDOUBLE_MAXMINT	C(LDBL_PREFIX,_MAXMINT)
#define	LDOUBLE_SIGN	C(LDBL_PREFIX,_SIGN)

#define	DOUBLE_NAN	C(DBL_PREFIX,_NAN)
#define	DOUBLE_INF	C(DBL_PREFIX,_INF)
#define	DOUBLE_ZERO	C(DBL_PREFIX,_ZERO)
#define	DOUBLE_NEG	C(DBL_PREFIX,_NEG)
#define	DOUBLE_ISZ	C(DBL_PREFIX,_ISZ)
#define	DOUBLE_ISINF	C(DBL_PREFIX,_ISINF)
#define	DOUBLE_ISNAN	C(DBL_PREFIX,_ISNAN)
#define	DOUBLE_ISZERO	C(DBL_PREFIX,_ISZERO)
#define	DOUBLE_BIAS	C(DBL_PREFIX,_BIAS)
#define	DOUBLE_TOOLARGE	C(DBL_PREFIX,_TOOLARGE)
#define	DOUBLE_TOOSMALL	C(DBL_PREFIX,_TOOSMALL)
#define	DOUBLE_MAKE	C(DBL_PREFIX,_MAKE)

#define	FLOAT_NAN	C(FLT_PREFIX,_NAN)
#define	FLOAT_INF	C(FLT_PREFIX,_INF)
#define	FLOAT_ZERO	C(FLT_PREFIX,_ZERO)
#define	FLOAT_NEG	C(FLT_PREFIX,_NEG)
#define	FLOAT_ISZ	C(FLT_PREFIX,_ISZ)
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

void madd(MINT *a, MINT *b, MINT *c);
void msub(MINT *a, MINT *b, MINT *c);
void mult(MINT *a, MINT *b, MINT *c);
void mdiv(MINT *a, MINT *b, MINT *c, MINT *r);
void minit(MINT *m);
void mshl(MINT *m, int nbits);
static void chomp(MINT *a);
void mdump(char *c, MINT *a);


/*
 * IEEE specials:
 * Zero:	Exponent 0, mantissa 0
 * Denormal:	Exponent 0, mantissa != 0
 * Infinity:	Exponent all 1, mantissa 0
 * QNAN:	Exponent all 1, mantissa MSB 1 (indeterminate)
 * SNAN:	Exponent all 1, mantissa MSB 0 (invalid)
 */

#define	LX(x,n)	((uint64_t)x.fp[n] << n*32)

/*
 * Get long double mantissa without hidden bit.
 * Hidden bit is expected to be at position 65.
 */
static uint64_t
ldouble_mant(SF sf)
{
	uint64_t rv;

	rv = (LX(sf,0) | LX(sf,1)) << 1; /* XXX */
	return rv;
}

#define	ldouble_exp(x)	(x.fp[2] & 0x7FFF)
#define	ldouble_sign(x)	((x.fp[2] >> 15) & 1)

#define	double_mant(x)	(((uint64_t)x.fp[1] << 44) | ((uint64_t)x.fp[0] << 12))
#define	double_exp(x)	((x.fp[1] >> 20) & 0x7fff)
#define	double_sign(x)	((x.fp[1] >> 31) & 1)

#define	float_mant(x)	((uint64_t)(x.fp[0] & 0x7fffff) << 41)
#define	float_exp(x)	((x.fp[0] >> 23) & 0xff)
#define	float_sign(x)	((x.fp[0] >> 31) & 1)

/*
 * convert a long double to MINT.
 * Known here to only be valid numbers.
 */
static void
ldbl2mint(MINT *a, SF sf)
{
	uint64_t rv = (LX(sf,0) | LX(sf,1));
	int exp = ldouble_exp(sf);

	minit(a);
	a->val[0] = rv;
	a->val[1] = rv >> 16;
	a->val[2] = rv >> 32;
	a->val[3] = rv >> 48;
	a->len = 4;
	mshl(a, exp + 16); /* 16 == guard bits, 64 bit mant is in len */
	a->sign = ldouble_sign(sf);
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
mcopy(MINT *a, MINT *b)
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
	doadd = 0;
	if (getbit(a, h-1)) { /* guard bit set */
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
		minit(&d);
		mcopy(&e, a);
		d.len = (h/16)+1;
		d.val[(h/16)] = 1 << (h % 16);
		madd(&d, &e, a);
	}
}

static SF
mint2ldbl(MINT *a)
{
	uint64_t mant;
	SF rv;
	int exp = 0;
	int len;

	chomp(a);
	grsround(a);
	len = a->len-1;
	while ((a->val[len] & 0x8000) == 0)
		mshl(a, 1), exp--;
	mant = (uint64_t)a->val[len] << 48;
	if (len > 0) mant |= (uint64_t)a->val[len-1] << 32;
	if (len > 1) mant |= (uint64_t)a->val[len-2] << 16;
	if (len > 2) mant |= (uint64_t)a->val[len-3];
	if (len > 3) { /* do some rounding */
		
	}
	exp += len * 16;
	exp -= 64; /* bits in mantissa */
	mant <<= 1;
	LDOUBLE_MAKE(rv, a->sign, exp, mant);
	return rv;
}

/*
 * Convert a extended float (x80) number to float (32-bit). 
 * Store as float.
 */
static SF
floatx80_to_float32(SF a)
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
		FLOAT_INF(rv, sign);
//printf("1\n");
	} else if (LDOUBLE_ISNAN(a)) {
		FLOAT_NAN(rv, sign);
		rv.fp[0] |= mant >> 41;
//printf("2\n");
	} else if (LDOUBLE_ISZERO(a)) {
//printf("3\n");
		FLOAT_ZERO(rv, sign);
	} else {
//printf("4\n");
		exp = exp - LDOUBLE_BIAS + FLOAT_BIAS;
//printf("4: ecp %d\n", exp);
		if (FLOAT_TOOLARGE(exp, mant)) {
			FLOAT_INF(rv, sign);
		} else if (FLOAT_TOOSMALL(exp, mant)) {
			FLOAT_ZERO(rv, sign);
		} else {
			FLOAT_MAKE(rv, sign, exp, mant);
		}
	}
	return rv;
}

/*
 * Convert a extended float (x80) number to double (64-bit). 
 * Store as double.
 */
static SF
floatx80_to_float64(SF a)
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
		DOUBLE_INF(rv, sign);
//printf("1\n");
	} else if (LDOUBLE_ISNAN(a)) {
		DOUBLE_NAN(rv, sign);
		rv.fp[1] |= (mant >> 44);
		rv.fp[0] = mant >> 12;
//printf("2\n");
	} else if (LDOUBLE_ISZERO(a)) {
//printf("3\n");
		DOUBLE_ZERO(rv, sign);
	} else {
//printf("4\n");
		exp = exp - LDOUBLE_BIAS + DOUBLE_BIAS;
//printf("4: exp %d\n", exp);
		if (DOUBLE_TOOLARGE(exp, mant)) {
			DOUBLE_INF(rv, sign);
		} else if (DOUBLE_TOOSMALL(exp, mant)) {
			DOUBLE_ZERO(rv, sign);
		} else {
			DOUBLE_MAKE(rv, sign, exp, mant);
		}
//printf("X: %x %x %x\n", rv.fp[0], rv.fp[1], rv.fp[2]);
	}
#ifdef DEBUGFP
	{ 	double d = a.debugfp;
		if (memcmp(&rv, &d, sizeof(double)))
			fpwarn("floatx80_to_float64",
			    (long double)*(double*)&rv.debugfp, (long double)d);
	}
#endif
	return rv;
}

/*
 * Opposite to above; move a 64-bit float into an 80-bit value.
 */
static SF
float64_to_floatx80(SF a)
{
	SF rv;
	int exp, sign;
	uint64_t mant;

	sign = double_sign(a);
	switch (soft_classify(a, DOUBLE)) {
	case SOFT_ZERO:
		LDOUBLE_ZERO(rv, sign);
		break;
	case SOFT_INFINITE:
		LDOUBLE_INF(rv, sign);
		break;
	case SOFT_NAN:
		LDOUBLE_NAN(rv, sign);
		break;
	default:
		mant = double_mant(a);
		exp = double_exp(a);
		exp = exp - DOUBLE_BIAS + LDOUBLE_BIAS;
		LDOUBLE_MAKE(rv, sign, exp, mant);
		break;
	}
	return rv;
}

/*
 * Opposite to above; move a 32-bit float into an 80-bit value.
 */
static SF
float32_to_floatx80(SF a)
{
	SF rv;
	int exp, sign;
	uint64_t mant;

	sign = float_sign(a);
//printf("float32_to_floatx80: classify %d\n", soft_classify(a, FLOAT));
	switch (soft_classify(a, FLOAT)) {
	case SOFT_ZERO:
		LDOUBLE_ZERO(rv, sign);
		break;
	case SOFT_INFINITE:
		LDOUBLE_INF(rv, sign);
		break;
	case SOFT_NAN:
		LDOUBLE_NAN(rv, sign);
		break;
	default:
		mant = float_mant(a);
		exp = float_exp(a);
//printf("exp %x\n", exp);
		exp = exp - FLOAT_BIAS + LDOUBLE_BIAS;
//printf("exp %x sign %d mant %llx\n", exp, sign, mant);
		LDOUBLE_MAKE(rv, sign, exp, mant);
		break;
	}
	return rv;
}

#if 0
/*
 * Conversion between Hauser code and internal. XXX - merge.
 */
static SF
jrh32tofp(float32 f)
{
	SF rv;
	rv.fp[0] = f;
	rv.fp[1] = f >> 16;
	rv.fp[2] = 0;
	rv.fp[3] = 0;
	rv.fp[4] = 0;
	rv.fp[4] = 0;
	return rv;
}

static SF
jrh64tofp(float64 f)
{
	SF rv;
	rv.fp[0] = f;
	rv.fp[1] = f >> 16;
	rv.fp[2] = f >> 32;
	rv.fp[3] = f >> 48;
	rv.fp[4] = 0;
	rv.fp[5] = 0;
	return rv;
}

static SF
jrhx80tofp(floatx80 f)
{
	SF rv;
	rv.fp[0] = f.low;
	rv.fp[1] = f.low >> 16;
	rv.fp[2] = f.low >> 32;
	rv.fp[3] = f.low >> 48;
	rv.fp[4] = f.high;
	rv.fp[5] = 0;
	return rv;
}

static float32
fptojrh32(SF sf)
{
	float32 f;

	f = sf.fp[0];
	f |= (sf.fp[1] << 16);
	return f;
}

static float64
fptojrh64(SF sf)
{
	float64 f;

	f = sf.fp[0];
	f |= (sf.fp[1] << 16);
	f |= ((float64)sf.fp[2] << 32);
	f |= ((float64)sf.fp[3] << 48);
	return f;
}

static floatx80
fptojrhx80(SF sf)
{
	floatx80 f;

	f.low = sf.fp[0];
//printf("fptojrhx80: %llx\n", f.low);
	f.low |= ((uint64_t)sf.fp[1] << 16);
//printf("fptojrhx80: %llx\n", f.low);
	f.low |= ((uint64_t)sf.fp[2] << 32);
//printf("fptojrhx80: %llx\n", f.low);
	f.low |= ((uint64_t)sf.fp[3] << 48);
//printf("fptojrhx80: %llx\n", f.low);
	f.high = sf.fp[4];

	return f;
}
#endif

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
 * Returns a (signed) zero softfloat.
 * "kind" (sign and exceptions) is merged into.
 */
SF
zerosf(int kind)
{
	SF rv;

	/*static_*/assert(SF_Zero == 0);
#if 0
	rv.kind &= ~SF_kmask;
#else
	rv.kind = SF_Zero | (kind & ~SF_kmask);
#endif
	rv.significand = rv.exponent = rv.kind = 0;
	return rv;
}

/*
 * Returns a (signed) infinite softfloat.
 * If the target does not support infinites, the "infinite" will propagate
 * until sfround() below, where it will be transformed to DBL_MAX and exception
 */
SF
infsf(int kind)
{
	SF rv;

	rv.kind = SF_Infinite | (kind & ~SF_kmask);
	rv.significand = NORMALMANT;
	rv.exponent = fpis[LDOUBLE-FLOAT]->emax + 1;
	return rv;
}

/*
 * Returns a NaN softfloat.
 */
SF
nansf(int kind)
{
	SF rv;

	rv.kind = SF_NaN | (kind & ~SF_kmask);
	rv.significand = 3 * ONEZEROES(WORKBITS-2);
	rv.exponent = fpis[LDOUBLE-FLOAT]->emax + 1;
	return rv;
}

/*
 * Returns a (signed) huge, perhaps infinite, softfloat.
 */
SF
hugesf(int kind, TWORD t)
{
	FPI *fpi = fpis[t-FLOAT];
	SF rv;

	if (fpi->has_inf_nan)
		return infsf(kind);
	rv.kind = (kind & ~SF_kmask) | SF_Normal;
	rv.significand = ONES(fpi->nbits - 1);
	rv.exponent = fpi->emax;
	return rv;
}

/*
 * The algorithms for the operations were derived from John Hauser's 
 * SoftFloat package (which is also used in libpcc/libsoftfloat.) 
 *
 * Results are rounded to odd ("jamming" in John Hauser's code)
 * in order to avoid double rounding errors. See
 *	Sylvie Boldo, Guillaume Melquiond, "When double rounding is odd",
 *	Research report No 2004-48, Normale Sup', Lyon, Nov 2004;
 *	http://www.ens-lyon.fr/LIP/Pub/Rapports/RR/RR2004/RR2004-48.pdf
 *	17th IMACS World Congress, Paris, Jul 2005; pp.11;
 *	http://hal.inria.fr/inria-00070603/document
 */

/*
 * Shift right double-sized, rounding to odd.
 */
static DULLong
rshiftdro(ULLong a, ULLong b, int count)
{
	struct DULLong z;
	assert(count >= 0);
	if ((unsigned)count >= 2*WORKBITS) {
		z.hi = 0;
		z.lo = (a != 0) | (b != 0);
	}
	else if (count >= WORKBITS) {
		z.hi = 0;
		z.lo = (a >> (count - WORKBITS)) | (b != 0);
	}
	else {
		z.hi = a >> count;
		z.lo = (a << (WORKBITS - count)) | (b >> count) | (b != 0); /* XXX err */
	}
	return z;
}

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
 * Shift left double-sized.
 */
static DULLong
lshiftd(ULLong a, ULLong b, int count)
{
	struct DULLong z;
	assert((unsigned)count < WORKBITS);
	z.hi = a << count;
	z.lo = (a >> (WORKBITS-count)) | (b << count);
	return z;
}

/*
 * Full-range multiply, result to double-sized.
 */
static DULLong
muld(ULLong a, ULLong b)
{
	struct DULLong z;
	ULong ahi, bhi;
	ULLong mid;

#define HALFWORKBITS	(WORKBITS/2)
#define LOWHALFMASK	ONES(WORKBITS-HALFWORKBITS)
	ahi = (ULong)(a >> HALFWORKBITS);
	a &= LOWHALFMASK;
	bhi = (ULong)(b >> HALFWORKBITS);
	b &= LOWHALFMASK;
	z.lo = a * b;
	a *= bhi;
	b *= ahi;
	mid = (z.lo >> HALFWORKBITS) + (a & LOWHALFMASK) + (b & LOWHALFMASK);
	z.lo &= LOWHALFMASK;
	z.lo |= (mid & LOWHALFMASK) << HALFWORKBITS;
	z.hi = (ULLong) ahi * bhi + (a >> HALFWORKBITS) +
		(b >> HALFWORKBITS) + (mid >> HALFWORKBITS);
	return z;
}

/*
 * Explicit cast into some floating-point format, and assigments.
 * Drop precision (rounding correctly) and clamp exponent in range.
 */
typedef int bool;

static SF
sfround(SF sf, ULLong extra, TWORD t)
{
	FPI *fpi;
	ULLong minmant, mant, maxmant;
	DULLong z;
	int exp = sf.exponent, excess, doinc, rd;

	assert(t>=FLOAT && t<=LDOUBLE);
	fpi = fpis[t-FLOAT];
	switch(sf.kind & SF_kmask) {
	  case SF_Zero:
		if (! fpi->has_neg_zero)
			sf.kind &= ~SF_Neg;
		/* FALLTHROUGH */
	  default:
/* XXX revise: SF_NaN escapes here, but what to do if !fpi->has_inf_nan */
		return sf;
	  case SF_Infinite:
		return fpi->has_inf_nan ? sf :
/* XXX revise: IEEE says overflow and invalid cannot be both, but this is for VAX... */
			hugesf(sf.kind | SFEXCP_Overflow | SFEXCP_Invalid, t);
	  case SF_NaNbits:
		cerror("Unexpected softfloat NaNbits");
		sf.kind -= SF_NaNbits - SF_NaN;
		return sf;
	  case SF_Denormal:
		if (exp != fpi->emin || extra) {
			/*static_*/assert(SF_Denormal > SF_Normal);
			sf.kind -= SF_Denormal - SF_Normal;
		}
		break;
	  case SF_Normal:
		break;
	}

	maxmant = ONES(fpi->nbits - 1);
	if (fpi->has_radix_16)
		minmant = ONEZEROES(fpi->nbits - 4);
	else
		minmant = ONEZEROES(fpi->nbits - 1);
	assert(sf.significand);
	excess = 0;
	if (sf.significand < minmant) {
		/* Not normalized */
		if ((sf.kind & SF_kmask) != SF_Denormal) {
			mant = sf.significand;
			for (; mant < minmant; --excess)
				mant <<= 1;
			if (fpi->has_radix_16 && (exp + excess) & 3)
				excess -= (exp + excess) & 3;
		}
	}
	else {
		if ((sf.kind & SF_kmask) == SF_Denormal)
			sf.kind -= SF_Denormal - SF_Normal;
		if ((sf.significand & ~maxmant) != 0) {
			/* More bits than allowed in significand */
			if (sf.significand & NORMALMANT)
				excess = WORKBITS - fpi->nbits;
			else {
				mant = sf.significand;
				for (; mant > maxmant; ++excess)
					mant >>= 1;
			}
		}
	}
	if (fpi->has_radix_16 && (exp + excess) & 3)
		excess += 4 - ((exp + excess) & 3);
	if (excess) {
		if (excess < 0)
			z = lshiftd(sf.significand, extra, -excess);
		else
			z = rshiftdro(sf.significand, extra, excess);
		sf.significand = z.hi;
		extra = z.lo;
		exp += excess;
	}
	assert((sf.kind & SF_kmask) == SF_Denormal ? sf.significand < minmant
	    : (sf.significand & ~(minmant-1)) == minmant || fpi->has_radix_16);

/* XXX check limit cases (emin, emin-1, emin-2) to avoid double rounding... */

	rd = fpi->rounding;
	if (sf_constrounding != FPI_RoundNotSet)
		rd = sf_constrounding;
	if (sf.kind & SF_Neg && rd == FPI_Round_down)
		rd = FPI_Round_up;
	else if (sf.kind & SF_Neg && rd == FPI_Round_up)
		rd = FPI_Round_down;
	if (extra != 0) {
		doinc = rd == FPI_Round_up;
		if (rd == FPI_Round_near && extra == NORMALMANT)
			doinc = (int)sf.significand & 1;
		else if ((rd & 3) == FPI_Round_near && extra >= NORMALMANT)
			doinc = 1;
/* XXX set SFEXCP_Inex(hi|lo) ? later ? */
		if (doinc) {
			if (sf.significand == maxmant) {
				sf.significand = minmant;
				++exp;
			}
			else
				sf.significand++;
		}
	}
	else doinc = 0;

	if (exp < fpi->emin) {
/* XXX NO! IEEE754 says that if result is less than DBL_MIN but can be
 * represented exactly (as denormal), Underflow exception is NOT signaled.
 */
		sf.kind |= SFEXCP_Underflow;
		if (fpi->sudden_underflow || exp < fpi->emin - fpi->nbits)
			return zerosf(sf.kind | SFEXCP_Inexlo);
		if (doinc) {
			if (sf.significand == minmant) {
				sf.significand = maxmant;
				--exp;
			}
			else
				sf.significand--;
		}
		excess = fpi->emin - exp;
		z = rshiftdro(sf.significand, extra, excess);
/* XXX need to consider extra here... */
		doinc = rd == FPI_Round_up;
		if ((rd & 3) == FPI_Round_near) {
			if (z.lo > NORMALMANT)
				doinc = 1;
			else if (rd == FPI_Round_near && z.lo == NORMALMANT)
				doinc = (int)z.hi & 1;
			else if (rd == FPI_Round_near_from0 && z.lo == NORMALMANT)
				doinc = 1;
		}
		if (doinc) z.hi++;
/* XXX revise: it seems there should be a missed case where the delivered result
 * was DBL_MIN-DBL_EPSILON, thus just below the bar, but when rounded to the lower
 * precision of denormals it should be rounded up to normal...
 * (in the exact half case, note extra==0)
 */
		if (z.hi) {
			sf.significand = z.hi;
			sf.kind += SF_Denormal - SF_Normal;
			sf.kind |= doinc ? SFEXCP_Inexhi : SFEXCP_Inexlo;
			exp = fpi->emin;
		}
		else {
			sf = zerosf(sf.kind | SFEXCP_Inexlo);
			exp = 0;
		}
	}
	else if (exp > fpi->emax) {
		sf.kind |= SFEXCP_Overflow | SFEXCP_Inexhi;
		if (! fpi->has_inf_nan || rd == FPI_Round_zero || 
		    rd == FPI_Round_down) {
			sf.significand = maxmant;
			exp = fpi->emax;
		}
		else {
			sf.kind = SF_Infinite | (sf.kind & ~SF_kmask);
			sf.significand = minmant;
			exp = fpi->emax+1;
		}
	}
	else if (extra)
		sf.kind = doinc ? SFEXCP_Inexhi : SFEXCP_Inexlo;
	sf.exponent = exp;
	return sf;
}

/*
 * Conversions.
 */

/*
 * Convert from integer type f to floating-point type t.
 * Rounds correctly to the target type.
 */
SF
soft_int2fp(CONSZ l, TWORD f, TWORD t)
{
	SF rv;
	int64_t ll = l;
	uint64_t mant;
	int sign = 0, exp;

	if (!ISUNSIGNED(f) && ll < 0) {
		ll = -ll;
		sign = 1;
	}

	if (ll == 0) {
		LDOUBLE_ZERO(rv, 0);
	} else {
		exp = LDOUBLE_BIAS + 64;
		while (ll > 0)
			ll <<= 1, exp--;
		ll <<= 1, exp--;
		mant = ll;

		LDOUBLE_MAKE(rv, sign, exp, mant);
		if (t == FLOAT || t == DOUBLE)
			rv = soft_fp2fp(rv, t);
	}
#ifdef DEBUGFP
	{ long double dl;
		dl = ISUNSIGNED(f) ? (long double)(U_CONSZ)(l) :
		    (long double)(CONSZ)(l);
		dl = t == FLOAT ? (float)dl : t == DOUBLE ? (double)dl : dl;
		if (dl != rv.debugfp)
			fpwarn("soft_int2fp", rv.debugfp, dl);
	}
#endif
	return rv;
}

/*
 * Explicit cast into some floating-point format.
 */
SF
soft_fp2fp(SF sf, TWORD t)
{
	SF rv;

	if (t == DOUBLE) {
		rv = floatx80_to_float64(sf);
		rv = float64_to_floatx80(rv);
	} else if (t == FLOAT) {
		rv = floatx80_to_float32(sf);
//printf("soft_fp2fp: %f\n", (double)*(float *)&rv.debugfp);
		rv = float32_to_floatx80(rv);
//printf("soft_fp2fpX: %Lf\n", rv.debugfp);
	} else
		rv = sf;
//printf("soft_fp2fp: t %d\n", t);
#ifdef DEBUGFP
	{ long double l = (t == DOUBLE ? (double)sf.debugfp :
	    (t == FLOAT ? (float)sf.debugfp : sf.debugfp));
	if (memcmp(&l, &rv.debugfp, SZLD))
		fpwarn("soft_fp2fp", rv.debugfp, l);
	}
#endif
	return rv;
}

/*
 * Convert a fp number to a CONSZ. Always chop toward zero.
 */
CONSZ
soft_fp2int(SF sf, TWORD t)
{
	uint64_t mant;
	int exp;

	if (soft_classify(sf, LDOUBLE) != SOFT_NORMAL)
		return 0;
	
	exp = ldouble_exp(sf) - LDOUBLE_BIAS - 64 + 1;
	mant = ldouble_mant(sf);
	mant = (mant >> 1) | (1LL << 63);
	while (exp > 0)
		mant <<= 1, exp--;
	while (exp < 0)
		mant >>= 1, exp++;

	if (ldouble_sign(sf))
		mant = -(int64_t)mant;
#ifdef DEBUGFP
	{ uint64_t u = (uint64_t)sf.debugfp;
	  int64_t s = (int64_t)sf.debugfp;
		if (ISUNSIGNED(t)) {
			if (u != mant)
				fpwarn("soft_fp2int:u", 0.0, sf.debugfp);
		} else {
			if (s != (int64_t)mant)
				fpwarn("soft_fp2int:s", 0.0, sf.debugfp);
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
SF
soft_neg(SF sf)
{
	LDOUBLE_NEG(sf);
	return sf;
}

/*
 * IEEE754 operations on sign bit. Always well defined, even with NaN.
 */
CONSZ
soft_signbit(SF sf)
{
	return sf.kind & SF_Neg;
}

SF
soft_copysign(SF sf, SF src)
{
	SFCOPYSIGN(sf, src);
	return sf;
}

/*
 * Add two numbers of same sign.
 * The devil is in the details, like those negative zeroes...
 */
static SF
sfadd(SF x1, SF x2, TWORD t)
{
	SF rv;
	DULLong z;
	int diff;

	if (SFISINF(x1))
		return x1;
	if (SFISINF(x2))
		return x2;
	if (SFISZ(x2)) /* catches all signed zeroes, delivering x1 */
		return x1;
	if (SFISZ(x1))
		return x2;
	assert(x1.significand && x2.significand);
	SFNORMALIZE(x1);
	SFNORMALIZE(x2);
	if (x1.exponent - WORKBITS > x2.exponent) {
		x1.kind |= SFEXCP_Inexlo;
		return x1;
	}
	if (x2.exponent - WORKBITS > x1.exponent) {
		x2.kind |= SFEXCP_Inexlo;
		return x2;
	}
	diff = x1.exponent - x2.exponent;
	if (diff < 0) {
		rv = x2;
		z = rshiftdro(x1.significand, 0, -diff );
	}
	else {
		rv = x1;
		z = rshiftdro(x2.significand, 0, diff );
	}
	rv.significand += z.hi;
	if (rv.significand < NORMALMANT) {
		/* target mantissa overflows */
		z = rshiftdro(rv.significand, z.lo, 1);
		rv.significand = z.hi | NORMALMANT;
		++rv.exponent;
	}
	return sfround(rv, z.lo, t);
}

/*
 * Substract two positive numbers.
 * Special hack when the type number t being negative, to indicate
 * that rounding rules should be reversed (because the operands were.)
 */
static SF
sfsub(SF x1, SF x2, TWORD t)
{
	SF rv;
	DULLong z;
	int diff;

	if (SFISINF(x1) && SFISINF(x2))
		return nansf(x1.kind | SFEXCP_Invalid);
	if (SFISINF(x1))
		return x1;
	if (SFISINF(x2))
		return SFNEG(x2);
	if (SFISZ(x2)) /* catches 0 - 0, delivering +0 */
		return x1;
	if (SFISZ(x1))
		return SFNEG(x2);
	assert(x1.significand && x2.significand);
	SFNORMALIZE(x1);
	SFNORMALIZE(x2);
	if (x1.exponent - WORKBITS > x2.exponent) {
		x1.kind |= (int)t < 0 ? SFEXCP_Inexlo : SFEXCP_Inexhi;
		return x1;
	}
	if (x2.exponent - WORKBITS > x1.exponent) {
		x2.kind |= (int)t < 0 ? SFEXCP_Inexlo : SFEXCP_Inexhi;
		return SFNEG(x2);
	}
	diff = x1.exponent - x2.exponent;
	if (diff == 0 && x1.significand == x2.significand) {
		if ((int)t < 0)
			t = -(int)t;
/* XXX sf_constrounding */
		if ((fpis[t-FLOAT]->rounding & 3) == FPI_Round_down)
			return zerosf(SF_Neg | (x1.kind & ~SF_Neg));
		return zerosf(x1.kind & ~SF_Neg); /* x1==x2==-0 done elsewhere */
	}
	if (diff < 0 || (diff == 0 && x1.significand < x2.significand)) {
		rv = SFNEG(x2);
		z = rshiftdro(x1.significand, 0, -diff );
	}
	else {
		rv = x1;
		z = rshiftdro(x2.significand, 0, diff );
	}
	if ((rv.kind & SF_kmask) == SF_Denormal)
		rv.kind -= SF_Denormal - SF_Normal;
	rv.significand -= z.hi;
	if ((int)t < 0) {
		int rd;

		t = -(int)t;
		rd = fpis[t-FLOAT]->rounding;
/* XXX sf_constrounding */
		if ((rd & 3) == FPI_Round_up || (rd & 3) == FPI_Round_down) {
			rv = sfround(SFNEG(rv), z.lo, t);
			return SFNEG(rv);
		}
	}
	return sfround(rv, z.lo, t);
}

SF
soft_plus(SF x1, SF x2, TWORD t)
{
	MINT a, b, c;
	SF rv;

	if (LDOUBLE_ISINF(x1) && LDOUBLE_ISINF(x2)) {
		if (ldouble_sign(x1) == ldouble_sign(x2))
			return x1;
		LDOUBLE_NAN(x1,0);
		return x1;
	}
	if (LDOUBLE_ISNAN(x1) || LDOUBLE_ISINF(x1))
		return x1;
	if (LDOUBLE_ISNAN(x2) || LDOUBLE_ISNAN(x2))
		return x2;

	ldbl2mint(&a, x1);
//mdump("plus a", &a);
	ldbl2mint(&b, x2);
//mdump("plus b", &b);
	madd(&a, &b, &c);
//mdump("plus c", &c);
	rv = mint2ldbl(&c);
#ifdef DEBUGFP
	if (x1.debugfp + x2.debugfp != rv.debugfp)
		fpwarn("soft_plus", rv.debugfp, x1.debugfp + x2.debugfp);
#endif
	return rv;
}

SF
soft_minus(SF x1, SF x2, TWORD t)
{
	x1.kind |= x2.kind & SFEXCP_ALLmask;
	x2.kind |= x1.kind & SFEXCP_ALLmask;
	if (SFISNAN(x1))
		return x1;
	else if (SFISNAN(x2))
		return x2;
	if ((x1.kind & SF_Neg) != (x2.kind & SF_Neg))
		return sfadd(x1, SFNEG(x2), t);
	else if (SFISZ(x1) && SFISZ(x2))
		return x1; /* special case -0 - -0, should return -0 */
	else if (x1.kind & SF_Neg)
		return sfsub(SFNEG(x2), SFNEG(x1), - (int)t);
	else
		return sfsub(x1, x2, t);
}

/*
 * Multiply two softfloats.
 */
SF
soft_mul(SF x1, SF x2, TWORD t)
{
#if 0
	ULong x1hi, x2hi;
	ULLong mid1, mid, extra;
#else
	DULLong z;
#endif

	x1.kind |= x2.kind & SFEXCP_ALLmask;
	x2.kind |= x1.kind & SFEXCP_ALLmask;
	x1.kind ^= x2.kind & SF_Neg;
	SFCOPYSIGN(x2, x1);
	if (SFISNAN(x1))
		return x1;
	else if (SFISNAN(x2))
		return x2;
	if ((SFISINF(x1) && SFISZ(x2)) || (SFISZ(x1) && SFISINF(x2)))
		return nansf(x1.kind | SFEXCP_Invalid);
	if (SFISINF(x1) || SFISZ(x1))
		return x1;
	if (SFISINF(x2) || SFISZ(x2))
		return x2;
	assert(x1.significand && x2.significand);
	SFNORMALIZE(x1);
	SFNORMALIZE(x2);
	x1.exponent += x2.exponent + WORKBITS;
#if 0
	x1hi = x1.significand >> 32;
	x1.significand &= ONES(32);
	x2hi = x2.significand >> 32;
	x2.significand &= ONES(32);
	extra = x1.significand * x2.significand;
	mid1 = x1hi * x2.significand;
	mid = mid1 + x1.significand * x2hi;
	x1.significand = (ULLong) x1hi * x2hi;
	x1.significand += ((ULLong)(mid < mid1) << 32) | (mid >> 32);
	mid <<= 32;
	extra += mid;
#ifdef LONGLONG_WIDER_THAN_WORKBITS
	if (extra < mid || (extra>>WORKBITS)) {
		x1.significand++;
		extra &= ONES(WORKBITS);
	}
#else
	x1.significand += (extra < mid);
#endif
	if (x1.significand < NORMALMANT) {
		x1.exponent--;
		x1.significand <<= 1;
		if (extra >= NORMALMANT) {
			x1.significand++;
			extra -= NORMALMANT;
		}
		extra <<= 1;
	}
	return sfround(x1, extra, t);
#else
	z = muld(x1.significand, x2.significand);
	if (z.hi < NORMALMANT) {
		x1.exponent--;
		z = lshiftd(z.hi, z.lo, 1);
	}
	x1.significand = z.hi;
	return sfround(x1, z.lo, t);
#endif
}

SF
soft_div(SF x1, SF x2, TWORD t)
{
	ULLong q, r, oppx2;
	int exp;

	x1.kind |= x2.kind & SFEXCP_ALLmask;
	x2.kind |= x1.kind & SFEXCP_ALLmask;
	x1.kind ^= x2.kind & SF_Neg;
	SFCOPYSIGN(x2, x1);
	if (SFISNAN(x1))
		return x1;
	else if (SFISNAN(x2))
		return x2;
	if ((SFISINF(x1) && SFISINF(x2)) || (SFISZ(x1) && SFISZ(x2)))
		return nansf(x1.kind | SFEXCP_Invalid);
	if (SFISINF(x1) || SFISZ(x1))
		return x1;
	else if (SFISINF(x2))
		return zerosf(x1.kind);
	else if (SFISZ(x2))
		return infsf(x2.kind | SFEXCP_DivByZero);
	assert(x1.significand && x2.significand);
	SFNORMALIZE(x1);
	SFNORMALIZE(x2);
	exp = x1.exponent - x2.exponent - WORKBITS;
	if (exp < -32767)
		/* huge underflow, flush to 0 to avoid issues */
		return zerosf(x1.kind | SFEXCP_Inexlo | SFEXCP_Underflow);
	q = 0;
	if (x1.significand >= x2.significand) {
		++exp;
		++q;
		x1.significand -= x2.significand;
	}
	r = x1.significand;
	oppx2 = (ONES(WORKBITS-1) - x2.significand) + 1;
	do {
		q <<= 1;
		if (r & NORMALMANT) {
			r &= ~NORMALMANT;
			r <<= 1;
			r += oppx2;
			++q;
		}
		else {
			r <<= 1;
			if (r >= x2.significand) {
				r -= x2.significand;		
				++q;
			}
		}
	} while((q & NORMALMANT) == 0);
	x1.significand = q;
	x1.exponent = exp;
	if (r) {
		/* be sure to set correctly highest bit of extra */
		r += oppx2 / 2;
		r |= 1; /* rounds to odd */
/* XXX can remainder be power-of-2? doesn't seem it may happen... */
	}
	return sfround(x1, r, t);
}

#ifndef NO_COMPLEX
/*
 * Perform the addition or subtraction of two products of finite numbers.
 * Keep the extra bits (do not round).
 * Note that maximum return exponent is 2*emax+WORKBITS.
 */
#define FMMPLUS 	0
#define FMMMINUS	SF_Neg

static SF
finitemma(SF a, SF b, int op, SF c, SF d, ULLong * extrap)
{
	SF rv;
	DULLong z, z1, z2;
	int diff, z1k, z1exp, z2k, z2exp, excess;
	ULLong x;

	z1k = z2k = SF_Normal |
		(a.kind & SFEXCP_ALLmask) | (b.kind & SFEXCP_ALLmask) |
		(c.kind & SFEXCP_ALLmask) | (d.kind & SFEXCP_ALLmask);
	z1k |= (a.kind & SF_Neg) ^ (b.kind & SF_Neg);
	z2k |= (c.kind & SF_Neg) ^ (d.kind & SF_Neg) ^ op;
	assert(a.significand && b.significand && c.significand && d.significand);
	SFNORMALIZE(a);
	SFNORMALIZE(b);
	SFNORMALIZE(c);
	SFNORMALIZE(d);
	z1exp = a.exponent + b.exponent + WORKBITS;
	z2exp = c.exponent + d.exponent + WORKBITS;
#if 0
	if (z1exp - WORKBITS > z2exp) {
		x1.kind |= (int)t < 0 ? SFEXCP_Inexlo : SFEXCP_Inexhi;
		return x1;
	}
	if (z2exp - WORKBITS > z1exp) {
		x2.kind |= (int)t < 0 ? SFEXCP_Inexlo : SFEXCP_Inexhi;
		return SFNEG(x2);
	}
#endif
	z1 = muld(a.significand, b.significand);
	if (z1.hi < NORMALMANT) {
		z1exp--;
		z1 = lshiftd(z1.hi, z1.lo, 1);
	}
	z2 = muld(c.significand, d.significand);
	if (z2.hi < NORMALMANT) {
		z2exp--;
		z2 = lshiftd(z2.hi, z2.lo, 1);
	}
	diff = z1exp - z2exp;
	if (z1k == z2k) { /* same sign, add them; easier */
		rv.kind = z1k;
		if (diff < 0) {
			z = z2, z2 = z1, z1 = z;
			rv.exponent = z2exp;
		}
		else
			rv.exponent = z1exp;
		z2 = rshiftdro(z2.hi, z2.lo, diff );
		rv.significand = z1.hi + z2.hi;
		z1.lo += z2.lo;
		if (z1.lo < z2.lo)
			++rv.significand;
		if (rv.significand < NORMALMANT) {
			/* target mantissa overflows */
			z = rshiftdro(rv.significand, z1.lo, 1);
			rv.significand = z.hi | NORMALMANT;
			++rv.exponent;
		}
		else
			z.lo = z1.lo;
		*extrap = z.lo;
	}
	else { /* opposite sign, substraction, and possible cancellation */
		if (diff == 0 && z1.hi == z2.hi && z1.lo == z2.lo) {
			*extrap = 0;
/* XXX compute sign of 0 if rounding, merge exceptions... */
			return zerosf(z1k & ~SF_Neg);
		}
		else if (diff == 0 && z1.hi == z2.hi) {
			if (z1.lo > z2.lo) {
				rv.kind = z1k;
				rv.significand = z1.lo - z2.lo;
			}
			else {
				rv.kind = z2k;
				rv.significand = z2.lo - z1.lo;
			}
			rv.exponent = z1exp - WORKBITS;
			z.lo = 0;
		}
		else {
			if (diff < 0 || (diff == 0 && z1.hi < z2.hi)) {
				rv.kind = z2k ^ SF_Neg;
				rv.exponent = z2exp;
				if (diff != 0) {
					z = z2;
					z2 = rshiftdro(z1.hi, z1.lo, -diff );
					z1 = z;
				}
				else {
					z = z2, z2 = z1, z1 = z;
				}
			}
			else {
				rv.kind = z1k;
				rv.exponent = z1exp;
				if (diff != 0)
					z2 = rshiftdro(z2.hi, z2.lo, diff );
			}
			z.hi = z1.hi - z2.hi;
			if (z2.lo > z1.lo)
				--z.hi;
			z.lo = z1.lo - z2.lo;
			x = z.hi;
			for (excess = 0; x < NORMALMANT; ++excess)
				x <<= 1;
			z = lshiftd(z.hi, z.lo, excess);
			rv.exponent -= excess;
			rv.significand = z.hi;
		}
		*extrap = z.lo;
	}
	return rv;
}

#define CXSFISZ(r,i)	(SFISZ(r)   && SFISZ(i))
#define CXSFISINF(r,i)	(SFISINF(r) || SFISINF(i))
#define CXSFISNAN(r,i)	(!CXSFISINF(r,i) && (SFISNAN(r) || SFISNAN(i)))

/*
 * Multiply two complexes (pairs of softfloats)
 */
void
soft_cxmul(SF r1, SF i1, SF r2, SF i2, SF *rrv, SF *irv, TWORD t)
{
	SF sf;
	ULLong extra;

# if 0
	x1.kind |= x2.kind & SFEXCP_ALLmask;
	x2.kind |= x1.kind & SFEXCP_ALLmask;
	x1.kind ^= x2.kind & SF_Neg;
	SFCOPYSIGN(x2, x1);
#endif
	if (CXSFISINF(r1, i1)) {
		if (CXSFISZ(r2, i2)) {
			return;
		}
		else if (SFISNAN(r2) && SFISNAN(i2)) {
			return;
		}
		/* result is an infinity */
	}
	else if (CXSFISINF(r2, i2)) {
		if (CXSFISZ(r1, i1)) {
			return;
		}
		else if (SFISNAN(r1) && SFISNAN(i1)) {
			return;
		}
		/* result is an infinity */
	}

/* XXX missing many special cases with NaN or zeroes... */

	sf = finitemma(r1, r2, FMMMINUS, i1, i2, &extra);
	*rrv = sfround(sf, extra, t);
	sf = finitemma(r1, i2, FMMPLUS,  i1, r2, &extra);
	*irv = sfround(sf, extra, t);
}

/*
 * Divide two complexes (pairs of softfloats.) Indeed complex.
 */
/*
 * Helper function: division double by double
 * Result is correctly rounded.
 */
static SF
sfddiv(SF num, ULLong extran, SF den, ULLong extrad, TWORD t)
{
	DULLong zn, zd, r, oppden;
	ULLong q;
	int exp, excess;

#if 0
	num.kind |= den.kind & SFEXCP_ALLmask;
	den.kind |= num.kind & SFEXCP_ALLmask;
	num.kind ^= den.kind & SF_Neg;
	SFCOPYSIGN(den, num);
#endif
	assert(num.significand && den.significand);
	q = num.significand;
	for (excess = 0; q < NORMALMANT; ++excess)
		q <<= 1;
	zn = lshiftd(num.significand, extran, excess);
	num.exponent -= excess;
	q = den.significand;
	for (excess = 0; q < NORMALMANT; ++excess)
		q <<= 1;
	zd = lshiftd(den.significand, extrad, excess);
	den.exponent -= excess;
	exp = num.exponent - den.exponent - WORKBITS;
	if (exp < -32767) {
		/* huge underflow, flush to 0 to avoid issues */
		return zerosf(num.kind | SFEXCP_Inexlo | SFEXCP_Underflow);
	}
	q = 0;
	if (zn.hi >= zd.hi) {
		++exp;
		++q;
		zn.hi -= zd.hi;
	}
	r = zn;
	if (zd.lo) {
		oppden.hi = (ONES(WORKBITS-1) - zd.hi);
		oppden.lo = (ONES(WORKBITS-1) - zd.lo) + 1;
	}
	else {
		oppden.hi = (ONES(WORKBITS-1) - zd.hi) + 1;
		oppden.lo = 0;
	}
	do {
		q <<= 1;
		if (r.hi & NORMALMANT) {
			r.hi &= ~NORMALMANT;
			r = lshiftd(r.hi, r.lo, 1);
			r.hi += oppden.hi;
			r.lo += oppden.lo;
			if (r.lo < oppden.lo)
				++r.hi;
			++q;
		}
		else {
			r = lshiftd(r.hi, r.lo, 1);
			if (r.hi > zd.hi || (r.hi == zd.hi && r.lo >= zd.lo)) {
				r.hi -= zd.hi;
				if (zd.lo > r.lo)
					--r.hi;
				r.lo -= zd.lo;
				++q;
			}
		}
	} while((q & NORMALMANT) == 0);
	num.significand = q;
	num.exponent = exp;
	if (r.hi) {
		/* be sure to set correctly highest bit of extra */
		r.hi += oppden.hi / 2;
		r.hi |= 1; /* rounds to odd */
/* XXX is there special case if remainder is power-of-2? can it happen? */
	}
	return sfround(num, r.hi, t);
}

void
soft_cxdiv(SF r1, SF i1, SF r2, SF i2, SF *rrv, SF *irv, TWORD t)
{
	SF den, sf;
	ULLong extrad, extra;

	if (CXSFISINF(r1, i1)) {
		if (CXSFISINF(r2, i2)) {
			return;
		}
		else if (SFISNAN(r2) && SFISNAN(i2)) {
			return;
		}
		/* result is an infinity */
	}
	else if (CXSFISINF(r2, i2)) {
		if (SFISNAN(r1) && SFISNAN(i1)) {
			return;
		}
		/* result is zero */
	}
	else if (CXSFISZ(r2, i2)) {
		if (SFISNAN(r2) && SFISNAN(i2)) {
			return;
		}
		/* result is an infinity */
	}

/* XXX missing many special cases with NaN or zeroes... */

	den= finitemma(r2, r2, FMMPLUS,  i2, i2, &extrad);
	sf = finitemma(r1, r2, FMMPLUS,  i1, i2, &extra);
	*rrv = sfddiv(sf, extra, den, extrad, t);
	sf = finitemma(i1, r2, FMMMINUS, r1, i2, &extra);
	*irv = sfddiv(sf, extra, den, extrad, t);
}
#endif

/*
 * Classifications and comparisons.
 */

/*
 * Return true if fp number is zero. Easy.
 */
int
soft_isz(SF sf)
{
	int r = LDOUBLE_ISZ(sf);
#ifdef DEBUGFP
	if ((sf.debugfp == 0.0 && r == 0) || (sf.debugfp != 0.0 && r == 1))
		fpwarn("soft_isz", sf.debugfp, (long double)r);
#endif
	return r;
}

int
soft_isnan(SF sf)
{
	return (sf.kind & SF_kmask) >= SF_NaN;
}

/*
 * Do classification as in C99 7.12.3, for internal use.
 * No subnormal yet.
 */
int
soft_classify(SF sf, TWORD t)
{
	int rv;

	switch (t) {
	case FLOAT:
		if (FLOAT_ISINF(sf))
			rv = SOFT_INFINITE;
		else if (FLOAT_ISNAN(sf))
			rv = SOFT_NAN;
		else if (FLOAT_ISZERO(sf))
			rv = SOFT_ZERO;
		else
			rv = SOFT_NORMAL;
		break;

	case DOUBLE:	
		if (DOUBLE_ISINF(sf))
			rv = SOFT_INFINITE;
		else if (DOUBLE_ISNAN(sf))
			rv = SOFT_NAN;
		else if (DOUBLE_ISZERO(sf))
			rv = SOFT_ZERO;
		else
			rv = SOFT_NORMAL;
		break;

	case LDOUBLE:
		if (LDOUBLE_ISINF(sf))
			rv = SOFT_INFINITE;
		else if (LDOUBLE_ISNAN(sf))
			rv = SOFT_NAN;
		else if (LDOUBLE_ISZERO(sf))
			rv = SOFT_ZERO;
		else
			rv = SOFT_NORMAL;
		break;
	}
	return rv;
}

static int
soft_cmp_eq(SF x1, SF x2)
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
soft_cmp_gl(SF x1, SF x2, int isless)
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
soft_cmp(SF v1, SF v2, int v)
{
	int rv = 0;

	if (LDOUBLE_ISNAN(v1) || LDOUBLE_ISNAN(v2))
		return 0; /* never equal */

	switch (v) {
	case GT:
	case LT:
		rv = soft_cmp_gl(v1, v2, v == LT);
		break;
	case GE:
	case LE:
		if ((rv = soft_cmp_eq(v1, v2)))
			break;
		rv = soft_cmp_gl(v1, v2, v == LE);
		break;
	case EQ:
		rv = soft_cmp_eq(v1, v2);
		break;
	case NE:
		rv = !soft_cmp_eq(v1, v2);
		break;
	}
	return rv;
}

#endif /* FDFLOAT */

static void
vals2fp(SF *sf, int k, int exp, uint32_t *mant)
{
	int sign = (k & SF_Neg) != 0;
	uint64_t m;

	switch (k & SF_kmask) {
	case SF_Zero:
		LDOUBLE_ZERO((*sf), sign);
		break; /* already 0 */

	case SF_Normal:
		m = (((uint64_t)mant[1] << 32) | mant[0]) << 1;
//printf("vals2fp m %llx\n", m);
		exp += FPI_LDOUBLE.exp_bias;
		LDOUBLE_MAKE((*sf), sign, exp, m);
//printf("vals2fp: %llx %llx\n", *(long long *)&sf->debugfp, m);
#ifdef DEBUGFP
		if (mant[0] != sf->fp[0] || mant[1] != sf->fp[1])
			fpwarn("vals2fp", sf->debugfp, sf->debugfp);
#endif
		break;
	default:
		fprintf(stderr, "vals2fp: unhandled %x\n", k);
		break;
	}

	if (k & (SFEXCP_ALLmask & ~(SFEXCP_Inexlo|SFEXCP_Inexhi)))
		fprintf(stderr, "vals2fp: unhandled2 %x\n", k);
}

/*
 * Conversions from decimal and hexadecimal strings.
 * Rounds correctly to the target type (subject to FLT_EVAL_METHOD.)
 * dt is resulting type.
 */
SF
strtosf(char *str, TWORD tw)
{
	SF sf;
	char *eptr;
	ULong bits[2] = { 0, 0 };
	Long expt;
	int k;

	k = strtodg(str, &eptr, &FPI_LDOUBLE, &expt, bits);

	if (k & SFEXCP_Overflow)
		werror("Overflow in floating-point constant");
	if (k & SFEXCP_Inexact && (str[1] == 'x' || str[1] == 'X'))
		werror("Hexadecimal floating-point constant not exactly");
	vals2fp(&sf, k, expt, bits);
//printf("strtosf: %llx\n", *(long long *)&sf.debugfp);

#ifdef DEBUGFP
	{
		long double ld = strtold(str, NULL);
		if (ld != sf.debugfp)
			fpwarn("strtosf", sf.debugfp, ld);
	}
#endif

	return sf;
}

/*
 * return INF/NAN.
 */
SF
soft_huge_val(void)
{
	SF sf;

	LDOUBLE_INF(sf, 0);

#ifdef DEBUGFP
	if (sf.debugfp != __builtin_huge_vall())
		fpwarn("soft_huge_val", sf.debugfp, __builtin_huge_vall());
#endif
	return sf;
}

SF
soft_nan(char *c)
{
	SF sf;

	LDOUBLE_NAN(sf, 0);

	return sf;
}

/*
 * Return a LDOUBLE zero.
 */
SF
soft_zero()
{
	SF sf;

	LDOUBLE_ZERO(sf, 0);
	return sf;
}

/*
 * Convert internally stored floating point to fp type in TWORD.
 * Save as a static array of uint32_t.
 */
uint32_t *
soft_toush(SF osf, TWORD t)
{
	static SF sf;

//printf("soft_toush: osf %Lf %La t %d\n", osf.debugfp, osf.debugfp, t);
//printf("soft_toushLD: %x %x %x\n", osf.fp[2], osf.fp[1], osf.fp[0]);
//float d = osf.debugfp; printf("soft_toush-D: d %x %x\n", *(((int *)&d)+1), *(int *)&d);

	memset(&sf, 0, sizeof(SF));
	if (t == LDOUBLE) {
		sf = osf;
	} else if (t == DOUBLE) {
		sf = floatx80_to_float64(osf);
//printf("soft_toushD: sf %f\n", *(double *)&sf.debugfp);
//printf("soft_toushD2: %x %x\n", sf.fp[1], sf.fp[0]);
	} else /* if (t == FLOAT) */ {
		sf = floatx80_to_float32(osf);
//printf("soft_toushD: sf %f\n", (double)*(float *)&sf.debugfp);
//printf("soft_toushD2: %x\n", sf.fp[0]);
	}
#ifdef DEBUGFP
	{ float ldf; double ldd; long double ldt;
	ldt = (t == FLOAT ? (float)osf.debugfp :
	    t == DOUBLE ? (double)osf.debugfp : (long double)osf.debugfp);
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
minit(MINT *m)
{
	m->sign = 0;
	m->len = 0;
	memset(m->val, 0, MAXMINT);
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

	/* XXXXXXX must improve significantly */
	for (j = 0; j < nbits; j++) {
		if (a->val[a->len-1] & 0x8000) {
			if (a->len >= MAXMINT)
				fpwarn("mshl: shifting out", 0, 0);
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

