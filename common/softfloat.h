/*	$Id$	*/

/*
 * Copyright (c) 2015 Anders Magnusson. All rights reserved.
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

#include <stdint.h>

/*
 * Definitions for softfloat routines.
 *
 * Floating point numbers will always be stored as the largest supported
 * float type (long double).  This in turn will be stuffed bitwise into
 * an array of uint32_t for addressing.
 */
#ifndef CROSS_COMPILING
#define	DEBUGFP	/* compare everything with native fp */
#endif

typedef struct softfloat {
	union {
		uint32_t fp[(SZLDOUBLE+31)/32];
#ifdef DEBUGFP
		long double debugfp;
#endif
	};
} SF;
typedef SF *SFP;

#define C(x,y) C2(x,y)
#define C2(x,y) x##y

/*
 * These defines are used in cpp.
 */
#ifdef USE_IEEEFP_32
#define	IEEEFP_32_RADIX 2
#define IEEEFP_32_DIG 6
#define IEEEFP_32_EPSILON 1.19209290E-07F
#define IEEEFP_32_MAX_10_EXP +38
#define IEEEFP_32_MAX_EXP +128
#define IEEEFP_32_MAX 3.40282347E+38F
#define IEEEFP_32_MIN_10_EXP -37
#define IEEEFP_32_MIN_EXP -125
#define IEEEFP_32_MIN 1.17549435E-38F
#define IEEEFP_32_MANT_DIG 24
#define IEEEFP_32_HAS_SUBNORM 1
#endif
#ifdef USE_IEEEFP_64
#define IEEEFP_64_DIG 15
#define IEEEFP_64_EPSILON 2.22044604925031308085e-16
#define IEEEFP_64_MAX_10_EXP 308
#define IEEEFP_64_MAX_EXP 1024
#define IEEEFP_64_MAX 1.79769313486231570815e+308
#define IEEEFP_64_MIN_10_EXP (-307)
#define IEEEFP_64_MIN_EXP (-1021)
#define IEEEFP_64_MIN 2.22507385850720138309e-308
#define IEEEFP_64_MANT_DIG 53
#endif
#ifdef USE_IEEEFP_X80
#define IEEEFP_X80_DIG 18
#define IEEEFP_X80_EPSILON 1.08420217248550443401e-19L
#define IEEEFP_X80_MAX_10_EXP 4932
#define IEEEFP_X80_MAX_EXP 16384
#define IEEEFP_X80_MAX 1.18973149535723176502e+4932L
#define IEEEFP_X80_MIN_10_EXP (-4931)
#define IEEEFP_X80_MIN_EXP (-16381)
#define IEEEFP_X80_MIN 3.36210314311209350626e-4932L
#define IEEEFP_X80_MANT_DIG 64
#endif
#ifdef IEEEFP_128
#endif

#define	TARGET_FLT_RADIX	C(FLT_FP,_RADIX)

#ifndef CC_DRIVER
void soft_neg(SF *);
void soft_int2fp(SFP, CONSZ p, TWORD f, TWORD v);
CONSZ soft_fp2int(SF *p, TWORD v);
void soft_fp2fp(SFP p, TWORD v);
void soft_plus(SFP, SFP, TWORD);
void soft_minus(SFP, SFP, TWORD);
void soft_mul(SFP, SFP, TWORD);
void soft_div(SFP, SFP, TWORD);
int soft_cmp(SF*, SF*, int);
int soft_isz(SF*);
void strtosf(SFP, char *, TWORD);
CONSZ soft_signbit(SF sf);
int soft_isnan(SF sf);
void soft_huge_val(SFP);
void soft_nan(SFP, char *);
uint32_t *soft_toush(SFP, TWORD, int *);
#ifdef DEBUGFP
void fpwarn(const char *s, long double soft, long double hard);
#endif
#endif
