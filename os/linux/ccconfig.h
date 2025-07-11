/*	$Id$	*/

/*
 * Copyright (c) 2004 Anders Magnusson (ragge@ludd.luth.se).
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
 * Various settings that controls how the C compiler works.
 */

/* common cpp predefines */
#define CPPADD	{ "-D__linux__", "-D__ELF__", NULL, }

#define CRT0		"crt1.o"
#define GCRT0		"gcrt1.o"

#define STARTLABEL "_start"

#if defined(mach_arm)
#define CPPMDADD	{ "-D__arm__", NULL, }
#define	DYNLINKLIB	"/lib/ld-linux.so.2"
#elif defined(mach_i386)
#define CPPMDADD	{ "-D__i386__", NULL, }
#define	DYNLINKLIB	"/lib/ld-linux.so.2"
#define MUSL_DYLIB	"/lib/ld-musl-i386.so.1"
#elif defined(mach_powerpc)
#define CPPMDADD	{ "-D__ppc__", NULL, }
#define	DYNLINKLIB	"/lib/ld-linux.so.2"
#define MUSL_DYLIB	"/lib/ld-musl-powerpc.so.1"
#elif defined(mach_amd64)
#include "../inc/amd64.h"
#define	DYNLINKLIB	"/lib64/ld-linux-x86-64.so.2"
#define MUSL_DYLIB	"/lib/ld-musl-x86_64.so.1"
#ifndef MULTIARCH_PATH
#define	DEFLIBDIRS	{ "/usr/lib64/", 0 }
#else
#define	DEFLIBDIRS	{ "/usr/lib64/", "/usr/lib/" MULTIARCH_PATH "/", 0 }
#define	STDINC		"/usr/include", "/usr/include/x86_64-linux-gnu"
#endif
#elif defined(mach_mips)
#define CPPMDADD	{ "-D__mips__", NULL, }
#define	DYNLINKLIB	"/lib/ld.so.1"
#define MUSL_ROOT	"/lib/ld-musl-mips"
#define MUSL_EL		"el"
#define MUSL_SF		"-sf"
#elif defined(mach_aarch64)
#define CPPMDADD        { "-D__aarch64__", NULL, }
#define MUSL_DYLIB      "/lib/ld-musl-aarch64.so.1"
#elif defined(mach_m68k)
#define CPPMDADD        { "-D__m68k__", NULL, }
#else
#error defines for arch missing
#endif

/*
 * When USE_MUSL is defined, we either provide MUSL_DYLIB, or
 * code to construct the dynamic linker name at runtime
 */
#ifdef USE_MUSL
#ifdef MUSL_DYLIB
#define DYNLINKLIB MUSL_DYLIB
#else
#ifndef MUSL_EB
#define MUSL_EB	NULL
#endif
#ifndef MUSL_EL
#define MUSL_EL	NULL
#endif
#ifndef MUSL_SF
#define MUSL_SF	NULL
#endif
#ifndef MUSL_HF
#define MUSL_HF	NULL
#endif
#ifndef MUSL_EXT
#define MUSL_EXT ".so.1"
#endif

#define PCC_SETUP_LD_ARGS	{				\
		char *t = MUSL_ROOT;				\
		t = cat(t, bigendian ? MUSL_EB : MUSL_EL);	\
		t = cat(t, softfloat ? MUSL_SF : MUSL_HF);	\
		dynlinklib = cat(t, MUSL_EXT);			\
	}
#endif
#endif
