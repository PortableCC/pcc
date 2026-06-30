/*
 * Copyright (c) 2025 Michal Pleban.
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
 * Various settings that control how the C compiler works for
 * the Coherent OS on the Zilog Z8001 (Commodore 900).
 */

/* cpp predefines: Coherent identifies itself with these macros */
#define CPPADD		{ NULL }
#define CPPMDADD	{ "-DZ8001", "-Dcoherent", "-Dunix", NULL }

/* Startup object: segmented Z8001 C run-time start-off (csu/crts0.s),
 * entry point "start" which calls main_.  No ELF-style crti/crtn. */
#define CRT0		"/lib/crts0.o"
#define CRTBEGIN	0
#define CRTEND		0
#define CRTI		0
#define CRTN		0

/* Default library linked into every C program */
#define DEFLIBS		{ "-lc", 0 }

/*
 * Library search paths: /lib first, then /usr/lib.
 * Confirmed from linker source (_examples/cmd/ld/main.c).
 */
#define DEFLIBDIRS	{ "/lib/", "/usr/lib/", 0 }

/*
 * System include paths: /include first, then /usr/include.
 * Assembler and linker paths are not set here; they are
 * configured at build time via --with-assembler / --with-linker.
 */
#define STDINC		"/include/"
#define STDINCS		{ "/include/", "/usr/include/", 0 }
