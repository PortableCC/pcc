/*	$Id$	*/

/*
 * Copyright (c) 2012 Anders Magnusson (ragge@ludd.luth.se).
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

#define CPPMDADD	{ "-D__x86_64__", "-D__x86_64", "-D__amd64__", \
	"-D__amd64", "-D__LP64__", "-D_LP64", NULL, }

/* fixup small m options */
#ifndef AMD64_64_EMUL
#define	AMD64_64_EMUL	"elf_x86_64"
#endif
#ifndef AMD64_32_EMUL
#define	AMD64_32_EMUL	"elf_i386"
#endif
#define PCC_EARLY_ARG_CHECK	{					\
	if (match(argp, "-m32")) {					\
		argp = "-m" AMD64_32_EMUL;				\
		strlist_append(&middle_linker_flags, argp);		\
		continue;						\
	} else if (match(argp, "-m64")) {				\
		argp = "-m" AMD64_64_EMUL;				\
		strlist_append(&middle_linker_flags, argp);		\
		continue;						\
	} else if (strncmp(argp, "-mcmodel", 9) == 0) {			\
		strlist_append(&compiler_flags, argp);			\
		continue;						\
	} else if (match(argp, "-melf_i386")) {				\
		pass0 = LIBEXECDIR "/ccom_i386";			\
		amd64_i386 = 1;						\
		continue;						\
	}								\
}

#define	TARGET_GLOBALS	int amd64_i386;

#define	TARGET_ASFLAGS	{ &amd64_i386, 1, "--32" },
