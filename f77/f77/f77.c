/*	$Id$	*/

/*-
 * Copyright (c) 2011 Joerg Sonnenberger <joerg@NetBSD.org>.
 * All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * 1. Redistributions of source code must retain the above copyright
 *    notice, this list of conditions and the following disclaimer.
 * 2. Redistributions in binary form must reproduce the above copyright
 *    notice, this list of conditions and the following disclaimer in
 *    the documentation and/or other materials provided with the
 *    distribution.
 *
 * THIS SOFTWARE IS PROVIDED BY THE COPYRIGHT HOLDERS AND CONTRIBUTORS
 * ``AS IS'' AND ANY EXPRESS OR IMPLIED WARRANTIES, INCLUDING, BUT NOT
 * LIMITED TO, THE IMPLIED WARRANTIES OF MERCHANTABILITY AND FITNESS
 * FOR A PARTICULAR PURPOSE ARE DISCLAIMED.  IN NO EVENT SHALL THE
 * COPYRIGHT HOLDERS OR CONTRIBUTORS BE LIABLE FOR ANY DIRECT, INDIRECT,
 * INCIDENTAL, SPECIAL, EXEMPLARY OR CONSEQUENTIAL DAMAGES (INCLUDING,
 * BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS OR SERVICES;
 * LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION) HOWEVER CAUSED
 * AND ON ANY THEORY OF LIABILITY, WHETHER IN CONTRACT, STRICT LIABILITY,
 * OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING IN ANY WAY OUT
 * OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE POSSIBILITY OF
 * SUCH DAMAGE.
 */

/*
 * Copyright(C) Caldera International Inc. 2001-2002. All rights reserved.
 *
 * Redistribution and use in source and binary forms, with or without
 * modification, are permitted provided that the following conditions
 * are met:
 *
 * Redistributions of source code and documentation must retain the above
 * copyright notice, this list of conditions and the following disclaimer.
 * Redistributions in binary form must reproduce the above copyright
 * notice, this list of conditionsand the following disclaimer in the
 * documentation and/or other materials provided with the distribution.
 * All advertising materials mentioning features or use of this software
 * must display the following acknowledgement:
 * 	This product includes software developed or owned by Caldera
 *	International, Inc.
 * Neither the name of Caldera International, Inc. nor the names of other
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * USE OF THE SOFTWARE PROVIDED FOR UNDER THIS LICENSE BY CALDERA
 * INTERNATIONAL, INC. AND CONTRIBUTORS ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED.  IN NO EVENT SHALL CALDERA INTERNATIONAL, INC. BE LIABLE
 * FOR ANY DIRECT, INDIRECT INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OFLIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE 
 * POSSIBILITY OF SUCH DAMAGE.
 */

/*
 * Front-end to the fortran compiler.
 *
 * Brief description of its syntax:
 * - Files that end with .e are passed via efl->fcom->as->ld
 * - Files that end with .r are passed via ratfor->fcom->as->ld
 * - Files that end with .f are passed via fcom->as->ld
 * - Files that end with .s are passed via as->ld
 * - Files that end with .o are passed directly to ld
 * - Multiple files may be given on the command line.
 * -c or -S cannot be combined with -o if multiple files are given.
 *
 * This file should be rewritten readable.
 */
#include "config.h"

#include <sys/types.h>
#ifdef HAVE_SYS_WAIT_H
#include <sys/wait.h>
#endif

#include <ctype.h>
#include <errno.h>
#include <fcntl.h>
#include <signal.h>
#include <stdarg.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#ifdef HAVE_UNISTD_H
#include <unistd.h>
#endif
#include <assert.h>
#include <time.h>

#ifdef  _WIN32
#include <windows.h>
#include <process.h>
#include <io.h>
#define F_OK	0x00
#define R_OK	0x04
#define W_OK	0x02
#define X_OK	R_OK
#endif

#include "compat.h"

#include "macdefs.h"

#include "xalloc.h"
#include "strlist.h"

#include "ccconfig.h"
/* C command */

#define CC_DRIVER
#include "softfloat.h"	/* for CPP floating point macros */

#define	MKS(x) _MKS(x)
#define _MKS(x) #x

/* default program names in pcc */
/* May be overridden if cross-compiler is generated */
#ifndef FCOMPILER
#define FCOMPILER	"fcom"
#endif
#ifndef ASSEMBLER
#define ASSEMBLER	"as"
#endif
#ifndef LINKER
#define LINKER		"ld"
#endif
#define	EFL		"efl"
#define	RATFOR		"ratfor"

#ifndef CC2
#define CC2	"cc2"
#endif

char	*passp;	/* Set before call */
char	*fpass0 = FCOMPILER;
char	*as = ASSEMBLER;
char	*ld = LINKER;
char	*sysroot = "";


/* crt files using pcc default names */
#ifndef CRTBEGIN_S
#define	CRTBEGIN_S	"crtbeginS.o"
#endif
#ifndef CRTEND_S
#define	CRTEND_S	"crtendS.o"
#endif
#ifndef CRTBEGIN_T
#define	CRTBEGIN_T	"crtbeginT.o"
#endif
#ifndef CRTEND_T
#define	CRTEND_T	"crtendT.o"
#endif
#ifndef CRTBEGIN
#define	CRTBEGIN	"crtbegin.o"
#endif
#ifndef CRTEND
#define	CRTEND		"crtend.o"
#endif
#ifndef CRTI
#define	CRTI		"crti.o"
#endif
#ifndef CRTN
#define	CRTN		"crtn.o"
#endif
#ifndef CRT0
#define	CRT0		"crt0.o"
#endif
#ifndef GCRT0
#define	GCRT0		"gcrt0.o"
#endif
#ifndef RCRT0
#define	RCRT0		"rcrt0.o"
#endif

/* preprocessor stuff */
#ifndef STDINC
#define	STDINC	  	"/usr/include/"
#endif
#ifdef MULTIARCH_PATH
#define STDINC_MA	STDINC MULTIARCH_PATH "/"
#endif


char *cppadd[] = CPPADD;
char *cppmdadd[] = CPPMDADD;

/* Default libraries and search paths */
#ifndef PCCLIBDIR	/* set by autoconf */
#define PCCLIBDIR	NULL
#endif
#ifndef LIBDIR
#define LIBDIR		"/usr/lib/"
#endif
#ifndef DEFLIBDIRS	/* default library search paths */
#ifdef MULTIARCH_PATH
#define DEFLIBDIRS	{ LIBDIR, LIBDIR MULTIARCH_PATH "/", 0 }
#else
#define DEFLIBDIRS	{ LIBDIR, 0 }
#endif
#endif
#ifndef DEFLIBS		/* default libraries included */
#define	DEFLIBS		{ "-lF77", "-lI77", "-lm", "-lpcc", "-lc", "-lpcc", 0 }
#endif
#ifndef DEFPROFLIBS	/* default profiling libraries */
#define	DEFPROFLIBS	{ "-lF77", "-lI77", "-lm", "-lpcc", "-lc_p", "-lpcc", 0 }
#endif
#ifndef STARTLABEL
#define STARTLABEL	"__start"
#endif
#ifndef DYNLINKARG
#define DYNLINKARG	"-dynamic-linker"
#endif
#ifndef DYNLINKLIB
#define DYNLINKLIB	NULL
#endif

char *dynlinkarg = DYNLINKARG;
char *dynlinklib = DYNLINKLIB;
char *pcclibdir = PCCLIBDIR;
char *deflibdirs[] = DEFLIBDIRS;
char *deflibs[] = DEFLIBS;
char *defproflibs[] = DEFPROFLIBS;

char	*outfile, *MFfile, *fname;
static char **lav;
static int lac;
static char *find_file(const char *file, struct strlist *path, int mode);
static int preprocess_input(char *input, char *output, int dodep);
static int compile_input(char *input, char *output);
static int assemble_input(char *input, char *output);
static int run_linker(void);
static int strlist_exec(struct strlist *l);

char *cat(const char *, const char *);
char *setsuf(char *, char);
int getsuf(char *);
char *getsufp(char *s);
int main(int, char *[]);
void errorx(int, char *, ...);
int cunlink(char *);
void exandrm(char *);
void dexit(int);
void idexit(int);
char *gettmp(void);
void oerror(char *);
char *argnxt(char *, char *);
char *nxtopt(char *o);
void setup_fcom_flags(void);
void setup_as_flags(void);
void setup_ld_flags(void);
#ifdef  _WIN32
char *win32pathsubst(char *);
char *win32commandline(struct strlist *l);
#endif
int	sspflag;
int	freestanding;
int	Sflag;
int	cflag;
int	gflag;
int	rflag;
int	vflag;
int	noexec;	/* -### */
int	tflag;
int	Eflag;
int	Oflag;
int	kflag;	/* generate PIC/pic code */
#define F_PIC	1
#define F_pic	2
int	pgflag;
int	pieflag;
int	Xflag;
int	nostartfiles, Bstatic, shared;
int	printprogname, printfilename, printsearchdirs;

#ifdef SOFTFLOAT
int	softfloat = 1;
#else
int	softfloat = 0;
#endif

#define	match(a,b)	(strcmp(a,b) == 0)

#ifndef USHORT
/* copied from mip/manifest.h */
#define	USHORT		5
#define	INT		6
#define	UNSIGNED	7
#endif

/*
 * Wide char defines.
 */
#if WCHAR_TYPE == USHORT
#define	WCT "short unsigned int"
#define WCM "65535U"
#if WCHAR_SIZE != 2
#error WCHAR_TYPE vs. WCHAR_SIZE mismatch
#endif
#elif WCHAR_TYPE == INT
#define WCT "int"
#define WCM "2147483647"
#if WCHAR_SIZE != 4
#error WCHAR_TYPE vs. WCHAR_SIZE mismatch
#endif
#elif WCHAR_TYPE == UNSIGNED
#define WCT "unsigned int"
#define WCM "4294967295U"
#if WCHAR_SIZE != 4
#error WCHAR_TYPE vs. WCHAR_SIZE mismatch
#endif
#else
#error WCHAR_TYPE not defined or invalid
#endif

#ifdef GCC_COMPAT
#ifndef REGISTER_PREFIX
#define REGISTER_PREFIX ""
#endif
#ifndef USER_LABEL_PREFIX
#define USER_LABEL_PREFIX ""
#endif
#endif

#ifndef PCC_WINT_TYPE
#define PCC_WINT_TYPE "unsigned int"
#endif

#ifndef PCC_SIZE_TYPE
#define PCC_SIZE_TYPE "unsigned long"
#endif

#ifndef PCC_PTRDIFF_TYPE
#define PCC_PTRDIFF_TYPE "long int"
#endif


struct strlist preprocessor_flags;
struct strlist depflags;
struct strlist incdirs;
struct strlist user_sysincdirs;
struct strlist includes;
struct strlist sysincdirs;
struct strlist dirafterdirs;
struct strlist crtdirs;
struct strlist libdirs;
struct strlist progdirs;
struct strlist early_linker_flags;
struct strlist middle_linker_flags;
struct strlist late_linker_flags;
struct strlist inputs;
struct strlist assembler_flags;
struct strlist temp_outputs;
struct strlist compiler_flags;

int
main(int argc, char *argv[])
{
	struct string *s;
	char *t, *argp;
	char *msuffix;
	int ninput, j;

	lav = argv;
	lac = argc;
	ninput = 0;

	strlist_init(&crtdirs);
	strlist_init(&libdirs);
	strlist_init(&progdirs);
	strlist_init(&preprocessor_flags);
	strlist_init(&incdirs);
	strlist_init(&user_sysincdirs);
	strlist_init(&includes);
	strlist_init(&sysincdirs);
	strlist_init(&dirafterdirs);
	strlist_init(&depflags);
	strlist_init(&early_linker_flags);
	strlist_init(&middle_linker_flags);
	strlist_init(&late_linker_flags);
	strlist_init(&inputs);
	strlist_init(&assembler_flags);
	strlist_init(&temp_outputs);
	strlist_init(&compiler_flags);

	if ((t = strrchr(argv[0], '/')))
		t++;
	else
		t = argv[0];

#ifdef F77_EARLY_SETUP
	F77_EARLY_SETUP
#endif

#ifdef _WIN32
	/* have to prefix path early.  -B may override */
	incdir = win32pathsubst(incdir);
	altincdir = win32pathsubst(altincdir);
	libdir = win32pathsubst(libdir);
#ifdef PCCINCDIR
	pccincdir = win32pathsubst(pccincdir);
	pxxincdir = win32pathsubst(pxxincdir);
#endif
#ifdef PCCLIBDIR
	pcclibdir = win32pathsubst(pcclibdir);
#endif
	passp = win32pathsubst(passp);
	pass0 = win32pathsubst(pass0);
#ifdef STARTFILES
	for (i = 0; startfiles[i] != NULL; i++)
		startfiles[i] = win32pathsubst(startfiles[i]);
	for (i = 0; endfiles[i] != NULL; i++)
		endfiles[i] = win32pathsubst(endfiles[i]);
#endif
#ifdef STARTFILES_T
	for (i = 0; startfiles_T[i] != NULL; i++)
		startfiles_T[i] = win32pathsubst(startfiles_T[i]);
	for (i = 0; endfiles_T[i] != NULL; i++)
		endfiles_T[i] = win32pathsubst(endfiles_T[i]);
#endif
#ifdef STARTFILES_S
	for (i = 0; startfiles_S[i] != NULL; i++)
		startfiles_S[i] = win32pathsubst(startfiles_S[i]);
	for (i = 0; endfiles_S[i] != NULL; i++)
		endfiles_S[i] = win32pathsubst(endfiles_S[i]);
#endif
#endif

	while (--lac) {
		++lav;
		argp = *lav;

#ifdef F77_EARLY_ARG_CHECK
		F77_EARLY_ARG_CHECK
#endif

		if (*argp != '-' || match(argp, "-")) {
			/* Check for duplicate .o files. */
			if (getsuf(argp) == 'o') {
				j = 0;
				STRLIST_FOREACH(s, &inputs)
					if (match(argp, s->value))
						j++;
				if (j)
					continue; /* skip it */
			}
			strlist_append(&inputs, argp);
			ninput++;
			continue;
		}

		switch (argp[1]) {
		default:
			oerror(argp);
			break;

		case '#':
			if (match(argp, "-###")) {
				printf("%s\n", VERSSTR);
				vflag++;
				noexec++;
			} else
				oerror(argp);
			break;

		case '-': /* double -'s */
			if (match(argp, "--version")) {
				printf("%s\n", VERSSTR);
				return 0;
			} else if (strncmp(argp, "--sysroot=", 10) == 0) {
				sysroot = argp + 10;
			} else if (strncmp(argp, "--sysroot", 9) == 0) {
				sysroot = nxtopt(argp);
			} else if (strcmp(argp, "--param") == 0) {
				/* NOTHING YET */;
				(void)nxtopt(0); /* ignore arg */
			} else
				oerror(argp);
			break;

		case 'B': /* other search paths for binaries */
			t = nxtopt("-B");
			strlist_append(&crtdirs, t);
			strlist_append(&libdirs, t);
			strlist_append(&progdirs, t);
			break;

		case 'c':
			cflag++;
			break;

		case 'd': /* debug options */
			if (match(argp, "-dumpmachine")) {
 				/* Print target and immediately exit */
 				puts(TARGSTR);
 				exit(0);
 			}
 			if (match(argp, "-dumpversion")) {
 				/* Print claimed gcc level, immediately exit */
 				puts("4.3.1");
 				exit(0);
 			}
			for (t = &argp[2]; *t; t++) {
				if (*t == 'M')
					strlist_append(&preprocessor_flags, "-dM");

				/* ignore others */
			}
			break;

		case 'g': /* create debug output */
			if (argp[2] == '0')
				gflag = 0;
			else
				gflag++;
			break;


		case 'X':
			Xflag++;
			break;

		case 'k': /* generate PIC code */
			kflag = argp[2] ? argp[2] - '0' : F_pic;
			break;

		case 'l':
		case 'L':
			if (argp[2] == 0)
				argp = cat(argp, nxtopt(0));
			strlist_append(&inputs, argp);
			break;

		case 'p':
			if (strcmp(argp, "-pg") == 0 ||
			    strcmp(argp, "-p") == 0)
				pgflag++;
			else
				oerror(argp);
			break;

		case 'S':
			Sflag++;
			cflag++;
			break;

		case 'o':
			if (outfile)
				errorx(8, "too many -o");
			outfile = nxtopt("-o");
			break;

		case 'O':
			Oflag = 1;	/* optimize */
			break;

		case 'v':
			printf("%s\n", VERSSTR);
			vflag++;
			break;

		case 'w': /* no warnings at all emitted */
			strlist_append(&compiler_flags, "-w");
			break;

		}
		continue;

	}

	if (ninput == 0)
		errorx(8, "no input files");
	if (outfile && (cflag || Sflag) && ninput > 1)
		errorx(8, "-o given with -c || -S and more than one file");

	if (signal(SIGINT, SIG_IGN) != SIG_IGN)	/* interrupt */
		signal(SIGINT, idexit);
	if (signal(SIGTERM, SIG_IGN) != SIG_IGN)	/* terminate */
		signal(SIGTERM, idexit);

	/* after arg parsing */
	strlist_append(&progdirs, LIBEXECDIR);
	if (pcclibdir)
		strlist_append(&crtdirs, pcclibdir);
	for (j = 0; deflibdirs[j]; j++) {
		if (sysroot)
			deflibdirs[j] = cat(sysroot, deflibdirs[j]);
		strlist_append(&crtdirs, deflibdirs[j]);
	}

	setup_fcom_flags();
	setup_as_flags();

	msuffix = NULL;
	STRLIST_FOREACH(s, &inputs) {
		char *suffix;
		char *ifile, *ofile = NULL;

		ifile = s->value;
		if (ifile[0] == ')') { /* -x source type given */
			msuffix = ifile[1] ? &ifile[1] : NULL;
			continue;
		}
		if (ifile[0] == '-' && ifile[1] == 0)
			suffix = msuffix ? msuffix : "c";
		else if (ifile[0] == '-')
			suffix = "o"; /* source files cannot begin with - */
		else if (msuffix)
			suffix = msuffix;
		else
			suffix = getsufp(ifile);
		/*
		 * C preprocessor
		 */
		if (match(suffix, "e") || match(suffix, "r")) {
			/* find out next output file */
			/* to temp file */
			passp = match(suffix, "e") ? EFL : RATFOR;
			if (preprocess_input(ifile, ofile, 0))
				exandrm(ofile);
			ifile = ofile;
			suffix = "f";
		}

		/*
		 * C compiler
		 */
		if (match(suffix, "f")) {
			/* find out next output file */
			if (Sflag) {
				ofile = outfile;
				if (outfile == NULL)
					ofile = setsuf(s->value, 's');
			} else
				strlist_append(&temp_outputs, ofile = gettmp());
			if (compile_input(ifile, ofile))
				exandrm(ofile);
			if (Sflag)
				continue;
			ifile = ofile;
			suffix = "s";
		}

		/*
		 * Assembler
		 */
		if (match(suffix, "s")) {
			if (cflag) {
				ofile = outfile;
				if (ofile == NULL)
					ofile = setsuf(s->value, 'o');
			} else {
				strlist_append(&temp_outputs, ofile = gettmp());
				/* strlist_append linker */
			}
			if (assemble_input(ifile, ofile))
				exandrm(ofile);
			ifile = ofile;
		}

		strlist_append(&middle_linker_flags, ifile);
	}

	if (cflag)
		dexit(0);

	/*
	 * Linker
	 */
	setup_ld_flags();
	if (run_linker())
		exandrm(0);

#ifdef notdef
	strlist_free(&crtdirs);
	strlist_free(&libdirs);
	strlist_free(&progdirs);
	strlist_free(&incdirs);
	strlist_free(&preprocessor_flags);
	strlist_free(&user_sysincdirs);
	strlist_free(&includes);
	strlist_free(&sysincdirs);
	strlist_free(&dirafterdirs);
	strlist_free(&depflags);
	strlist_free(&early_linker_flags);
	strlist_free(&middle_linker_flags);
	strlist_free(&late_linker_flags);
	strlist_free(&inputs);
	strlist_free(&assembler_flags);
	strlist_free(&temp_outputs);
	strlist_free(&compiler_flags);
#endif
	dexit(0);
	return 0;
}

/*
 * exit and cleanup after interrupt.
 */
void
idexit(int arg)
{
	dexit(100);
}

/*
 * exit and cleanup.
 */
void
dexit(int eval)
{
	struct string *s;

	if (!Xflag) {
		STRLIST_FOREACH(s, &temp_outputs)
			cunlink(s->value);
	}
	exit(eval);
}

/*
 * Called when something failed.
 */
void
exandrm(char *s)
{
	if (s && *s)
		strlist_append(&temp_outputs, s);
	dexit(1);
}

/*
 * complain and exit.
 */
void
errorx(int eval, char *s, ...)
{
	va_list ap;

	va_start(ap, s);
	fputs("error: ", stderr);
	vfprintf(stderr, s, ap);
	putc('\n', stderr);
	va_end(ap);
	dexit(eval);
}

static char *
find_file(const char *file, struct strlist *path, int mode)
{
	struct string *s;
	char *f;
	size_t lf, lp;
	int need_sep;

	lf = strlen(file);
	STRLIST_FOREACH(s, path) {
		lp = strlen(s->value);
		need_sep = (lp && s->value[lp - 1] != '/') ? 1 : 0;
		f = xmalloc(lp + lf + need_sep + 1);
		memcpy(f, s->value, lp);
		if (need_sep)
			f[lp] = '/';
		memcpy(f + lp + need_sep, file, lf + 1);
		if (access(f, mode) == 0)
			return f;
		free(f);
	}
	return xstrdup(file);
}

#ifdef HAVE_CC2
#ifdef NEED_CC2
#define	C2check	1
#else
#define	C2check	Oflag
#endif
#else
#define	C2check	0
#endif

#ifdef TWOPASS
static int
compile_input(char *input, char *output)
{
	struct strlist args;
	char *tfile;
	int retval;

	strlist_append(&temp_outputs, tfile = gettmp());

	strlist_init(&args);
	strlist_append_list(&args, &compiler_flags);
	strlist_append(&args, input);
	strlist_append(&args, tfile);
	strlist_prepend(&args,
	    find_file(cxxflag ? CXX0 : CC0, &progdirs, X_OK));
	retval = strlist_exec(&args);
	strlist_free(&args);
	if (retval)
		return retval;

	strlist_init(&args);
	strlist_append_list(&args, &compiler_flags);
	strlist_append(&args, tfile);
	strlist_append(&args, output);
	strlist_prepend(&args,
	    find_file(cxxflag ? CXX1: CC1, &progdirs, X_OK));
	retval = strlist_exec(&args);
	strlist_free(&args);
	return retval;
}
#else
static int
compile_input(char *input, char *output)
{
	struct strlist args;
	char *tfile;
	int retval;

	tfile = output;
	if (C2check)
		strlist_append(&temp_outputs, tfile = gettmp());

	strlist_init(&args);
	strlist_append_list(&args, &compiler_flags);
	strlist_append(&args, input);
	strlist_append(&args, tfile);
	strlist_prepend(&args, find_file(fpass0, &progdirs, X_OK));
	retval = strlist_exec(&args);
	strlist_free(&args);
	if (retval)
		return retval;
	if (C2check) {
		strlist_init(&args);
		strlist_append(&args, tfile);
		strlist_append(&args, output);
		strlist_prepend(&args, find_file(CC2, &progdirs, X_OK));
		retval = strlist_exec(&args);
		strlist_free(&args);
	}
	return retval;
}
#endif

static int
assemble_input(char *input, char *output)
{
	struct strlist args;
	int retval;

	strlist_init(&args);
#ifdef PCC_EARLY_AS_ARGS
	PCC_EARLY_AS_ARGS
#endif
	strlist_append_list(&args, &assembler_flags);
	strlist_append(&args, "-o");
	strlist_append(&args, output);
	strlist_append(&args, input);
	strlist_prepend(&args,
	    find_file(as, &progdirs, X_OK));
#ifdef PCC_LATE_AS_ARGS
	PCC_LATE_AS_ARGS
#endif
	retval = strlist_exec(&args);
	strlist_free(&args);
	return retval;
}

static int
preprocess_input(char *input, char *output, int dodep)
{
	struct strlist args;
	int retval;

	strlist_init(&args);
	strlist_append_list(&args, &preprocessor_flags);
	strlist_append(&args, input);
	if (output)
		strlist_append(&args, output);

	strlist_prepend(&args, find_file(passp, &progdirs, X_OK));
	retval = strlist_exec(&args);
	strlist_free(&args);
	return retval;
}

static int
run_linker(void)
{
	struct strlist linker_flags;
	int retval;

	if (outfile) {
		strlist_prepend(&early_linker_flags, outfile);
		strlist_prepend(&early_linker_flags, "-o");
	}
	strlist_init(&linker_flags);
	strlist_append_list(&linker_flags, &early_linker_flags);
	strlist_append_list(&linker_flags, &middle_linker_flags);
	strlist_append_list(&linker_flags, &late_linker_flags);
	strlist_prepend(&linker_flags, find_file(ld, &progdirs, X_OK));

	retval = strlist_exec(&linker_flags);

	strlist_free(&linker_flags);
	return retval;
}

char *
getsufp(char *s)
{
	register char *p;

	if ((p = strrchr(s, '.')) && p[1] != '\0')
		return &p[1];
	return "";
}

int
getsuf(char *s)
{
	register char *p;

	if ((p = strrchr(s, '.')) && p[1] != '\0' && p[2] == '\0')
		return p[1];
	return(0);
}

/*
 * Get basename of string s, copy it and change its suffix to ch.
 */
char *
setsuf(char *s, char ch)
{
	char *e, *p, *rp;

	e = NULL;
	for (p = s; *p; p++) {
		if (*p == '/')
			s = p + 1;
		if (*p == '.')
			e = p;
	}
	if (s > e)
		e = p;

	rp = p = xmalloc(e - s + 3);
	while (s < e)
		*p++ = *s++;

	*p++ = '.';
	*p++ = ch;
	*p = '\0';
	return rp;
}

#ifdef _WIN32

static int
strlist_exec(struct strlist *l)
{
	char *cmd;
	STARTUPINFO si;
	PROCESS_INFORMATION pi;
	DWORD exitCode;
	BOOL ok;

	cmd = win32commandline(l);
	if (vflag)
		printf("%s\n", cmd);
	if (noexec)
		return 0;

	ZeroMemory(&si, sizeof(STARTUPINFO));
	si.cb = sizeof(STARTUPINFO);
	ZeroMemory(&pi, sizeof(PROCESS_INFORMATION));

	ok = CreateProcess(NULL,  // the executable program
		cmd,   // the command line arguments
		NULL,       // ignored
		NULL,       // ignored
		TRUE,       // inherit handles
		HIGH_PRIORITY_CLASS,
		NULL,       // ignored
		NULL,       // ignored
		&si,
		&pi);

	if (!ok)
		errorx(100, "Can't find %s\n", STRLIST_FIRST(l)->value);

	WaitForSingleObject(pi.hProcess, INFINITE);
	GetExitCodeProcess(pi.hProcess, &exitCode);
	CloseHandle(pi.hProcess);
	CloseHandle(pi.hThread);

	return (exitCode != 0);
}

#else

static int
strlist_exec(struct strlist *l)
{
	sig_atomic_t exit_now = 0;
	sig_atomic_t child;
	char **argv;
	size_t argc;
	ssize_t result;
	int rv;

	strlist_make_array(l, &argv, &argc);
	if (vflag) {
		printf("Calling ");
		strlist_print(l, stdout, noexec, " ");
		printf("\n");
	}
	if (noexec)
		return 0;

	switch ((child = fork())) {
	case 0:
		execvp(argv[0], argv);
		result = write(STDERR_FILENO, "Exec of ", 8);
		result = write(STDERR_FILENO, argv[0], strlen(argv[0]));
		result = write(STDERR_FILENO, " failed\n", 8);
		(void)result;
		_exit(127);
	case -1:
		errorx(1, "fork failed");
	default:
		while (waitpid(child, &rv, 0) == -1 && errno == EINTR)
			/* nothing */(void)0;
		rv = WEXITSTATUS(rv);
		if (rv)
			errorx(1, "%s terminated with status %d", argv[0], rv);
		while (argc-- > 0)
			free(argv[argc]);
		free(argv);
		break;
	}
	return exit_now;
}

#endif

/*
 * Catenate two (optional) strings together
 */
char *
cat(const char *a, const char *b)
{
	size_t len;
	char *rv;

	len = (a ? strlen(a) : 0) + (b ? strlen(b) : 0) + 1;
	rv = xmalloc(len);
	snprintf(rv, len, "%s%s", (a ? a : ""), (b ? b : ""));
	return rv;
}

int
cunlink(char *f)
{
	if (f==0 || Xflag)
		return(0);
	return (unlink(f));
}

#ifdef _WIN32
char *
gettmp(void)
{
	DWORD pathSize;
	char pathBuffer[MAX_PATH + 1];
	char tempFilename[MAX_PATH];
	UINT uniqueNum;

	pathSize = GetTempPath(sizeof(pathBuffer), pathBuffer);
	if (pathSize == 0 || pathSize > sizeof(pathBuffer))
		pathBuffer[0] = '\0';
	uniqueNum = GetTempFileName(pathBuffer, "ctm", 0, tempFilename);
	if (uniqueNum == 0)
		errorx(8, "GetTempFileName failed: path \"%s\"", pathBuffer);

	return xstrdup(tempFilename);
}

#else

char *
gettmp(void)
{
	char *sfn = xstrdup("/tmp/ctm.XXXXXX");
	int fd = -1;

	if ((fd = mkstemp(sfn)) == -1)
		errorx(8, "%s: %s\n", sfn, strerror(errno));
	close(fd);
	return sfn;
}
#endif

void
oerror(char *s)
{
	errorx(8, "unknown option '%s'", s);
}

/*
 * See if m matches the beginning of string str, if it does return the
 * remaining of str, otherwise NULL.
 */
char *
argnxt(char *str, char *m)
{
	if (strncmp(str, m, strlen(m)))
		return NULL; /* No match */
	return str + strlen(m);
}

/*
 * Return next argument to option, or complain.
 */
char *
nxtopt(char *o)
{
	size_t l;

	if (o != NULL) {
		l = strlen(o);
		if (lav[0][l] != 0)
			return &lav[0][l];
	}
	if (lac == 1)
		errorx(8, "missing argument to '%s'", o);
	lav++;
	lac--;
	return lav[0];
}

struct flgcheck {
	int *flag;
	int set;
	char *def;
};

static void
cksetflags(struct flgcheck *fs, struct strlist *sl, int which)
{
	void (*fn)(struct strlist *, const char *);

	fn = which == 'p' ? strlist_prepend : strlist_append;
	for (; fs->flag; fs++) {
		if (fs->set && *fs->flag)
			fn(sl, fs->def);
		if (!fs->set && !*fs->flag)
			fn(sl, fs->def);
	}
}

struct flgcheck fcomflgcheck[] = {
	{ &Oflag, 1, "-xtemps" },
	{ &Oflag, 1, "-xdeljumps" },
	{ &Oflag, 1, "-xinline" },
	{ &Oflag, 1, "-xdce" },
	{ &Oflag, 1, "-xssa" },
	{ &pgflag, 1, "-p" },
	{ &gflag, 1, "-g" },
	{ 0 }
};

void
setup_fcom_flags(void)
{

	cksetflags(fcomflgcheck, &compiler_flags, 'a');
}

#if defined(USE_YASM) || defined(os_win32) || defined(os_darwin) || \
	(defined(os_sunos) && defined(mach_sparc64))
static int one = 1;
#endif

struct flgcheck asflgcheck[] = {
#if defined(USE_YASM)
	{ &one, 1, "-p" },
	{ &one, 1, "gnu" },
	{ &one, 1, "-f" },
#if defined(os_win32)
	{ &one, 1, "win32" },
#elif defined(os_darwin)
	{ &one, 1, "macho" },
#else
	{ &one, 1, "elf" },
#endif
#endif
#if defined(os_sunos) && defined(mach_sparc64)
	{ &one, 1, "-m64" },
#endif
#if defined(os_darwin)
	{ &Bstatic, 1, "-static" },
#endif
#if !defined(USE_YASM) && !defined(NO_AS_V)
	{ &vflag, 1, "-v" },
#endif
#if defined(os_openbsd) && defined(mach_mips64)
	{ &kflag, 1, "-KPIC" },
#else
	{ &kflag, 1, "-k" },
#endif
#ifdef os_darwin
	{ &one, 1, "-arch" },
#if mach_amd64
	{ &amd64_i386, 1, "i386" },
	{ &amd64_i386, 0, "x86_64" },
#else
	{ &one, 1, "i386" },
#endif
#else
#ifdef mach_amd64
	{ &amd64_i386, 1, "--32" },
#endif
#endif
	{ 0 }
};
void
setup_as_flags(void)
{
#ifdef PCC_SETUP_AS_ARGS
	PCC_SETUP_AS_ARGS
#endif
	cksetflags(asflgcheck, &assembler_flags, 'a');
}

struct flgcheck ldflgcheck[] = {
#ifndef MSLINKER
	{ &vflag, 1, "-v" },
#endif
#ifdef os_darwin
	{ &shared, 1, "-dylib" },
#elif defined(os_win32)
	{ &shared, 1, "-Bdynamic" },
#else
	{ &shared, 1, "-shared" },
#endif
#if !defined(os_sunos) && !defined(os_win32)
#ifndef os_darwin
	{ &shared, 0, "-d" },
#endif
#endif
#ifdef os_darwin
	{ &Bstatic, 1, "-static" },
#else
	{ &Bstatic, 1, "-Bstatic" },
#endif
#if !defined(os_darwin) && !defined(os_sunos)
	{ &gflag, 1, "-g" },
#endif
	{ 0 },
};

static void
strap(struct strlist *sh, struct strlist *cd, char *n, int where)
{
	void (*fn)(struct strlist *, const char *);
	char *fil;

	if (n == 0)
		return; /* no crtfile */

	fn = where == 'p' ? strlist_prepend : strlist_append;
	fil = find_file(n, cd, R_OK);
	(*fn)(sh, fil);
}

void
setup_ld_flags(void)
{
	char *b, *e;
	int i;

#ifdef PCC_SETUP_LD_ARGS
	PCC_SETUP_LD_ARGS
#endif

	cksetflags(ldflgcheck, &early_linker_flags, 'a');
	if (Bstatic == 0 && shared == 0 && rflag == 0) {
		if (dynlinklib) {
			strlist_append(&early_linker_flags, dynlinkarg);
			strlist_append(&early_linker_flags, dynlinklib);
		}
#ifndef os_darwin
		strlist_append(&early_linker_flags, "-e");
		strlist_append(&early_linker_flags, STARTLABEL);
#endif
	}
	if (shared == 0 && rflag)
		strlist_append(&early_linker_flags, "-r");
#ifdef STARTLABEL_S
	if (shared == 1) {
		strlist_append(&early_linker_flags, "-e");
		strlist_append(&early_linker_flags, STARTLABEL_S);
	}
#endif
	if (sysroot && *sysroot)
		strlist_append(&early_linker_flags, cat("--sysroot=", sysroot));
	/* library search paths */
	if (pcclibdir)
		strlist_append(&late_linker_flags, cat("-L", pcclibdir));
	for (i = 0; deflibdirs[i]; i++)
		strlist_append(&late_linker_flags, cat("-L", deflibdirs[i]));
	/* standard libraries */
	if (pgflag) {
		for (i = 0; defproflibs[i]; i++)
			strlist_append(&late_linker_flags, defproflibs[i]);
	} else {
		for (i = 0; deflibs[i]; i++)
			strlist_append(&late_linker_flags, deflibs[i]);
	}
	if (Bstatic) {
		b = CRTBEGIN_T;
		e = CRTEND_T;
	} else if (shared /* || pieflag */) {
		b = CRTBEGIN_S;
		e = CRTEND_S;
	} else {
		b = CRTBEGIN;
		e = CRTEND;
	}
	strap(&middle_linker_flags, &crtdirs, b, 'p');
	strap(&late_linker_flags, &crtdirs, e, 'a');
	strap(&middle_linker_flags, &crtdirs, CRTI, 'p');
	strap(&late_linker_flags, &crtdirs, CRTN, 'a');
#ifdef os_win32
	/*
	 * On Win32 Cygwin/MinGW runtimes, the profiling code gcrtN.o
	 * comes in addition to crtN.o or dllcrtN.o
	 */
	if (pgflag)
		strap(&middle_linker_flags, &crtdirs, GCRT0, 'p');
	if (shared == 0)
		b = CRT0;
	else
		b = CRT0_S;     /* dllcrtN.o */
	strap(&middle_linker_flags, &crtdirs, b, 'p');
#else
	if (shared == 0) {
		if (pgflag)
			b = GCRT0;
		else if (pieflag)
			b = RCRT0;
		else
			b = CRT0;
#ifndef os_darwin
		strap(&middle_linker_flags, &crtdirs, b, 'p');
#endif
	}
#endif
}

#ifdef _WIN32
char *
win32pathsubst(char *s)
{
	char env[1024];
	DWORD len;

	len = ExpandEnvironmentStrings(s, env, sizeof(env));
	if (len == 0 || len > sizeof(env))
		errorx(8, "ExpandEnvironmentStrings failed, len %lu", len);

	len--;	/* skip nil */
	while (len-- > 0 && (env[len] == '/' || env[len] == '\\'))
		env[len] = '\0';

	return xstrdup(env);
}

char *
win32commandline(struct strlist *l)
{
	const struct string *s;
	char *cmd;
	char *p;
	int len;
	int j, k;

	len = 0;
	STRLIST_FOREACH(s, l) {
		len++;
		for (j = 0; s->value[j] != '\0'; j++) {
			if (s->value[j] == '\"') {
				for (k = j-1; k >= 0 && s->value[k] == '\\'; k--)
					len++;
				len++;
			}
			len++;
		}
		for (k = j-1; k >= 0 && s->value[k] == '\\'; k--)
			len++;
		len++;
		len++;
	}

	p = cmd = xmalloc(len);

	STRLIST_FOREACH(s, l) {
		*p++ = '\"';
		for (j = 0; s->value[j] != '\0'; j++) {
			if (s->value[j] == '\"') {
				for (k = j-1; k >= 0 && s->value[k] == '\\'; k--)
					*p++ = '\\';
				*p++ = '\\';
			}
			*p++ = s->value[j];
		}
		for (k = j-1; k >= 0 && s->value[k] == '\\'; k--)
			*p++ = '\\';
		*p++ = '\"';
		*p++ = ' ';
	}
	p[-1] = '\0';

	return cmd;
}
#endif
