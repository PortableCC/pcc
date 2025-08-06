/*	$Id$	*/

/*
 * Copyright (c) 2004,2010 Anders Magnusson (ragge@ludd.luth.se).
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
 * The C preprocessor.
 * This code originates from the V6 preprocessor with some additions
 * from V7 cpp, and at last ansi/c99 support.
 *
 * 	- kfind() expands the input buffer onto an output buffer.
 *	- exparg() expand one buffer into another.
 *		Recurses into submac() for fun-like macros.
 *	- submac() replaces the given macro.
 *		Recurses into subarg() for fun-like macros.
 *	- subarg() expands fun-like macros.
 *		Create strings, concats args, recurses into exparg.
 */

#ifdef pdp11
#include <sys/types.h>
#include <sys/file.h>
#else
#include "config.h"
#endif

#include <sys/stat.h>

#include <fcntl.h>
#if defined(HAVE_UNISTD_H) || defined(pdp11)
#include <unistd.h>
#endif
#include <stdio.h>
#include <stdarg.h>
#include <stdlib.h>
#include <string.h>
#include <time.h>

#ifndef pdp11
#include "compat.h"
#endif
#include "cpp.h"

#ifdef pdp11
#define	VERSSTR "Portable C Compiler 1.2.0.DEVEL 20190327"
#endif

#ifndef S_ISDIR
#define S_ISDIR(m)	(((m) & S_IFMT) == S_IFDIR)
#endif

/*
 * Buffers used:
 *	- expansion buffers (BNORMAL)
 *	- string buffers (used to store macros)
 */

static int	counter, didexpand;
/* C command */

int tflag;	/* traditional cpp syntax */
#ifdef PCC_DEBUG
int dflag;	/* debug printouts */
static void prline(const usch *s);
static void prrep(mvtyp);
#define	DPRINT(x) if (dflag) printf x
#else
#define DPRINT(x)
#endif
#define	PUTOB(ob, ch) (ob->cptr == ob->bsz ? \
	(putob(ob, ch), 1) : (ob->buf[ob->cptr++] = ch))
#define	cunput(x)	*--inp = x

int Aflag, Cflag, Eflag, Mflag, dMflag, Pflag, MPflag, MMDflag;
char *Mfile, *MPfile;
char *Mxfile;
int warnings, Mxlen, skpows, readinc;

#if LIBVMF
struct vspace ibspc;
#endif

struct symtab *symhsh[SYMHSZ];
FILE *tmpfd, *mfp;

/* include dirs */
struct incs {
	struct incs *next;
	usch *dir;
	dev_t dev;
	ino_t ino;
} *incdir[2];

static struct symtab *filloc;
static struct symtab *linloc;
static struct symtab *pragloc;
static struct symtab *defloc;
static struct symtab *ctrloc;
int	trulvl;
int	flslvl;
int	elflvl;
int	elslvl;

/*
 * Macro replacement list syntax:
 * - For object-type macros, replacement strings are stored as-is.
 * - For function-type macros, macro args are substituted for the
 *   character WARN followed by the argument number.
 * - The value element points to the beginning of the string.
 *
 * The first character in the replacement list is the number of arguments:
 *   VARG  - ends with ellipsis, next char is argcount without ellips.
 *   OBJCT - object-type macro
 *   0	   - empty parenthesis, foo()
 *   1->   - number of args.
 *
 * WARN is used:
 *	- in stored replacement lists to tell that an argument comes
 *	- When expanding replacement lists to tell that the list ended.
 *
 * To ensure that an already expanded identifier won't get expanded
 * again a EBLOCK char + its number is stored directly before any
 * expanded identifier.
 */

/*
 * No-replacement array.  If a macro is found and exists in this array
 * then no replacement shall occur.
 */
struct blok {
	int nidx;
	struct symtab *sp;
};
struct blok *blokx[L2MAX];
#define	BLKPTR(x)	((x) & ((CPPBUF/sizeof(struct blok))-1))
#define	BLKBUF(x)	((x) / (CPPBUF/sizeof(struct blok)))
int blkidp;

static struct iobuf *readargs(struct iobuf *, struct symtab *, const usch **);
static struct iobuf *exparg(int, struct iobuf *, struct iobuf *, int);
static struct iobuf *subarg(struct symtab *sp, const usch **args, int, int);
static void usage(void);
static void addidir(char *idir, struct incs **ww);
static void vsheap(struct iobuf *, const char *, va_list);
static int skipws(struct iobuf *ib);
static int getyp(usch *s);
static void fstrstr(struct iobuf *ib, struct iobuf *ob);
static FILE *chkfile(const usch *n1, const usch *n2);
static usch *addname(const usch *str);
static void *addblock(int sz);

int
main(int argc, char **argv)
{
	register int ch;
	register const usch *fn2;
	char *a, buf[50];

#ifdef TIMING
	struct timeval t1, t2;

	(void)gettimeofday(&t1, NULL);
#endif

	if ((tmpfd = tmpfile()) == NULL)
		error("tmpfile creation failed");
	if ((mfp = tmpfile()) == NULL)
		error("macro file creation failed");

#if LIBVMF
	if (vminit(NVMPGS))
		error("vminit");
	if (vmopen(&ibspc, NULL) < 0)
		error("vmopen ibspc");
#endif

	while ((ch = getopt(argc, argv, "ACD:d:EI:i:MPS:tU:Vvx:")) != -1) {
		switch (ch) {
		case 'A': /* assembler input */
			Aflag++;
			break;

		case 'C': /* Do not discard comments */
			Cflag++;
			break;

		case 'E': /* treat warnings as errors */
			Eflag++;
			break;

		case 'D': /* define something */
			if ((a = strchr(optarg, '=')) != NULL)
				*a = ' ';
			fprintf(tmpfd, "#define %s%s",
			    optarg, a ? "\n" : " 1\n");
			break;

		case 'i': /* include */
			fprintf(tmpfd, "#include \"%s\"\n", optarg);
			break;

		case 'U': /* undef */
			fprintf(tmpfd, "#undef %s\n", optarg);
			break;

		case 'd':
			while (*optarg) {
				switch(*optarg) {
				case 'M': /* display macro definitions */
					dMflag = 1;
					Mflag = 1;
					break;

				default: /* ignore others */
					break;
				}
				optarg++;
			}
			break;

		case 'I':
		case 'S':
			addidir(optarg, &incdir[ch == 'I' ? INCINC : SYSINC]);
			break;

		case 'M': /* Generate dependencies for make */
			Mflag++;
			break;

		case 'P': /* Inhibit generation of line numbers */
			Pflag++;
			break;

		case 't':
			tflag = 1;
			break;

#ifdef PCC_DEBUG
		case 'V':
			dflag++;
			break;
#endif
		case 'v':
			fprintf(stderr, "PCC preprocessor version "VERSSTR"\n");
			break;

		case 'x':
			if (strcmp(optarg, "MMD") == 0) {
				MMDflag++;
			} else if (strcmp(optarg, "MP") == 0) {
				MPflag++;
			} else if (strncmp(optarg, "MT,", 3) == 0 ||
			    strncmp(optarg, "MQ,", 3) == 0) {
				int l = (int)strlen(optarg+3) + 2;
				char *cp, *up;

				if (optarg[1] == 'Q')
					for (cp = optarg+3; *cp; cp++)
						if (*cp == '$')
							l++;
				Mxlen += l;
				Mxfile = cp = realloc(Mxfile, Mxlen);
				for (up = Mxfile; *up; up++)
					;
				if (up != Mxfile)
					*up++ = ' ';
				for (cp = optarg+3; *cp; cp++) {
					*up++ = *cp;
					if (optarg[1] == 'Q' && *cp == '$')
						*up++ = *cp;
				}
				*up = 0;
			} else
				usage();
			break;

		case '?':
		default:
			usage();
		}
	}

	argc -= optind;
	argv += optind;

	filloc = lookup((usch *)"__FILE__", ENOADD);
	linloc = lookup((usch *)"__LINE__", ENOADD);
	pragloc = lookup((usch *)"_Pragma", ENOADD);
	defloc = lookup((usch *)"defined", ENOADD);
	ctrloc = lookup((usch *)"__COUNTER__", ENOADD);

#ifdef pdp11
	/* set predefined symbols here (not from cc) */
	fprintf(tmpfd, "#define __BSD2_11__ 1\n");
	fprintf(tmpfd, "#define BSD2_11 1\n");
	fprintf(tmpfd, "#define __pdp11__ 1\n");
	fprintf(tmpfd, "#define pdp11 1\n");
	fprintf(tmpfd, "#define unix 1\n"); /* XXX go away */
	addidir("/usr/include", &incdir[SYSINC]);
	if (tflag == 0)
		fprintf(tmpfd, "#define __STDC__ 1\n");
#endif

	filloc->valoff = linloc->valoff = pragloc->valoff =
	    ctrloc->valoff = defloc->valoff = 1;
	fprintf(mfp, "%cdefined%c", 0, 0);

	filloc->type = FILLOC;
	linloc->type = LINLOC;
	pragloc->type = PRAGLOC;
	defloc->type = DEFLOC;
	ctrloc->type = CTRLOC;

	if (Mflag && !dMflag) {
		char *c;

		if (argc < 1)
			error("-M and no infile");
		if ((c = strrchr(argv[0], '/')) == NULL)
			c = argv[0];
		else
			c++;
		Mfile = (char *)addname((usch *)c);
		if (MPflag)
			MPfile = (char *)addname((usch *)c);
		if (Mxfile)
			Mfile = Mxfile;
		if ((c = strrchr(Mfile, '.')) == NULL)
			error("-M and no extension: ");
		c[1] = 'o';
		c[2] = 0;
	}

	if (argc == 2) {
		if (freopen(argv[1], "w", stdout) == NULL)
			error("Can't freopen %s", argv[1]);
	}
	fn2 = (const usch *)"<stdin>";
	if (argc && strcmp(argv[0], "-")) {
		fn2 = (usch *)argv[0];
		if ((freopen(argv[0], "r", stdin)) == NULL)
			error("freopen failed");
	}

	/* initialization defines */
	if (dMflag) {
		rewind(tmpfd);
		while ((ch = fread(buf, 1, sizeof buf, tmpfd)) > 0)
			fwrite(buf, ch, 1, stdout);
	}
	rewind(tmpfd);
	pushfile(tmpfd, "<command line>", 0, 0);

	pushfile(stdin, fn2, 0, NULL);

	if (Mflag == 0 && skpows)
		fputc('\n', stdout);

#ifdef TIMING
	(void)gettimeofday(&t2, NULL);
	t2.tv_sec -= t1.tv_sec;
	t2.tv_usec -= t1.tv_usec;
	if (t2.tv_usec < 0) {
		t2.tv_usec += 1000000;
		t2.tv_sec -= 1;
	}
	fprintf(stderr, "cpp total time: %ld s %ld us\n",
	     (long)t2.tv_sec, (long)t2.tv_usec);
#endif
	if (Eflag && warnings > 0)
		return 2;

	return 0;
}

/*
 * Write a character to an out buffer.
 */
void
putob(register struct iobuf *ob, register int ch)
{
	if (ob->cptr == ob->bsz) {
		int sz = ob->bsz;
		switch (ob->type) {
		case BNORMAL:
			ob->buf = xrealloc(ob->buf, sz + CPPBUF+1);
			/* ob->cptr = ob->buf + sz; */
			ob->bsz = sz + CPPBUF;
			break;
		case BINBUF:
			error("putob %d", ob->type);
			break;
		}
	}
	ob->buf[ob->cptr++] = ch;
}

static struct iobuf *ioblnk;

static struct iobuf *
giob(int typ, register const usch *bp, int bsz)
{
	register struct iobuf *iob;

	if (ioblnk) {
		iob = ioblnk;
		ioblnk = (void *)iob->buf;
	} else
		iob = addblock(sizeof(*iob));

	if (bp == NULL)
		bp = xmalloc(bsz);
	iob->buf = (usch *)bp;
	iob->cptr = 0;
	iob->bsz = bsz;
	iob->ro = 0;
	iob->type = typ;
	return iob;
}


int nbufused;
/*
 * Get a new buffer.
 */
struct iobuf *
getobuf(register int type)
{
	register struct iobuf *iob = 0;

	switch (type) {
	case BNORMAL:
		nbufused++;
		iob = giob(BNORMAL, NULL, CPPBUF);
		iob->bsz = CPPBUF-1; /* space for \0 */
		break;
	case BINBUF:
#if LIBVMF
		iob = giob(BINBUF, (usch *)ifiles->vseg->s_cinfo, BYTESPERSEG);
#else
		iob = giob(BINBUF, NULL, CPPBUF);
#endif
		break;
	default:
		error("getobuf");
	}
	return iob;
}

/*
 * Create a read-only input buffer.
 */
static struct iobuf *
mkrobuf(register const usch *s)
{
	register struct iobuf *iob;

	nbufused++;
	iob = giob(BNORMAL, s, strlen((char *)s));
	iob->ro = 1;
	DPRINT(("mkrobuf %s\n", s));
	return iob;
}

/*
 * Copy a buffer to another buffer.
 */
struct iobuf *
buftobuf(register struct iobuf *in, register struct iobuf *iob)
{
	register int cp;

	DPRINT(("buftobuf in %p out %p instr %s\n", in, iob, in->buf));
	if (iob == NULL)
		iob = getobuf(BNORMAL);
	for (cp = 0; cp < in->cptr; cp++)
		putob(iob, in->buf[cp]);
	return iob;
}

/*
 * Copy a string to a buffer.
 */
struct iobuf *
strtobuf(register const usch *str, register struct iobuf *iob)
{
	if (iob == NULL)
		iob = getobuf(BNORMAL);
	DPRINT(("strtobuf iob %p buf %p str %s\n", iob, iob->buf, str));
	do {
		PUTOB(iob, *str);
	} while (*str++);
	iob->cptr--;
	return iob;
}

static int
macget(register mvtyp a)
{
	fseek(mfp, a, SEEK_SET);
	return fgetc(mfp);
}

/*
 * Create a replacement buffer containing the macro to be substituted.
 */
static struct iobuf *
macrepbuf(struct symtab *sp)
{
	register struct iobuf *ob;
	register int ch;

	ob = getobuf(BNORMAL);
	fseek(mfp, sp->valoff, SEEK_SET);
	while ((ch = getc(mfp)) != 0) {
		putob(ob, ch);
		if (ch == WARN)
			putob(ob, getc(mfp));
	}
	putob(ob, 0);
	ob->cptr = 0;
	return ob;
}

void
bufree(register struct iobuf *iob)
{
	if (iob->type == BNORMAL)
		nbufused--;
	if (iob->ro == 0)
		free(iob->buf);
	iob->buf = (void *)ioblnk;
	ioblnk = iob;
}

static void
addidir(register char *idir, register struct incs **ww)
{
	register struct incs *w;
	struct stat st;

	if (stat(idir, &st) == -1 || !S_ISDIR(st.st_mode))
		return; /* ignore */
	if (*ww != NULL) {
		for (w = *ww; w->next; w = w->next) {
#ifdef _WIN32
			if (strcmp(w->dir, idir) == 0)
				return;
#else
			if (w->dev == st.st_dev && w->ino == st.st_ino)
				return;
#endif
		}
#ifdef _WIN32
		if (strcmp(w->dir, idir) == 0)
			return;
#else
		if (w->dev == st.st_dev && w->ino == st.st_ino)
			return;
#endif
		ww = &w->next;
	}
	if ((w = calloc(sizeof(struct incs), 1)) == NULL)
		error("couldn't add path %s", idir);
	w->dir = (usch *)idir;
	w->dev = st.st_dev;
	w->ino = st.st_ino;
	*ww = w;
}

void
line(void)
{
	register struct iobuf *ob;
	register int x, n, ln = 0, oidx;

	oidx = ifiles->idx;

	x = 0;
	if (yylex() == NUMBER &&
	    (yynode.nd_val >= 1 || yynode.nd_val <= 2147483647L)) {
		ln = yynode.nd_val;
		escln = 0;

		if ((x = yylex()) == STRING) {
			ob = yynode.nd_ob;
			ob->buf[--ob->cptr] = 0; /* remove trailing \" */
			if (strcmp((char *)ifiles->fname, (char *)ob->buf+1))
				ifiles->fname = addname(ob->buf+1);
			bufree(ob);

			if ((x = yylex()) == NUMBER &&
			    ((n = yynode.nd_val) >= 0 || n <= 9)) {
				if (n == 3)
					ifiles->idx = SYSINC;
				x = yylex();
			}
		}
	}

	if (x != WARN)
		error("bad #line");

	ifiles->lineno = ln;
	prtline(1);
	ifiles->idx = oidx;
	ifiles->lineno--;

}

#ifdef MACHOABI

/*
 * Example:
 * Library/Frameworks/VideoToolbox.framework/Headers/VTSession.h
 *
 * Search for framework header file.
 * Return 1 on success.
 */

static int
fsrch_macos_framework(const usch *fn, const usch *dir)
{
	struct iobuf *ob;
	usch *s = (usch *)strchr((const char*)fn, '/');
	usch *p, *q, *nm;
	int len  = s - fn;

	if (s == NULL)
		return 0;

	nm = addname(dir);
	p = addname(fn);
	*(p + len) = 0;

	q = (usch *)strstr((const char *)nm, (const char *)p);
	if (q != NULL) {
		*q = 0;
		return fsrch_macos_framework(fn, nm);
	}
	free(p);

	p = nm + strlen((char *)nm) - 1;
	while (*p == '/')
		p--;
	while (*p != '/')
		p--;
	++p;
	
	ob = bsheap(NULL, "%s/Frameworks/%s.framework/Headers%s", nm, fn, s);
	free(nm);
	nm = addname(ob->buf);
	bufree(ob);
	pushfile(nm, fn, SYSINC, NULL);

	return 0;
}

#endif

/*
 * Search for and include next file.
 * Return 1 on success.
 */
static int
fsrch(const usch *fn, int idx, register struct incs *w)
{
	register FILE *fd;
	register int i;

	for (i = idx; i < 2; i++) {
		if (i > idx)
			w = incdir[i];
		for (; w; w = w->next) {
			if ((fd = chkfile(fn, w->dir)) != NULL) {
				pushfile(fd, fn, i, w->next);
				return 1;
			}
		}
	}

#ifdef MACHOABI
	/*
	 * On MacOS, we may have to do some clever stuff
	 * to resolve framework headers.
	 */
	{
		/*
		 * Dig out org filename path and try to find.
		 */
		usch *p, *dir = addname(ifiles->orgfn);
		if ((p = (usch *)strrchr((char *)dir, '/')) != NULL) {
			p[1] = 0;
			if (fsrch_macos_framework(fn, dir) == 1)
				return 1;
		}

		if (fsrch_macos_framework(fn,
		    (const usch *)"/Library/Frameworks/") == 1)
			return 1;

		if (fsrch_macos_framework(fn,
		    (const usch *)"/System/Library/Frameworks/") == 1)
			return 1;
	}
#endif

	return 0;
}

/*
 * concatenate n1 with n2 and see if the result is an accessible file.
 * if so, open it and return the fd.
 */
static FILE *
chkfile(register const usch *n1, register const usch *n2)
{
	char buf[FILENAME_MAX];
	register FILE *fd;

	if (n2 != NULL) {
		snprintf(buf, sizeof buf, "%s/%s", n2, n1);
	} else
		snprintf(buf, sizeof buf, "%s", n1);
//	if (access(buf, R_OK) == 0)
//		res = addname(buf);
	if ((fd = fopen(buf, "r")) == NULL)
		error("chkfile");
	return fd;
}

/*
 * Include a file. Include order:
 * - For <...> files, first search -I directories, then system directories.
 * - For "..." files, first search "current" dir, then as <...> files.
 */
void
include(void)
{
	register struct iobuf *ob;
	register usch *fn, *nm = NULL;
	FILE *fd;

	if (flslvl)
		return;

	readinc++;
	if (yylex() != STRING)
		error("bad #include");
	readinc = 0;
	ob = yynode.nd_ob;
	ob->buf[ob->cptr-1] = 0; /* last \" */

	fn = &ob->buf[1];
	if (fn[0] == '/') {
		 if ((fd = chkfile(fn, 0)) != NULL)
			goto okret;
	}
	if (ob->buf[0] == '\"') {
		if ((nm = (usch *)strrchr((char *)ifiles->orgfn, '/'))) {
			*nm = 0;
		 	fd = chkfile(fn, ifiles->orgfn);
			*nm = '/';
		} else 
			fd = chkfile(fn, 0);
		if (fd != NULL)
			goto okret;
	}
	fn = addname(fn);
	bufree(ob);
	if (fsrch(fn, 0, incdir[0]))
		goto prt;

	error("cannot find '%s'", fn);
	fd = NULL; /* cannot happen */
	/* error() do not return */

okret:	bufree(ob);
	pushfile(fd, fn, 0, NULL);
prt:	prtline(1);
}

void
include_next(void)
{
	register struct iobuf *ob;
	register usch *fn;

	if (flslvl)
		return;

	readinc++;
	if (yylex() != STRING)
		error("bad #include_next");
	readinc = 0;
	ob = yynode.nd_ob;
	ob->buf[ob->cptr-1] = 0; /* last \" */

	fn = addname(&ob->buf[1]);
	bufree(ob);
	if (fsrch(fn, ifiles->idx, ifiles->incs) == 0)
		error("cannot find '%s'", fn);

	prtline(1);
}

/*
 * Compare two replacement lists, taking in account comments etc.
 */
static int
cmprepl(mvtyp oin, mvtyp nin)
{
	register int o, n;

	for (; ; oin++, nin++) {
		/* comment skip */
		o = macget(oin);
		n = macget(nin);
		if (o == '/' && macget(oin+1) == '*') {
			oin+=2;
			while (macget(oin) != '*' || macget(oin+1) != '/')
				oin++;
			oin += 2;
		}
		if (n == '/' && macget(nin+1) == '*') {
			nin+=2;
			while (macget(nin) != '*' || macget(nin+1) != '/')
				nin++;
			nin += 2;
		}
		while ((o = macget(oin)) == ' ' || o == '\t')
			oin++;
		while ((n = macget(nin)) == ' ' || n == '\t')
			nin++;
		if (o != n)
			return 1;
		if (o == 0)
			break;
	}
	return 0;
}

static int
isell(void)
{
	if (cinput() != '.' || cinput() != '.')
		return 0;
	return 1;
}

static int
findarg(register char *ab, char *arg[], int narg)
{
	register int i;

	for (i = 0; i < narg; i++)
		if (strcmp(ab, arg[i]) == 0)
			return i;
	return -1;
}

#define	SKPWS()	while (*lncur == ' ' || *lncur == '\t') lncur++
#define	SKPID() while (ISID(*lncur)) lncur++

/*
 * gcc extensions:
 * #define e(a...) f(s, a) ->  a works as __VA_ARGS__
 * #define e(fmt, ...) f(s, fmt , ##__VA_ARGS__) -> remove , if no args
 *
 * The line buffer (which is at least one line long) is also used as a 
 * macro replacement work buffer.
 */
void
define(void)
{
	register struct iobuf *ab;
	register struct symtab *np;
	char *arg[MAXARGS+1], *vararg, *mwa, *mb, *rbeg;
	register int c, i, redef;
	int type, narg, begpos, needws;
	int wascon, gotsnuff;

	SKPWS();
	if (!ISID0(*lncur))
		goto bad;
	np = lookup(lncur, ENTER);
	redef = np->valoff != 0;
	SKPID();
	c = *lncur++;

	type = OBJCT;
	narg = 0;
	ab = getobuf(BNORMAL);
	vararg = NULL;
	mwa = lnbeg;

#define	CMAC()	for (mb = mwa; ISID(*lncur); *mwa++ = *lncur++); *mwa++ = 0

//printf("X0: '%s'\n", lncur);
	if (c == '(') {
		type = FUNLIKE;
		SKPWS();
//printf("X3: %s\n", lncur);
		if ((c = *lncur) != ')')
		for (;;) {
//printf("X4: %s\n", lncur);
			if (c == '.') {
				if (!isell())
					goto bad;
				vararg = (usch *)"__VA_ARGS__";
				break;
			} else if (!ISID0(c))
				goto bad;
			CMAC();
			if (findarg(mb, arg, narg) >= 0)
				error("Duplicate parameter \"%s\"", mb);
			arg[narg++] = mb;
			if (*lncur == '.') {
				if (!isell()) 
					goto bad;
				vararg = arg[--narg];
				break;
			}
			SKPWS();
			if ((c = *lncur) == ')')
				break;
			if (c != ',')
				goto bad;
			lncur++;
			SKPWS();
			c = *lncur;
		}
		lncur++;
	}
//printf("X1: '%s'\n", lncur);
	SKPWS();

	fseek(mfp, 0, SEEK_END);
	begpos = ftell(mfp);

	/* parse replacement-list, substituting arguments */
	gotsnuff = wascon = needws = 0;
	rbeg = mwa; /* replacement buffer after macro names */
#define	RWR(x)	*mwa++ = x
#define	RWP(x)	mwa[-1] = x
	while ((c = *lncur++) != 0) {

		switch (c) {
		case ' ':
		case '\t':
			continue;

		case '#':
//printf("X2: '%s'\n", lncur);
			RWR(c);
			if (*lncur == '#') {
				/* concat op */
				RWP(CONC);
				lncur++;
				SKPWS();
				if (ISID0(c = *lncur) && type == FUNLIKE)
					wascon = 1;
				if (c == 0)
					goto bad; /* 6.10.3.3 p1 */
				continue;
			}

			if (type == OBJCT) {
				/* no meaning in object-type macro */
				continue;
			}

			/* remove spaces between # and arg */
			SKPWS();
//printf("X5: '%s'\n", lncur);
			if (!ISID0(c = *lncur))
				goto bad;
			RWP(SNUFF);
//printf("X6: '%s'\n", lncur);
			gotsnuff = 1;
			break;

		case '/':
			if (*lncur == '/') {
				lncur = lnend;
			} else if (*lncur == '*') {
				lncur++;
#if 0
				mwa = defcmnt(arg, narg, mwa, &copied);
				if (Cflag)
					RWR('/'), RWR('*');
				for (;;) {
					if (lncur[0] == '*' && lncur[1] == '/')
						break;
					if ((c = *lncur++) == 0) {
						error("notyet");
						if (newline(0))
							goto bad;
						c = *lncur++;
					}
					if (Cflag)
						RWR(c);
				}
				lncur += 2;
				if (Cflag)
					RWR('*'), RWR('/');
#endif
			} else
				RWR(c);
			break;

		case '.': 
			if (!ISDIGIT(*lncur))
				break;
			if (needws)
				RWR(' '), needws = 0;
			if (c == '.')
				RWR(c), c = *lncur++;
			for (;;) {
				RWR(i = c), c = *lncur++;
				if (c == '-' || c == '+') {
					if ((i & 0337) != 'E' && i != 'P')
						break;
				} else if ((c != '.') && ((ISID(c)) == 0))
					break;
			}
			continue;

		case '\"':
		case '\'':
			if (needws)
				RWR(' '), needws = 0;
			if (tflag) {
				RWR(c);
			} else {
				extern int instr;
				int bc;
				while (c != '\"' && c != '\'')
					RWR(c), c = *lncur++;

				bc = c;
				instr = 1;
				RWR(c), c = *lncur++;
				while (c != bc) {
					if (c == '\\')
						RWR(c), c = *lncur++;
					else if (c == '\n')
						goto bad;
					RWR(c), c = *lncur++;
				}
				RWR(c);
				instr = 0;
			}
			break;

		default:
//printf("X10: '%s'\n", lncur);
			if (needws)
				RWR(' '), needws = 0;
			if (!ISID0(c)) {
				RWR(c);
				break;
			}

			RWR(c);
			if (c == 'u' && lncur[0] == '8' && lncur[1] == '\"') {
				RWR('8');
				lncur++;
				break;
			}
			if ((c == 'u' || c == 'U' || c == 'L') &&
			    *lncur == '\"')
				break;

//printf("X13: c '%c'\n", c);
			CMAC(); /* copy string onto heap */
			mwa--; /* overwrite last 0 */
			mb--;
//printf("X11: mb '%s'\n", mb);
			if (type == OBJCT)
				break; /* keep on heap */
			if (vararg && strcmp(mb, vararg) == 0) {
				i = wascon ? GCCARG : C99ARG;
			} else if ((i = findarg(mb, arg, narg)) < 0) {
				/* check if its an argument */
				break;
			}
//printf("X12: '%s'\n", lncur);
			mwa = mb; /* remove name from heap */
			RWR(WARN),RWR(i);
			if (gotsnuff)
				RWR(SNUFF), gotsnuff = 0;
			break;

		case 0:
			break;
			
		}
		wascon = 0;
	}
	/* remove trailing whitespace */

	RWR(0);
printf("en define: '");
prline(rbeg);
printf("'\n");

	if (vararg)
		type = VARG;

	if (*rbeg == CONC)
		goto bad; /* 6.10.3.3 p1 */

	if (redef && ifiles->idx != SYSINC) {
		if (cmprepl(np->valoff, rbeg) || 
		    np->type != type || np->narg != narg) { /* not equal */
			np->valoff = begpos;
			warning("%s redefined (previously defined at \"%s\" line %d)",
			    np->namep, np->file, np->line);
		}
	} else
		np->valoff = begpos;
	np->type = type;
	np->narg = narg;

#ifdef PCC_DEBUG
	if (dflag) {
		printf("!define %s: ", np->namep);
		if (type == OBJCT)
			printf("[object]");
		else if (type == VARG)
			printf("[VARG%d]", narg);
		else
			printf("[%d]", narg);
		putchar('\'');
		prrep(np->valoff);
		printf("\'\n");
		printf("%s: link %d off %d\n", np->namep, VALBUF(np->valoff), VALPTR(np->valoff));
	}
#endif
	bufree(ab);
	return;

bad:	error("bad #define");
}

void
warning(const char *fmt, ...)
{
	va_list ap;

	if (ifiles != NULL)
		fprintf(stderr, "%s:%d: warning: ",
		    ifiles->fname, ifiles->lineno);

	va_start(ap,fmt);
	vfprintf(stderr, fmt, ap);
	va_end(ap);
	fputc('\n', stderr);

	warnings++;
}

void
error(const char *fmt, ...)
{
	va_list ap;

	fflush(stdout);
	if (ifiles != NULL)
		fprintf(stderr, "%s:%d: error: ",
		    ifiles->fname, ifiles->lineno);

	va_start(ap, fmt);
	vfprintf(stderr, fmt, ap);
	va_end(ap);
	fputc('\n', stderr);
	exit(1);
}

static int
pragwin(register struct iobuf *ib)
{
	return ib ? ib->buf[ib->cptr++] : cinput();
}

static int
skipws(struct iobuf *ib)
{
	register int t;

	while ((t = pragwin(ib)) == ' ' || t == '\t')
		;
	return t;
}

/*
 * convert _Pragma() to #pragma for output.
 * Syntax is already correct.
 */
static void
pragoper(register struct iobuf *ib)
{
	register int t;

	if (skipws(ib) != '(' || ((t = skipws(ib)) != '\"' && t != 'L'))
		goto err;
	if (t == 'L' && (t = pragwin(ib)) != '\"')
		goto err;
	putstr((usch *)"\n#pragma ");
	while ((t = pragwin(ib)) != '\"') {
		if (t == BLKID || t == BLKID2) {
			pragwin(ib);
			if (t == BLKID2)
				pragwin(ib);
			continue;
		}
		if (t == '\"')
			continue;
		if (t == '\\') {
			if ((t = pragwin(ib)) != '\"' && t != '\\')
				putch('\\');
		}
		putch(t);
	}
	prtline(1);
	if (skipws(ib) == ')')
		return;

err:	error("_Pragma() syntax error");
}

#ifdef PCC_DEBUG
static void
prblocker(char *s, int id)
{
	printf("%s (blocker): ", s);
	
	for (; id; id = blokx[BLKBUF(id)][BLKPTR(id)].nidx)
		printf("%s ", blokx[BLKBUF(id)][BLKPTR(id)].sp->namep);
	printf("\n");
		
}
#else
#define	prblocker(x,y)
#endif

/*
 * Check if symtab is in blocklist based on index l.
 */
static int
expok(struct symtab *sp, register int id)
{

	if (id == 0)
		return 1;
#ifdef PCC_DEBUG
	if (dflag)
		prblocker("expok", id);
#endif
	for (; id; id = blokx[BLKBUF(id)][BLKPTR(id)].nidx) {
		if (blokx[BLKBUF(id)][BLKPTR(id)].sp == sp)
			return 0;
	}
	return 1;
}

#define	expokb(s,l)	expok(s,l)

static int
blkget(struct symtab *sp, int id)
{
	register int upper = BLKBUF(blkidp);
	register int off = BLKPTR(blkidp);

	if (upper == L2MAX)
		error("too complex macro");
	if (blokx[upper] == NULL)
		blokx[upper] = xmalloc(CPPBUF);
	blokx[upper][off].sp = sp;
	blokx[upper][off].nidx = id;
	id = blkidp++;
	if ((blkidp & 0377) == 0)
		blkidp++;
	return id;
}

static int
mergeadd(register int l, register int m)
{

	DPRINT(("mergeadd: %d %d\n", l, m));
#ifdef PCC_DEBUG
	if (dflag > 1) {
		prblocker("mergeadd", l);
		if (m) prblocker("mergeadd", m);
	}
#endif
	if (l == 0)
		return m;
	if (m == 0 || l == m)
		return l;

	for (; m; m = blokx[BLKBUF(m)][BLKPTR(m)].nidx)
		l = blkget(blokx[BLKBUF(m)][BLKPTR(m)].sp, l);

	DPRINT(("mergeadd return: %d ", l));
#ifdef PCC_DEBUG
	if (dflag)
		prblocker("mergeadd", l);
#endif
	return l;
}

static void
storeblk(register int l, register struct iobuf *ob)
{
	DPRINT(("storeblk: %d\n", l));
	if (l == 0)
		return;
	if (l > 255) {
		putob(ob, BLKID2);
		putob(ob, l >> 8);
	} else
		putob(ob, BLKID);
	putob(ob, l & 255);
}

/*
 * Save filename on heap (with escaped chars).
 */
static struct iobuf *
unfname(void)
{
	register struct iobuf *ob = getobuf(BNORMAL);
	register const usch *bp = ifiles->fname;

	putob(ob, '\"');
	for (; *bp; bp++) {
		if (*bp == '\"' || *bp == '\'' || *bp == '\\')
			putob(ob, '\\');
		putob(ob, *bp);
	}
	putob(ob, '\"');
	return ob;
}

/*
 * Version of fastnum that reads from a string and saves in ob.
 * We know that it is a number before calling this routine.
 */
static void
fstrnum(struct iobuf *ib, register struct iobuf *ob)  
{	
	register usch *s = ib->buf+ib->cptr;
	register int c2;

	if (*s == '.') {
		/* not digit, dot.  Next will be digit */
		putob(ob, *s++);
	}
	for (;;) {
		putob(ob, *s++);
		if ((c2 = (*s & 0337)) == 'E' || c2 == 'P') {
			if (s[1] != '-' && s[1] != '+')
				break;
			putob(ob, *s++);
		} else if ((*s != '.') && ((ISID(*s)) == 0))
			break;
	}
	ib->cptr = (int)(s - ib->buf);
}

/*
 * get a string or character constant.
 * similar to faststr.
 */
static void
fstrstr(struct iobuf *ib, struct iobuf *ob)
{
	register usch *p, *q;
	register int ch;

	q = p = ib ? ib->buf+ib->cptr : inp;
	if (*p == 'L' || (*p|040) == 'u')
		p++;
	if (*p == '8')
		p++;
	ch = *p++;
	for (;;) {
		while (ISESTR(*p++) == 0)
			;
		if (*--p == 0 && ib == NULL) {
			/* only from stdin */
			strtobuf(inp, ob);
			inp = p;
			inpbuf();
			q = p = inp;
			p--;
		} else if (*p == '\\') {
			p++;
		} else if (*p == '\n' && ib == NULL) {
			warning("unterminated literal");
			p--;
			break;
		} else if (ch == *p)
			break;
		p++;
	}
	++p;
	while (q < p)
		putob(ob, *q++);
	if (ib == 0) inp = p; else ib->cptr = p  - ib->buf;
}

/*
 * Save standard comments if found.
 */
static void
fcmnt(struct iobuf *ib, register struct iobuf *ob)
{
	register usch *s = ib->buf+ib->cptr;

	putob(ob, *s++); /* / */
	putob(ob, *s++); /* * */
	for (;;s++) {
		putob(ob, *s);
		if (s[-1] == '*' && *s == '/')
			break;
	}
	ib->cptr = (int)(s - ib->buf + 1);
}

static int
getyp(register usch *s)
{

	if (ISID0(*s)) return IDENT;
	if ((*s == 'L' || *s == 'U' || *s == 'u') &&
	    (s[1] == '\'' || s[1] == '\"')) return STRING;
	if (s[0] == 'u' && s[1] == '8' && s[2] == '\"') return STRING;
	if (s[0] == '\'' || s[0] == '\"') return STRING;
	if (ISDIGIT(*s)) return NUMBER;
	if (*s == '.' && (ISDIGIT(s[1]))) return NUMBER;
	if (*s == '/' && (s[1] == '/' || s[1] == '*')) return CMNT;
	return *s;
	
}

/*
 * Check ib and print out the symbols there.
 * If expandable symbols found recurse and expand them.
 * If last identifier on the input list is expandable return it.
 * Expect ib to be zero-terminated.
 */
static struct symtab *
loopover(register struct iobuf *ib, register struct iobuf *ob)
{
	struct iobuf *xb, *xob;
	struct symtab *sp;
	register usch *cp;
	int l, c, t, cn;

	ib->cptr = 0; /* start from beginning */
#ifdef PCC_DEBUG
	if (dflag) {
		printf("loopover: '");
		prline(ib->buf+ib->cptr);
		printf("'\n");
	}
#endif

	xb = getobuf(BNORMAL);
	while ((c = ib->buf[ib->cptr])) {
		switch (t = getyp(ib->buf+ib->cptr)) {
		case CMNT:
			fcmnt(ib, ob);
			continue;
		case NUMBER:
			fstrnum(ib, ob);
			continue;
		case STRING:
			xb->cptr = 0;
			fstrstr(ib, xb);
			xb->buf[xb->cptr] = 0;
			for (cp = xb->buf; *cp; cp++) {
				if (*cp <= BLKID2 && *cp > 0) {
					if (*cp == BLKID)
						cp++;
					if (*cp == BLKID2)
						cp++, cp++;
					continue;
				}
				putob(ob, *cp);
			}
			continue;
		case BLKID:
		case BLKID2:
			l = (unsigned char)ib->buf[++ib->cptr];
			if (t == BLKID2)
				l = (l << 8) | (unsigned char)ib->buf[++ib->cptr];
			ib->cptr++;
			/* FALLTHROUGH */
		case IDENT:
			if (t == IDENT)
				l = 0;
			/*
			 * Tricky: if this is the last identifier
			 * in the expanded list, and it is defined
			 * as a function-like macro, then push it
			 * back on the input stream and let fastscan
			 * handle it as a new macro.
			 * BUT: if this macro is blocked then this
			 * should not be done.
			 */
			for (cn = ib->cptr;
			    ISID(ib->buf[ib->cptr]); ib->cptr++)
				;
			if ((sp = lookup(cn+ib->buf, FIND)) == NULL) {
sstr:				for (; cn < ib->cptr; cn++)
					putob(ob, ib->buf[cn]);
				continue;
			}
			if (expok(sp, l) == 0) {
				/* blocked */
				goto sstr;
			} else {
				if (sp->type != OBJCT) {
					cn = ib->cptr;
					while (ISWS(ib->buf[ib->cptr]))
						ib->cptr++;
					if (ib->buf[ib->cptr] == 0) {
						bufree(xb);
						return sp;
					}
					ib->cptr = cn;
				}
newmac:				if ((xob = submac(sp, 1, ib, 0)) == NULL) {
					strtobuf((usch *)sp->namep, ob);
				} else {
					sp = loopover(xob, ob);
					bufree(xob);
					if (sp != NULL)
						goto newmac;
				}
			}
			continue;
		default:
			putob(ob, c);
		}

		ib->cptr++;
	}

	bufree(xb);
	DPRINT(("loopover return 0\n"));
	return 0;
}

/*
 * Handle defined macro keywords found on input stream.
 * When finished print out the full expanded line.
 * Input here is from the lex buffer.
 * Return 1 if success, 0 otherwise.
 * Scanned data is stored on heap.  Last scan prints out the buffer.
 */
struct iobuf *
kfind(struct symtab *sp)
{
	register struct iobuf *ib, *ob, *outb, *ab;
	const usch *argary[MAXARGS+1];
	int c, n = 0;
	int l, oldused;

	oldused = nbufused;
	blkidp = 1;
	outb = NULL;
	DPRINT(("%d:enter kfind(%s)\n",0,sp->namep));
	switch ((unsigned int)sp->type) {
	case FILLOC:
		ob = unfname();
		return ob;

	case LINLOC:
		return bsheap(NULL, "%d", ifiles->lineno);

	case PRAGLOC:
		pragoper(NULL);
		return getobuf(BNORMAL);

	case DEFLOC:
	case OBJCT:
		l = blkget(sp, 0);
		ib = macrepbuf(sp);
		ob = getobuf(BNORMAL);
		ob = exparg(1, ib, ob, l);
		bufree(ib);
		break;

	case CTRLOC:
		return bsheap(NULL, "%d", counter++);

	default:
		/* Search for '(' */
		while (ISWSNL(c = cinput()))
			if (c == '\n')
				n++;
		if (c != '(') {
			putstr(sp->namep);
			if (n == 0)
				putch(' ');
			else for (ifiles->lineno += n; n; n--)
				putch('\n');
			cunput(c);
			return 0; /* Failed */
		}

		/* fetch arguments */
again:		if ((ab = readargs(NULL, sp, argary)) == 0)
			error("readargs");

		l = blkget(sp, 0);
		ib = subarg(sp, argary, 1, l);
		bufree(ab);
		ob = getobuf(BNORMAL);
		ob = exparg(1, ib, ob, l);
		bufree(ib);
		break;
	}

	/*
	 * Loop over ob, output the data and remove remaining  
	 * directives.  Start with extracting the last keyword (if any).
	 */
	putob(ob, 0); /* XXX needed? */

	if (outb == NULL)
		outb = getobuf(BNORMAL);

	if ((sp = loopover(ob, outb))) {
		/* Search for '(' */
		while (ISWSNL(c = cinput()))
			if (c == '\n')
				n++;
		if (c == '(') {
			bufree(ob);
			goto again;
		}
		cunput(c);
		strtobuf((usch *)sp->namep, outb);
	}
	bufree(ob);

	for (ifiles->lineno += n; n; n--)
		putob(outb, '\n');
	if (nbufused - oldused != 1)
		error("lost buffer");
	return outb;
}

/*
 * Replace and push-back on input stream the eventual replaced macro.
 * The check for whether it can expand or not should already have been done.
 * Blocks for this identifier will be added via insblock() after expansion.
 * The same as kfind but read a string.
 */
struct iobuf *
submac(struct symtab *sp, int lvl, register struct iobuf *ib, int l)
{
	int bl;
	register struct iobuf *ob, *ab;
	const usch *argary[MAXARGS+1];
	int cn;

	DPRINT(("%d:submac: trying '%s'\n", lvl, sp->namep));
	switch ((unsigned int)sp->type) {
	case FILLOC:
		ob = unfname();
		break;
	case LINLOC:
		ob = bsheap(NULL, "%d", ifiles->lineno);
		break;
	case PRAGLOC:
		pragoper(ib);
		ob = getobuf(BNORMAL);
		break;
	case DEFLOC:
	case OBJCT:
		bl = blkget(sp, l);
		ib = macrepbuf(sp);
		ob = getobuf(BNORMAL);
		DPRINT(("%d:submac: calling exparg\n", lvl));
		ob = exparg(lvl+1, ib, ob, bl);
		bufree(ib);
		DPRINT(("%d:submac: return exparg\n", lvl));
		break;
	case CTRLOC:
		ob = bsheap(NULL, "%d", counter++);
		break;
	default:
		cn = ib->cptr;
		while (ISWSNL(ib->buf[ib->cptr]))
			ib->cptr++;
		if (ib->buf[ib->cptr] != '(') {
			ib->cptr = cn;
			return 0;
		}
		cn = ib->cptr++;
		if ((ab = readargs(ib, sp, argary)) == 0) {
			/* Bailed out in the middle of arg list */
			ib->cptr = cn; /* XXX */
			return 0;
		}
		bl = blkget(sp, l);
		ib = subarg(sp, argary, lvl+1, bl);
		bufree(ab);

		ob = getobuf(BNORMAL);
		DPRINT(("%d:submac(: calling exparg\n", lvl));
		ob = exparg(lvl+1, ib, ob, bl);
		bufree(ib);
		DPRINT(("%d:submac(: return exparg\n", lvl));
		break;
	}
	putob(ob, 0);
	ob->cptr--;

	return ob;
}

static int
skpws(void)
{
	register int c;
	while ((c = cinput()) == ' ' || c == '\t')
		;
	return c;
}

/*
 * Read arguments and put in argument array.
 * Follow the guidelines from Fred Tydeman's proposal of line numbering.
 */
struct iobuf *
readargs(register struct iobuf *in, struct symtab *sp, const usch **args)
{
	usch *opbeg, *opend, *oinp;
	register struct iobuf *ab;
	register int c, infil, i, j, plev, narg, ellips = 0;
	int argary[MAXARGS+1];

	DPRINT(("readargs: in %p\n", in));
	narg = sp->narg;
	ellips = sp->type == VARG;

#ifdef __GNUC__
	opbeg = opend = oinp = 0;
#endif

	infil = ifiles->infil;
	if (in) {
		oinp = inp;
		opend = pend;
		opbeg = pbeg;
		ifiles->infil = -1;
		pbeg = in->buf;
		inp = pbeg + in->cptr;
		pend = pbeg + in->bsz;
	}

#ifdef PCC_DEBUG
	if (dflag > 1) {
		printf("narg %d varg %d: ", narg, ellips);
		prrep(sp->valoff);
		printf("\n");
	}
#endif

	/*
	 * read arguments and store them on heap.
	 */
	ab = getobuf(BNORMAL);
	c = '(';
	for (i = 0; i < narg && c != ')'; i++) {
		argary[i] = ab->cptr;
		plev = 0;

		c = skpws();
		for (;;) {
			if (plev == 0 && (c == ')' || c == ','))
				break;
			if (c == '(') plev++;
			if (c == ')') plev--;
			switch (c) {
			case 0:
				if (in) {
					in->cptr = inp - pbeg;
					pend = opend;
					inp = oinp;
					pbeg = opbeg;
					in = NULL;
				} else
					error("eof in macro");
				break;
			case BLKID2:
			case BLKID:
				putob(ab, c);
				putob(ab, *inp++);
				if (c == BLKID2)
					putob(ab, *inp++);
				break;
			case '/':
				if ((c = cinput()) == '*' || c == '/')
					Ccmnt2(ab, c);
				else {
					putob(ab, '/');
					cunput(c);
				}
				break;
			case '\n':
				escln++;
				c = skpws();
				if (c == '#') {
					ppdir();
				} else {
					/* only if not first char on line */
					if (argary[i] != ab->cptr)
						putob(ab, ' ');
					continue;
				}
				break;
			case '\"':
			case '\'':
				*--inp = c;
				fstrstr(NULL, ab);
				break;
			default:
				if (ISID0(c)) {
					bufid(c, ab);
				} else
					putob(ab, c);
				break;
			}
			c = cinput();
		}

		while (argary[i] < ab->cptr && ISWSNL(ab->buf[ab->cptr-1]))
			ab->cptr--;
		putob(ab, '\0');
#ifdef PCC_DEBUG
		if (dflag) {
			printf("readargs: save arg %d '", i);
			prline(ab->buf+argary[i]);
			printf("'\n");
		}
#endif
	}

	/* Handle varargs readin */
	argary[i] = ab->cptr;
	putob(ab, 0);
	ab->cptr--;
	if (ellips && c != ')') {
		plev = 0;
		c = skpws();
		for (;;) {
			if ((plev == 0 && c == ')') || c == 0)
				break;
			if (c == '(') plev++;
			if (c == ')') plev--;
			if (c == '\"' || c == '\'') {
				*--inp = c;
				fstrstr(NULL, ab);
			} else
				putob(ab, c);
			if ((c = cinput()) == '\n')
				escln++, c = ' ';
		}
		if (c == 0)
			error("unterminated macro invocation");
		while (argary[i] < ab->cptr && ISWSNL(ab->buf[ab->cptr-1]))
			ab->cptr--;
		putob(ab, '\0');
#ifdef PCC_DEBUG
		if (dflag) {
			printf("readargs: vararg arg %d '", i);
			prline(ab->buf+argary[i]);
			printf("'\n");
		}
#endif
	}
	if (ellips)
		i++;
	if (narg == 0 && ellips == 0)
		c = skpws();

	if (c != ')' || (i != narg && ellips == 0) || (i < narg && ellips == 1))
		error("wrong arg count");
	for (j = 0; j < i; j++)
		args[j] = ab->buf + argary[j];

	ifiles->infil = infil;
	if (in) {
		in->cptr = inp - pbeg;
		inp = oinp;
		pend = opend;
		pbeg = opbeg;
	}
	return ab;
}

/*
 * escape "\ inside strings.
 */
static void
escstr(register const usch *bp, register struct iobuf *ob)
{
	register int instr = 0;

	while (*bp) {
		if (!instr && ISWS(*bp)) {
			while (ISWS(*bp))
				bp++;
			putob(ob, ' ');
		}

		if (*bp == '\'' || *bp == '"') {
			instr ^= 1;
			if (*bp == '"')
				putob(ob, '\\');
		} 
		if (instr && *bp == '\\') {
			putob(ob, *bp);
			if (bp[1] == '\"') 
				putob(ob, *bp), putob(ob, *bp++);
		}
		putob(ob, *bp);
		bp++;
	}
}

/*
 * expand a function-like macro.
 * vp points to end of replacement-list
 * reads function arguments from input stream.
 * result is pushed-back for more scanning.
 */
struct iobuf *
subarg(struct symtab *nl, const usch **args, int lvl, int l)
{
	int lw;
	register struct iobuf *ob, *cb, *nb, *vb;
	int narg, snuff, c2;
	usch *sp, *vp;
	const usch *bp, *ap;

	DPRINT(("%d:subarg '%s'\n", lvl, nl->namep));
	ob = getobuf(BNORMAL);
	vb = macrepbuf(nl);
	vp = vb->buf;
	narg = nl->narg;

	sp = vp;
	snuff = 0;
#ifdef PCC_DEBUG
	if (dflag>1) {
		printf("%d:subarg ARGlist for %s: '", lvl, nl->namep);
		prrep(nl->valoff);
		printf("'\n");
		prblocker("subarg", l);
	}
#endif

	/*
	 * walk forward over replacement-list while replacing
	 * arguments.  Arguments are macro-expanded if required.
	 */
	while (*sp) {
		if (*sp == SNUFF)
			putob(ob, '\"'), snuff ^= 1;
		else if (*sp == CONC)
			;
		else if (*sp == WARN) {

			if (sp[1] == (usch)C99ARG) {
				bp = ap = args[narg];
				sp++;
#ifdef GCC_COMPAT
			} else if (sp[1] == (usch)GCCARG) {
				/* XXX remove last , not add 0 */
				ap = args[narg];
				if (ap[0] == 0)
					ap = (const usch *)"0";
				bp = ap;
				sp++;
#endif
			} else
				bp = ap = args[(unsigned char)*++sp];
#ifdef PCC_DEBUG
			if (dflag>1){
				printf("%d:subarg GOTwarn; arglist '", lvl);
				prline(bp);
				printf("'\n");
			}
#endif
			c2 = (sp-2 < vp ? 0 : sp[-2]);
			if (c2 != CONC && !snuff && sp[1] != CONC) {
				/*
				 * Expand an argument; 6.10.3.1:
				 * "A parameter in the replacement list,
				 *  is replaced by the corresponding argument
				 *  after all macros contained therein have
				 *  been expanded.".
				 */
				lw = l ? blokx[BLKBUF(l)][BLKPTR(l)].nidx : 0;
				nb = mkrobuf(bp);
				DPRINT(("%d:subarg: calling exparg\n", lvl));
				do {
					cb = nb;
					cb->cptr = 0;
					didexpand = 0;
					nb = getobuf(BNORMAL);
					nb = exparg(lvl+1, cb, nb, lw);
					bufree(cb);
				} while (didexpand);
				DPRINT(("%d:subarg: return exparg\n", lvl));
				strtobuf(nb->buf, ob);
				bufree(nb);
			} else {
				if (snuff)
					escstr(bp, ob);
				else
					strtobuf(bp, ob);
			}
		} else if (ISID0(*sp)) {
			if (lookup(sp, FIND))
				storeblk(l, ob);
			while (ISID(*sp))
				putob(ob, *sp++);
			sp--;
		} else
			putob(ob, *sp);
		sp++;
	}
	putob(ob, 0);
	ob->cptr = 0;
	DPRINT(("%d:subarg retline %s\n", lvl, ob->buf));
	bufree(vb);
	return ob;
}

/*
 * Do a (correct) expansion of a buffer of tokens.
 * Data is read from the input buffer, result on output buffer.
 * Expansion blocking is not altered here unless when tokens are
 * concatenated, in which case the blocking is removed.
 */
struct iobuf *
exparg(int lvl, register struct iobuf *ib, register struct iobuf *ob, int l)
{
	struct iobuf *nob, *tb;
	struct symtab *nl;
	int c, m;
	register usch *cp;

	DPRINT(("%d:exparg: entry ib %s\n", lvl, ib->buf+ib->cptr));
#ifdef PCC_DEBUG
	if (dflag > 1) {
		printf("exparg entry: full ");
		prline(ib->buf+ib->cptr);
		printf("\n");
		prblocker("exparg", l);
	}
#endif

	while ((c = getyp(ib->buf+ib->cptr)) != 0) {
		switch (c) {

		case CMNT:
			fcmnt(ib, ob);
			break;
		case NUMBER:
			fstrnum(ib, ob);
			break;
		case STRING:
			fstrstr(ib, ob);
			break;
		case BLKID2:
		case BLKID:
			m = (unsigned char)ib->buf[++ib->cptr];
			if (c == BLKID2)
				m = (m << 8) | (unsigned char)ib->buf[++ib->cptr];
			ib->cptr++;
			/* FALLTHROUGH */
		case IDENT:
			if (c == IDENT)
				m = 0;
			tb = getobuf(BNORMAL);
			cp = ib->buf+ib->cptr;
			for (; ISID(*cp) || *cp == BLKID || *cp == BLKID2; cp++) {
				if (*cp == BLKID || *cp == BLKID2) {
					/* XXX add to block list */
					cp++;
					if (cp[-1] == BLKID2)
						cp++;
				} else
					putob(tb, *cp);
			}
			tb->buf[tb->cptr] = 0;
			ib->cptr = (int)(cp - ib->buf);

			/* Any match? */
			if ((nl = lookup(tb->buf, FIND)) == NULL) {
				buftobuf(tb, ob);
			} else if (expokb(nl, l) && expok(nl, m) &&
			    (nob = submac(nl, lvl+1, ib, l))) {
				didexpand = 1;
				if (nob->buf[0] == '-' || nob->buf[0] == '+')
					putob(ob, ' ');
				strtobuf(nob->buf, ob);
				if (ob->cptr > 0 &&
				    (ob->buf[ob->cptr-1] == '-' ||
				     ob->buf[ob->cptr-1] == '+'))
					putob(ob, ' ');
				bufree(nob);
			} else {
				storeblk(mergeadd(l, m), ob);
				buftobuf(tb, ob);
			}
			bufree(tb);
			break;

		default:
			PUTOB(ob, c);
			ib->cptr++;
			break;
		}
	}
	putob(ob, 0);
	ob->cptr--;
	DPRINT(("%d:exparg return: ob %s\n", lvl, ob->buf));
#ifdef PCC_DEBUG
	if (dflag > 1) {
		printf("%d:exparg: full ", lvl);
		prline(ob->buf);
		printf("\n");
		prblocker("exparg", l);
	}
#endif
	return ob;
}

#ifdef PCC_DEBUG

static void
blkprint(int l)
{
	printf("<BLKID%s(", l > 255 ? "2" : "");
	for (; l; l = blokx[BLKBUF(l)][BLKPTR(l)].nidx)
		printf("%s ", blokx[BLKBUF(l)][BLKPTR(l)].sp->namep);
	printf(")>");
}

static void
prrep(mvtyp ptr)
{
	int s;

	while ((s = macget(ptr++))) {
		switch (s) {
		case WARN:
			s = macget(ptr++);
			if (s == (usch)C99ARG) printf("<C99ARG>");
			else if (s == (usch)GCCARG) printf("<GCCARG>");
			else printf("<ARG(%d)>", s);
			break;
		case CONC: printf("<CONC>"); break;
		case SNUFF: printf("<SNUFF>"); break;
		case BLKID: blkprint(macget(ptr++)); break;
		case BLKID2: blkprint(macget(ptr) << 8 | macget(ptr+1)); ptr += 2; break;
		default: printf("%c", s); break;
		}
	}
}

static void
prline(const usch *s)
{
	while (*s) {
		switch (*s) {
		case BLKID: blkprint((unsigned char)*++s); break;
		case BLKID2: blkprint((unsigned char)s[1] << 8 | (unsigned char)s[2]); s += 2; break;
		case WARN: printf("<WARN><ARG(%d)>", *++s); break;
		case CONC: printf("<CONC>"); break;
		case SNUFF: printf("<SNUFF>"); break;
		case '\n': printf("<NL>"); break;
		default: 
			if ((unsigned char)*s > 0x7f)
				printf("<0x%x>", *s);
			else
				printf("%c", *s);
			break;
		}
		s++;
	}
}
#endif

/*
 * Print out (eventual) saved \n.
 */
void
cntline(void)
{
	if (skpows < 10)
		for (; skpows > 0; skpows--)
			putchar('\n');
	else
		prtline(1);
	skpows = 0;
}

void
putch(register int ch)
{
	if (skpows) {
		if (ch == '\n')
			skpows++;
		if (ISWSNL(ch))
			return;
		cntline();
	} else if (ch == '\n' && tflag == 0) {
		skpows = 1;
		return;
	}
	if (Mflag == 0)
		putchar(ch);
}

void
putstr(const usch *s)
{
	if (skpows)
		cntline();
	fprintf(stdout, "%s", s);
}

/*
 * convert a number to an ascii string. Store it on the heap.
 */
static void
num2str(struct iobuf *ob, register int num)
{
	static usch buf[12];
	register usch *b = buf;
	register int m = 0;

	if (num < 0)
		num = -num, m = 1;
	do {
		*b++ = (usch)(num % 10 + '0');
		num /= 10;
	} while (num);
	if (m)
		*b++ = '-';
	while (b > buf)
		putob(ob, *--b);
}

/*
 * similar to sprintf, but only handles %c, %s and %d.
 * saves result on heap.
 */
static void
vsheap(register struct iobuf *ob, register const char *fmt, va_list ap)
{
	for (; *fmt; fmt++) {
		if (*fmt == '%') {
			fmt++;
			switch (*fmt) {
			case 's':
				strtobuf(va_arg(ap, usch *), ob);
				break;
			case 'd':
				num2str(ob, va_arg(ap, int));
				break;
			case 'c':
				putob(ob, va_arg(ap, int));
				break;
			default:
				error("bad sheap");
			}
		} else
			putob(ob, *fmt);
	}
	putob(ob, 0);
	ob->cptr--;
}

struct iobuf *
bsheap(register struct iobuf *ob, const char *fmt, ...)
{
	va_list ap;

	if (ob == NULL)
		ob = getobuf(BNORMAL);

	va_start(ap, fmt);
	vsheap(ob, fmt, ap);
	va_end(ap);

	return ob;
}

static void
usage(void)
{
	error("Usage: cpp [-Cdt] [-Dvar=val] [-Uvar] [-Ipath] [-Spath]");
}

/*
 * Allocate a symtab struct and store the string.
 */
static struct symtab *
getsymtab(const usch *str)
{
	register struct symtab *sp;

	sp = addblock(sizeof(*sp));

	sp->namep = str;
	sp->valoff = 0;
	sp->file = ifiles ? ifiles->orgfn : (const usch *)"<initial>";
	sp->line = ifiles ? ifiles->lineno : 0;
	return sp;
}

/*
 * Do symbol lookup.
 */
struct symtab *
lookup(usch *key, int enterf)
{
	register struct symtab *sp;
	register usch *k;
	register int len, hsh;

	/* Count full string length */
	for (hsh = 0, k = key; ISID(*k); k++)
		hsh += *k;
	hsh %= SYMHSZ;
	len = k - key;

	for (sp = symhsh[hsh]; sp; sp = sp->next)
		if (*sp->namep == *key && sp->namep[len] == 0 &&
		    strncmp(sp->namep, key, len) == 0)
			break;

	if (enterf == FIND) {
		if (sp && sp->valoff)
			return sp;
		return NULL;
	}

	/* symbol not found, enter into symtab */
	if (enterf == ENTER) {
		int ch = *k;
		*k = 0;
		key = addname(key);
		*k = ch;
	}
	sp = getsymtab(key);
	sp->next = symhsh[hsh];
	symhsh[hsh] = sp;
	return sp;
}

void *
xmalloc(int sz)
{
	register usch *rv;

	if ((rv = (void *)malloc(sz)) == NULL)
		error("xmalloc: out of mem");
	return rv;
}

void *
xrealloc(void *p, int sz)
{
	register usch *rv;

	if ((rv = (void *)realloc(p, sz)) == NULL)
		error("xrealloc: out of mem");
	return rv;
}

/*
 *
 */
static usch *
addname(const usch *str)
{
	static usch *nbase;
	static int nsz;
	const usch *w = str;
	usch *p;
	int len;

	while (*w++)
		;
	len = w - str;
	if (len > nsz) {
		nbase = xmalloc(MINBUF);
		nsz = MINBUF;
	}
	nsz -= len;
	p = nbase;
	while ((*nbase++ = *str++))
		;
	return p;
}

/*
 * Get permanent storage space for a struct.
 */
static void *
addblock(register int sz)
{
	static usch *nbase;
	static int nsz;
	register usch *str;

	/* round up to pointer alignment */
	sz = (sz + sizeof(int *)-1) & ~(sizeof(int *)-1);

	if (nsz < sz) {
		nbase = xmalloc(MINBUF);
		nsz = MINBUF;
	}
	str = nbase;
	nsz -= sz;
	nbase += sz;
	return str;
}

