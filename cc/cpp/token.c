/*
 * Copyright (c) 2004,2009 Anders Magnusson. All rights reserved.
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
 * Tokenizer for the C preprocessor.
 * There are three main routines:
 *	- fastscan() loops over the input stream searching for magic
 *		characters that may require actions.
 *	- yylex() returns something from the input stream that
 *		is suitable for yacc.
 *
 *	Other functions of common use:
 *	- inpch() returns a raw character from the current input stream.
 *	- inch() is like inpch but \\n are expanded.
 *	- unch() pushes back a character to the input stream.
 *
 * Input data can be read from either stdio or a buffer.
 * If a buffer is read, it will return EOF when ended and then jump back
 * to the previous buffer.
 *	- setibuf(usch *ptr). Buffer to read from, until NULL, return EOF.
 *		When EOF returned, pop buffer.
 *	- setobuf(usch *ptr).  Buffer to write to
 *
 * There are three places data is read:
 *	- fastscan() which has a small loop that will scan over input data.
 *	- flscan() where everything is skipped except directives (flslvl)
 *	- inch() that everything else uses.
 *
 * 5.1.1.2 Translation phases:
 *	1) Convert UCN to UTF-8 which is what pcc uses internally (chkucn).
 *	   Remove \r (unwanted)
 *	2) Remove \\\n.	 Need extra care for identifiers and #line.
 *	3) Tokenize.
 *	   Remove comments (fastcmnt)
 *
 * Handling of newline:
 *	- In a define with \\n, print out \n when found and inc lineno.
 *	- While expanding a macro whose args spans multiple lines, 
 *	  save in escln.
 */
/*  (low address)					      (high address)
 *  pbeg								pend
 *  |									  |
 *  _______________________________________________________________________
 * |_______________________________________________________________________|
 *	    |		    |		    |
 *	    |<-- waiting -->|		    |<-- waiting -->
 *	    |	 to be	    |<-- current -->|	 to be
 *	    |	 written    |	 token	    |	 scanned
 *	    |		    |		    |
 *	    outp	    inp		    p
 *
 *  *outp   first char not yet written to output file
 *  *inp    first char of current token
 *  *p	    first char not yet scanned
 */

#ifndef pdp11
#include "config.h"
#endif

#include <stdlib.h>
#include <string.h>
#if defined(HAVE_UNISTD_H) || defined(pdp11)
#include <unistd.h>
#endif
#include <fcntl.h>

#ifndef pdp11
#include "compat.h"
#endif
#include "cpp.h"

static void cvtdig(int);
static int dig2num(int);
static int charcon(void);
static void elsestmt(void);
static void ifdefstmt(void);
static void ifndefstmt(void);
static void endifstmt(void);
static void ifstmt(void);
static void cpperror(void);
static void cppwarning(void);
static void undefstmt(void);
static void pragmastmt(void);
static void elifstmt(void);

#define unch(x) *--inp = x

/* protection against recursion in #include */
#define MAX_INCLEVEL	100
int inclevel;
int incmnt, instr;
extern int skpows;
int escln;

struct includ *ifiles;
usch *pbeg, *inp, *pend;

/* used by yylex() buffer expansion */
static struct iobuf *lb;
static usch *lpbeg, *lpend, *linp;
static struct rdline *lifp;

static void ucn(int ch, FILE *ifp, FILE *ofp);
static void fastcmnt2(int);
static int chktg(int ch);

/* some common special combos for initialization */
#define C_NL	(C_SPEC|C_WSNL|C_PACK|C_ESTR)
#define C_DX	(C_SPEC|C_ID0|C_DIGIT)
#define C_I	(C_SPEC|C_ID0)
#define C_IX	(C_SPEC|C_ID0)
#define C_NBS	(C_SPEC|C_Q|C_PACK|C_ESTR)

#define FIRST_128							\
	C_NBS,	0,	0,	0,	C_SPEC, C_SPEC, 0,	0,	\
	0,	C_WSNL, C_NL,	0,	0,	C_PACK, 0,	0,	\
	0,	0,	0,	0,	0,	0,	0,	0,	\
	0,	0,	0,	0,	0,	0,	0,	0,	\
	\
	C_WSNL, C_2,	C_SPEC|C_ESTR, 0, 0,	0,	C_2,	C_SPEC|C_ESTR, \
	0,	0,	0,	C_2,	0,	C_2,	0,	C_SPEC|C_Q, \
	C_DX,	C_DX,	C_DX,	C_DX,	C_DX,	C_DX,	C_DX,	C_DX,	\
	C_DX,	C_DX,	0,	0,	C_2,	C_2,	C_2,	C_PACK, \
	\
	0,	C_IX,	C_IX,	C_IX,	C_IX,	C_IX,	C_IX,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	0,	C_PACK|C_ESTR,	0, 0,	C_I,	\
	\
	0,	C_IX,	C_IX,	C_IX,	C_IX,	C_IX,	C_IX,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	0,	C_2,	0,	0,	0,

/* utf-8 */
#define LAST_128							\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,

short spechr[256] = {
	FIRST_128 LAST_128
};

char cppmap[256] = {
	0,	0,	0,	0,	F_BID,	F_BID,	0,	0,
	0,	0,	0,	0,	0,	0,	0,	0,
	0,	0,	0,	0,	0,	0,	0,	0,
	0,	0,	0,	0,	0,	0,	0,	0,

	0,	0,	F_STR,	0,	0,	0,	0,	F_STR,
	0,	0,	0,	0,	0,	0,	F_DOT,	F_SLASH,
	F_NUM,	F_NUM,	F_NUM,	F_NUM,	F_NUM,	F_NUM,	F_NUM,	F_NUM,
	F_NUM,	F_NUM,	0,	0,	0,	0,	0,	0,

	0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_LU,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_LU,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	0,	0,	0,	0,	F_ID0,

	0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_LU,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	0,	0,	0,	0,	0,

	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,

	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,

	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,

	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,	F_ID0,
};


#define ENDFREE 4	/* space left at end of buffer */

#define INFLIRD (CPPBUF-ENDFREE)

/*
 * fill up the input buffer
 * n tells how nany chars at least.  0 == standard.
 * 0 if EOF, != 0 if something could fill up buf.
 */
int
inpbuf(void)
{
	struct rdline *rdp = ifiles->rdp;

	if (rdp == NULL)
		return 0;

	if (inp < pend)
		error("inp < pend");

	if (templine(ifiles->rdp) == NULL)
		return 0;

	inp = (usch *)rdp->curpos;
	pend = inp + rdp->len;
	return rdp->len;
}

/*
 * Return a quick-cooked character.
 * If buffer empty; return 0.
 */
static int
qcchar(void)
{
	register int ch;

newone: ch = *inp++;
	if (ISCQ(ch) == 0)
		return ch;

	switch (ch) {
	case '\n':
		*--inp = 0;
		return ch;

	case 0:
		inp--;
		if (lb) {
			pend = lpend, pbeg = lpbeg, inp = linp;
			ifiles->rdp = lifp;
			bufree(lb);
			lb = 0;
			goto newone;
		}
		if (inpbuf())
			goto newone;
		return 0; /* end of file */

	case '/':
		if (Cflag || incmnt || instr)
			return '/';
		incmnt++;
		ch = qcchar();
		incmnt--;
		if (ch == '/' || ch == '*') {
			int n = ifiles->lineno;
			fastcmnt2(ch);
			if (n == ifiles->lineno)
				return ' ';
		} else {
			*--inp = ch;
			return '/';
		}
		goto newone;
	}
	error("ch error: %d", ch);
	return 0; /* XXX */
}

/*
 * Return trigraph mapping char or 0.
 */
static int
chktg(register int ch)
{
	switch (ch) {
	case '=':  return '#';
	case '(':  return '[';
	case ')':  return ']';
	case '<':  return '{';
	case '>':  return '}';
	case '/':  return '\\';
	case '\'': return '^';
	case '!':  return '|';
	case '-':  return '~';
	}
	return 0;
}

/*
 * deal with comments in the fast scanner.
 */
static void
fastcmnt2(register int ch)
{
	register int lastline = ifiles->lineno;

	incmnt = 1;
	if (ch == '/') { /* C++ comment */
		while ((ch = qcchar()) != '\n')
			;
		unch(ch);
	} else if (ch == '*') {
		for (;;) {
			ch = *inp++;
			if (ISCQ(ch)) {
				--inp;
				if ((ch = qcchar()) == 0)
					break;
			}
			if (ch == '*') {
				if ((ch = qcchar()) == '/') {
					break;
				} else
					unch(ch);
			} else if (ch == '\n') {
				putch('\n');
				ifiles->lineno++;
			}
		}
	} else
		error("fastcmnt2");
	if (ch == 0)
		error("comment at line %d never ends", lastline);
	incmnt = 0;
}

/*
 * Skip over a comment.
 */
static char *
skpcmnt(char *s)
{
	char *lastw = s;

	s+=2;	/* skip initial / + * */
	for (;;) {
		while (*s != '*' && *s != '\n')
			s++;
		if (*s == '\n') {
			if (Cflag)
				putblk(lastw, s);
			putch('\n');
			ifiles->lineno++;
			if (templine(ifiles->rdp) == NULL)
				error("EOF in comment");
			lastw = s = ifiles->rdp->curpos;
			continue;
		}
		/* found a '*' */
		s++;
		if (*s == '/') {
			if (Cflag)
				putblk(lastw, s+1);
			return ++s;
		}
	}
}

/*
 * Skip over whitespaces and comments to next char.
 */
static char *
skpwscmnt(char *s)
{
	for (;;) {
		while (ISWS(*s))
			s++;
		if (*s == '/' && s[1] == '*')
			s = skpcmnt(s);
		else
			return s;
	}
}

/*
 * check for universal-character-name on input, and
 * write to the output buffer, encoded as UTF-8.
 */
static void
ucn(register int ch, FILE *ifp, FILE *ofp)
{
	unsigned long cp, m;
	usch bs[6], *p;
	int n;

	n = ch == 'u' ? 4 : 8;
	cp = 0;
	while (n-- > 0) {
		if ((ch = fgetc(ifp)) < 0 ||
		    (ISDIGIT(ch) || ((ch|040) >= 'a' && (ch|040) <= 'f')) == 0) {
#if 0			/* leave untouched */
			warning("invalid universal character name");
#endif
			return;
		}
		cp = cp * 16 + dig2num(ch);
	}

#if 0
	if ((cp < 0xa0 && cp != 0x24 && cp != 0x40 && cp != 0x60)
	    || (cp >= 0xd800 && cp <= 0xdfff))	/* 6.4.3.2 */
		error("universal character name cannot be used");

	if (cp > 0x7fffffff)
		error("universal character name out of range");
#endif

	if (cp == 0)
		return; /* ignore zeroes */
	n = 0;
	m = 0x7f;
	p = bs;
	while (cp > m) {
		*p++ = (0x80 | (cp & 0x3f));
		cp >>= 6;
		m >>= (n++ ? 1 : 2);
	}
	*p++ = (((m << 1) ^ 0xfe) | cp);
	while (p > bs) {
		fputc(*--p, ofp);
	}
}

/*
 * deal with comments when -C is active.
 * Save comments in expanded macros???
 */
void
Ccmnt2(register struct iobuf *ob, register int ch)
{

	if (skpows)
		cntline();

	if (ch == '/') { /* C++ comment */
		putob(ob, ch);
		do {
			putob(ob, ch);
		} while ((ch = qcchar()) && ch != '\n');
		unch(ch);
	} else if (ch == '*') {
		strtobuf((usch *)"/*", ob);
		for (;;) {
			ch = qcchar();
			putob(ob, ch);
			if (ch == '*') {
				if ((ch = qcchar()) == '/') {
					putob(ob, ch);
					break;
				} else
					unch(ch);
			} else if (ch == '\n') {
				ifiles->lineno++;
			}
		}
	}
}

/*
 * Traverse over spaces and comments from the input stream,
 * Returns first non-space character.
 */
static int
fastspc(void)
{
	register int ch;

	while ((ch = qcchar()), ISWS(ch))
		;
	return ch;
}

/*
 * readin chars and store in buf. Warn about too long names.
 */
usch *
bufid(int ch, register struct iobuf *ob)
{
	register int n = ob->cptr;

	do {
		if (ob->cptr - n == MAXIDSZ)
			warning("identifier exceeds C99 5.2.4.1");
		if (ob->cptr < ob->bsz)
			ob->buf[ob->cptr++] = ch;
		else
			putob(ob, ch);
	} while (ISID(ch = qcchar()));
	ob->buf[ob->cptr] = 0; /* legal */
	unch(ch);
	return ob->buf+n;
}

static usch *idbuf;
static int maxidsz;

/*
 * readin chars and store in buf. Warn about too long names.
 */
usch *
readid(int ch)
{
	register int p = 0;

	do {
		if (p == MAXIDSZ)
			warning("identifier exceeds C99 5.2.4.1");
		if (p == maxidsz)
			idbuf = xrealloc(idbuf, maxidsz += MAXIDSZ);
		idbuf[p++] = ch;
	} while (ISID(ch = qcchar()));
	idbuf[p] = 0;
	unch(ch);
	return idbuf;
}

/*
 * Scan quickly the input file searching for:
 *	- '#' directives
 *	- keywords (if not flslvl)
 *	- comments
 *
 *	Handle strings and numbers.
 *	Only data from pp files are scanned here, never any rescans.
 *	This loop is always at trulvl.
 */
void
fastscan(void)
{
	struct iobuf *ob;
	struct symtab *nl;
	register int ch, c2;
	struct rdline *rdp = ifiles->rdp;
	char *s, *p, *lastw;

	/*
	 * An outer and an inner loop.
	 * The outer loop reads in lines (terminated by \n), the inner loop
	 * checks each character.
	 * lastw is the last char written to the output buffer, and either
	 * when a macro is found or when the whole line is read the chars
	 * between s and lastw are written out.
	 */
	for (;;) {
		while (escln > 0) {
			ifiles->lineno++;
			putch('\n'), escln--;
		}
		if (templine(rdp) == NULL)
			return;
		s = lastw = rdp->curpos;
		if (Cflag == 0 && *s == '/' && s[1] == '*') {
			/* Remove leading comments */
			lastw = s = skpwscmnt(s);
		}
		// XXX compat
		inp = (usch *)s;
		pend = (usch *)rdp->curpos + rdp->len;
		// XXX end compat

		if (*s == '#') {
			inp++;
			ppdir(++s);
			escln++;
			s = skpwscmnt((char *)inp);
			continue;
		}

		/*
		 * Loop over string. Search for:
		 * - strings
		 * - Character constants
		 * - Comments (if Cflag)
		 * - cpp numbers
		 * - identifiers
		 *
		 * A continue statement will fetch next char for parsing.
		 * A break will:
		 * - flush unwritten parts of the input to output.
		 * - add the \n to the output.
		 * - write eventual saved \n to the output.
		 */
		for (;;) {
			ch = *s++;
			switch (F_TYP(ch)) {
			case 0:
				if (ch == '\n') {
					s--;
					break;
				}
				continue;

			case F_STR:
				while ((c2 = *s) && c2 != ch) {
					if (c2 == '\n') {
						warning("unterminated literal");
						break;
					}
					if (c2 == '\\')
						s++;
					s++;
				}
				s++;
				continue;

			case F_SLASH:
				if (*s == '/') { /* C++-style comment */
					s--; /* skip first / */
					if (Cflag)
						s = ifiles->rdp->line +
						    ifiles->rdp->len - 1;
					break;
				}
				if (*s != '*')
					continue;
				putblk(lastw, --s);
				lastw = s = skpcmnt(s);
				// XXX compat
				inp = (usch *)s;
				pend = (usch *)rdp->line + rdp->len;
				// XXX end compat
				continue;

			case F_DOT:
				if (F_TYP(*s) != F_NUM)
					continue;
				/* FALLTHROUGH */
			case F_NUM:
				for (;;) {
					ch = *s++;
					if ((F_ISID(ch)) == 0 && ch != '.')
						break;
					if ((ch|040) == 'e' || (ch|040) == 'p') 
{
						if ((c2 = *s) == '-' || c2 == '+')
							s++;
					}
				}
				s--;
				continue;

			case F_LU:
				if (*s == '\"' || *s == '\'')
					continue;
				if (ch == 'u' && *s == '8' && s[1] == '\"') {
					s++;
					continue;
				}
				/* FALLTHROUGH */

			case F_ID0:
				/*
				 * Search for identifier (quick look).
				 */
				p = s-1;
				while (F_ISID(*s))
					s++;
				if (flslvl)
					continue;
				if ((nl = lookup((usch *)p, FIND)) == NULL)
					continue;
				putblk(lastw, p);
				lastw = p;
				rdp->curpos = s;
				inp = (usch *)s;
				if ((ob = kfind(nl)) != NULL) {
					if (*ob->buf == '-' || *ob->buf == '+')
						putch(' ');
					if (skpows)
						cntline();
					ob->buf[ob->cptr] = 0;
					putstr(ob->buf);
					if (ob->cptr > 0 &&
					    (ob->buf[ob->cptr-1] == '-' ||
					    ob->buf[ob->cptr-1] == '+'))
						putch(' ');
					bufree(ob);
				}
				s = (char *)inp;
				rdp->curpos = s;
				lastw = s;
				continue;

			default:
				continue;
			}
			break;
		}
		if (s != lastw)
			putblk(lastw, s);
		escln++;
	}
}

/*
 */
int
yylex(void)
{
	extern int readinc;
	register int ch, c2, t;
	struct iobuf *ob;
	struct symtab *nl;

igen:	while ((ch = qcchar()) == ' ' || ch == '\t')
		;
	t = ISDIGIT(ch) ? NUMBER : ch;
	if (ch < 128 && (ISC2(ch)))
		c2 = qcchar();
	else
		c2 = 0;

	switch (t) {
	case '=':
		if (c2 == '=') ch = EQ;
		else goto pb;
		break;
	case '!':
		if (c2 == '=') ch = NE;
		else goto pb;
		break;
	case '|':
		if (c2 == '|') ch = OROR;
		else goto pb;
		break;
	case '&':
		if (c2 == '&') ch = ANDAND;
		else goto pb;
		break;
	case '<':
		if (readinc) {
			unch(c2);
			t = '>';
			goto str;
		}
		if (c2 == '<') ch = LS; else
		if (c2 == '=') ch = LE;
		else goto pb;
		break;
	case '>':
		if (c2 == '>') ch = RS; else
		if (c2 == '=') ch = GE;
		else goto pb;
		break;
	case '+':
	case '-':
		if (ch == c2)
			error("invalid preprocessor operator %c%c", ch, c2);
		goto pb;

	case 'L':
	case 'u':
	case 'U':
		if (*inp != '\'')
			goto ident;
		inp++;
		/* FALLTHROUGH */
	case '\'':
		yynode.op = NUMBER;
		yynode.nd_val = charcon();
		ch = NUMBER;
		break;

	case NUMBER:
		cvtdig(ch);
		ch = NUMBER;
		break;

	case '\"':
str:		ob = getobuf(BNORMAL);
		do {
			putob(ob, ch);
			if ((ch = qcchar()) == '\\') {
				putob(ob, ch);
				ch = qcchar();
			} else if (ch == '\n')
				error("bad lex string");
		} while (ch != t);
		putob(ob, ch);
		putob(ob, 0);
		ob->cptr--;
		yynode.nd_ob = ob;
		ch = STRING;
		break;

	case '\n':
		*--inp = t;
		ch = WARN;
		break;

	default:
ident:		if (ISID0(t) == 0)
			break;

		yynode.op = NUMBER;
		yynode.nd_val = 0;
		ch = NUMBER;
		if ((nl = lookup(readid(t), FIND))) {
			if (nl->type == DEFLOC) {
				c2 = 0;
				while ((t = qcchar()), ISWS(t))
					;
				if (t == '(')
					c2++, t = qcchar();
				yynode.nd_val = lookup(readid(t), FIND) != NULL;
				while ((t = qcchar()), ISWS(t))
					;
				if (c2) {
					if (t != ')')
						error("bad defined");
				} else
					*--inp = t;
			} else /* if (nl) */ {
				if (nl->type == FUNLIKE) {
					while ((t = qcchar()), ISWS(t))
						;
					*--inp = t;
					if (t != '(')
						break;
				}
				if ((ob = kfind(nl))) {
					ob->buf[ob->cptr] = 0;
					lpbeg = pbeg, lpend = pend, linp = inp;
					lifp = ifiles->rdp, ifiles->rdp = 0;
					lb = ob;
					inp = pbeg = ob->buf,
					    pend = pbeg + ob->cptr;
					goto igen;
				}
			}
		}
		break;
	}
	return ch;

pb:	*--inp = c2;
	return ch;
}

/*
 * Cleanup input file before parsing.
 *	- Convert trigraphs (if -T)
 *	- Convert UCN
 *	- Complain (and remove) unwanted characters
 *	- Remove \\n
 *	- Remove initial whitespace
 *	- Convert initial digraphs.
 */
static FILE *
cleanup(FILE *ifd)
{
	FILE *ofd = tmpfile();
	int ch, c2, beginning, numlf;

	beginning = 1;
	numlf = 0;
	while ((ch = getc(ifd)) != EOF) {
		if (ch < ' ') {
			if (ch == '\r' || ch == '\f')
				continue;
			if (ch != '\n' && ch != '\t')
				warning("input file has char %d, ignored", ch);
		}
		if (Tflag && ch == '?') {
	chk2:		if ((ch = fgetc(ifd)) == '?') {
				if (chktg(ch = fgetc(ifd))) {
					ch = chktg(ch);
				} else {
					ungetc(ch, ifd);
					fputc('?', ofd);
					goto chk2;
				}
			} else {
				ungetc(ch, ifd);
				ch = '?';
			}
		}
		if (ch == '\\') {
			if ((c2 = fgetc(ifd)) == 'u' || c2 == 'U') {
				/* UCN */
				ucn(c2, ifd, ofd);
				continue;
			}

			if (c2 == '\r')
				c2 = fgetc(ifd);
			if (c2 == '\n') {
				numlf++;
				continue;
			}
			ungetc(c2, ifd);
		}
		if (beginning) {
			if (ch == ' ' || ch == '\t')
				continue;
			if (ch == '%') {
				if ((c2 = fgetc(ifd)) == ':')
					ch = '#';
				else
					ungetc(c2, ifd);
			}
		}
		beginning = 0;
		putc(ch, ofd);
		if (ch == '\n') {
			beginning = 1;
			while (numlf) {
				fputc('\n', ofd);
				numlf--;
			}
		}
	}
	fclose(ifd);
	rewind(ofd);
	return ofd;
}

/*
 * A new file included.
 */
void
pushfile(FILE *ifp, const usch *file, int idx, void *incs)
{
	struct includ ibuf;
	struct rdline rdline;
	register struct includ *ic;
	register int otrulvl;
	struct rdline *rdp = &rdline;

	rdp = tempfile(cleanup(ifp));

	ic = &ibuf;
	ic->next = ifiles;
	ifiles = ic;

	ic->rdp = rdp;
	ic->orgfn = ic->fname = file;

	ic->opend = pend - pbeg;
	ic->oinp = inp - pbeg;
	ic->opbeg = pbeg;

	pend = inp = pbeg = xmalloc(ic->maxend = 5);

	*inp = 0;
	ic->lineno = 1;
	escln = 0;
	ic->idx = idx;
	ic->incs = incs;
	prtline(1);
	otrulvl = trulvl;

	fastscan();

	if (otrulvl != trulvl || flslvl)
		error("unterminated conditional");

	ifiles = ic->next;
	inclevel--;
	free(pbeg);
	pbeg = ic->opbeg;
	pend = pbeg + ic->opend;
	inp = pbeg + ic->oinp;

	tempclose(rdp);
}

/*
 * Print current position to output file.
 */
void
prtline(int nl)
{
	if (Mflag) {
		if (dMflag)
			return; /* no output */
		if (ifiles->lineno == 1 &&
		    (MMDflag == 0 || ifiles->idx != SYSINC) &&
		    ifiles->fname[0] != '<') {
			printf("%s: %s\n", Mfile, ifiles->fname);
			if (MPflag &&
			    strcmp((const char *)ifiles->fname, (char *)MPfile))
				printf("%s:\n", ifiles->fname);
		}
	} else if (!Pflag) {
		skpows = 0;
		printf("\n# %d \"%s\"", ifiles->lineno, ifiles->fname);
		if (ifiles->idx == SYSINC)
			printf(" 3");
		if (nl) printf("\n");
	} else
		putch('\n');
}

static int
dig2num(register int c)
{
	if (c >= 'a')
		c = c - 'a' + 10;
	else if (c >= 'A')
		c = c - 'A' + 10;
	else
		c = c - '0';
	return c;
}

/*
 * Convert string numbers to unsigned long long and check overflow.
 */
static void
cvtdig(register int c)
{
	unsigned long long rv = 0;
	unsigned long long rv2 = 0;
	register int rad;

	if (c == '0') {
		rad = 8;
		if (((c = qcchar()) | 0x20) == 'x') {
			rad <<= 1;
			c = qcchar();
		} else
			*--inp = c, c = '0';
	} else
		rad = 10;

	while (ISDIGIT(c) || ((c|040) >= 'a' && (c|040) <= 'f')) {
		rv = rv * rad + dig2num(c);
		/* check overflow */
		if (rv / rad < rv2)
			error("constant is out of range");
		rv2 = rv;
		c = qcchar();
	}

	yynode.op = NUMBER;
	while ((c | 0x20) == 'l' || (c | 0x20) == 'u') {
		if ((c | 0x20) == 'u')
			yynode.op = UNUMBER;
		c = qcchar();
	}
	*--inp = c;
	yynode.nd_uval = rv;
	if ((rad == 8 || rad == 16) && yynode.nd_val < 0)
		yynode.op = UNUMBER;
	if (yynode.op == NUMBER && yynode.nd_val < 0)
		/* too large for signed, see 6.4.4.1 */
		error("constant is out of range");
}

static int
charcon(void)
{
	register int val, c;

	val = 0;
	if ((c = qcchar()) == '\\') {
		switch (c = qcchar()) {
		case 'a': val = '\a'; break;
		case 'b': val = '\b'; break;
		case 'f': val = '\f'; break;
		case 'n': val = '\n'; break;
		case 'r': val = '\r'; break;
		case 't': val = '\t'; break;
		case 'v': val = '\v'; break;
		case '\"': val = '\"'; break;
		case '\'': val = '\''; break;
		case '\\': val = '\\'; break;
		case 'x':
			while (ISDIGIT(c = qcchar()) ||
			    ((c|040) >= 'a' && (c|040) <= 'f'))
				val = val * 16 + dig2num(c);
			*--inp = c;
			break;
		case '0': case '1': case '2': case '3': case '4':
		case '5': case '6': case '7':
			do
				val = val * 8 + (c - '0');
			while ((ISDIGIT(c = qcchar())));
			*--inp = c;
			break;
		default: val = c;
		}

	} else
		val = c;
	if (qcchar() != '\'')
		error("bad charcon");
	return val;
}

static void
chknl(int ignore)
{
	register void (*f)(const char *, ...);
	register int t, c;

	c = Cflag;
	Cflag = 0;
	f = ignore ? warning : error;
	if ((t = fastspc()) != '\n') {
		if (t) {
#ifndef pdp11
			f("newline expected");
#endif
			/* ignore rest of line */
			while ((t = qcchar()) > 0 && t != '\n')
				;
		} else
			f("no newline at end of file");
	}
	Cflag = c;
	unch(t);
}

static void
elsestmt(void)
{
	if (flslvl) {
		if (elflvl > trulvl)
			;
		else if (--flslvl!=0)
			flslvl++;
		else
			trulvl++;
	} else if (trulvl) {
		flslvl++;
		trulvl--;
	} else
		error("#else in non-conditional section");
	if (elslvl==trulvl+flslvl)
		error("too many #else");
	elslvl=trulvl+flslvl;
	chknl(1);
}

#define TYP_ELIF	1
#define TYP_ELIFDEF	2
#define TYP_ELIFNDEF	3
static void elifcommon(int typ);
static int chktyp(int typ);

static void
ifdefstmt(void)
{
	if (chktyp(TYP_ELIFDEF))
		trulvl++;
	else
		flslvl++;
}

static void
ifndefstmt(void)
{
	if (chktyp(TYP_ELIFNDEF))
		trulvl++;
	else
		flslvl++;
}

static void
endifstmt(void)
{
	if (flslvl)
		flslvl--;
	else if (trulvl)
		trulvl--;
	else
		error("#endif in non-conditional section");
	if (flslvl == 0)
		elflvl = 0;
	elslvl = 0;
	chknl(1);
}

static void
ifstmt(void)
{
	register int oCflag = Cflag;

	Cflag = 0;
	yyparse() ? trulvl++ : flslvl++;
	Cflag = oCflag;
}

static void
elifstmt(void)
{
	return elifcommon(TYP_ELIF);
}

static void
elifdefstmt(void)
{
	return elifcommon(TYP_ELIFDEF);
}

static void
elifndefstmt(void)
{
	return elifcommon(TYP_ELIFNDEF);
}


static int
chktyp(int typ)
{
	register usch *bp;
	register int rv, ch;

	if (typ == TYP_ELIF)
		return yyparse();

	if (!ISID0(ch = fastspc()))
		error("bad #elifdef");
	bp = readid(ch);
	rv = lookup(bp, FIND) == NULL;
	if (typ == TYP_ELIFDEF)
		rv = !rv;
	chknl(0);
	return rv;
}


static void
elifcommon(int typ)
{
	register int oCflag = Cflag;

	Cflag = 0;
	if (flslvl == 0)
		elflvl = trulvl;
	if (flslvl) {
		if (elflvl > trulvl)
			;
		else if (--flslvl!=0)
			flslvl++;
		else if (chktyp(typ))
			trulvl++;
		else
			flslvl++;
	} else if (trulvl) {
		flslvl++;
		trulvl--;
	} else
		error("#elif in non-conditional section");
	Cflag = oCflag;
}

/* save line into iobuf */
static void
prwoe(void)
{
	register usch *p;

	p = inp;
	for (;;) {
		while (ISESTR(*p++) == 0)
			;
		if (*--p == 0) {
			fprintf(stderr, "%s", inp);
			inp = p;
			inpbuf();
			p = inp-1;
		} else if (*p == '\n')
			break;
		p++;
	}
	*p = 0;
	fprintf(stderr, "%s\n", inp);
	*p = '\n';
	inp = p;
}

static void
cpperror(void)
{
	if (flslvl)
		return;
	fflush(stdout);

	fprintf(stderr, "#error");
	prwoe();
	exit(1);
}

static void
cppwarning(void)
{
	extern int warnings;

	if (flslvl)
		return;
	fprintf(stderr, "#warning");
	prwoe();
	warnings++;
}

static void
undefstmt(void)
{
	register struct symtab *np;
	register usch *bp;
	register int ch;

	if (flslvl)
		return;
	if (!ISID0(ch = fastspc()))
		error("bad #undef");
	bp = readid(ch);
	if ((np = lookup(bp, FIND)) != NULL)
		np->macoff = 0;
	chknl(0);
}

static void
identstmt(void)
{
	int x = 0;

	if (flslvl)
		return;
	if (yylex() == STRING) {
		bufree(yynode.nd_ob);
		x = yylex();
	}
	if (x != WARN)
		error("bad #ident directive");
}

static void
pragmastmt(void)
{
	register int ch;

	if (flslvl)
		return;
	putstr((const usch *)"\n#pragma");
	while ((ch = qcchar()) != '\n' && ch > 0)
		putch(ch);
	unch(ch);
	prtline(1);
}

int
cinput(void)
{

	return qcchar();
}

#define DIR_FLSLVL	001
#define DIR_FLSINC	002
static struct {
	const char *name;
	void (*fun)(void);
	int flags;
} ppd[] = {
	{ "ifndef", ifndefstmt, DIR_FLSINC },
	{ "ifdef", ifdefstmt, DIR_FLSINC },
	{ "if", ifstmt, DIR_FLSINC },
	{ "include", include, 0 },
	{ "else", elsestmt, DIR_FLSLVL },
	{ "endif", endifstmt, DIR_FLSLVL },
	{ "error", cpperror, 0 },
	{ "warning", cppwarning, 0 },
	{ "define", define, 0 },
	{ "undef", undefstmt, 0 },
	{ "line", line, 0 },
	{ "pragma", pragmastmt, 0 },
	{ "elif", elifstmt, DIR_FLSLVL },
	{ "elifdef", elifdefstmt, DIR_FLSLVL },
	{ "elifndef", elifndefstmt, DIR_FLSLVL },
	{ "ident", identstmt, 0 },
#ifdef GCC_COMPAT
	{ "include_next", include_next, 0 },
#endif
};
#define NPPD	(int)(sizeof(ppd) / sizeof(ppd[0]))

static void
skpln(void)
{
	register int ch;

	/* just ignore the rest of the line */
	while ((ch = qcchar()) != 0) {
		if (ch == '\n') {
			unch('\n');
			break;
		}
	}
}

/*
 * Handle a preprocessor directive.
 * # is already found.
 */
void
ppdir(char *s)
{
	register int ch, i;
	char *bp;

	s = skpwscmnt(s);
	if (*s == '\n') {
		inp = (usch *)s;
		return;
	}

	for (bp = s; F_ISID(*s); s++)
		;
	ch = *s, *s = 0;
	for (i = 0; i < NPPD; i++)
		if (strcmp(bp, ppd[i].name) == 0)
			break;
	if (i == NPPD || !F_ISWSNL(ch))
		goto bad;

	*s = ch;
	inp = (usch *)s;
	if (flslvl == 0) {
		(*ppd[i].fun)();
		if (flslvl == 0)
			return;
	} else {
		if (ppd[i].flags & DIR_FLSLVL) {
			(*ppd[i].fun)();
			if (flslvl == 0)
				return;
		} else if (ppd[i].flags & DIR_FLSINC)
			flslvl++;
	}
	return;

bad:
	if (flslvl == 0 && Aflag == 0)
		error("invalid preprocessor directive");

	unch(ch);
	skpln();
}
