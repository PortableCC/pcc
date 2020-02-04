/*	$Id$	*/

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
 *	- inch() is like inpch but \\n and trigraphs are expanded.
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
 *	   Convert trigraphs (chktg)
 *	2) Remove \\\n.  Need extra care for identifiers and #line.
 *	3) Tokenize.
 *	   Remove comments (fastcmnt)
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

#define	unch(x)	*--inp = x

/* protection against recursion in #include */
#define MAX_INCLEVEL	100
int inclevel;
int incmnt, instr;
extern int skpows;

struct includ *ifiles;
usch *pbeg, *outp, *inp, *pend;

/* used by yylex() buffer expansion */
static struct iobuf *lb;
static usch *lpbeg, *lpend, *linp;
static int lif;

static void ucn(int n);
static void fastcmnt2(int);
static int chktg2(int ch);

/* some common special combos for initialization */
#define C_NL	(C_SPEC|C_WSNL)
#define C_DX	(C_SPEC|C_ID0|C_DIGIT|C_HEX)
#define C_I	(C_SPEC|C_ID0)
#define C_IX	(C_SPEC|C_ID0|C_HEX)
#define C_NBS	(C_SPEC|C_Q|C_PACK)

#define FIRST_128							\
	C_NBS,	0,	0,	0,	C_SPEC,	C_SPEC,	0,	0,	\
	0,	C_WSNL,	C_NL,	0,	0,	C_PACK, 0,	0,	\
	0,	0,	0,	0,	0,	0,	0,	0,	\
	0,	0,	0,	0,	0,	0,	0,	0,	\
	\
	C_WSNL,	C_2,	C_SPEC,	0,	0,	0,	C_2,	C_SPEC,	\
	0,	0,	0,	C_2,	0,	C_2,	0,	C_SPEC|C_Q, \
	C_DX,	C_DX,	C_DX,	C_DX,	C_DX,	C_DX,	C_DX,	C_DX,	\
	C_DX,	C_DX,	0,	0,	C_2,	C_2,	C_2,	C_PACK,	\
	\
	0,	C_IX,	C_IX,	C_IX,	C_IX,	C_IX,	C_IX,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	C_I,	\
	C_I,	C_I,	C_I,	0,	C_NBS,	0,	0,	C_I,	\
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

usch spechr[256] = {
#ifdef CHAR_UNSIGNED
	FIRST_128 LAST_128
#else
	LAST_128 FIRST_128
#endif
};

#define	ENDFREE	4	/* space left at end of buffer */

#if LIBVMF
#define	INFLIRD	(BYTESPERSEG-PBMAX-ENDFREE)
#else
#define	INFLIRD	(CPPBUF-PBMAX-ENDFREE)
#endif

/*
 * Convert trigraphs and remove \\n from input stream.
 */
static void
packbuf(void)
{
	static usch pbb[2];
	register usch *p, *q;
	register int l;

	/* if we found potential trigraph */
	if (pbb[0]) {
		*--inp = pbb[0];
		if (pbb[1])
			*--inp = pbb[1];
		pbb[0] = pbb[1] = 0;
	}

	p = inp;
	q = NULL;
fast:	while (ISPACK(*p++) == 0)
		;
	if (--p >= pend)
		return;

	switch ((l = *p++)) {
	case '?':
		if (*p == '?') {
			if ((l = chktg2(p[1])))
				goto slow;
		}
		if (pend-p < 3) {
			/* Save for future use */
			if (p[1])
				pbb[0] = p[1], pbb[1] = *p;
			else
				pbb[0] = *p;
			*p = 0;
			pend = p;
			return;
		}
		break;
	case '\r':
		goto slow;
	default:
		break;
	}
	goto fast;

/* need to pack, so we must write as well */
slow:	q = --p;

more:	if (*p == '\r') {
		p++;
	} else if (*p == '?' && p[1] == '?' && (l = chktg2(p[2]))) {
		/* found trigraph */
		*q++ = l;
		p += 3;
	} else p++, q++;
	while (ISPACK(*q++ = *p++) == 0)
		;
	if (--p >= pend) {
		*--q = 0;
		pend = q;
		return;
	}
	q--;
	goto more;

}

/*
 * fill up the input buffer
 * n tells how nany chars at least.  0 == standard.
 * 0 if EOF, != 0 if something could fill up buf.
 */
static int
inpbuf(int n)
{
	register int len, sz = 0;
	register usch *rdpos;

	if (n > 0) {
		if (pend > inp + n)
			return 1; /* enough in buffer */
		sz = pend - inp;
		memcpy(pbeg+PBMAX - sz, inp, sz);
	}

	if (ifiles->infil == -1)
		return 0;
	rdpos = pbeg+PBMAX;
	pend = rdpos+INFLIRD;
	do {
		if ((len = (int)read(ifiles->infil, rdpos, pend - rdpos)) < 0)
			error("read error on file %s", ifiles->orgfn);
		if (len == 0)
			break;
		rdpos += len;
	} while (rdpos < pend);

	*rdpos = 0;
	pend = rdpos;
	inp = pbeg + PBMAX - sz;
	packbuf();
	return pend - inp;
}

/*
 * Return a quick-cooked character.
 * If buffer empty; return 0.
 */
static int
qcchar(void)
{
	register int ch;

newone:	do {
		if (inp < pend) {
			if (!ISCQ(ch = *inp++))
				return ch;
			break;
		}
	} while ((ch = inpbuf(0)) > 0);

	switch (ch) {
	case 0:
		if (lb) {
			pend = lpend, pbeg = lpbeg, inp = linp;
			ifiles->infil = lif;
			bufree(lb);
			lb = 0;
			goto newone;
		}
		return 0; /* end of file */

	case '\\':
		if (inp == pend)
			inpbuf(0);
		switch (ch = *inp) {
		case 'u':
		case 'U': 
			if (incmnt) 
				return '\\';
			inp++;
			ucn(ch == 'u' ? 4 : 8);
			break;
		case '\n':
			inp++;
			ifiles->escln++;
			break;
		default:
			return '\\';
		}
		goto newone;

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
	error("ch error");
	return 0; /* XXX */
}

/*
 * Return trigraph mapping char or 0.
 */
static int
chktg2(register int ch)
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
 * check for universal-character-name on input, and
 * unput to the pushback buffer encoded as UTF-8.
 */
static void
ucn(register int n)
{
	unsigned long cp, m;
	register int ch;

	if (incmnt) {
		inp--;
		*--inp = '\\';
		return;
	}

	cp = 0;
	while (n-- > 0) {
		if ((ch = (unsigned char)qcchar()) == 0 || (ISHEX(ch)) == 0) {
			warning("invalid universal character name");
			/* XXX should actually unput the chars and return 0 */
			unch(ch); /* XXX eof */
			break;
		}
		cp = cp * 16 + dig2num(ch);
	}

	if ((cp < 0xa0 && cp != 0x24 && cp != 0x40 && cp != 0x60)
	    || (cp >= 0xd800 && cp <= 0xdfff))	/* 6.4.3.2 */
		error("universal character name cannot be used");

	if (cp > 0x7fffffff)
		error("universal character name out of range");

	n = 0;
	m = 0x7f;
	while (cp > m) {
		unch(0x80 | (cp & 0x3f));
		cp >>= 6;
		m >>= (n++ ? 1 : 2);
	}
	unch(((m << 1) ^ 0xfe) | cp);
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

usch idbuf[MAXIDSZ+1];
/*
 * readin chars and store in buf. Warn about too long names.
 */
usch *
readid(int ch)
{
	register int p = 0;

	do {
		if (p == MAXIDSZ)
			warning("identifier exceeds C99 5.2.4.1, truncating");
		if (p < MAXIDSZ)
			idbuf[p] = ch;
		p++;
	} while (ISID(ch = qcchar()));
	idbuf[p] = 0;
	unch(ch);
	return idbuf;
}

/*
 * get a string or character constant and save it as given by d.
 */
struct iobuf *
faststr(int bc, register struct iobuf *ob)
{
	register int ch;

	if (ob == NULL)
		ob = getobuf(BNORMAL);

	instr = 1;
	putob(ob, bc);
	for (;;) {
		if (inp == pend)
			ch = qcchar();
		else if (ISCQ(ch = *inp))
			ch = qcchar();
		else
			inp++;
		switch (ch) {
		case '\\':
			putob(ob, ch);
			if (inp == pend)
				inpbuf(0);
			incmnt = 1;
			putob(ob, qcchar());
			incmnt = 0;
			continue;
		case '\n':
			warning("unterminated literal");
			instr = 0;
			unch(ch);
			return ob;
		}
		putob(ob, ch);
		if (ch == bc)
			break;
	}
	putob(ob, 0);
	ob->cptr--;
	instr = 0;
	return ob;
}

/*
 * get a preprocessing number and save it as given by ob.
 * returns first non-pp-number char.
 * We know that this is a valid number already.
 *
 *	pp-number:	digit
 *			. digit
 *			pp-number digit
 *			pp-number identifier-nondigit
 *			pp-number e sign
 *			pp-number E sign
 *			pp-number p sign
 *			pp-number P sign
 *			pp-number .
 */
int
fastnum(register int ch, register struct iobuf *ob)
{
	register int c2;

	if (ch == '.') { /* not digit, dot */
		putob(ob, ch);
		ch = qcchar();
	}
	for (;;) {
		putob(ob, ch);
		if ((ch = qcchar()) == 0)
			break;
		if ((ISID(ch)) == 0 && ch != '.')
			break;
		if (ch == 'e' || ch == 'E' || ch == 'p' || ch == 'P') {
			if ((c2 = qcchar()) == '-' || c2 == '+') {
				putob(ob, ch);
				ch = c2;
				continue;
			}
			unch(c2);
		}
	}
	return ch;
}

/*
 * Scan quickly the input file searching for:
 *	- '#' directives
 *	- keywords (if not flslvl)
 *	- comments
 *
 *	Handle strings, numbers and trigraphs with care.
 *	Only data from pp files are scanned here, never any rescans.
 *	This loop is always at trulvl.
 */
void
fastscan(void)
{
	register struct iobuf *ob;
	extern struct iobuf pb;
	struct symtab *nl;
	register int ch, c2;
	usch *dp;

	goto run;

	for (;;) {
		/* tight loop to find special chars */
		/* should use getchar/putchar here */
		for (;;) {
			if (inp < pend)
				ch = *inp++;
			else
				ch = qcchar();
xloop:
			if ((ISSPEC(ch)) != 0)
				break;
			putch(ch);
		}

		switch (ch) {
		case 0:
			return;

		case WARN:
		case CONC:
			error("bad char passed");
			break;

		case '/': /* Comments */
			incmnt++;
			ch = qcchar();
			incmnt--;
			if (ch  == '/' || ch == '*') {
				if (Cflag == 0) {
					int n = ifiles->lineno;
					fastcmnt2(ch);
					if (n == ifiles->lineno)
						putch(' '); /* 5.1.1.2 p3 */
				} else
					Ccmnt2(&pb, ch);
			} else {
				putch('/');
				goto xloop;
			}
			break;

		case '\n': /* newlines, for pp directives */
			/* take care of leftover \n */
			while (ifiles->escln > 0) {
				putch('\n');
				ifiles->escln--;
				ifiles->lineno++;
			}
			putch('\n');
			ifiles->lineno++;

			/* search for a # */
run:			while ((ch = qcchar()) == '\t' || ch == ' ')
				putch(ch);
			if (ch == '%') {
				if ((c2 = qcchar()) != ':')
					unch(c2);
				else
					ch = '#';
			}
			if (ch  == '#')
				ppdir();
			else
				goto xloop;
			break;

		case '\'': /* character constant */
			if (tflag) {
				putch(ch);
				break;	/* character constants ignored */
			}
			/* FALLTHROUGH */
		case '\"': /* strings */
			if (skpows)
				cntline();
			faststr(ch, &pb);
			break;

		case '0': case '1': case '2': case '3': case '4':
		case '5': case '6': case '7': case '8': case '9':
			if (skpows)
				cntline();
			ch = fastnum(ch, &pb);
			goto xloop;

		case 'L':
		case 'U':
		case 'u':
			if (inp+2 >= pend)
				inpbuf(2);
			if ((c2 = *inp) == '\"' || c2 == '\'') {
				putch(ch);
				break;
			} if (c2 == '8' && ch == 'u' && inp[1] == '\"') {
				inp++;
				putstr((usch *)"u8");
				break;
			}
			/* FALLTHROUGH */
		default:
#ifdef PCC_DEBUG
			if ((ISID(ch)) == 0)
				error("fastscan");
#endif
			if (flslvl)
				error("fastscan flslvl");

			dp = readid(ch);
			if ((nl = lookup(dp, FIND)) != NULL) {
				if ((ob = kfind(nl)) != NULL) {
					if (*ob->buf == '-' || *ob->buf == '+')
						putch(' ');
					if (skpows)
						cntline();
					buftobuf(ob, &pb);
					if (ob->cptr > 0 &&
					    (ob->buf[ob->cptr-1] == '-' ||
					    ob->buf[ob->cptr-1] == '+'))
						putch(' ');
					bufree(ob);
				}
			} else {
				putstr(dp);
			}
			break;

		case '\\':
			*--inp = '\\';
			if ((ch = qcchar()) != '\\')
				goto xloop;
			putch('\\');
			break;
		}
	}
}

/*
 */
int
yylex(void)
{
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

	case '\'':
		yynode.op = NUMBER;
		yynode.nd_val = charcon();
		ch = NUMBER;
		break;

	case NUMBER:
		cvtdig(ch);
		ch = NUMBER;
		break;

	case '\n':
		*--inp = t;
		ch = WARN;
		break;

	default:
		if (ISID0(t) == 0)
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
					lif = ifiles->infil, ifiles->infil = -1;
					lb = ob;
					inp = pbeg = ob->buf,
					    pend = pbeg + ob->cptr;
					goto igen;
				}
			}
		}
		break;
	}
//fprintf(stderr, "uulex1: ch '%c' %d val=%lld '%s'\n", ch, ch, yynode.nd_val, inp);
	return ch;

pb:	*--inp = c2;
//fprintf(stderr, "uulex2: ch '%c' %d val=%lld '%s'\n", ch, ch, yynode.nd_val, inp);
	return ch;
}

/*
 * A new file included.
 * If ifiles == NULL, this is the first file and already opened (stdin).
 */
void
pushfile(const usch *file, const usch *fn, int idx, void *incs)
{
	struct includ ibuf;
	register struct includ *ic;
	register int otrulvl;

	ic = &ibuf;
	ic->next = ifiles;

	if (file != NULL) {
		if ((ic->infil = open((const char *)file, O_RDONLY)) < 0)
			error("pushfile: error open %s", file);
		ic->orgfn = ic->fname = file;
		if (++inclevel > MAX_INCLEVEL)
			error("limit for nested includes exceeded");
	} else {
		ic->infil = 0;
		ic->orgfn = ic->fname = (const usch *)"<stdin>";
	}
#if LIBVMF
	if (ifiles) {
		vmmodify(ifiles->vseg);
		vmunlock(ifiles->vseg);
	}
	ic->vseg = vmmapseg(&ibspc, inclevel);
	vmlock(ic->vseg);
#endif
	ifiles = ic;

	ic->opend = pend - pbeg;
	ic->oinp = inp - pbeg;
	ic->opbeg = pbeg;
	/* dump(); */
#if LIBVMF
	pend = inp = pbeg = (usch *)ifiles->vseg->s_cinfo;
#else
	pend = inp = pbeg = xmalloc(CPPBUF);
#endif
	ic->lineno = 1;
	ic->escln = 0;
	ic->idx = idx;
	ic->incs = incs;
	ic->fn = fn;
	prtline(1);
	otrulvl = trulvl;

	fastscan();

	if (otrulvl != trulvl || flslvl)
		error("unterminated conditional");

	ifiles = ic->next;
	inclevel--;
#if LIBVMF
	vmmodify(ic->vseg);
	vmunlock(ic->vseg);
	if (ifiles) {
		ifiles->vseg = vmmapseg(&ibspc, inclevel);
		vmlock(ifiles->vseg);

		pbeg = (usch *)ifiles->vseg->s_cinfo;
		pend = pbeg + ic->opend;
		inp = pbeg + ic->oinp;
		/* XXX adjust offsets */
	}
#else /* LIBVMF */
	free(pbeg);
	pbeg = ic->opbeg;
	pend = pbeg + ic->opend;
	inp = pbeg + ic->oinp;
#endif /* LIBVMF */
	close(ic->infil);
}

/*
 * Print current position to output file.
 */
void
prtline(int nl)
{
	register struct iobuf *ob;

	if (Mflag) {
		if (dMflag)
			return; /* no output */
		if (ifiles->lineno == 1 &&
		    (MMDflag == 0 || ifiles->idx != SYSINC)) {
			ob = bsheap(0, "%s: %s\n", Mfile, ifiles->fname);
			if (MPflag &&
			    strcmp((const char *)ifiles->fname, (char *)MPfile))
				bsheap(ob, "%s:\n", ifiles->fname);
			write(1, ob->buf, ob->cptr);
			bufree(ob);
		}
	} else if (!Pflag) {
		skpows = 0;
		bsheap(&pb, "\n# %d \"%s\"", ifiles->lineno, ifiles->fname);
		if (ifiles->idx == SYSINC)
			strtobuf((usch *)" 3", &pb);
		if (nl) strtobuf((usch *)"\n", &pb);
	} else
		putob(&pb, '\n');
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

	while ((ISHEX(c))) {
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
			while ((ISHEX(c = qcchar())))
				val = val * 16 + dig2num(c);
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
	register int t;

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

static void
ifdefstmt(void)
{
	register usch *bp;
	register int ch;

	if (!ISID0(ch = fastspc()))
		error("bad #ifdef");
	bp = readid(ch);

	if (lookup(bp, FIND) == NULL)
		flslvl++;
	else
		trulvl++;
	chknl(0);
}

static void
ifndefstmt(void)
{
	register usch *bp;
	register int ch;

	if (!ISID0(ch = fastspc()))
		error("bad #ifndef");
	bp = readid(ch);
	if (lookup(bp, FIND) != NULL)
		flslvl++;
	else
		trulvl++;
	chknl(0);
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
	register int oCflag = Cflag;

	Cflag = 0;
	if (flslvl == 0)
		elflvl = trulvl;
	if (flslvl) {
		if (elflvl > trulvl)
			;
		else if (--flslvl!=0)
			flslvl++;
		else if (yyparse())
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
struct iobuf *
savln(void)
{
	register struct iobuf *ob = getobuf(BNORMAL);
	register int c;

	while ((c = qcchar()) != 0) {
		if (c == '\n') {
			unch(c);
			break;
		}
		if (c == '\'' || c == '\"')
			faststr(c, ob);
		else
			putob(ob, c);
	}
	ob->buf[ob->cptr] = 0;
	return ob;
}

static void
cpperror(void)
{
	register struct iobuf *ob = savln();
	error("#error%s", ob->buf);
	bufree(ob);
}

static void
cppwarning(void)
{
	register struct iobuf *ob = savln();
	warning("#warning%s", ob->buf);
	bufree(ob);
}

static void
undefstmt(void)
{
	register struct symtab *np;
	register usch *bp;
	register int ch;

	if (!ISID0(ch = fastspc()))
		error("bad #undef");
	bp = readid(ch);
	if ((np = lookup(bp, FIND)) != NULL)
		np->valoff = 0;
	chknl(0);
}

static void
identstmt(void)
{
	struct iobuf *ob = NULL;
	struct symtab *sp;
	usch *bp;
	int ch;

	if (ISID0(ch = fastspc())) {
		bp = readid(ch);
		if ((sp = lookup(bp, FIND)))
			ob = kfind(sp);
		if (ob->buf[0] != '\"')
			goto bad;
		if (ob)
			bufree(ob);
	} else if (ch == '\"') {
		bufree(faststr(ch, NULL));
		
	} else
		goto bad;
	chknl(1);
	return;
bad:
	error("bad #ident directive");
}

static void
pragmastmt(void)
{
	register int ch;

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

#define	DIR_FLSLVL	001
#define	DIR_FLSINC	002
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
	{ "ident", identstmt, 0 },
#ifdef GCC_COMPAT
	{ "include_next", include_next, 0 },
#endif
};
#define	NPPD	(int)(sizeof(ppd) / sizeof(ppd[0]))

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
 * do an even faster scan than fastscan while at flslvl.
 * just search for a new directive.
 */
static void
flscan(void)
{
	register int ch;

	for (;;) {
		ch = qcchar();
again:		switch (ch) {
		case 0:
			return;
		case '\n':
			putch('\n');
			ifiles->lineno++;
			while ((ch = qcchar()) == ' ' || ch == '\t')
				;
			if (ch == '#')
				return;
			if (ch == '%' && (ch = qcchar()) == ':')
				return;
			goto again;
		case '\'':
			while ((ch = qcchar()) != '\'') {
				if (ch == '\\')
					qcchar();
				if (ch == '\n')
					goto again;
			}
			break;
		case '\"':
			instr = 1;
			while ((ch = qcchar()) != '\"') {
				switch (ch) {
				case '\\':
					incmnt = 1;
					qcchar();
					incmnt = 0;
					break;
				case '\n':
					goto again;
				case 0:
					instr = 0;
					return;
				}
			}
			instr = 0;
			break;
		case '/':
			ch = qcchar();
			if (ch == '/' || ch == '*')
				fastcmnt2(ch);
			goto again;
		}
        }
}


/*
 * Handle a preprocessor directive.
 * # is already found.
 */
void
ppdir(void)
{
	register int ch, i, oldC;
	usch *bp;

	oldC = Cflag;
redo:	Cflag = 0;
	if ((ch = fastspc()) == '\n') { /* empty directive */
		unch(ch);
		Cflag = oldC;
		return;
	}
	Cflag = oldC;
	if ((ISID0(ch)) == 0)
		goto out;
	bp = readid(ch);

	/* got some keyword */
	for (i = 0; i < NPPD; i++) {
		if (bp[0] == ppd[i].name[0] &&
		    strcmp((char *)bp, ppd[i].name) == 0) {
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
			flscan();
			goto redo;
		}
	}
	if (flslvl == 0) {
		if (Aflag)
			skpln();
		return;
	}
	flscan();
	goto redo;

out:
	if (flslvl == 0 && Aflag == 0)
		error("invalid preprocessor directive");

	unch(ch);
	skpln();
}
