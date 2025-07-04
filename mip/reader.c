/*	$Id$	*/
/*
 * Copyright (c) 2003 Anders Magnusson (ragge@ludd.luth.se).
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
 * Everything is entered via pass2_compile().  No functions are 
 * allowed to recurse back into pass2_compile().
 */

# include "pass2.h"

#include <string.h>
#include <stdarg.h>
#include <stdlib.h>

/*	some storage declarations */
int nrecur;
int thisline;
int fregs;
int p2autooff, p2maxautooff;

NODE *nodepole;
struct interpass prepole;

void saveip(struct interpass *ip);
void deltemp(NODE *p, void *);
static void cvtemps(struct interpass *ipole, int op, int off);
static void fixxasm(struct p2env *);

static void gencode(NODE *p, int cookie);
static void genxasm(NODE *p);
static void afree(void);

struct p2env p2env;

int crslab2 = 11; 
/*
 * Return a number for internal labels.
 */
int
getlab2(void)
{
        crslab2++;
	if (crslab2 < p2env.ipp->ip_lblnum)
		comperr("getlab2 %d outside boundaries %d-%d",
		    crslab2, p2env.ipp->ip_lblnum, p2env.epp->ip_lblnum);
	if (crslab2 >= p2env.epp->ip_lblnum)
		p2env.epp->ip_lblnum = crslab2+1;
        return crslab2++;
}


#ifdef PCC_DEBUG
static int *lbldef, *lbluse;
static void
cktree(NODE *p, void *arg)
{
	int i;

	if (p->n_op > MAXOP)
		cerror("%p) op %d slipped through", p, p->n_op);
#ifndef FIELDOPS
	if (p->n_op == FLD)
		cerror("%p) FLD slipped through", p);
#endif
	if (BTYPE(p->n_type) > MAXTYPES)
		cerror("%p) type %x slipped through", p, p->n_type);
	if (p->n_op == CBRANCH) {
		 if (!logop(p->n_left->n_op))
			cerror("%p) not logop branch", p);
		i = (int)getlval(p->n_right);
		if (i < p2env.ipp->ip_lblnum || i >= p2env.epp->ip_lblnum)
			cerror("%p) label %d outside boundaries %d-%d",
			    p, i, p2env.ipp->ip_lblnum, p2env.epp->ip_lblnum);
		lbluse[i-p2env.ipp->ip_lblnum] = 1;
	}
	if ((dope[p->n_op] & ASGOPFLG) && p->n_op != RETURN)
		cerror("%p) asgop %d slipped through", p, p->n_op);
	if (p->n_op == TEMP &&
	    (regno(p) < p2env.ipp->ip_tmpnum || regno(p) >= p2env.epp->ip_tmpnum))
		cerror("%p) temporary %d outside boundaries %d-%d",
		    p, regno(p), p2env.ipp->ip_tmpnum, p2env.epp->ip_tmpnum);
	if (p->n_op == GOTO && p->n_left->n_op == ICON) {
		i = (int)getlval(p->n_left);
		if (i < p2env.ipp->ip_lblnum || i >= p2env.epp->ip_lblnum)
			cerror("%p) label %d outside boundaries %d-%d",
			    p, i, p2env.ipp->ip_lblnum, p2env.epp->ip_lblnum);
		lbluse[i-p2env.ipp->ip_lblnum] = 1;
	}
}

/*
 * Check that the trees are in a suitable state for pass2.
 */
static void
sanitychecks(struct p2env *p2e)
{
	struct interpass *ip;
	int i, sz;

	sz = (int)sizeof(int) * (p2e->epp->ip_lblnum - p2e->ipp->ip_lblnum);
	lbldef = xcalloc(sz, 1);
	lbluse = xcalloc(sz, 1);

	DLIST_FOREACH(ip, &p2env.ipole, qelem) {
		if (ip->type == IP_DEFLAB) {
			i = ip->ip_lbl;
			if (i < p2e->ipp->ip_lblnum || i >= p2e->epp->ip_lblnum)
				cerror("label %d outside boundaries %d-%d",
				    i, p2e->ipp->ip_lblnum, p2e->epp->ip_lblnum);
			lbldef[i-p2e->ipp->ip_lblnum] = 1;
		}
		if (ip->type == IP_NODE)
			walkf(ip->ip_node, cktree, 0);
	}
	for (i = 0; i < (p2e->epp->ip_lblnum - p2e->ipp->ip_lblnum); i++)
		if (lbluse[i] != 0 && lbldef[i] == 0)
			cerror("internal label %d not defined",
			    i + p2e->ipp->ip_lblnum);

	free(lbldef);
	free(lbluse);
}
#endif

/*
 * Look if a temporary comes from a on-stack argument, in that case
 * use the already existing stack position instead of moving it to
 * a new place, and remove the move-to-temp statement.
 */
static int
stkarg(int tnr, int (*soff)[2])
{
	struct p2env *p2e = &p2env;
	struct interpass *ip;
	NODE *p;

	ip = DLIST_NEXT((struct interpass *)p2e->ipp, qelem);
	while (ip->type != IP_DEFLAB) /* search for first DEFLAB */
		ip = DLIST_NEXT(ip, qelem);

	ip = DLIST_NEXT(ip, qelem); /* first NODE */

	for (; ip->type != IP_DEFLAB; ip = DLIST_NEXT(ip, qelem)) {
		if (ip->type != IP_NODE)
			continue;

		p = ip->ip_node;
		if (p->n_op == XASM)
			continue; /* XXX - hack for x86 PIC */
#ifdef notdef
		if (p->n_op != ASSIGN || p->n_left->n_op != TEMP)
			comperr("temparg");
#endif
		if (p->n_op != ASSIGN || p->n_left->n_op != TEMP)
			continue; /* unknown tree */

		if (p->n_right->n_op != OREG && p->n_right->n_op != UMUL)
			continue; /* arg in register */
		if (tnr != regno(p->n_left))
			continue; /* wrong assign */
		p = p->n_right;
		if (p->n_op == UMUL &&
		    p->n_left->n_op == PLUS &&
		    p->n_left->n_left->n_op == REG &&
		    p->n_left->n_right->n_op == ICON) {
			soff[0][0] = regno(p->n_left->n_left);
			soff[0][1] = (int)getlval(p->n_left->n_right);
		} else if (p->n_op == OREG) {
			soff[0][0] = regno(p);
			soff[0][1] = (int)getlval(p);
		} else
			comperr("stkarg: bad arg");
		tfree(ip->ip_node);
		DLIST_REMOVE(ip, qelem);
		return 1;
	}
	return 0;
}

/*
 * See if an ADDROF is somewhere inside the expression tree.
 * If so, fill in the offset table.
 */
static void
findaof(NODE *p, void *arg)
{
	int (*aof)[2] = arg;
	int tnr;

	if (p->n_op != ADDROF || p->n_left->n_op != TEMP)
		return;
	tnr = regno(p->n_left);
	if (aof[tnr][0])
		return; /* already gotten stack address */
	if (stkarg(tnr, &aof[tnr]))
		return;	/* argument was on stack */
	aof[tnr][0] = FPREG;
	aof[tnr][1] = freetemp(szty(p->n_left->n_type));
}

/*
 * Check if a node has side effects.
 */
static int
isuseless(NODE *n)
{
	switch (n->n_op) {
	case XASM:
	case FUNARG:
	case UCALL:
	case UFORTCALL:
	case FORCE:
	case ASSIGN:
	case CALL:
	case FORTCALL:
	case CBRANCH:
	case RETURN:
	case GOTO:
	case STCALL:
	case USTCALL:
	case STASG:
	case STARG:
		return 0;
	default:
		return 1;
	}
}

/*
 * Delete statements with no meaning (like a+b; or 513.4;)
 */
NODE *
deluseless(NODE *p)
{
	struct interpass *ip;
	NODE *l, *r;

	if (optype(p->n_op) == LTYPE) {
		nfree(p);
		return NULL;
	}
	if (isuseless(p) == 0)
		return p;

	if (optype(p->n_op) == UTYPE) {
		l = p->n_left;
		nfree(p);
		return deluseless(l);
	}

	/* Be sure that both leaves may be valid */
	l = deluseless(p->n_left);
	r = deluseless(p->n_right);
	nfree(p);
	if (l && r) {
		ip = ipnode(l);
		DLIST_INSERT_AFTER(&prepole, ip, qelem);
		return r;
	} else if (l)
		return l;
	else if (r)
		return r;
	return NULL;
}

/*
 * Do some checks after optimization is finished.
 */
static void
latechecks(NODE *p, void *arg)
{
	int *flags = arg;

	/* Check if frame pointer is needed */
	if (p->n_op == ASSIGN && p->n_left->n_op == REG &&
	    regno(p->n_left) == FPREG)
		*flags |= IF_NEEDFP; /* FP is assigned */
	if (p->n_op == CALL && p->n_left->n_op == ICON && 
	    strcmp(p->n_left->n_name, "alloca") == 0)
		*flags |= IF_NEEDFP; /* alloca may modify FP */
	if (callop(p->n_op))
		*flags |= IF_NOTLEAF;
}

#ifdef PASS2

#define	SKIPWS(p) while (*p == ' ') p++
#define	SZIBUF 	256
static int inpline;
static char inpbuf[SZIBUF];
static char *
rdline(void)
{
	int l;

	if (fgets(inpbuf, sizeof(inpbuf), stdin) == NULL)
		return NULL;
	inpline++;
	l = strlen(inpbuf);
	if (inpbuf[0] < 33 || inpbuf[1] != ' ' || inpbuf[l-1] != '\n')
		comperr("sync error in-line %d string '%s'", inpline, inpbuf);
	inpbuf[l-1] = 0;
	return inpbuf;
}

/*
 * Read an int and traverse over it. count up s.
 */
static int
rdint(char **s)
{
	char *p = *s;
	int rv;

	SKIPWS(p);
	rv = atoi(p);
	if (*p == '-' || *p == '+') p++;
	while (*p >= '0' && *p <= '9') p++;
	*s = p;
	return rv;
}

static struct attr *
rdattr(char **p)
{
	struct attr *ap, *app = NULL;
	int i, a, sz;

	(*p)++; /* skip + */
onemore:
	a = rdint(p);
	sz = rdint(p);
	ap = attr_new(a, sz);
	for (i = 0; i < sz; i++)
		ap->iarg(i) = rdint(p);
	ap->next = app;
	app = ap;
	SKIPWS((*p));
	if (**p != 0)
		goto onemore;

	return app;
}

/*
 * Read in an indentifier and save on tmp heap.  Return saved string.
 */
static char *
rdstr(char **p)
{
	char *t, *s = *p;
	int sz;

	SKIPWS(s);
	*p = s;
	for (sz = 0; *s && *s != ' '; s++, sz++)
		;
	t = tmpalloc(sz+1);
	memcpy(t, *p, sz);
	t[sz] = 0;
	*p = s;
	return t;
}

/*
 * Read and check node structs from pass1.
 */
static NODE *
rdnode(char *s)
{
	NODE *p = talloc();
	int ty;

	if (s[0] != '"')
		comperr("rdnode sync error");
	s++; s++;
	p->n_regw = NULL;
	p->n_ap = NULL;
	p->n_su = p->n_rval = 0;
	setlval(p, 0);
	p->n_op = rdint(&s);
	p->n_type = rdint(&s);
	p->n_qual = rdint(&s);
	p->n_name = "";
	SKIPWS(s);
	ty = optype(p->n_op);
	if (p->n_op == XASM) {
		int i = strlen(s);
		p->n_name = tmpalloc(i+1);
		memcpy(p->n_name, s, i);
		p->n_name[i] = 0;
		s += i;
	}
	if (ty == UTYPE) {
		p->n_rval = rdint(&s);
	} else if (ty == LTYPE) {
		setlval(p, strtoll(s, &s, 10));
		if (p->n_op == NAME || p->n_op == ICON) {
			SKIPWS(s);
			if (*s && *s != '+')
				p->n_name = rdstr(&s);
		} else
			p->n_rval = rdint(&s);
	}
	SKIPWS(s);
	if (p->n_op == XARG) {
		int i = strlen(s);
		p->n_name = tmpalloc(i+1);
		memcpy(p->n_name, s, i);
		p->n_name[i] = 0;
		s += i;
	}
	if (*s == '+')
		p->n_ap = rdattr(&s);
	SKIPWS(s);
	if (*s)
		comperr("in-line %d failed read, buf '%s'", inpline, inpbuf);
	if (ty != LTYPE)
		p->n_left = rdnode(rdline());
	if (ty == BITYPE)
		p->n_right = rdnode(rdline());
	return p;
}

/*
 * Read everything from pass1.
 */
void
mainp2()
{
	static int foo[] = { 0 };
	struct interpass_prolog *ipp;
	struct interpass *ip;
	char nam[SZIBUF], *p, *b;
	extern char *ftitle;

	while ((p = rdline()) != NULL) {
		b = p++;
		p++;

		switch (*b) {
		case '*': /* pass thru line */
			printf("%s\n", p);
			break;
		case '&': /* current filename */
			free(ftitle);
			ftitle = xstrdup(p);
			break;
		case '#':
			lineno = atoi(p);
			break;
		case '"':
			ip = malloc(sizeof(struct interpass));
			ip->type = IP_NODE;
			ip->ip_node = rdnode(b);
			pass2_compile(ip);
			break;
		case '^':
			ip = malloc(sizeof(struct interpass));
			ip->type = IP_DEFLAB;
			ip->ip_lbl = atoi(p);
			pass2_compile(ip);
			break;
		case '!': /* prolog */
			ipp = malloc(sizeof(struct interpass_prolog));
			ip = (void *)ipp;
			ip->type = IP_PROLOG;
			sscanf(p, "%d %d %d %d %d %s", &ipp->ipp_type,
			    &ipp->ipp_flags, &ip->ip_lbl, &ipp->ip_tmpnum,
			    &ipp->ip_lblnum, nam);
			ipp->ipp_name = xstrdup(nam);
			ipp->ipp_autos = -1;
			ipp->ip_labels = foo;
#ifdef TARGET_IPP_MEMBERS
			if (*(p = rdline()) != '(')
				comperr("target member error");
			p += 2;
			target_members_read_prolog(ipp);
			SKIPWS(p);
			if (*p)
				comperr("bad prolog '%s' '%s'", p, inpbuf);
#endif
			pass2_compile((struct interpass *)ipp);
			break;

		case '%': /* epilog */
			ipp = malloc(sizeof(struct interpass_prolog));
			ip = (void *)ipp;
			ip->type = IP_EPILOG;
			ipp->ipp_autos = rdint(&p);
			ip->ip_lbl = rdint(&p);
			ipp->ip_tmpnum = rdint(&p);
			ipp->ip_lblnum = rdint(&p);
			ipp->ipp_name = rdstr(&p);
			SKIPWS(p);
			if (*p == '+') {
				int num, i;
				p++;
				num = rdint(&p) + 1;
				ipp->ip_labels = tmpalloc(sizeof(int)*num);
				for (i = 0; i < num; i++)
					ipp->ip_labels[i] = rdint(&p);
				ipp->ip_labels[num] = 0;
			} else
				ipp->ip_labels = foo;
			SKIPWS(p);
			if (*p)
				comperr("bad epilog '%s' '%s'", p, inpbuf);
#ifdef TARGET_IPP_MEMBERS
			if (*(p = rdline()) != ')')
				comperr("target epi member error");
			p += 2;
			target_members_read_epilog(ipp);
			SKIPWS(p);
			if (*p)
				comperr("bad epilog2 '%s' '%s'", p, inpbuf);
#endif
			pass2_compile((struct interpass *)ipp);
			break;
		case '$': /* assembler */
			if (*p) {
				int sz = strlen(p);
				ip = malloc(sizeof(struct interpass));
				ip->type = IP_ASM;
				ip->ip_asm = tmpalloc(sz+1);
                		memcpy(ip->ip_asm, p, sz);
				ip->ip_asm[sz] = 0;
				pass2_compile(ip);
			}
			break;
		default:
			comperr("bad string %s", b);
		}
	}
}


#endif

#ifdef NEWPARAMS
static void
prepnode(NODE *p, struct interpass *iplnk)
{
	struct interpass *ip;

	ip = ipnode(p);
	DLIST_INSERT_BEFORE(iplnk, ip, qelem);
}

/*
 * If a CALL has its parameters in registers then prepend all CALLs and UCALLs
 * below to its own IP links.
 * But for any CALL which only has its parameters in memory we do
 * 1) not care about UCALLs below and 2) leave the topmost call in the tree.
 */
static void
callsrch(NODE *p, struct interpass *iplnk, int prepucall)
{
	NODE *q, *r;
	int o = p->n_op;
	int prepcall = 0;

	if (o == CALL || o == STCALL) {
		for (q = p->n_right; q->n_op == CM; q = q->n_left)
			if (q->n_right->n_op == ASSIGN && 
			    q->n_right->n_left->n_op == REG)
				prepucall = 1;
		prepcall = 1;
	}

	if (optype(o) == BITYPE)
		callsrch(p->n_right, iplnk, prepucall);
	if (optype(o) != LTYPE)
		callsrch(p->n_left, iplnk, prepucall);

	if (callop(o) == 0)
		return;

	if (o == CALL || o == STCALL) {
		/* prepend function args before this call */
		for (q = p->n_right; q->n_op == CM; q = nfree(q))
			prepnode(q->n_right, iplnk);
		prepnode(q, iplnk);
		p->n_op++; /* make UCALL */
	}
	if (prepcall || prepucall) {
		if (iplnk->ip_node != p) {
			int num = p2env.epp->ip_tmpnum++;
			q = mklnode(TEMP, 0, num, p->n_type);
			r = talloc(); *r = *p;
			q = mkbinode(ASSIGN, q, r, p->n_type);
			prepnode(q, iplnk);
			p->n_op = TEMP;
			regno(p) = num;
		}
	}
	return;
}

/*
 * For each tree, search for calls.
 */
static void
nodesrch(struct p2env *p2e)
{
	struct interpass *ip;

	DLIST_FOREACH(ip, &p2e->ipole, qelem) {
		if (ip->type != IP_NODE)
			continue;
		callsrch(ip->ip_node, ip, 0);
	}
}
#endif

/*
 * Receives interpass structs from pass1.
 */
void
pass2_compile(struct interpass *ip)
{
	void deljumps(struct p2env *);
	struct p2env *p2e = &p2env;
	int (*addrp)[2];

	if (ip->type == IP_PROLOG) {
		memset(p2e, 0, sizeof(struct p2env));
		p2e->ipp = (struct interpass_prolog *)ip;
		if (crslab2 < p2e->ipp->ip_lblnum)
			crslab2 = p2e->ipp->ip_lblnum;
		DLIST_INIT(&p2e->ipole, qelem);
	}
	DLIST_INSERT_BEFORE(&p2e->ipole, ip, qelem);
	if (ip->type != IP_EPILOG)
		return;

	afree();
	p2e->epp = (struct interpass_prolog *)DLIST_PREV(&p2e->ipole, qelem);
	p2maxautooff = p2autooff = p2e->epp->ipp_autos;

#ifdef PCC_DEBUG
	if (e2debug) {
		printf("Entering pass2\n");
		printip(&p2e->ipole);
	}
#endif

#ifdef PCC_DEBUG
	sanitychecks(p2e);
#endif
	myreader(&p2e->ipole); /* local massage of input */

	/*
	 * Do initial modification of the trees.  Two loops;
	 * - first, search for ADDROF of TEMPs, these must be
	 *   converterd to OREGs on stack.
	 * - second, do the actual conversions, in case of not xtemps
	 *   convert all temporaries to stack references.
	 */

	if (p2e->epp->ip_tmpnum != p2e->ipp->ip_tmpnum) {
		addrp = xcalloc(sizeof(*addrp),
		    (p2e->epp->ip_tmpnum - p2e->ipp->ip_tmpnum));
		addrp -= p2e->ipp->ip_tmpnum;
	} else
		addrp = NULL;
	if (xtemps) {
		DLIST_FOREACH(ip, &p2e->ipole, qelem) {
			if (ip->type == IP_NODE)
				walkf(ip->ip_node, findaof, addrp);
		}
	}
	DLIST_FOREACH(ip, &p2e->ipole, qelem)
		if (ip->type == IP_NODE)
			walkf(ip->ip_node, deltemp, addrp);
	if (addrp)
		free(addrp + p2e->ipp->ip_tmpnum);

#ifdef PCC_DEBUG
	if (e2debug) {
		printf("Efter ADDROF/TEMP\n");
		printip(&p2e->ipole);
	}
#endif

	DLIST_INIT(&prepole, qelem);
	DLIST_FOREACH(ip, &p2e->ipole, qelem) {
		if (ip->type != IP_NODE)
			continue;
		canon(ip->ip_node);
		if ((ip->ip_node = deluseless(ip->ip_node)) == NULL) {
			DLIST_REMOVE(ip, qelem);
		} else while (!DLIST_ISEMPTY(&prepole, qelem)) {
			struct interpass *tipp;

			tipp = DLIST_NEXT(&prepole, qelem);
			DLIST_REMOVE(tipp, qelem);
			DLIST_INSERT_BEFORE(ip, tipp, qelem);
		}
	}

#ifdef NEWPARAMS
	nodesrch(p2e);	/* fix call order */
#endif

	fixxasm(p2e); /* setup for extended asm */

	optimize(p2e);
	ngenregs(p2e);

	if (xtemps && xdeljumps)
		deljumps(p2e);

	DLIST_FOREACH(ip, &p2e->ipole, qelem)
		if (ip->type == IP_NODE)
			walkf(ip->ip_node, latechecks, &p2env.ipp->ipp_flags);

	DLIST_FOREACH(ip, &p2e->ipole, qelem)
		emit(ip);
}

void
emit(struct interpass *ip)
{
	NODE *p, *r;
	struct optab *op;
	int o;

	switch (ip->type) {
	case IP_NODE:
		p = ip->ip_node;

		nodepole = p;
		canon(p); /* may convert stuff after genregs */
#ifdef PCC_DEBUG
		if (c2debug > 1) {
			printf("emit IP_NODE:\n");
			fwalk(p, e2print, 0);
		}
#endif
		switch (p->n_op) {
		case CBRANCH:
			/* Only emit branch insn if RESCC */
			/* careful when an OPLOG has been elided */
			if (p->n_left->n_su == 0 && p->n_left->n_left != NULL) {
				op = &table[TBLIDX(p->n_left->n_left->n_su)];
				r = p->n_left;
			} else {
				op = &table[TBLIDX(p->n_left->n_su)];
				r = p;
			}
			if (op->rewrite & RESCC) {
				o = p->n_left->n_op;
				gencode(r, FORCC);
				cbgen(o, getlval(p->n_right));
			} else {
				gencode(r, FORCC);
			}
			break;
		case FORCE:
			gencode(p->n_left, INREGS);
			break;
		case XASM:
			genxasm(p);
			break;
		default:
			if (p->n_op != REG || p->n_type != VOID) /* XXX */
				gencode(p, FOREFF); /* Emit instructions */
		}

		tfree(p);
		break;
	case IP_PROLOG:
		prologue((struct interpass_prolog *)ip);
		break;
	case IP_EPILOG:
		eoftn((struct interpass_prolog *)ip);
		p2maxautooff = p2autooff = AUTOINIT/SZCHAR;
		break;
	case IP_DEFLAB:
		deflab(ip->ip_lbl);
		break;
	case IP_ASM:
		printf("%s\n", ip->ip_asm);
		break;
	default:
		cerror("emit %d", ip->type);
	}
}

#ifdef PCC_DEBUG
char *cnames[] = {
	"SANY",
	"SAREG",
	"SBREG",
	"SCREG",
	"SDREG",
	"SCC",
	"SNAME",
	"SCON",
	"SFLD",
	"SOREG",
	"STARNM",
	"STARREG",
	"INTEMP",
	"FORARG",
	"SWADD",
	0,
};

/*
 * print a nice-looking description of cookie
 */
char *
prcook(int cookie)
{
	static char buf[50];
	int i, flag;

	if (cookie & SPECIAL) {
		switch (cookie) {
		case SZERO:
			return "SZERO";
		case SONE:
			return "SONE";
		case SMONE:
			return "SMONE";
		default:
			snprintf(buf, sizeof(buf), "SPECIAL+%d", cookie & ~SPECIAL);
			return buf;
		}
	}

	flag = 0;
	buf[0] = 0;
	for (i = 0; cnames[i]; ++i) {
		if (cookie & (1<<i)) {
			if (flag)
				strlcat(buf, "|", sizeof(buf));
			++flag;
			strlcat(buf, cnames[i], sizeof(buf));
		}
	}
	return buf;
}
#endif

int
geninsn(NODE *p, int cookie)
{
	NODE *p1, *p2;
	int q, o, rv = 0;

#ifdef PCC_DEBUG
	if (o2debug) {
		printf("geninsn(%p, %s)\n", p, prcook(cookie));
		fwalk(p, e2print, 0);
	}
#endif

	q = cookie & QUIET;
	cookie &= ~QUIET; /* XXX - should not be necessary */

again:	switch (o = p->n_op) {
	case EQ:
	case NE:
	case LE:
	case LT:
	case GE:
	case GT:
	case ULE:
	case ULT:
	case UGE:
	case UGT:
		p1 = p->n_left;
		p2 = p->n_right;
		if (p2->n_op == ICON && getlval(p2) == 0 && *p2->n_name == 0 &&
		    (dope[p1->n_op] & (FLOFLG|DIVFLG|SIMPFLG|SHFFLG))) {
#ifdef mach_pdp11 /* XXX all targets? */
			if ((rv = geninsn(p1, FORCC|QUIET)) != FFAIL)
				break;
#else
			if (findops(p1, FORCC) > 0)
				break;
#endif
		}
		rv = relops(p);
		break;

	case PLUS:
	case MINUS:
	case MUL:
	case DIV:
	case MOD:
	case AND:
	case OR:
	case ER:
	case LS:
	case RS:
		rv = findops(p, cookie);
		break;

	case ASSIGN:
#ifdef FINDMOPS
		if ((rv = findmops(p, cookie)) != FFAIL)
			break;
		/* FALLTHROUGH */
#endif
	case STASG:
		rv = findasg(p, cookie);
		break;

	case UMUL: /* May turn into an OREG */
		rv = findumul(p, cookie);
		break;

	case REG:
	case TEMP:
	case NAME:
	case ICON:
	case FCON:
	case OREG:
		rv = findleaf(p, cookie);
		break;

	case STCALL:
	case CALL:
		/* CALL arguments are handled special */
		for (p1 = p->n_right; p1->n_op == CM; p1 = p1->n_left)
			(void)geninsn(p1->n_right, FOREFF);
		(void)geninsn(p1, FOREFF);
		/* FALLTHROUGH */
	case FLD:
	case COMPL:
	case UMINUS:
	case PCONV:
	case SCONV:
/*	case INIT: */
	case GOTO:
	case FUNARG:
	case STARG:
	case UCALL:
	case USTCALL:
	case ADDROF:
		rv = finduni(p, cookie);
		break;

	case CBRANCH:
		p1 = p->n_left;
		p2 = p->n_right;
		p1->n_label = (int)getlval(p2);
		(void)geninsn(p1, FORCC);
		p->n_su = 0;
		break;

	case FORCE: /* XXX needed? */
		(void)geninsn(p->n_left, INREGS);
		p->n_su = 0; /* su calculations traverse left */
		break;

	case XASM:
		for (p1 = p->n_left; p1->n_op == CM; p1 = p1->n_left)
			(void)geninsn(p1->n_right, FOREFF);
		(void)geninsn(p1, FOREFF);
		break;	/* all stuff already done? */

	case XARG:
		/* generate code for correct class here */
		break;

	default:
		comperr("geninsn: bad op %s, node %p", opst[o], p);
	}
	if (rv == FFAIL && !q)
		comperr("Cannot generate code, node %p op %s", p,opst[p->n_op]);
	if (rv == FRETRY)
		goto again;
#ifdef PCC_DEBUG
	if (o2debug) {
		printf("geninsn(%p, %s) rv %d\n", p, prcook(cookie), rv);
		fwalk(p, e2print, 0);
	}
#endif
	return rv;
}

#ifdef PCC_DEBUG
#define	CDEBUG(x) if (c2debug) printf x
#else
#define	CDEBUG(x)
#endif

/*
 * Do a register-register move if necessary.
 * Called if a RLEFT or RRIGHT is found.
 */
static void
ckmove(NODE *p, NODE *q)
{
	struct optab *t = &table[TBLIDX(p->n_su)];
	int reg;
	char *w;

	if (q->n_op != REG || p->n_reg == -1)
		return; /* no register */

	/* do we have a need for special reg? */

	if ((w = hasneed(t->needs,  p->n_left == q ? cNL : cNR)) != NULL)
		reg = w[1];
	else
		reg = DECRA(p->n_reg, 0);

	if (reg < 0 || reg == DECRA(q->n_reg, 0))
		return; /* no move necessary */

	CDEBUG(("rmove: node %p, %s -> %s\n", p, rnames[DECRA(q->n_reg, 0)],
	    rnames[reg]));
	rmove(DECRA(q->n_reg, 0), reg, p->n_type);
	q->n_reg = q->n_rval = reg;
}

/*
 * Rewrite node to register after instruction emit.
 */
static void
rewrite(NODE *p, int dorewrite, int cookie)
{
	NODE *l, *r;
	int o;

	l = getlr(p, 'L');
	r = getlr(p, 'R');
	o = p->n_op;
	p->n_op = REG;
	setlval(p, 0);
	p->n_name = "";

	if (o == ASSIGN || o == STASG) {
		/* special rewrite care */
		int reg = DECRA(p->n_reg, 0);
#define	TL(x) (TBLIDX(x->n_su) || x->n_op == REG)
		if (p->n_reg == -1)
			;
		else if (TL(l) && (DECRA(l->n_reg, 0) == reg))
			;
		else if (TL(r) && (DECRA(r->n_reg, 0) == reg))
			;
		else if (TL(l))
			rmove(DECRA(l->n_reg, 0), reg, p->n_type);
		else if (TL(r))
			rmove(DECRA(r->n_reg, 0), reg, p->n_type);
#if 0
		else
			comperr("rewrite");
#endif
#undef TL
	}
	if (optype(o) != LTYPE)
		tfree(l);
	if (optype(o) == BITYPE)
		tfree(r);
	if (dorewrite == 0)
		return;
	CDEBUG(("rewrite: %p, reg %s\n", p,
	    p->n_reg == -1? "<none>" : rnames[DECRA(p->n_reg, 0)]));
	p->n_rval = DECRA(p->n_reg, 0);
}

#ifndef XASM_TARGARG
#define	XASM_TARGARG(x,y) 0
#endif

/*
 * printout extended assembler.
 */
void
genxasm(NODE *p)
{
	NODE *q, **nary;
	int n = 1, o = 0, v = 0;
	char *w;

	if (p->n_left->n_op != ICON || p->n_left->n_type != STRTY) {
		for (q = p->n_left; q->n_op == CM; q = q->n_left)
			n++;
		nary = tmpcalloc(sizeof(NODE *)*(n+1));
		o = n;
		for (q = p->n_left; q->n_op == CM; q = q->n_left) {
			gencode(q->n_right->n_left, INREGS);
			nary[--o] = q->n_right;
		}
		gencode(q->n_left, INREGS);
		nary[--o] = q;
	} else
		nary = 0;

	w = p->n_name;
	putchar('\t');
	while (*w != 0) {
		if (*w == '%') {
			if (w[1] == '%')
				putchar('%');
			else if (XASM_TARGARG(w, nary))
				; /* handled by target */
			else if (w[1] == '=') {
				if (v == 0) v = getlab2();
				printf("%d", v);
			} else if (w[1] == 'c') {
				q = nary[(int)w[2]-'0']; 
				if (q->n_left->n_op != ICON)
					uerror("impossible constraint");
				printf(CONFMT, getlval(q->n_left));
				w++;
			} else if (w[1] < '0' || w[1] > (n + '0'))
				uerror("bad xasm arg number %c", w[1]);
			else {
				if (w[1] == (n + '0'))
					q = nary[(int)w[1]-'0' - 1]; /* XXX */
				else
					q = nary[(int)w[1]-'0'];
				adrput(stdout, q->n_left);
			}
			w++;
		} else if (*w == '\\') { /* Always 3-digit octal */
			int num = *++w - '0';
			num = (num << 3) + *++w - '0';
			num = (num << 3) + *++w - '0';
			putchar(num);
		} else
			putchar(*w);
		w++;
	}
	putchar('\n');
}

/*
 * Allocate temporary registers for use while emitting this table entry.
 */
static void
allo(NODE *p, struct optab *q)
{
	extern int stktemp;
	int i, n;

	n = ncnt(q->needs);

	for (i = 0; i < NRESC; i++)
		if (resc[i].n_op != FREE)
			comperr("allo: used reg");
	if (n == 0 && hasneed(q->needs, cNTEMP) == 0)
		return;
	for (i = 0; i < n+1; i++) {
		resc[i].n_op = REG;
		resc[i].n_type = p->n_type; /* XXX should be correct type */
		resc[i].n_rval = DECRA(p->n_reg, i);
		resc[i].n_su = p->n_su; /* ??? */
	}
	if (i > NRESC)
		comperr("allo: too many allocs");
	if (hasneed(q->needs, cNTEMP)) {
#ifdef	MYALLOTEMP
		MYALLOTEMP(resc[i], stktemp);
#else
		resc[i].n_op = OREG;
		setlval(&resc[i], stktemp);
		resc[i].n_rval = FPREG;
		resc[i].n_su = p->n_su; /* ??? */
		resc[i].n_name = "";
#endif
	}
}

static void
afree(void)
{
	int i;

	for (i = 0; i < NRESC; i++)
		resc[i].n_op = FREE;
}

void
gencode(NODE *p, int cookie)
{
	struct optab *q = &table[TBLIDX(p->n_su)];
	NODE *p1, *l, *r;
	int o = optype(p->n_op);
#ifdef FINDMOPS
	int ismops = (p->n_op == ASSIGN && (p->n_su & ISMOPS));
#endif

	l = p->n_left;
	r = p->n_right;

	if (TBLIDX(p->n_su) == 0) {
		if (o == BITYPE && (p->n_su & DORIGHT))
			gencode(r, 0);
		if (optype(p->n_op) != LTYPE)
			gencode(l, 0);
		if (o == BITYPE && !(p->n_su & DORIGHT))
			gencode(r, 0);
		return;
	}

	CDEBUG(("gencode: node %p\n", p));

	if (p->n_op == REG && DECRA(p->n_reg, 0) == p->n_rval)
		return; /* meaningless move to itself */

	if (callop(p->n_op))
		lastcall(p); /* last chance before function args */
	if (p->n_op == CALL || p->n_op == FORTCALL || p->n_op == STCALL) {
		/* Print out arguments first */
		for (p1 = r; p1->n_op == CM; p1 = p1->n_left)
			gencode(p1->n_right, FOREFF);
		gencode(p1, FOREFF);
		o = UTYPE; /* avoid going down again */
	}

	if (o == BITYPE && (p->n_su & DORIGHT)) {
		gencode(r, INREGS);
		if (q->rewrite & RRIGHT)
			ckmove(p, r);
	}
	if (o != LTYPE) {
		gencode(l, INREGS);
#ifdef FINDMOPS
		if (ismops)
			;
		else
#endif
		     if (q->rewrite & RLEFT)
			ckmove(p, l);
	}
	if (o == BITYPE && !(p->n_su & DORIGHT)) {
		gencode(r, INREGS);
		if (q->rewrite & RRIGHT)
			ckmove(p, r);
	}

#ifdef FINDMOPS
	if (ismops) {
		/* reduce right tree to make expand() work */
		if (optype(r->n_op) != LTYPE) {
			p->n_op = r->n_op;
			r = tcopy(r->n_right);
			tfree(p->n_right);
			p->n_right = r;
		}
	}
#endif

	canon(p);

	if (q->needs) {
		char *w;
		int rr = ((w = hasneed(q->needs, cNR)) ? w[1] : -1);
		int lr = ((w = hasneed(q->needs, cNL)) ? w[1] : -1);

		if (rr >= 0) {
#ifdef PCC_DEBUG
			if (optype(p->n_op) != BITYPE)
				comperr("gencode: rspecial borked");
#endif
			if (r->n_op != REG)
				comperr("gencode: rop != REG");
			if (rr != r->n_rval)
				rmove(r->n_rval, rr, r->n_type);
			r->n_rval = r->n_reg = rr;
		}
		if (lr >= 0) {
			if (l->n_op != REG)
				comperr("gencode: %p lop != REG", p);
			if (lr != l->n_rval)
				rmove(l->n_rval, lr, l->n_type);
			l->n_rval = l->n_reg = lr;
		}
		if (rr >= 0 && lr >= 0 && (l->n_reg == rr || r->n_reg == lr))
			comperr("gencode: cross-reg-move");
	}

	if (p->n_op == ASSIGN &&
	    p->n_left->n_op == REG && p->n_right->n_op == REG &&
	    p->n_left->n_rval == p->n_right->n_rval &&
	    (p->n_su & RVCC) == 0) { /* XXX should check if necessary */
		/* do not emit anything */
		CDEBUG(("gencode(%p) assign nothing\n", p));
		rewrite(p, q->rewrite, cookie);
		return;
	}

	CDEBUG(("emitting node %p\n", p));
	if (TBLIDX(p->n_su) == 0)
		return;

	allo(p, q);
	expand(p, cookie, q->cstring);

#ifdef FINDMOPS
	if (ismops && DECRA(p->n_reg, 0) != regno(l) && cookie != FOREFF) {
		CDEBUG(("gencode(%p) rmove\n", p));
		rmove(regno(l), DECRA(p->n_reg, 0), p->n_type);
	} else
#endif
	if (callop(p->n_op) && cookie != FOREFF &&
	    DECRA(p->n_reg, 0) != RETREG(p->n_type)) {
		CDEBUG(("gencode(%p) retreg\n", p));
		rmove(RETREG(p->n_type), DECRA(p->n_reg, 0), p->n_type);
	} else if (q->needs) {
		char *w;
		int rr = ((w = hasneed(q->needs, cNRES)) ? w[1] : -1);

		if (rr >= 0 && DECRA(p->n_reg, 0) != rr) {
			CDEBUG(("gencode(%p) nspec retreg\n", p));
			rmove(rr, DECRA(p->n_reg, 0), p->n_type);
		}
	} else if ((q->rewrite & RESC1) &&
	    (DECRA(p->n_reg, 1) != DECRA(p->n_reg, 0))) {
		CDEBUG(("gencode(%p) RESC1 retreg\n", p));
		rmove(DECRA(p->n_reg, 1), DECRA(p->n_reg, 0), p->n_type);
	}
#if 0
		/* XXX - kolla upp det h{r */
	   else if (p->n_op == ASSIGN) {
		/* may need move added if RLEFT/RRIGHT */
		/* XXX should be handled in sucomp() */
		if ((q->rewrite & RLEFT) && (p->n_left->n_op == REG) &&
		    (p->n_left->n_rval != DECRA(p->n_reg, 0)) &&
		    TCLASS(p->n_su)) {
			rmove(p->n_left->n_rval, DECRA(p->n_reg, 0), p->n_type);
		} else if ((q->rewrite & RRIGHT) && (p->n_right->n_op == REG) &&
		    (p->n_right->n_rval != DECRA(p->n_reg, 0)) &&
		    TCLASS(p->n_su)) {
			rmove(p->n_right->n_rval, DECRA(p->n_reg, 0), p->n_type);
		}
	}
#endif
	rewrite(p, q->rewrite, cookie);
	afree();
}

#ifdef PCC_DEBUG
#undef	PRTABLE
void
e2print(NODE *p, int down, int *a, int *b)
{
	struct attr *ap;
#ifdef PRTABLE
	extern int tablesize;
#endif

	*a = *b = down+1;
	while( down >= 2 ){
		printf("\t");
		down -= 2;
		}
	if( down-- ) printf("    " );


	printf("%p) %s", p, opst[p->n_op] );
	switch( p->n_op ) { /* special cases */

	case FLD:
		printf(" sz=%d, shift=%d",
		    UPKFSZ(p->n_rval), UPKFOFF(p->n_rval));
		break;

	case REG:
		printf(" %s", rnames[p->n_rval] );
		break;

	case TEMP:
		printf(" %d", regno(p));
		break;

	case XASM:
	case XARG:
		printf(" '%s'", p->n_name);
		break;

	case ICON:
	case NAME:
	case OREG:
		printf(" " );
		adrput(stdout, p );
		break;

	case STCALL:
	case USTCALL:
	case STARG:
	case STASG:
		ap = attr_find(p->n_ap, ATTR_P2STRUCT);
		printf(" size=%d", ap->iarg(0));
		printf(" align=%d", ap->iarg(1));
		break;
		}

	printf(", " );
	tprint(p->n_type, p->n_qual);
	printf(", " );

	prtreg(p);
	printf(", SU= %d(%cREG,%s,%s,%s,%s)\n",
	    TBLIDX(p->n_su), 
	    TCLASS(p->n_su)+'@',
#ifdef PRTABLE
	    TBLIDX(p->n_su) >= 0 && TBLIDX(p->n_su) <= tablesize ?
	    table[TBLIDX(p->n_su)].cstring : "",
#else
	    "",
#endif
	    p->n_su & RVEFF ? "RVEFF" : "", p->n_su & RVCC ? "RVCC" : "",
	    p->n_su & DORIGHT ? "DORIGHT" : "");
}
#endif

/*
 * change left TEMPs into OREGs
 */
void
deltemp(NODE *p, void *arg)
{
	int (*aor)[2] = arg;
	NODE *l;

	if (p->n_op == TEMP) {
		if (aor[regno(p)][0] == 0) {
			if (xtemps)
				return;
			aor[regno(p)][0] = FPREG;
			aor[regno(p)][1] = freetemp(szty(p->n_type));
		}
		storemod(p, aor[regno(p)][1], aor[regno(p)][0]);
	} else if (p->n_op == ADDROF && p->n_left->n_op == OREG) {
		p->n_op = PLUS;
		l = p->n_left;
		l->n_op = REG;
		l->n_type = INCREF(l->n_type);
		p->n_right = mklnode(ICON, getlval(l), 0, INT);
	} else if (p->n_op == ADDROF && p->n_left->n_op == UMUL) {
		l = p->n_left;
		*p = *p->n_left->n_left;
		nfree(l->n_left);
		nfree(l);
	}
}

/*
 * for pointer/integer arithmetic, set pointer at left node
 */
static void
setleft(NODE *p, void *arg)
{        
	NODE *q;

	/* only additions for now */
	if (p->n_op != PLUS)
		return;
	if (ISPTR(p->n_right->n_type) && !ISPTR(p->n_left->n_type)) {
		q = p->n_right;
		p->n_right = p->n_left;
		p->n_left = q;
	}
}

/* It is OK to have these as externals */
static int oregr;
static CONSZ oregtemp;
static char *oregcp;
/*
 * look for situations where we can turn * into OREG
 * If sharp then do not allow temps.
 */
int
oregok(NODE *p, int sharp)
{

	NODE *q;
	NODE *ql, *qr;
	int r;
	CONSZ temp;
	char *cp;

	q = p->n_left;
#if 0
	if ((q->n_op == REG || (q->n_op == TEMP && !sharp)) &&
	    q->n_rval == DECRA(q->n_reg, 0)) {
#endif
	if (q->n_op == REG || (q->n_op == TEMP && !sharp)) {
		temp = getlval(q);
		r = q->n_rval;
		cp = q->n_name;
		goto ormake;
	}

	if (q->n_op != PLUS && q->n_op != MINUS)
		return 0;
	ql = q->n_left;
	qr = q->n_right;

#ifdef R2REGS

	/* look for doubly indexed expressions */
	/* XXX - fix checks */

	if( q->n_op == PLUS) {
		int i;
		if( (r=base(ql))>=0 && (i=offset(qr, tlen(p)))>=0) {
			makeor2(p, ql, r, i);
			return 1;
		} else if((r=base(qr))>=0 && (i=offset(ql, tlen(p)))>=0) {
			makeor2(p, qr, r, i);
			return 1;
		}
	}


#endif

#if 0
	if( (q->n_op==PLUS || q->n_op==MINUS) && qr->n_op == ICON &&
			(ql->n_op==REG || (ql->n_op==TEMP && !sharp)) &&
			szty(qr->n_type)==1 &&
			(ql->n_rval == DECRA(ql->n_reg, 0) ||
			/* XXX */
			 ql->n_rval == FPREG || ql->n_rval == STKREG)) {
#endif
	if ((q->n_op==PLUS || q->n_op==MINUS) && qr->n_op == ICON &&
	    (ql->n_op==REG || (ql->n_op==TEMP && !sharp))) {
	    
		temp = getlval(qr);
		if( q->n_op == MINUS ) temp = -temp;
		r = ql->n_rval;
		temp += getlval(ql);
		cp = qr->n_name;
		if( *cp && ( q->n_op == MINUS || *ql->n_name ) )
			return 0;
		if( !*cp ) cp = ql->n_name;

		ormake:
		if( notoff( p->n_type, r, temp, cp ))
			return 0;
		oregtemp = temp;
		oregr = r;
		oregcp = cp;
		return 1;
	}
	return 0;
}

static void
ormake(NODE *p)
{
	NODE *q = p->n_left;

	p->n_op = OREG;
	p->n_rval = oregr;
	setlval(p, oregtemp);
	p->n_name = oregcp;
	tfree(q);
}

/*
 * look for situations where we can turn * into OREG
 */
void
oreg2(NODE *p, void *arg)
{
	if (p->n_op != UMUL)
		return;
	if (oregok(p, 1))
		ormake(p);
	if (p->n_op == UMUL)
		myormake(p);
}

void
canon(NODE *p)
{
	/* put p in canonical form */

	walkf(p, setleft, 0);	/* ptrs at left node for arithmetic */
	walkf(p, oreg2, 0);	/* look for and create OREG nodes */
	mycanon(p);		/* your own canonicalization routine(s) */
}

void
comperr(char *str, ...)
{
	extern char *ftitle;
	va_list ap;

	if (nerrors) {
		fprintf(stderr,
		    "cannot recover from earlier errors: goodbye!\n");
		exit(1);
	}

	va_start(ap, str);
	fprintf(stderr, "%s, line %d: compiler error: ", ftitle, thisline);
	vfprintf(stderr, str, ap);
	fprintf(stderr, "\n");
	va_end(ap);

#ifdef PCC_DEBUG
	if (nodepole && nodepole->n_op != FREE)
		fwalk(nodepole, e2print, 0);
#endif
	exit(1);
}

/*
 * allocate k integers worth of temp space
 * we also make the convention that, if the number of words is
 * more than 1, it must be aligned for storing doubles...
 * Returns bytes offset from base register.
 */
int
freetemp(int k)
{
	int t, al, sz;

#ifdef WORD_ADDRESSED
	sz = k;	/* temps is in "words" */
	al = k;
#else
	al = (k > 1 ? ALDOUBLE/ALCHAR : ALINT/ALCHAR);
	sz = k * (SZINT/SZCHAR);
#endif

#ifndef STACK_DOWN
	SETOFF(p2autooff, al);
	t = p2autooff;
	p2autooff += sz;
#else
	p2autooff += sz;
	SETOFF(p2autooff, al);
	t = ( -p2autooff );
#endif
	if (p2autooff > p2maxautooff)
		p2maxautooff = p2autooff;
	return (t);
}

NODE *
storenode(TWORD t, int off)
{
	NODE *p;

	p = talloc();
	p->n_type = t;
	storemod(p, off, FPREG); /* XXX */
	return p;
}

#ifndef MYSTOREMOD
void
storemod(NODE *q, int off, int reg)
{
	NODE *l, *r, *p;

	l = mklnode(REG, 0, reg, INCREF(q->n_type));
	r = mklnode(ICON, off, 0, INT);
	p = mkbinode(PLUS, l, r, INCREF(q->n_type));
	q->n_op = UMUL;
	q->n_left = p;
	q->n_rval = q->n_su = 0;
}
#endif

NODE *
mklnode(int op, CONSZ lval, int rval, TWORD type)
{
	NODE *p = talloc();

	p->n_name = "";
	p->n_qual = 0;
	p->n_ap = 0;
	p->n_op = op;
	setlval(p, lval);
	p->n_rval = rval;
	p->n_type = type;
	p->n_regw = NULL;
	p->n_su = 0;
	return p;
}

NODE *
mkbinode(int op, NODE *left, NODE *right, TWORD type)
{
	NODE *p = talloc();

	p->n_name = "";
	p->n_qual = 0;
	p->n_ap = 0;
	p->n_op = op;
	p->n_left = left;
	p->n_right = right;
	p->n_type = type;
	p->n_regw = NULL;
	p->n_su = 0;
	return p;
}

NODE *
mkunode(int op, NODE *left, int rval, TWORD type)
{
	NODE *p = talloc();

	p->n_name = "";
	p->n_qual = 0;
	p->n_ap = 0;
	p->n_op = op;
	p->n_left = left;
	p->n_rval = rval;
	p->n_type = type;
	p->n_regw = NULL;
	p->n_su = 0;
	return p;
}

struct interpass *
ipnode(NODE *p)
{
	struct interpass *ip = tmpalloc(sizeof(struct interpass));

	ip->ip_node = p;
	ip->type = IP_NODE;
	ip->lineno = thisline;
	return ip;
}

#ifndef XASM_NUMCONV
#define	XASM_NUMCONV(x,y,z)	0
#endif

/*
 * change numeric argument redirections to the correct node type after 
 * cleaning up the other nodes.
 * be careful about input operands that may have different value than output.
 */
static void
delnums(NODE *p, void *arg)
{
	struct interpass *ip = arg, *ip2;
	NODE *r = ip->ip_node->n_left;
	NODE *q;
	TWORD t;
	int cnt, num;

	/* gcc allows % in constraints, but we ignore it */
	if (p->n_name[0] == '%' && p->n_name[1] >= '0' && p->n_name[1] <= '9')
		p->n_name++;

	if (p->n_name[0] < '0' || p->n_name[0] > '9')
		return; /* not numeric */
	if ((q = listarg(r, p->n_name[0] - '0', &cnt)) == NIL)
		comperr("bad delnums");

	/* target may have opinions whether to do this conversion */
	if (XASM_NUMCONV(ip, p, q))
		return;

	/* Delete number by adding move-to/from-temp.  Later on */
	/* the temps may be rewritten to other LTYPEs */
	num = p2env.epp->ip_tmpnum++;

	/* pre node */
	t = p->n_left->n_type;
	r = mklnode(TEMP, 0, num, t);
	ip2 = ipnode(mkbinode(ASSIGN, tcopy(r), p->n_left, t));
	DLIST_INSERT_BEFORE(ip, ip2, qelem);
	p->n_left = r;

	/* post node */
	t = q->n_left->n_type;
	r = mklnode(TEMP, 0, num, t);
	ip2 = ipnode(mkbinode(ASSIGN, q->n_left, tcopy(r), t));
	DLIST_INSERT_AFTER(ip, ip2, qelem);
	q->n_left = r;

	p->n_name = tmpstrdup(q->n_name);
	if (*p->n_name == '=')
		p->n_name++;
}

/*
 * Ensure that a node is correct for the destination.
 */
static void
ltypify(NODE *p, void *arg)
{
	struct interpass *ip = arg;
	struct interpass *ip2;
	TWORD t = p->n_left->n_type;
	NODE *q, *r;
	int cw, ooff, ww;
	char *c;

again:
	if (myxasm(ip, p))
		return;	/* handled by target-specific code */

	cw = xasmcode(p->n_name);
	switch (ww = XASMVAL(cw)) {
	case 'p':
		/* pointer */
		/* just make register of it */
		p->n_name = tmpstrdup(p->n_name);
		c = strchr(p->n_name, XASMVAL(cw)); /* cannot fail */
		*c = 'r';
		/* FALLTHROUGH */
	case 'g':  /* general; any operand */
		if (ww == 'g' && p->n_left->n_op == ICON) {
			/* should only be input */
			p->n_name = "i";
			break;
		}
		/* FALLTHROUGH */
	case 'r': /* general reg */
		/* set register class */
		if (p->n_left->n_op == REG || p->n_left->n_op == TEMP)
			break;
		q = p->n_left;
		r = (cw & XASMINOUT ? tcopy(q) : q);
		p->n_left = mklnode(TEMP, 0, p2env.epp->ip_tmpnum++, t);
		if ((cw & XASMASG) == 0) {
			ip2 = ipnode(mkbinode(ASSIGN, tcopy(p->n_left), r, t));
			DLIST_INSERT_BEFORE(ip, ip2, qelem);
		}
		if (cw & (XASMASG|XASMINOUT)) {
			/* output parameter */
			ip2 = ipnode(mkbinode(ASSIGN, q, tcopy(p->n_left), t));
			DLIST_INSERT_AFTER(ip, ip2, qelem);
		}
		break;

	case '0': case '1': case '2': case '3': case '4':
	case '5': case '6': case '7': case '8': case '9':
		break;

	case 'm': /* memory operand */
		/* store and reload value */
		q = p->n_left;
		if (optype(q->n_op) == LTYPE) {
			if (q->n_op == TEMP) {
				ooff = freetemp(szty(t));
				cvtemps(ip, q->n_rval, ooff);
			} else if (q->n_op == REG)
				comperr("xasm m and reg");
		} else if (q->n_op == UMUL && 
		    (q->n_left->n_op != TEMP && q->n_left->n_op != REG)) {
			t = q->n_left->n_type;
			ooff = p2env.epp->ip_tmpnum++;
			ip2 = ipnode(mkbinode(ASSIGN,
			    mklnode(TEMP, 0, ooff, t), q->n_left, t));
			q->n_left = mklnode(TEMP, 0, ooff, t);
			DLIST_INSERT_BEFORE(ip, ip2, qelem);
		}
		break;

	case 'i': /* immediate constant */
	case 'n': /* numeric constant */
		if (p->n_left->n_op == ICON)
			break;
		p->n_name = tmpstrdup(p->n_name);
		c = strchr(p->n_name, XASMVAL(cw)); /* cannot fail */
		if (c[1]) {
			c[0] = c[1], c[1] = 0;
			goto again;
		} else
			uerror("constant required");
		break;

	default:
		uerror("unsupported xasm option string '%s'", p->n_name);
	}
}

/* Extended assembler hacks */
static void
fixxasm(struct p2env *p2e)
{
	struct interpass *pole = &p2e->ipole;
	struct interpass *ip;
	NODE *p;

	DLIST_FOREACH(ip, pole, qelem) {
		if (ip->type != IP_NODE || ip->ip_node->n_op != XASM)
			continue;
		thisline = ip->lineno;
		p = ip->ip_node->n_left;

		if (p->n_op == ICON && p->n_type == STRTY)
			continue;

		/* replace numeric redirections with its underlying type */
		flist(p, delnums, ip);

		/*
		 * Ensure that the arg nodes can be directly addressable
		 * We decide that everything shall be LTYPE here.
		 */
		flist(p, ltypify, ip);
	}
}

/*
 * Extract codeword from xasm string */
int
xasmcode(char *s)
{
	int cw = 0, nm = 0;

	while (*s) {
		switch ((int)*s) {
		case '=': cw |= XASMASG; break;
		case '&': cw |= XASMCONSTR; break;
		case '+': cw |= XASMINOUT; break;
		case '%': break;
		default:
			if ((*s >= 'a' && *s <= 'z') ||
			    (*s >= 'A' && *s <= 'Z') ||
			    (*s >= '0' && *s <= '9')) {
				if (nm == 0)
					cw |= *s;
				else
					cw |= (*s << ((nm + 1) * 8));
				nm++;
				break;
			}
			uerror("bad xasm constraint %c", *s);
		}
		s++;
	}
	return cw;
}

static int xasnum, xoffnum;

static void
xconv(NODE *p, void *arg)
{
	if (p->n_op != TEMP || p->n_rval != xasnum)
		return;
	storemod(p, xoffnum, FPREG); /* XXX */
}

/*
 * Convert nodes of type TEMP to op with lval off.
 */
static void
cvtemps(struct interpass *ipl, int tnum, int off)
{
	struct interpass *ip;

	xasnum = tnum;
	xoffnum = off;

	DLIST_FOREACH(ip, ipl, qelem)
		if (ip->type == IP_NODE)
			walkf(ip->ip_node, xconv, 0);
	walkf(ipl->ip_node, xconv, 0);
}
