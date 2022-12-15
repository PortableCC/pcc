/*	$Id$	*/
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
 *	This product includes software developed or owned by Caldera
 *	International, Inc.
 * Neither the name of Caldera International, Inc. nor the names of other
 * contributors may be used to endorse or promote products derived from
 * this software without specific prior written permission.
 *
 * USE OF THE SOFTWARE PROVIDED FOR UNDER THIS LICENSE BY CALDERA
 * INTERNATIONAL, INC. AND CONTRIBUTORS ``AS IS'' AND ANY EXPRESS OR
 * IMPLIED WARRANTIES, INCLUDING, BUT NOT LIMITED TO, THE IMPLIED
 * WARRANTIES OF MERCHANTABILITY AND FITNESS FOR A PARTICULAR PURPOSE ARE
 * DISCLAIMED.	IN NO EVENT SHALL CALDERA INTERNATIONAL, INC. BE LIABLE
 * FOR ANY DIRECT, INDIRECT INCIDENTAL, SPECIAL, EXEMPLARY, OR CONSEQUENTIAL
 * DAMAGES (INCLUDING, BUT NOT LIMITED TO, PROCUREMENT OF SUBSTITUTE GOODS
 * OR SERVICES; LOSS OF USE, DATA, OR PROFITS; OR BUSINESS INTERRUPTION)
 * HOWEVER CAUSED AND ON ANY THEORY OFLIABILITY, WHETHER IN CONTRACT,
 * STRICT LIABILITY, OR TORT (INCLUDING NEGLIGENCE OR OTHERWISE) ARISING
 * IN ANY WAY OUT OF THE USE OF THIS SOFTWARE, EVEN IF ADVISED OF THE 
 * POSSIBILITY OF SUCH DAMAGE.
 */
#include <stdio.h>

#include "defines.h"
#include "defs.h"

/*
 * put out a character string constant.	 Begin every string on
 * a long integer boundary, and pad with nulls (by aligning).
 */
void
putstr(char *s, ftnint n)
{
	int ch;

	printf("\t.align 2\n");
	printf("\t.ascii \"");
	while(--n >= 0) {
		ch = (unsigned)*s++;
		if (ch < 32 || ch > 126)
			printf("\\%03o", ch);
		else
			printf("%c", ch);
	}
	printf("\"\n");
	printf("\t.align 2\n");
}

/*
 * Print out segment. Must correspond with numbers in defs.h.
 */
void
setloc(int l)
{
	static int lastloc = -1;
	static char *loctbl[] =
	    { "text", "data", "section .rodata", "section .rodata", "bss" };
	if (l == lastloc)
		return;
	printf("\t.%s\n", loctbl[l]);
	lastloc = l;
}


/*
	PDP11-780/VAX - SPECIFIC PRINTING ROUTINES
*/

/*
 * Called just before return from a subroutine.
 */
void
goret(int type)
{
	printf("# GORET\n");
}

/*
 * Print out a label.
 */
void
prlabel(int k)
{
	printf(LABFMT ":\n", k);
}

#if 0
/*
 * Print naming for location.
 * name[0] is location type.
 */
void
prnloc(char *name)
{
	if (*name == '0')
		setloc(DATA);
	else
		fatal("unhandled prnloc %c", *name);
	printf("%s:\n", name+1);
}
#endif

/*
 * Print integer constant (to either temp file or stdout).
 */
void
prconi(FILE *fp, int type, ftnint n)
{
	fprintf(fp, "\t%s\t%ld\n", (type==TYSHORT ? ".word" : ".long"), n);
}

/*
 * Print address constant, given as a label number (to stdout).
 */
void
prcona(ftnint a)
{
	printf("\t.long\t" LABFMT "\n", (int)a);
}

/*
 * Print out a floating constant (to temp file or stdout).
 */
void
prconr(FILE *fp, int type, double x)
{
	fprintf(fp, "\t%s\t0f%e\n", (type==TYREAL ? ".float" : ".double"), x);
}

void
preven(int k)
{
	static int algsz[] = { 1,2,4,8,16 };
	int i;

	for (i = 0; i < 5 && algsz[i] != k; i++)
		;
	if (algsz[i] != k)
		err("bad align size %d", k);
	printf("\t.align\t%d\n", i);
}

/*
 * Convert a tag and offset into the symtab table to a string.
 * An external string is never longer than XL bytes.
 */
char *
memname(int stg, int mem)
{
	static char s[XL];

	switch(stg) {
	case STGCOMMON:
	case STGEXT:
		snprintf(s, XL, "%s", varstr(XL, extsymtab[mem].extname));
		break;

	case STGBSS:
	case STGINIT:
		snprintf(s, XL, "v.%d", mem);
		break;

	case STGCONST:
		snprintf(s, XL, ".L%d", mem);
		break;

	case STGEQUIV:
		snprintf(s, XL, "q.%d", mem);
		break;

	default:
		fatal1("memname: invalid vstg %d", stg);
	}
	return(s);
}

void
prvar(char *s, ftnint len, int global)
{
	if (len == 0)
		printf("\t.globl\t%s\n", s);
	else
		printf("\t.%scomm\t%s,%ld\n", global ? "" : "l", s, len);
}

void
prendproc(void)
{
	printf("# END prendproc\n");
}

/*
 * Called just before exit.
 */
void
prtail(void)
{
	printf("# TAIL prtail\n");
}

void
prolog(struct entrypoint *ep, struct bigblock *argvec)
{
	/* Ignore for now.  ENTRY is not supported */
	printf("# BEGIN %s\n", ep->entryname->extname);
}

static void
fcheck(NODE *p, void *arg)
{
	NODE *r, *l;

	switch (p->n_op) {
	case CALL: /* fix arguments */
		for (r = p->n_right; r->n_op == CM; r = r->n_left) {
			r->n_right = mkunode(FUNARG, r->n_right, 0,
			    r->n_right->n_type);
		}
		l = talloc();
		*l = *r;
		r->n_op = FUNARG;
		r->n_left = l;
		r->n_type = l->n_type;
		break;
	}
}

/*
 * Called just before the tree is written out to pass2.
 */
void p2tree(NODE *p);
void
p2tree(NODE *p)
{
	walkf(p, fcheck, 0);
}
