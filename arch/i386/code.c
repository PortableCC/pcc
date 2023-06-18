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
 * 3. The name of the author may not be used to endorse or promote products
 *    derived from this software without specific prior written permission
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


# include "pass1.h"

#ifdef LANG_CXX
#define	p1listf	listf
#define	p1tfree tfree
#else
#define	NODE P1ND
#define	talloc p1alloc
#endif

/*
 * Print out assembler segment name.
 */
void
setseg(int seg, char *name)
{
	switch (seg) {
	case PROG: name = ".text"; break;
	case DATA:
	case LDATA: name = ".data"; break;
	case UDATA: break;
#ifdef MACHOABI
	case PICLDATA:
	case PICDATA: name = ".section .data.rel.rw,\"aw\""; break;
	case PICRDATA: name = ".section .data.rel.ro,\"aw\""; break;
	case STRNG: name = ".cstring"; break;
	case RDATA: name = ".const_data"; break;
#else
	case PICLDATA: name = ".section .data.rel.local,\"aw\",@progbits";break;
	case PICDATA: name = ".section .data.rel.rw,\"aw\",@progbits"; break;
	case PICRDATA: name = ".section .data.rel.ro,\"aw\",@progbits"; break;
	case STRNG:
#ifdef AOUTABI
	case RDATA: name = ".data"; break;
#else
	case RDATA: name = ".section .rodata"; break;
#endif
#endif
	case TLSDATA: name = ".section .tdata,\"awT\",@progbits"; break;
	case TLSUDATA: name = ".section .tbss,\"awT\",@nobits"; break;
#ifdef MACHOABI
	case CTORS: name = ".mod_init_func\n\t.align 2"; break;
	case DTORS: name = ".mod_term_func\n\t.align 2"; break;
#else
	case CTORS: name = ".section\t.ctors,\"aw\",@progbits"; break;
	case DTORS: name = ".section\t.dtors,\"aw\",@progbits"; break;
#endif
	case NMSEG: 
		printf(PRTPREF "\t.section %s,\"a%c\",@progbits\n", name,
		    cftnsp ? 'x' : 'w');
		return;
	}
	printf(PRTPREF "\t%s\n", name);
}

#ifdef MACHOABI
void
defalign(int al)
{
	printf(PRTPREF "\t.align %d\n", ispow2(al/ALCHAR));
}
#endif

/*
 * Define everything needed to print out some data (or text).
 * This means segment, alignment, visibility, etc.
 */
void
defloc(struct symtab *sp)
{
	char *name;

	name = getexname(sp);
	if (sp->sclass == EXTDEF) {
		printf(PRTPREF "	.globl %s\n", name);
#if defined(ELFABI)
		printf(PRTPREF "\t.type %s,@%s\n", name,
		    ISFTN(sp->stype)? "function" : "object");
#endif
	}
#if defined(ELFABI)
	if (!ISFTN(sp->stype)) {
		if (sp->slevel == 0)
			printf(PRTPREF "\t.size %s,%d\n", name,
			    (int)tsize(sp->stype, sp->sdf, sp->sap)/SZCHAR);
		else
			printf(PRTPREF "\t.size " LABFMT ",%d\n", sp->soffset,
			    (int)tsize(sp->stype, sp->sdf, sp->sap)/SZCHAR);
	}
#endif
	if (sp->slevel == 0)
		printf(PRTPREF "%s:\n", name);
	else
		printf(PRTPREF LABFMT ":\n", sp->soffset);
}

#ifndef LANG_CXX

static TWORD reparegs[] = { EAX, EDX, ECX };
static TWORD fastregs[] = { ECX, EDX };
static TWORD longregs[] = { EAXEDX, EDXECX };

/*
 * Fill in struct defining how a function call should be handled.
 */
void
mycallspec(struct callspec *cs)
{
	extern int argstacksize;
	int regparmarg, nrarg, parmoff, parmoff2;
	int t = cs->rv.type;
	int sz, i;
	TWORD *regpregs;
#ifdef GCC_COMPAT
	struct attr *ap;
#endif

	parmoff = ARGINIT;
	nrarg = regparmarg = 0;

#ifdef GCC_COMPAT
	regpregs = reparegs;
	if ((ap = attr_find(cftnsp->sap, GCC_ATYP_REGPARM)))
		regparmarg = ap->iarg(0);
	if ((ap = attr_find(cftnsp->sap, GCC_ATYP_FASTCALL)))
		regparmarg = 2, regpregs = fastregs;
	if (regparmarg > 3)
		regparmarg = 3;
#endif


	/* Return values */
	if (ISPTR(t))
		t = UNSIGNED;

	switch (t) {
	case STRTY: case UNIONTY: /* struct return */
		sz = (int)tsize(t, cs->rv.df, cs->rv.ap);
		if (sz == SZLONGLONG && attr_find(cs->rv.ap, ATTR_COMPLEX)) {
			/* return in eax/edx */
			cs->rv.flags |= RV_STREG;
			cs->rv.reg[0] = EAX;
			cs->rv.reg[1] = EDX;
			cs->rv.rtp = UNSIGNED;
		} else {
			/* return struct in buffer given as hidden arg ptr */
			cs->rv.flags |= (RV_STRET|RV_RETADDR);
			cs->rv.reg[1] = EAX;
			cs->rv.rtp = UNSIGNED;
			if (regparmarg) {
				cs->rv.reg[0] = regpregs[nrarg++];
				cs->rv.flags |= RV_ARG0_REG;
			} else {
				cs->rv.off = parmoff;
				parmoff += SZINT;
			}
		}
		break;

	case CHAR: case UCHAR: case SHORT: case USHORT:
	case INT: case UNSIGNED: case LONG: case ULONG:
		cs->rv.flags |= RV_RETREG;
		cs->rv.reg[0] = EAX;
		cs->rv.rtp = cs->rv.type;
		break;

	case LONGLONG: case ULONGLONG:
		cs->rv.flags |= RV_RETREG;
		cs->rv.reg[0] = EAXEDX;
		cs->rv.rtp = cs->rv.type;
		break;

	case FLOAT: case DOUBLE: case LDOUBLE:
		cs->rv.flags |= RV_RETREG;
		cs->rv.reg[0] = 31;
		cs->rv.rtp = cs->rv.type;
		break;

	case VOID:
		break;

	default:
		cerror("mycallspec: %x", t);
	}
	parmoff2 = parmoff;

	/* arguments */
	for (i = 0; i < cs->nargs; i++) {
		struct rdef *rd = &cs->av[i];
		sz = (int)tsize(rd->type, rd->df, rd->ap);
		SETOFF(sz, SZINT);

		rd->rtp = rd->type;
		if (cisreg(rd->type) == 0 ||
		    ((regparmarg - nrarg) * SZINT < sz)) {
			rd->off = parmoff;
			parmoff += sz;
			nrarg = regparmarg;
			rd->flags |= (AV_STK|AV_STK_PUSH);
		} else {
			rd->reg[0] = sz > SZINT ?
			    longregs[nrarg] : regpregs[nrarg];
			nrarg += sz/SZINT;
			rd->flags |= AV_REG;
		}
	}
	if (cs->rv.flags & RV_CALLEE) {
		argstacksize = (parmoff2 - ARGINIT)/SZCHAR;
#ifdef notyet
		argpopsize = parmoff - parmoff2;
#endif
	}
}
#endif

int structrettemp;

/*
 * code for the end of a function
 * deals with struct return here
 */
void
efcode(void)
{
	extern int gotnr;

	gotnr = 0;	/* new number for next fun */

#ifdef LANG_CXX
	cerror("need return code");
#endif
}

/*
 * code for the beginning of a function; a is an array of
 * indices in symtab for the arguments; n is the number
 *
 * Classifying args on i386; not simple:
 * - Args may be on stack or in registers (regparm)
 * - There may be a hidden first arg, unless OpenBSD struct return.
 * - Regparm syntax is not well documented.
 * - There may be stdcall functions, where the called function pops stack
 * - ...probably more
 */
void
bfcode(struct symtab **sp, int cnt)
{
	extern int gotnr;
	NODE *p;

	/* Take care of PIC stuff first */
        if (kflag) {
#define STL     200
                char *str = xmalloc(STL);
#if !defined(MACHOABI)
                int l = getlab();
#else
                char *name;
#endif

                /* Generate extended assembler for PIC prolog */
                p = tempnode(0, INT, 0, 0);
                gotnr = regno(p);
                p = block(XARG, p, NIL, INT, 0, 0);
                p->n_name = "=g";
                p = block(XASM, p, bcon(0), INT, 0, 0);

#if defined(MACHOABI)
		name = getexname(cftnsp);
                if (snprintf(str, STL, "call L%s$pb\nL%s$pb:\n\tpopl %%0\n",
                    name, name) >= STL)
                        cerror("bfcode");
#else
                if (snprintf(str, STL,
                    "call " LABFMT ";" LABFMT ":;\tpopl %%0;"
                    "\taddl $_GLOBAL_OFFSET_TABLE_+[.-" LABFMT "], %%0;",
                    l, l, l) >= STL)
                        cerror("bfcode");
#endif
                p->n_name = addstring(str);
                p->n_right->n_type = STRTY;
		free(str);
                ecomp(p);
        }
}

#if defined(MACHOABI)
struct stub stublist;
struct stub nlplist;
#endif

/* called just before final exit */
/* flag is 1 if errors, 0 if none */
void
ejobcode(int flag)
{
#if defined(MACHOABI)
	/*
	 * iterate over the stublist and output the PIC stubs
`	 */
	if (kflag) {
		struct stub *p;

		DLIST_FOREACH(p, &stublist, link) {
			printf(PRTPREF "\t.section __IMPORT,__jump_table,symbol_stubs,self_modifying_code+pure_instructions,5\n");
			printf(PRTPREF "L%s$stub:\n", p->name);
			printf(PRTPREF "\t.indirect_symbol %s\n", p->name);
			printf(PRTPREF "\thlt ; hlt ; hlt ; hlt ; hlt\n");
			printf(PRTPREF "\t.subsections_via_symbols\n");
		}

		printf(PRTPREF "\t.section __IMPORT,__pointers,non_lazy_symbol_pointers\n");
		DLIST_FOREACH(p, &nlplist, link) {
			printf(PRTPREF "L%s$non_lazy_ptr:\n", p->name);
			printf(PRTPREF "\t.indirect_symbol %s\n", p->name);
			printf(PRTPREF "\t.long 0\n");
	        }

	}
#endif

	printf(PRTPREF "\t.ident \"PCC: %s\"\n", VERSSTR);
}

void
bjobcode(void)
{
#ifdef os_sunos
	astypnames[SHORT] = astypnames[USHORT] = "\t.2byte";
#endif
	astypnames[INT] = astypnames[UNSIGNED] = "\t.long";
#if defined(MACHOABI)
	DLIST_INIT(&stublist, link);
	DLIST_INIT(&nlplist, link);
#endif
#if defined(__GNUC__) || defined(__PCC__)
	/* Be sure that the compiler uses full x87 */
	/* XXX cross-compiling will fail here */
	volatile int fcw;
	__asm("fstcw (%0)" : : "r"(&fcw));
	fcw |= 0x300;
	__asm("fldcw (%0)" : : "r"(&fcw));
#endif
}

/*
 * Convert FUNARG to assign in case of regparm.
 */
static int regcvt, rparg, fcall;
static void
addreg(NODE *p)
{
	TWORD t;
	NODE *q;
	int sz, r;

	sz = (int)tsize(p->n_type, p->n_df, p->n_ap)/SZCHAR;
	sz = (sz + 3) >> 2;	/* sz in regs */
	if ((regcvt+sz) > rparg) {
		regcvt = rparg;
		return;
	}
	if (sz > 2)
		uerror("cannot put struct in 3 regs (yet)");

	if (sz == 2)
		r = regcvt == 0 ? EAXEDX : EDXECX;
	else if (fcall)
		r = regcvt == 0 ? ECX : EDX;
	else
		r = regcvt == 0 ? EAX : regcvt == 1 ? EDX : ECX;

	if (p->n_op == FUNARG) {
		/* at most 2 regs */
		if (p->n_type < INT) {
			p->n_left = ccast(p->n_left, INT, 0, 0, 0);
			p->n_type = INT;
		}

		p->n_op = ASSIGN;
		p->n_right = p->n_left;
	} else if (p->n_op == STARG) {
		/* convert to ptr, put in reg */
		q = p->n_left;
		t = sz == 2 ? LONGLONG : INT;
		q = cast(q, INCREF(t), 0);
		q = buildtree(UMUL, q, NIL);
		p->n_op = ASSIGN;
		p->n_type = t;
		p->n_right = q;
	} else
		cerror("addreg");
	p->n_left = block(REG, 0, 0, p->n_type, 0, 0);
	regno(p->n_left) = r;
	regcvt += sz;
}

/*
 * Called with a function call with arguments as argument.
 * This is done early in buildtree() and only done once.
 * Returns p.
 */
NODE *
funcode(NODE *p)
{
	extern int gotnr;
	struct attr *ap;
	NODE *r, *l;
	TWORD t = DECREF(DECREF(p->n_left->n_type));
	int stcall;

	stcall = ISSOU(t);
	/*
	 * We may have to prepend:
	 * - Hidden arg0 for struct return (in reg or on stack).
	 * - ebx in case of PIC code.
	 */

	/* Fix function call arguments. On x86, just add funarg */
	for (r = p->n_right; r->n_op == CM; r = r->n_left) {
		if (r->n_right->n_op != STARG)
			r->n_right = block(FUNARG, r->n_right, NIL,
			    r->n_right->n_type, r->n_right->n_df,
			    r->n_right->n_ap);
	}
	if (r->n_op != STARG) {
		l = talloc();
		*l = *r;
		r->n_op = FUNARG;
		r->n_left = l;
		r->n_type = l->n_type;
	}
#ifdef os_openbsd
	if (stcall && (ap = strattr(p->n_left->n_ap)) &&
	    ap->amsize != SZCHAR && ap->amsize != SZSHORT &&
	    ap->amsize != SZINT && ap->amsize != SZLONGLONG)
#else
	if (stcall &&
	    (attr_find(p->n_left->n_ap, ATTR_COMPLEX) == 0 ||
	     ((ap = strattr(p->n_left->n_ap)) && ap->amsize > SZLONGLONG)))
#endif
	{
		/* Prepend a placeholder for struct address. */
		/* Use EBP, can never show up under normal circumstances */
		l = talloc();
		*l = *r;
		r->n_op = CM;
		r->n_right = l;
		r->n_type = INT;
		l = block(REG, 0, 0, INCREF(VOID), 0, 0);
		regno(l) = EBP;
		l = block(FUNARG, l, 0, INCREF(VOID), 0, 0);
		r->n_left = l;
	}

#ifdef GCC_COMPAT
	fcall = 0;
	if ((ap = attr_find(p->n_left->n_ap, GCC_ATYP_REGPARM)))
		rparg = ap->iarg(0);
	else if ((ap = attr_find(p->n_left->n_ap, GCC_ATYP_FASTCALL)))
		fcall = rparg = 2;
	else
#endif
		rparg = 0;

	regcvt = 0;
	if (rparg)
		p1listf(p->n_right, addreg);

	if (kflag == 0)
		return p;

#if defined(ELFABI)
	/* Create an ASSIGN node for ebx */
	l = block(REG, NIL, NIL, INT, 0, 0);
	l->n_rval = EBX;
	l = buildtree(ASSIGN, l, tempnode(gotnr, INT, 0, 0));
	if (p->n_right->n_op != CM) {
		p->n_right = block(CM, l, p->n_right, INT, 0, 0);
	} else {
		for (r = p->n_right; r->n_left->n_op == CM; r = r->n_left)
			;
		r->n_left = block(CM, l, r->n_left, INT, 0, 0);
	}
#endif
	return p;
}

/* fix up type of field p */
void
fldty(struct symtab *p)
{
}

/*
 * XXX - fix genswitch.
 */
int
mygenswitch(int num, TWORD type, struct swents **p, int n)
{
	return 0;
}

NODE *	
builtin_return_address(const struct bitable *bt, NODE *a)
{	
	int nframes;
	NODE *f; 
	
	if (a->n_op != ICON)
		goto bad;

	nframes = (int)glval(a);
  
	p1tfree(a);	
			
	f = block(REG, NIL, NIL, PTR+VOID, 0, 0);
	regno(f) = FPREG;
 
	while (nframes--)
		f = block(UMUL, f, NIL, PTR+VOID, 0, 0);
				    
	f = block(PLUS, f, bcon(4), INCREF(PTR+VOID), 0, 0);
	f = buildtree(UMUL, f, NIL);	
   
	return f;
bad:						
	uerror("bad argument to __builtin_return_address");
	return bcon(0);
}

NODE *
builtin_frame_address(const struct bitable *bt, NODE *a)
{
	int nframes;
	NODE *f;

	if (a->n_op != ICON)
		goto bad;

	nframes = (int)glval(a);

	p1tfree(a);

	f = block(REG, NIL, NIL, PTR+VOID, 0, 0);
	regno(f) = FPREG;

	while (nframes--)
		f = block(UMUL, f, NIL, PTR+VOID, 0, 0);

	return f;
bad:
	uerror("bad argument to __builtin_frame_address");
	return bcon(0);
}

/*
 * Return "canonical frame address".
 */
NODE *
builtin_cfa(const struct bitable *bt, NODE *a)
{
	uerror("missing builtin_cfa");
	return bcon(0);
}

