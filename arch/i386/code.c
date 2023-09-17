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
#define	sss sap
#define	pss n_ap
#else
#define	NODE P1ND
#define	talloc p1alloc
#undef n_type
#define n_type ptype
#undef n_df
#define n_df pdf
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
			    (int)tsize(sp->stype, sp->sdf, sp->sss)/SZCHAR);
		else
			printf(PRTPREF "\t.size " LABFMT ",%d\n", sp->soffset,
			    (int)tsize(sp->stype, sp->sdf, sp->sss)/SZCHAR);
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
	if ((ap = attr_find(cs->rv.ap, GCC_ATYP_REGPARM)))
		regparmarg = ap->iarg(0);
	if ((ap = attr_find(cs->rv.ap, GCC_ATYP_FASTCALL)))
		regparmarg = 2, regpregs = fastregs;
	if (regparmarg > 3)
		regparmarg = 3;
#endif


	/* Return values */
	if (ISPTR(t))
		t = UNSIGNED;

	switch (t) {
	case STRTY: case UNIONTY: /* struct return */
		sz = (int)tsize(t, cs->rv.df, cs->rv.ss);
#if defined(os_openbsd)
		if (sz <= SZLONGLONG) {
			/* openbsd returns small structs in regs */
			cs->rv.flags |= RV_STREG;
			cs->rv.reg[0] = EAX;
			cs->rv.reg[1] = EDX;
			cs->rv.rtp = UNSIGNED;
		} else
#endif
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

	case BOOL: case CHAR: case UCHAR:
	case SHORT: case USHORT:
	case INT: case UNSIGNED: case LONG: case ULONG:
		cs->rv.flags |= RV_RETREG;
		cs->rv.reg[0] = EAX;
		cs->rv.rtp = INT;
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
		sz = (int)tsize(rd->type, rd->df, rd->ss);
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
	cs->stkadj = (parmoff-ARGINIT)/SZCHAR;
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
#ifndef LANG_CXX
	NODE *p;

	/* Take care of PIC stuff first */
        if (kflag) {
		NODE *q;
		p = tempnode(0, INT, 0, 0);
		gotreg = regno(p);
		q = block(REG, 0, 0, INT, 0, 0);
		regno(q) = EBX;
		p = buildtree(ASSIGN, p, q);
                ecomp(p);
        }
#endif
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
#ifdef __i386__
	/* Be sure that the compiler uses full x87 */
	/* XXX cross-compiling will fail here */
	volatile int fcw;
	__asm("fstcw (%0)" : : "r"(&fcw));
	fcw |= 0x300;
	__asm("fldcw (%0)" : : "r"(&fcw));
#endif
#endif
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

#ifdef LANG_CXX
NODE *
funcode(NODE *p)
{
	return p;
}
#endif
