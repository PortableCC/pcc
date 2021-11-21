/*	$Id$	*/
/*
 * Copyright (c) 2006 Anders Magnusson (ragge@ludd.luth.se).
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


# include "pass2.h"

# define ANYSIGNED TINT|TLONG|TSHORT|TCHAR
# define ANYUSIGNED TUNSIGNED|TULONG|TUSHORT|TUCHAR
# define ANYFIXED ANYSIGNED|ANYUSIGNED
# define ANYREG (INAREG|INBREG|INCREG)
# define TUWORD TUNSIGNED
# define TSWORD TINT
# define TWORD TUWORD|TSWORD

#define XSL(c)	NEEDS(NREG(c, 1), NSL(c))
#define	XNEEDA	NEEDS(NREG(A, 1))
#define	XNEEDB	NEEDS(NREG(B, 1))

struct optab table[] = {
/* First entry must be an empty entry */
{ -1, FOREFF, SANY, TANY, SANY, TANY, 0, 0, "", },

/*
 * Conversions.
 */
/* uchar to (u)int */
{ SCONV,	INAREG,
	SAREG,	TUCHAR,
	SAREG,	TINT|TUNSIGNED,
		0,	RLEFT,
		"",	},

{ SCONV,	INAREG,
	SAREG,	TINT|TUNSIGNED|TPOINT,
	SAREG,	TINT|TUNSIGNED,
		0,	RLEFT,
		"",	},

{ SCONV,	INAREG,
	SAREG,	TINT|TUNSIGNED,
	SAREG,	TCHAR,
		NEEDS(NLEFT(AC0)),	RLEFT,
		"	jsr __pcc_itoc\n",	},

{ SCONV,	INAREG,
	SOREG,	TLONG|TULONG,
	SAREG,	TINT|TUNSIGNED,
		NEEDS(NREG(A, 1)),	RESC1,
		"	lda A1,UL\n",	},

/* int/unsigned to long/ulong */
/* XXX kolla */
{ SCONV,	INBREG,
	SOREG|SNAME,	TWORD,
	SBREG,		TLONG|TULONG,
		NEEDS(NREG(B, 1), NSL(B)),	RESC1,
		"	lda U1,AL\n	subo A1,A1\n",	},

/* (reg) (u)long to unsigned */
{ SCONV,	INAREG,
	SBREG,	TLONG|TULONG,
	SAREG,	TINT|TUNSIGNED,
		NEEDS(NREG(A,1), NSL(A), NRES(AC1)),	RESC1,
		"",	},


{ PCONV,	INAREG,
	SAREG,	TSHORT|TUSHORT|TINT|TUNSIGNED,
	SAREG,	TPOINT,
		XSL(A),	RESC1,
		"	mov AL,A1\n",	},

/* word ptr to char ptr */
{ PCONV,	INAREG,
	SAREG,	TPTRTO|TSHORT|TUSHORT|TINT|TUNSIGNED|TSTRUCT,
	SAREG,	TPTRTO|TCHAR|TUCHAR,
		0,	RLEFT,
		"	movl AL,AL\n",	},


/*
 * All ASSIGN entries.
 */
/* reg->reg */
{ ASSIGN,	FOREFF|INAREG,
	SAREG,	TWORD|TPOINT,
	SAREG,	TWORD|TPOINT,
		0,	RDEST,
		"	mov AR,AL\n", },

/* reg->mem */
{ ASSIGN,	FOREFF|INAREG,
	SNAME|SOREG,	TCHAR|TUCHAR,
	SAREG,		TCHAR|TUCHAR,
		NEEDS(NOLEFT(AC0), NOLEFT(AC1), NRIGHT(AC0)),	RDEST,
		"	jsr __pcc_le_sbyt	# AR,AL\n", },

/* reg->mem */
{ ASSIGN,	FOREFF|INAREG,
	SNAME|SOREG,	TWORD|TPOINT,
	SAREG,		TWORD|TPOINT,
		NEEDS(NOLEFT(AC0), NOLEFT(AC1)),	RDEST,
		"	sta AR,AL\n", },

/* mem->reg */
{ ASSIGN,	FOREFF|INAREG,
	SAREG,		TWORD|TPOINT,
	SNAME|SOREG,	TWORD|TPOINT,
		NEEDS(NORIGHT(AC0), NORIGHT(AC1)),	RDEST,
		"	lda AL,AR\n", },

/* reg->mem */
{ ASSIGN,	FOREFF|INBREG,
	SNAME|SOREG,	TLONG|TULONG,
	SBREG,		TLONG|TULONG,
		0,	RDEST,
		"	sta AR,AL\n"
		"	sta UR,UL\n", },

/* mem->reg */
{ ASSIGN,	FOREFF|INBREG,
	SBREG,		TLONG|TULONG,
	SNAME|SOREG,	TLONG|TULONG,
		0,	RDEST,
		"	lda AL,AR\n"
		"	lda UL,UR\n", },

/* reg->reg */
/* this should be end up as a NOP since there is only one BREG */
{ ASSIGN,	FOREFF|INBREG,
	SBREG,		TLONG|TULONG,
	SBREG,		TLONG|TULONG,
		0,	RDEST,
		"	XXX - cannot happen\n", },

{ STASG,	INAREG|FOREFF,
	SOREG|SNAME,	TANY,
	SAREG,		TPTRTO|TANY,
		NEEDS(NRIGHT(AC2), NEVER(AC0), NEVER(AC1)),	RDEST,
		"ZQ", },

/*
 * LEAF type movements.
 */
/* 0 -> Areg */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SZERO,	TWORD,
		XNEEDA,	RESC1,
		"	subo A1,A1\n", },

/* 0 -> Breg */
{ OPLTYPE,	INBREG,
	SANY,	TANY,
	SZERO,	TWORD,
		XNEEDB,	RESC1,
		"	subo A1,A1\n	subo U1,U1\n", },

/* 1 -> Areg */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SONE,	TWORD,
		XNEEDA,	RESC1,
		"	subzl A1,A1\n", },

/* 1 -> Breg */
{ OPLTYPE,	INBREG,
	SANY,	TANY,
	SONE,	TLONG|TULONG,
		XNEEDB,	RESC1,
		"	subo A1,A1\n	subzl U1,U1\n", },

/* constant -> Areg */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SCON,	TCHAR|TUCHAR|TWORD|TPOINT,
		XNEEDA,	RESC1,
		"	lda A1,AR\n", },

/* constant -> Breg */
{ OPLTYPE,	INBREG,
	SANY,	TANY,
	SCON,	TLONG|TULONG,
		XNEEDB,	RESC1,
		"	lda A1,AR\n	lda U1,UR\n", },

/* mem -> reg */
{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SNAME|SOREG,	TWORD|TPOINT,
		XNEEDA,	RESC1,
		"	lda A1,AR\n", },

/* reg -> A-reg */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SAREG,	TWORD,
		XSL(A),	RESC1,
		"	mov AR,A1\n", },

/* temp -> reg */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SAREG,	TWORD|TPOINT,
		XNEEDA,	RESC1,
		"	mov AR,A1\n", },

/* temp -> Breg */
{ OPLTYPE,	INBREG,
	SANY,	TANY,
	SBREG,	TLONG|TULONG,
		XNEEDB,	RESC1,
		"	mov AR,A1\n	mov UR,U1\n", },

{ OPLTYPE,	INBREG,
	SANY,		TLONG|TULONG,
	SNAME|SOREG,	TLONG|TULONG,
		XNEEDB,	RESC1,
		"	lda A1,AR\n"
		"	lda U1,UR\n", },

/*
 * Simple ops.
 */
{ PLUS,		INAREG,
	SAREG,	TWORD|TPOINT,
	SONE,	TANY,
		0,	RLEFT,
		"	inc AL,AL\n", },

/*
 * Memory OPS. note that the extra mov is just to avoid a skip 
 * if passing 0.
 */
{ PLUS,		FOREFF,
	SNAME|SOREG,	TWORD,
	SONE,		TANY,
		0,	RLEFT,
		"	isz AL\n	mov 0,0\n", },

{ PLUS,		FOREFF,
	SNAME|SOREG,	TPOINT,
	SONE,		TANY,
		0,	RLEFT,
		"	isz AL\n", },

{ MINUS,	FOREFF,
	SNAME|SOREG,	TWORD,
	SONE,		TANY,
		0,	RLEFT,
		"	dsz AL\n	mov 0,0\n", },

{ MINUS,	FOREFF,
	SNAME|SOREG,	TPOINT,
	SONE,		TANY,
		0,	RLEFT,
		"	dsz AL\n", },

/* long add, 5 word */
{ PLUS,		INBREG,
	SBREG,		TLONG|TULONG,
	SOREG|SCON,	TLONG|TULONG,
		XNEEDA,	RLEFT,
		"	lda 2,UR\n"
		"	addz 2,1,szc\n"
		"	inc 0,0\n"
		"	lda 2,AR\n"
		"	add 2,0\n", },

/* basic entry of multiply */
{ MUL,		INAREG,
	SAREG,	TSWORD,
	SAREG,	TSWORD,
		0,	RLEFT,
		"	jsr @__pcc_smul\n", },

{ LS,		INAREG,
	SAREG,	TWORD|TPOINT,
	SAREG,	TINT,
		NEEDS(NLEFT(AC0), NRIGHT(AC2)),	RLEFT,
		"	jsr @__pcc_ls\n", },

{ RS,		INAREG,
	SAREG,	TUNSIGNED,
	SAREG,	TINT,
		NEEDS(NLEFT(AC0), NRIGHT(AC2)),	RLEFT,
		"	jsr @__pcc_urs\n", },

{ RS,		INAREG,
	SAREG,	TINT,
	SAREG,	TINT,
		NEEDS(NLEFT(AC0), NRIGHT(AC2)),	RLEFT,
		"	jsr @__pcc_rs\n", },

/* long left shft.  left in ac0-1 and right in ac2 */
{ LS,		INBREG,
	SBREG,	TLONG|TULONG,
	SAREG,	TANY,
		0,	RLEFT,
		"	jsr @__pcc_lsh32\n", },

/* indirection */
{ UMUL,	INBREG,
	SANY,	TANY,
	SOREG,	TLONG|TULONG,
		XNEEDB,	RESC1,
		"	lda A1,AL\n	lda U1,UL\n", },

{ OR,	INAREG|FOREFF,
	SAREG,	TWORD|TPOINT,
	SAREG,	TWORD|TPOINT,
		NEEDS(NTR),	RLEFT,
		"	com AR,AR\n	and AR,AL\n	adc AR,AL\n", },

{ OPSIMP,	INAREG|FOREFF,
	SAREG,	TWORD|TPOINT,
	SAREG,	TWORD|TPOINT,
		0,	RLEFT,
		"	O AR,AL\n", },

/*
 * Indirections
 */
{ UMUL,	INAREG,
	SANY,	TPTRTO|TUCHAR,
	SOREG,	TUCHAR,
		NEEDS(NREG(A, 1), NOLEFT(AC0), NOLEFT(AC1)), RESC1,
		"	jsr @__pcc_le_lbyt\n", },

{ UMUL,	INAREG,
	SANY,	TPTRTO|TCHAR,
	SOREG,	TCHAR,
		NEEDS(NREG(A, 1), NSL(A), NLEFT(AC2)), RESC1,
		"	jsr @__pcc_le_lsbyt\n", },

{ UMUL,	INAREG,
	SANY,	TPOINT|TWORD,
	SOREG,	TPOINT|TWORD,
		NEEDS(NOLEFT(AC0), NOLEFT(AC1), NREG(A,1)),	RESC1,
		"	lda A1,AL\n", },

/*
 * logops
 */
{ EQ,	FOREFF,
	SAREG,		TINT|TUNSIGNED|TPOINT,
	SZERO,		TINT|TUNSIGNED|TPOINT,
		0,	RNOP,
		"	mov# AL,AL,snr\n	jmp LC\n", },

{ EQ,	FOREFF,
	SAREG,	TINT|TUNSIGNED|TPOINT,
	SAREG,	TINT|TUNSIGNED|TPOINT,
		0,	RNOP,
		"	sub# AL,AR,snr\n	jmp LC\n", },

{ NE,	FOREFF,
	SAREG,	TINT|TUNSIGNED|TPOINT,
	SZERO,		TINT|TUNSIGNED|TPOINT,
		0,	RNOP,
		"	mov# AL,AL,szr\n	jmp LC\n", },

{ NE,	FOREFF,
	SAREG,	TINT|TUNSIGNED|TPOINT,
	SAREG,	TINT|TUNSIGNED|TPOINT,
		0,	RNOP,
		"	sub# AL,AR,szr\n	jmp LC\n", },

{ UGE,	FOREFF,
	SAREG,	TUNSIGNED|TPOINT,
	SAREG,	TUNSIGNED|TPOINT,
		0,	RNOP,
		"	adcz# AL,AR,snc\n	jmp LC\n", },

{ UGT,	FOREFF,
	SAREG,	TUNSIGNED|TPOINT,
	SAREG,	TUNSIGNED|TPOINT,
		0,	RNOP,
		"	subz# AL,AR,snc\n	jmp LC\n", },

/* test >= by subtracting and then looking at the sign bit */
/* XXX double/check */
{ GE,	FOREFF,
	SAREG,	TINT,
	SAREG,	TINT,
		0,	RNOP,
		"	subl# AL,AR,snc\n	jmp LC\n", },

/* Compare long against 0 */
{ OPLOG,	FORCC,
	SBREG,	TLONG,
	SZERO,	TANY,
		0,	RNOP,
		"ZZ",	},

/* Compare long against right side in memory */
{ OPLOG,	FORCC,
	SBREG,		TLONG,
	SOREG|SCON,	TLONG,
		NEEDS(NREG(A, 1)),	RNOP,
		"ZN",	},

/*
 * Subroutine calls.
 */

{ CALL,		FOREFF,
	SCON,	TANY,
	SANY,	TANY,
		0,	0,
		"	jsr CL\n", },

{ UCALL,	FOREFF,
	SCON,	TANY,
	SANY,	TANY,
		0,	0,
		"	jsr CL\n", },

{ CALL,		FOREFF,
	SAREG,	TANY,
	SANY,	TANY,
		0,	0,
		"	jsr 0,AL\n", },

{ UCALL,	FOREFF,
	SAREG,	TANY,
	SANY,	TANY,
		0,	0,
		"	jsr 0,AL\n", },

{ CALL,		INAREG,
	SCON,	TANY,
	SANY,	TANY,
		XSL(A),	RESC1,
		"	jsr CL\n", },

{ UCALL,	INAREG,
	SCON,	TANY,
	SANY,	TANY,
		XSL(A),	RESC1,
		"	jsr CL\n", },

{ CALL,		INAREG,
	SAREG,	TANY,
	SANY,	TANY,
		XSL(A),	RESC1,
		"	jsr 0,AL\n", },

{ UCALL,	INAREG,
	SAREG,	TANY,
	SANY,	TANY,
		XSL(A),	RESC1,
		"	jsr 0,AL\n", },

{ CALL,		INAREG,
	SCON,	TANY,
	SANY,	TANY,
		XSL(A),	RESC1,
		"	jsr CL\n", },

{ UCALL,	INAREG,
	SCON,	TANY,
	SANY,	TANY,
		XSL(A),	RESC1,
		"	jsr CL\n", },

{ CALL,		INBREG,
	SCON,	TANY,
	SANY,	TANY,
		XSL(B),	RESC1,
		"	jsr CL\n", },

{ UCALL,	INBREG,
	SCON,	TANY,
	SANY,	TANY,
		XSL(B),	RESC1,
		"	jsr CL\n", },

{ CALL,		INBREG,
	SAREG,	TANY,
	SANY,	TANY,
		XSL(B),	RESC1,
		"	jsr 0,AL\n", },

{ UCALL,	INBREG,
	SAREG,	TANY,
	SANY,	TANY,
		XSL(B),	RESC1,
		"	jsr 0,AL\n", },

{ GOTO,		FOREFF,
	SCON,	TANY,
	SANY,	TANY,
		0,	RNOP,
		"	jmp LL\n", },

{ FUNARG,	FOREFF,
	SAREG,	TCHAR|TUCHAR|TWORD|TPOINT,
	SANY,		TCHAR|TUCHAR|TWORD|TPOINT,
		0,	RNULL,
		"	sta AL,@sp\n", },

{ FUNARG,	FOREFF,
	SBREG,	TLONG|TULONG,
	SANY,	TLONG|TULONG,
		0,	RNULL,
		"	sta AL,@sp\n"
		"	sta UL,@sp\n" },

# define DF(x) FORREW,SANY,TANY,SANY,TANY,NEEDS(NREWRITE),x,""

{ UMUL, DF( UMUL ), },

{ ASSIGN, DF(ASSIGN), },

{ STASG, DF(STASG), },

{ FLD, DF(FLD), },

{ OPLEAF, DF(NAME), },

{ OPUNARY, DF(UMINUS), },

{ OPANY, DF(BITYPE), },

{ FREE,	FREE,	FREE,	FREE,	FREE,	FREE,	0,	FREE,	"help; I'm in trouble\n" },
};

int tablesize = sizeof(table)/sizeof(table[0]);
