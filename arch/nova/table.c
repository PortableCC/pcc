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
	SAREG,	TINT|TUNSIGNED,
	SAREG,	TINT|TUNSIGNED,
		0,	RLEFT,
		"",	},

{ SCONV,	INAREG,
	SOREG,	TLONG|TULONG,
	SAREG,	TINT|TUNSIGNED,
		NAREG,	RESC1,
		"	lda A1,UL\n",	},


{ PCONV,	INBREG,
	SAREG,	TSHORT|TUSHORT|TINT|TUNSIGNED,
	SBREG,	TPOINT,
		NBREG|NBSL,	RESC1,
		"	mov AL,A1\n",	},


/*
 * All ASSIGN entries.
 */
/* reg->reg */
{ ASSIGN,	FOREFF|INAREG,
	SAREG,	TWORD,
	SAREG,	TWORD,
		0,	RDEST,
		"	mov AR,AL\n", },
{ ASSIGN,	FOREFF|INBREG,
	SBREG,	TPOINT,
	SBREG,	TPOINT,
		0,	RDEST,
		"	mov AR,AL\n", },

/* reg->mem */
{ ASSIGN,	FOREFF|INAREG,
	SNAME|SOREG,	TWORD,
	SAREG,		TWORD,
		0,	RDEST,
		"	sta AR,AL\n", },
{ ASSIGN,	FOREFF|INBREG,
	SNAME|SOREG,	TPOINT,
	SBREG,	TPOINT,
		0,	RDEST,
		"	sta AR,AL\n", },

/* mem->reg */
{ ASSIGN,	FOREFF|INAREG|INBREG,
	SAREG|SBREG,	TWORD|TPOINT,
	SNAME|SOREG,	TWORD|TPOINT,
		0,	RDEST,
		"	lda AL,AR\n", },

/* reg->mem */
{ ASSIGN,	FOREFF|INCREG,
	SNAME|SOREG,	TLONG|TULONG,
	SCREG,		TLONG|TULONG,
		0,	RDEST,
		"	sta AR,AL\n"
		"	sta UR,UL\n", },

/* mem->reg */
{ ASSIGN,	FOREFF|INCREG,
	SCREG,		TLONG|TULONG,
	SNAME|SOREG,	TLONG|TULONG,
		0,	RDEST,
		"	lda AL,AR\n"
		"	lda UL,UR\n", },

/* reg->reg */
/* this should be end up as a NOP since there is only one CREG */
{ ASSIGN,	FOREFF|INCREG,
	SCREG,		TLONG|TULONG,
	SCREG,		TLONG|TULONG,
		0,	RDEST,
		"	XXX - cannot happen\n", },

/*
 * LEAF type movements.
 */
/* 0 -> Areg */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SZERO,	TWORD,
		NAREG,	RESC1,
		"	subo A1,A1\n", },

/* 0 -> Creg */
{ OPLTYPE,	INCREG,
	SANY,	TANY,
	SZERO,	TWORD,
		NCREG,	RESC1,
		"	subo A1,A1\n	subo U1,U1\n", },

/* 1 -> Areg */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SONE,	TWORD,
		NAREG,	RESC1,
		"	subzl A1,A1\n", },

/* 1 -> Creg */
{ OPLTYPE,	INCREG,
	SANY,	TANY,
	SONE,	TLONG|TULONG,
		NCREG,	RESC1,
		"	subo A1,A1\n	subzl U1,U1\n", },

/* constant -> Areg */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SCON,	TWORD|TPOINT,
		NAREG,	RESC1,
		"	lda A1,AR\n", },

/* constant -> Breg */
{ OPLTYPE,	INBREG,
	SANY,	TANY,
	SCON,	TWORD|TPOINT,
		NBREG,	RESC1,
		"	lda A1,AR\n", },

/* mem -> reg */
{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SNAME|SOREG,	TWORD,
		NAREG,	RESC1,
		"	lda A1,AR\n", },

/* reg -> A-reg */
{ OPLTYPE,	INAREG,
	SANY,		TANY,
	SAREG|SBREG,	TWORD,
		NAREG,	RESC1,
		"	mov AR,A1\n", },

/* reg -> B-reg */
{ OPLTYPE,	INBREG,
	SANY,		TANY,
	SAREG|SBREG,	TWORD|TPOINT,
		NBREG,	RESC1,
		"	mov AR,A1\n", },

/* temp -> reg */
{ OPLTYPE,	INAREG,
	SANY,	TANY,
	SAREG,	TWORD|TPOINT,
		NAREG,	RESC1,
		"	mov AR,A1\n", },

/* temp -> reg */
{ OPLTYPE,	INBREG,
	SANY,	TANY,
	SBREG,	TWORD|TPOINT,
		NBREG,	RESC1,
		"	mov AR,A1\n", },

/* temp -> Creg */
{ OPLTYPE,	INCREG,
	SANY,	TANY,
	SCREG,	TLONG|TULONG,
		NCREG,	RESC1,
		"	mov AR,A1\n	mov UR,U1\n", },

{ OPLTYPE,	INBREG,
	SANY,		TANY,
	SNAME|SOREG,	TPOINT,
		NBREG,	RESC1,
		"	lda A1,AR\n", },

{ OPLTYPE,	INBREG,
	SANY,		TANY,
	SLDFPSP,	TANY,
		NBREG,	RESC1,
		"	lda A1,AR\n", },

{ OPLTYPE,	INCREG,
	SANY,		TLONG|TULONG,
	SNAME|SOREG,	TLONG|TULONG,
		NCREG,	RESC1,
		"	lda A1,AR\n"
		"	lda U1,UR\n", },

/*
 * Simple ops.
 */
{ PLUS,		INBREG|INAREG,
	SAREG|SBREG,	TWORD|TPOINT,
	SONE,		TANY,
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
{ PLUS,		INCREG,
	SCREG,		TLONG|TULONG,
	SOREG,		TLONG|TULONG,
		NBREG,	RLEFT,
		"	lda 2,UR\n"
		"	addz 2,1,szc\n"
		"	inc 0,0\n"
		"	lda 2,AR\n"
		"	add 2,0\n", },

{ LS,		INAREG|INBREG,
	SAREG|SBREG,	TWORD|TPOINT,
	SAREG|SBREG,	TINT,
		NAREG,	RLEFT,
		"	neg AR,A1,snr\n"
		"	  jmp .+4\n"
		"	movzl AL,AL\n"
		"	inc A1,A1,szr\n"
		"	  jmp .-2\n", },

/* long left shft.  left in ac0-1 and right in ac2 */
{ LS,		INCREG,
	SCREG,	TLONG|TULONG,
	SAREG,	TANY,
		0,	RLEFT,
		"	jsr lsh32\n", },
#if 0
		"	neg AR,3,snr\n"
		"	  jmp .+5\n"
		"	movzl UL,UL\n"
		"	movl AL,AL\n"
		"	inc 3,3,szr\n"
		"	  jmp .-3\n"
		"	lda 3,fp\n", },
#endif

/* indirection */
{ UMUL,	INCREG,
	SANY,	TANY,
	SOREG,	TLONG|TULONG,
		NCREG,	RESC1,
		"	lda A1,AL\n	lda U1,UL\n", },



{ OPSIMP,	INBREG|INAREG|FOREFF,
	SAREG|SBREG,	TWORD|TPOINT,
	SAREG|SBREG,	TWORD|TPOINT,
		0,	RLEFT,
		"	O AR,AL\n", },

/*
 * Indirections
 */
#ifdef nova4
{ UMUL,	INAREG,
	SANY,				TPTRTO|TCHAR|TUCHAR,
	SOREG|SAREG|SBREG|SNAME,	TCHAR|TUCHAR,
		NAREG|NASL,	RESC1,
		"	ldb A1,AL\n", },
#endif
{ UMUL,	INAREG,
	SANY,	TPTRTO|TUCHAR,
	SOREG,	TUCHAR,
		NSPECIAL|NAREG,	RESC1,
		"	jsr @lbyt\n", },

{ UMUL,	INAREG,
	SANY,	TPTRTO|TCHAR,
	SOREG,	TCHAR,
		NSPECIAL|NAREG,	RESC1,
		"	jsr @lsbyt\n", },

{ UMUL,	INAREG,
	SANY,	TPOINT|TWORD,
	SOREG,	TPOINT|TWORD,
		NAREG|NASL,	RESC1,
		"	lda A1,AL\n", },

{ UMUL,	INBREG,
	SANY,	TPOINT|TWORD,
	SOREG,	TPOINT|TWORD,
		NBREG|NBSL,	RESC1,
		"	lda A1,AL\n", },

/*
 * logops
 */
{ EQ,	FOREFF,
	SAREG|SBREG,	TANY,
	SZERO,		TANY,
		0,	RNOP,
		"	mov# AL,AL,snr\n	jmp LC\n", },

{ EQ,	FOREFF,
	SAREG|SBREG,	TANY,
	SAREG|SBREG,	TANY,
		0,	RNOP,
		"	sub# AL,AR,snr\n	jmp LC\n", },

{ NE,	FOREFF,
	SAREG|SBREG,	TANY,
	SZERO,		TANY,
		0,	RNOP,
		"	mov# AL,AL,szr\n	jmp LC\n", },

{ NE,	FOREFF,
	SAREG|SBREG,	TANY,
	SAREG|SBREG,	TANY,
		0,	RNOP,
		"	sub# AL,AR,szr\n	jmp LC\n", },

/* test >= by subtracting and then looking at the sign bit */
{ GE,	FOREFF,
	SAREG|SBREG,	TANY,
	SAREG|SBREG,	TANY,
		0,	RNOP,
		"	subl# AL,AR,snc\n	jmp LC\n", },



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

{ CALL,		INAREG,
	SCON,	TANY,
	SANY,	TANY,
		NAREG|NASL|NASR,	RESC1,
		"	jsr CL\n", },

{ UCALL,	INAREG,
	SCON,	TANY,
	SANY,	TANY,
		NAREG|NASL|NASR,	RESC1,
		"	jsr CL\n", },

{ CALL,		INBREG,
	SCON,	TANY,
	SANY,	TANY,
		NBREG|NBSL|NBSR,	RESC1,
		"	jsr CL\n", },

{ UCALL,	INBREG,
	SCON,	TANY,
	SANY,	TANY,
		NBREG|NBSL|NBSR,	RESC1,
		"	jsr CL\n", },

{ GOTO,		FOREFF,
	SCON,	TANY,
	SANY,	TANY,
		0,	RNOP,
		"	jmp LL\n", },

{ FUNARG,	FOREFF,
	SAREG|SBREG,	TCHAR|TUCHAR|TWORD|TPOINT,
	SANY,		TCHAR|TUCHAR|TWORD|TPOINT,
		0,	RNULL,
		"	sta AL,@sp\n", },

{ FUNARG,	FOREFF,
	SCREG,	TLONG|TULONG,
	SANY,	TLONG|TULONG,
		0,	RNULL,
		"	sta AL,@sp\n"
		"	sta UL,@sp\n" },

# define DF(x) FORREW,SANY,TANY,SANY,TANY,REWRITE,x,""

{ UMUL, DF( UMUL ), },

{ ASSIGN, DF(ASSIGN), },

{ STASG, DF(STASG), },

{ FLD, DF(FLD), },

{ OPLEAF, DF(NAME), },

{ OPUNARY, DF(UMINUS), },

{ OPANY, DF(BITYPE), },

{ FREE,	FREE,	FREE,	FREE,	FREE,	FREE,	FREE,	FREE,	"help; I'm in trouble\n" },
};

int tablesize = sizeof(table)/sizeof(table[0]);
