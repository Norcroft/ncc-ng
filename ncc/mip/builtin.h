/*
 * mip/builtin.h:
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Codemist Ltd., 1987-1992.
 * Copyright (C) Advanced RISC Machines Limited, 1991-1992.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#ifndef _builtin_h
#define _builtin_h

#ifndef _defs_LOADED
#  include "defs.h"
#endif

extern FloatCon  *fc_two_31;    /* floating point constant 2^31 */

typedef struct {
    FloatCon *s;        /* short version */
    FloatCon *d;        /* double version */
} FPConst;

extern FPConst fc_zero;         /* floating point constants 0.0  */
#ifdef PASCAL /*ECN*/
extern FPConst fc_half;         /*                          0.5  */
extern FPConst fc_big;          /*               FLT or DBL MAX  */
#endif
extern FPConst fc_one;          /*                          1.0  */
extern FPConst fc_two;          /*                          2.0  */
extern FPConst fc_minusone;     /*                          -1.0  */

extern TypeExpr *te_boolean;    /* == te_int in C */
extern Expr *lit_false;         /* (int)0 in C    */
extern Expr *lit_true;          /* (int)1 in C    */
extern Expr *lit_zero;
extern Expr *lit_one;

extern TypeExpr *te_char;    /* = (global)primtype_(bitoftype_(s_char)) */
extern TypeExpr *te_int;     /* = (global)primtype_(bitoftype_(s_int)) */
extern TypeExpr *te_ushort, *te_uint, *te_lint, *te_ulint;  /* and friends */
extern TypeExpr *te_llint, *te_ullint;
extern TypeExpr *te_stringchar, *te_wstringchar, *te_wchar;
#ifdef EXTENSION_UNSIGNED_STRINGS
extern TypeExpr *te_ustringchar;
#endif
extern TypeExpr *te_double;  /* = (global)primtype_(bitoftype_(s_double)) */
extern TypeExpr *te_float;   /* its short friend */
extern TypeExpr *te_ldble;   /* and its long one */
extern TypeExpr *te_void;    /* = (global)primtype_(bitoftype_(s_void)) */
extern TypeExpr *te_charptr; /* = (global)ptrtotype_(te_char))) */
extern TypeExpr *te_intptr;  /* = (global)ptrtotype_(te_int))) */
extern TypeExpr *te_voidptr; /* = (global)ptrtotype_(te_void))) */
extern TypeExpr *te_fntype(TypeExpr *res, TypeExpr *a1, TypeExpr *a2,
                                          TypeExpr *a3, TypeExpr *a4,
                                          TypeExpr *a5);
extern TypeExpr *g_te_fntype(TypeExpr *res, TypeExpr *a1, TypeExpr *a2,
                                            TypeExpr *a3, TypeExpr *a4,
                                            TypeExpr *a5);

#define te_size_t (feature & FEATURE_PCC ? te_int : te_uint)

extern Binder *datasegment, *codesegment, *constdatasegment, *ddtorsegment;
#ifdef TARGET_HAS_BSS
extern Binder *bsssegment;
#endif
extern Binder *extablesegment, *exhandlersegment;
extern Symstr *mainsym, *setjmpsym, *assertsym, *first_arg_sym, *last_arg_sym;
#define DUFF_SYMSTR ((Symstr*)DUFF_ADDR)
#ifdef CPLUSPLUS
extern Symstr *thissym, *ctorsym, *dtorsym, *assignsym, *vtabsym,
              *deletesym, *dtorgenlabsym;
#else
#define thissym DUFF_SYMSTR
#define ctorsym DUFF_SYMSTR
#define dtorsym DUFF_SYMSTR
#define assignsym DUFF_SYMSTR
#define vtabsym DUFF_SYMSTR
#define deletesym DUFF_SYMSTR
#define dtorgenlabsym DUFF_SYMSTR
#endif
extern Symstr *libentrypoint, *stackoverflow, *stack1overflow,
              *countroutine, *count1routine;

extern Symstr *traproutine, *targeterrno;

typedef struct op_simulation {
   Expr *mulfn, *divfn, *udivfn, *divtestfn, *remfn, *uremfn;
#ifdef TARGET_HAS_DIV_10_FUNCTION
   Expr *div10fn, *udiv10fn, *rem10fn, *urem10fn;
#endif
   Expr *fdivfn, *ddivfn;
   Expr *memcpyfn, *memsetfn;
   Expr *inserted_word;
   Expr *readcheck1, *readcheck2, *readcheck4,
        *writecheck1, *writecheck2, *writecheck4;
   Expr *xprintf, *xfprintf, *xsprintf;
   Expr *realmemcpyfn, *realmemsetfn;
   Symstr *strcpysym, *strlensym;
   Symstr *yprintf, *yfprintf, *ysprintf;
#ifdef STRING_COMPRESSION
   Expr *xprintf_z, *xfprintf_z, *xsprintf_z, *yprintf_z, *yfprintf_z, *ysprintf_z;
#endif
#ifdef RANGECHECK_SUPPORTED
   Symstr *abcfault, *valfault;
#endif
   Expr *dadd, *dsubtract, *dmultiply, *ddivide, *dnegate,
     *dgreater, *dgeq, *dless, *dleq, *dequal, *dneq, *dfloat, *dfloatu,
     *dfix, *dfixu,
     *drsb, *drdiv;
   Expr *fadd, *fsubtract, *fmultiply, *fdivide, *fnegate,
     *fgreater, *fgeq, *fless, *fleq, *fequal, *fneq, *ffloat, *ffloatu,
     *ffix, *ffixu,
     *frsb, *frdiv;
   Expr *fnarrow, *dwiden;
   Expr *llnot, *llneg;
   Expr *lladd, *llrsb, *llsub, *llmul;
   Expr *llurdv, *lludiv, *llsrdv, *llsdiv;
   Expr *llurrem, *llurem, *llsrrem, *llsrem;
   Expr *lland, *llor, *lleor;
   Expr *llshiftl, *llushiftr, *llsshiftr;
   Expr *llcmpeq, *llcmpne;
   Expr *llucmpgt, *llucmplt, *llucmpge, *llucmple;
   Expr *llscmpgt, *llscmplt, *llscmpge, *llscmple;
   Expr *llfroml, *llfromu, *llsfromf, *llsfromd, *llufromf, *llufromd;
   Expr *lltol, *llstof, *llstod, *llutof, *llutod;

   Expr *proc_entry, *proc_exit;
   Symstr *dpow, *dfloor, *dceil, *dmod, *dabs;
} op_simulation;

extern op_simulation sim;

#ifdef CPLUSPLUS
typedef struct cpp_op_simulation {
   Symstr *xnew, *xdel;
   Binder *xpvfn;
   Expr *xpush_ddtor;
   Expr *x__throw;
   Expr *x__ex_pop;
   Expr *x__ex_push;
   Expr *x__ex_top;
   Expr *xnewvec, *xdelvec;
   Expr *xmapvec1, *xmapvec1c, *xmapvec1ci, *xmapvec2;
} cpp_op_simulation;

extern cpp_op_simulation cppsim;
#endif

extern bool returnsheapptr(Symstr *fn);

extern void builtin_init(void);

#endif

/* end of mip/builtin.h */
