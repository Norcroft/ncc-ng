/*
 * C compiler file cg.c
 * Copyright (C) Codemist Ltd, 1988.
 * Copyright (C) Acorn Computers Ltd., 1988.
 * Copyright 1991-1997 Advanced Risc Machines Limited. All rights reserved
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$ Codemist 119
 * Checkin $Date$
 * Revising $Author$
 */

/* AM memo: remove smashes to tree for long-term safety (e.g. find s_neg)  */
/* AM memo: bug in cse/deadcode kills fp voided div.                       */
/* AM Mar 89: Add s_wstring (treated here as s_string).  Memo: later add   */
/*            J_WSTRING similar to J_STRING for cross sex compilation.     */
/* AM Nov 88: Remove some (only!!!) magic numbers on mcreps for optional   */
/* double alignment.                                                       */
/* Memo: tidy up the current_/greatest_stackdepth edifice.                 */

/* see cg_exprreg() for half developed code to optimise the JOP            */
/* code to save space (and possibly time in regalloc).                     */

/* Note to reader:  the order of routines in here is extremely unnatural */
/* (hence the large number of inane 'static' forward references below).  */
/* It is so that the largest routine gets compiled first to save         */
/* (compile-time) space.  Yuk.  Undoes rationalisation of 4/12/86.       */

/*
 * ACN Feb 90: rework struct args support and '...' for 88000 etc.
 * AM aug 87:  improve the code for x.a++ etc, following ACN's LDRVK.
 * ACN aug 87  add 'valof' block extension.  Buggy for structs still.
 * AM 20-jun-87 fix bug in cg_cond on structs. fix fp/int reg confusion
 *              if registers active at cg_fnap.  Redo cg_fnargs removing
 *              50 limit on arg count, and improving code.
 * AM 26-may-87 redo CASEBRANCH.  Re-use store later.
 * AM 22-apr-87 fix bug in loadzero resulting in f()*0 doing nothing.
 * AM 27-dec-86 require just 2 free fpregs in cg_expr (why can't one work?)
 * AM 4-dec-86 put struct/unions of size 4 to regs, fix bug in f().a.
 * AM 4-dec-86 rationalisation(!) of order - i.e. Cmd stuff here.
 * AM 3-dec-86 separate 'C' case into s_break and s_endcase.
 */

#include <stddef.h>
#include <stdlib.h>
#include <string.h>

#include "globals.h"
#include "cg.h"
#include "store.h"
#include "codebuf.h"
#include "aeops.h"
#include "util.h"
#include "xrefs.h"
#include "jopcode.h"
#include "regalloc.h"
#include "regsets.h"
#include "cse.h"
#include "sr.h"
#include "flowgraf.h"
#include "mcdep.h"
#include "aetree.h"
#include "builtin.h"
#include "sem.h"       /* typeofexpr */
#include "syn.h"
#include "simplify.h"  /* mcrepofexpr */
#include "bind.h"
#include "errors.h"
#include "inline.h"
#include "inlnasm.h"

/* The following lines are in flux, but are here because similar things */
/* are wanted if TARGET_IS_ALPHA.  They also highlight the dependency   */
/* on alignof_struct==4 of code for struct-return in registers.         */
/* MEMCPYREG, MEMCPYQUANTUM now in defaults.h (needed by                */
/* returnsstructinregs())                                               */
#if MEMCPYREG == DBLREG
#define J_memcpy(op) ((op&~J_ALIGNMENT) - J_LDRK + (J_LDRDK|J_ALIGN8))
#else
#define J_memcpy(op) (op)
#endif
#define MOVC_ALIGN_MAX alignof_toplevel_auto
#define MOVC_ALIGN_MIN alignof_int         /* most old code */

#ifdef NEW_J_ALIGN_CODE
/* But this isn't quite true for TARGET_IS_ALPHA stack vars...          */
#  define J_ALIGN4V (alignof_toplevel_auto==8 ? J_ALIGN8 : J_ALIGN4)
#else
#  define J_ALIGN4V J_ALIGN4
#endif

/* The next routine is a nasty hack -- see its uses.   */
/* It copies a SynAlloc BindList into a BindAlloc one. */
static SynBindList *binderise(SynBindList *l)
{   SynBindList *f1 = NULL;
    for (; l != NULL; l = l->bindlistcdr)
        f1 = (SynBindList *)mkBindList(f1, l->bindlistcar);
    return (SynBindList *)dreverse((List *)f1);
}

#define NOTALABEL   ((LabelNumber *)DUFF_ADDR)
#define NOTINLOOP   NOTALABEL
#define NOTINSWITCH NOTALABEL

static int32 max_icode, max_block;          /* statistics (lies, damn lies) */

static Cmd *cg_current_cmd;
static int32 current_stackdepth;
static BindList *local_binders, *regvar_binders;
static Binder *integer_binder, *double_pad_binder;
bool has_main;
static bool defining_main;
static bool cg_infobodyflag;

static struct SwitchInfo {
    BindList *binders;            /* 'endcase' may be non-local goto */
    LabelNumber *defaultlab, *endcaselab;
} switchinfo;

static struct LoopInfo {
    BindList *binders;  /* 'break', 'continue' may be non-local goto */
    LabelNumber *breaklab, *contlab;
} loopinfo;

#ifdef EXTENSION_VALOF
static struct ValofInfo {
    BindList *binders;
    LabelNumber *lab;
    VRegnum r;
} valofinfo;
#endif

typedef struct CasePair { int32 caseval; LabelNumber *caselab;} CasePair;

static VRegnum cg_expr1(Expr *x,bool valneeded);
#ifndef ADDRESS_REG_STUFF
#define ensure_regtype(r,rsort) (r)
#endif
#define IsVolatile 1
#define IsUnaligned 2
#define BaseIsWordAligned 4
static VRegnum cg_stind(VRegnum r, Expr *val, Expr *x, const int32 flag, Binder *b,
                    const int32 mcmode, const int32 mclength,
                    bool address, int volatileorunaligned);
static VRegnum cg_var(VRegnum r, Binder *b, AEop flag,
                      int32 mcmode, int32 mclength, bool address);
static VRegnum reserveregister(RegSort precision);
static VRegnum getreservedreg(VRegnum r);
static void cg_bindlist(SynBindList *x,bool initflag);
static Binder *is_local_adcon(Expr *a);
static Expr *take_address(Expr *e);
static VRegnum open_compilable(Expr **xp,RegSort rsort,bool valneeded);
static VRegnum cg_fnap(Expr *x,VRegnum resreg,bool valneeded);
static VRegnum cg_cond
(Expr *c,bool valneeded,VRegnum targetreg,
                       LabelNumber *l3,bool structload);
static VRegnum cg_cast1(Expr *x1,int32 mclength,int32 mcmode);
static VRegnum cg_cast1_(VRegnum r, int32 mclength, int32 mcmode, int32 argrep);
static VRegnum cg_addr(Expr *sv,bool valneeded);

#ifdef EXTENSION_VALOF
static void cg_cmd(Cmd *x);
#endif
static void structure_assign(Expr *lhs,Expr *rhs,int32 length);
static void verify_integer(Expr *x);
static VRegnum cg_binary(J_OPCODE op,Expr *a1,Expr *a2,bool commutesp,
                         RegSort fpp);
static VRegnum cg_binary_or_fn(J_OPCODE op,TypeExpr *type,Expr *fname,
                               Expr *a1,Expr *a2,bool commutesp);
#define iszero(x) is_intzero(x)
#define isone(x) is_intone(x)
#define isminusone(x) is_intminusone(x)

static int32 ispoweroftwo(Expr *x);
static VRegnum cg_loadconst(int32 n,Expr *e);
static void cg_count(FileLine fl);
static void cg_return(Expr *x, bool implicitinvaluefn);
static void cg_loop(Expr *init, Expr *pretest, Expr *step, Cmd *body,
                    Expr *posttest);
static void cg_test(Expr *x, bool branchtrue, LabelNumber *dest);
static void casebranch(VRegnum r, CasePair *v, int32 ncases,
                       LabelNumber *defaultlab);
static void cg_case_or_default(LabelNumber *l1);
static void cg_condjump(J_OPCODE op,Expr *a1,Expr *a2,RegSort rsort,J_OPCODE cond,LabelNumber *dest);
static void emituse(VRegnum r,RegSort rsort);
static VRegnum load_integer_structure(Expr *e);
static Binder *gentempvar(TypeExpr *t, VRegnum r);
static void cg_cond1(Expr *e, bool valneeded, VRegnum targetreg,
                     LabelNumber *l3, bool structload);

/* result_variable is an extra first arg. for use with structure returning  */
/* functions - private to cg_return and cg_topdecl                          */
static Binder *result_variable, *result_temporary;
static LabelNumber *structretlab;

#define lowerbits(n) (((int32)1<<(n))-1)

/*************************************************************************/
/*                 Start of codegeneration proper.                       */
/*************************************************************************/

static bool ContainsUnalignedSubExpr(Expr *x)
{
    for (;;) switch (h0_(x))
    {
    case s_integer:
    case s_floatcon:
    case_s_any_string
    case s_binder:
        return NO;

/* monadic things... */
    case s_content:
    case s_content4:
        if (isunaligned_expr(x)) return YES;
        x = arg1_(x);
        continue;
    case s_cast:
        if (isunaligned_type(type_(x))) return YES;
        /* fall through */
    case s_bitnot:
    case s_boolnot:
    case s_monplus:
    case s_neg:
    case s_addrof:
        x = arg1_(x);
        continue;
    case s_cond:
        /* due to the fact that operands from s_cond are never combined */
        /* we do not need the complexity of binary operators below.     */
        return ContainsUnalignedSubExpr(arg1_(x)) ||
               ContainsUnalignedSubExpr(arg2_(x)) ||
               ContainsUnalignedSubExpr(arg3_(x));
    case s_assign:
    case s_displace:
    case s_andand:
    case s_oror:
    case s_equalequal:
    case s_notequal:
    case s_greater:
    case s_greaterequal:
    case s_less:
    case s_lessequal:
    case s_comma:
    case s_and:
    case s_plus:
    case s_minus:
    case s_leftshift:
    case s_or:
    case s_rightshift:
    case s_xor:
    case s_times:
    case s_div:
    case s_rem:
        return ContainsUnalignedSubExpr(arg1_(x)) ||
               ContainsUnalignedSubExpr(arg2_(x));
    case s_let:
        x = arg2_(x);
        continue;
    case s_fnap:
        if (ContainsUnalignedSubExpr(arg1_(x))) return YES;
        {   ExprList *l = exprfnargs_(x);
            for (; l != NULL; l = cdr_(l))
                if (ContainsUnalignedSubExpr(exprcar_(l)))
                    return YES;
        }
    default:
        return NO;
    }
}

#if defined TARGET_HAS_SCALED_ADDRESSING || defined TARGET_HAS_SCALED_OPS || \
    defined TARGET_HAS_SCALED_ADD

#ifndef target_shiftop_allowed
#define target_shiftop_allowed(n, len, mode, op) target_scalable(n, len)
#endif

#define unsigned_expression_(x) \
        ((mcrepofexpr(x) >> MCR_SORT_SHIFT) == 1)

static Expr *ignore_ineffectual_casts(Expr *x) {
    for (; h0_(x) == s_cast; x = arg1_(x)) {
        int32 resrep = mcrepofexpr(x),
              argrep = mcrepofexpr(arg1_(x));
        int32 ressort = resrep & MCR_SORT_MASK,
              argsort = argrep & MCR_SORT_MASK;
        if (ressort > MCR_SORT_UNSIGNED || argsort > MCR_SORT_UNSIGNED)
            break;
        {   int32 ressize = resrep & MCR_SIZE_MASK,
                  argsize = argrep & MCR_SIZE_MASK;
            if (ressort == argsort) {
                if (ressize < argsize)
                    break;
            } else if (ressize != argsize || ressize < 4)
              break;
        }
    }
    return x;
}

static Expr *shift_op1(Expr *x, int32 n)
{
    if (n==0) syserr(syserr_cg_shift0);
    while ((n & 1)==0) n >>= 1;
    if (n==1) return x;
    return mk_expr2(s_times, te_int, x,
                    mkintconst(te_int, n, 0));
}

static Expr *shift_operand(Expr *x)
/* if is_shifted() returned true this can be used to extract the operand */
{
    int32 n;
    Expr *arg;
    x = ignore_ineffectual_casts(x);
    switch (h0_(x))
    {
case s_rightshift:
case s_leftshift:
        arg = arg2_(x);
        if (h0_(arg) == s_integer && intval_(arg)==0)
            return shift_operand(arg1_(x));
        return arg1_(x);
case s_times:
        arg = arg1_(x);
        if (h0_(arg)==s_integer)
        {   n = intval_(arg);
            if ((n & 1)==0) return shift_op1(arg2_(x), n);
        }
        else return shift_op1(arg1_(x), intval_(arg2_(x)));
default:
        syserr(syserr_not_shift);
        return x;
    }
}

static int32 shift_amount(Expr *x)
/* if is_shifted() returned true this can be used to extract the shift   */
{
    int32 n;
    Expr *arg;
    x = ignore_ineffectual_casts(x);
    switch (h0_(x))
    {
case s_rightshift:
        n = intval_(arg2_(x));
        if (n == 0) return shift_amount(arg1_(x));
/* This is a horrid packing scheme */
        n = (n & SHIFT_MASK) | SHIFT_RIGHT;
        if (!unsigned_expression_(arg1_(x))) n |= SHIFT_ARITH;
        return n;
case s_leftshift:
        arg = arg2_(x);
        n = intval_(arg);
        if (n == 0) return shift_amount(arg1_(x));
        return n & SHIFT_MASK;
case s_times:
        arg = arg1_(x);
        if (h0_(arg)==s_integer)
        {   n = intval_(arg);
            if ((n & 1)==0) return logbase2(n) & SHIFT_MASK;
        }
        arg = arg2_(x);
        if (h0_(arg)==s_integer)
        {   n = intval_(arg);
            if ((n & 1)==0) return logbase2(n) & SHIFT_MASK;
        }
        /* drop through */
default:
        syserr(syserr_not_shift1);
        return 0;
    }
}

static int32 is_shifted(Expr *x, int32 mclength, int32 signedness, int32 op)
/* Predicate to test if an expression is of the form something shifted.  */
/* 11-Nov-87: changed to consult target_scalable() for 32016/vax.        */
/* Used to decide if scaled indexed addressing is wanted.                */
/*
 * mclength is zero for scaled-op investigation, or 1, 2, 4 or 8 for byte,
 * short, long or double memory references.  It is -1, -2, -4 or -8 for
 * memory references where the scaled index must be subtracted from the
 * base value rather than added. mclength is just handed down to a
 * target specific test for validity.
 */
{
    int32 n;
    Expr *arg;
    x = ignore_ineffectual_casts(x);
    switch (h0_(x))
    {
case s_rightshift:
case s_leftshift:
        arg = arg2_(x);
        if (h0_(arg)!=s_integer) return 0;
        n = intval_(arg);
        if (n == 0) return is_shifted(arg1_(x), mclength, signedness, op);
        if (n>=0 && n<=31)
            return target_shiftop_allowed(shift_amount(x), mclength, signedness, op);
        else return 0;
case s_times:                   /* detect multiplication by 2, 4, 6, ...  */
        if ((arg = arg1_(x), h0_(arg)) == s_integer ||
            (arg = arg2_(x), h0_(arg)) == s_integer)
        {   n = intval_(arg);
            if (n!=0 && (n & 1)==0)
                return target_shiftop_allowed(shift_amount(x), mclength, signedness, op);
        }
        return 0;
default:
        return 0;
    }
}

#endif /* TARGET_HAS_SCALED_ADDRESSING or _OPS */

/* The code that follows is too simplistic - I need a better estimate of */
/* the complexity of expressions, e.g. an estimate of the number of regs */
/* needed to evaluate something.                                         */

/* values for nastiness() */
#define ISCONST  0x100   /* assumed minimum for nastiness()              */
#define ISXCONST 0x101   /* floating, string, (addrof one day -- ask AM) */
#define ISBIND   0x102
#define ISEXPR   0x103
/* ISHARD *MUST BE* the maximum nastiness() can return:                  */
/* such expressions have function applications in them -- allows 2^10    */
/* terms in an expression (without fn calls) before we have to truncate  */
/* to avoid hitting the ISHARD ceiling.   See nastiness().               */
#define ISHARD   (ISEXPR+10)   /* assumed maximum for nastiness()        */

static int nastiness(Expr *x)
{
/* This procedure is used to provide an heuristic that helps me decide   */
/* what order to prepare arguments for functions in. It a value between  */
/* ISCONST and ISHARD to show if the expression x contains any function  */
/* calls (which clobber lots of regs) or otherwise a value estimating    */
/* the likely number of registers the expression is liable to take.      */
    AEop op;
    int n1, n2, n3, nr;
#define max_(a,b) ((a)>=(b) ? (a):(b))
    for (;;) switch (op = h0_(x))
    {
case s_integer:
        return ISCONST;
case s_floatcon:
case s_int64con:
case_s_any_string
        return ISXCONST;
case s_binder:
        return ISBIND;
/* monadic things... */
case s_content:
case s_content4:
#if 0
        {   int32 m = mcrepofexpr(x);
            if ((m >> MCR_SORT_SHIFT) == 3 && (m & MCR_SIZE_MASK) > 4)
                return ISHARD;  /* big struct */
        }
#endif
        if (memory_access_checks) return(ISHARD);
case s_cast:
case s_bitnot:
case s_boolnot:
case s_monplus:
case s_neg:
case s_addrof:
        x = arg1_(x);
        continue;
case s_cond:
        /* due to the fact that operands from s_cond are never combined */
        /* we do not need the complexity of binary operators below.     */
        nr = nastiness(arg1_(x));
        n2 = nastiness(arg2_(x));
        nr = max_(nr,n2);
        n3 = nastiness(arg3_(x));
        nr = max_(nr,n3);
        return max_(ISEXPR, nr);
case s_assign:
case s_displace:
        {   int32 m = mcrepofexpr(x);
            if ((m >> MCR_SORT_SHIFT) == 3 && (m & MCR_SIZE_MASK) > 4)
                return ISHARD;  /* big struct */
        }
        /* drop through */
case s_andand:
case s_oror:
case s_equalequal:
case s_notequal:
case s_greater:
case s_greaterequal:
case s_less:
case s_lessequal:
case s_comma:
case s_and:
case s_plus:
case s_minus:
case s_leftshift:
case s_or:
case s_rightshift:
case s_xor:
case s_times:
case s_div:
case s_rem:
        n1 = nastiness(arg1_(x));
        n2 = nastiness(arg2_(x));
/* A good estimate of the complexity (number of temp registers needed)  */
/*             n1==n2 ? n1+1 : max(n1,n2),                              */
/* but modify the middle term so that we never exceed ISHARD, nor       */
/* even attain it unless one term is ISHARD (thus ISHARD terms are only */
/* those containing function like things).  See cg_fnargs for why.      */
        nr = n1==n2 ? (n1>=ISHARD-1 ? n1 : n1+1) : max_(n1,n2);
#ifndef TARGET_HAS_MULTIPLY
          /* See if we will need a proc. call on the ARM and similar.      */
          /* However, this 'better' code seems to compile a slightly 0.01% */
          /* bigger compiler than if we omit the conjuncts which check for */
          /* (const) multiplies which do not require a function call!!!!   */
          /* Leave in the 'notionally correct code'.                       */
        if (op == s_times && h0_(arg1_(x)) != s_integer
                          && h0_(arg2_(x)) != s_integer) return ISHARD;
#endif
#ifndef TARGET_HAS_DIVIDE
        if ((op == s_div || op == s_rem) && h0_(arg2_(x)) != s_integer)
            return ISHARD;
#endif
        return max_(ISEXPR, nr);            /* always a little bit hard. */
case s_let:
        x = arg2_(x);
        continue;
default:   /* includes s_fnap */
        return ISHARD;
    }
#undef max_
}

#define unsigned_expression_(x) \
        ((mcrepofexpr(x) >> MCR_SORT_SHIFT) == 1)

static RegList *usedregs, *usedfpregs;
static int32 nusedregs, nusedfpregs, spareregs, sparefpregs, nreservedregs;

static BindList *datasegbinders;

#define NOT_OPEN_COMPILABLE ((VRegnum)(-2))
/* Temp - real distinguished non-GAP VRegnum wanted */
#define cg_loadzero(e) cg_loadconst(0,e)

#ifdef TARGET_HAS_DIVIDE
#define cg_divrem(op,type,fname,a1,a2) \
        cg_binary(op,a1,a2,0,INTREG)
#else
#define cg_divrem(op,type,fname,a1,a2) \
        cg_binary_or_fn(op,type,fname,a1,a2,0)
#endif

#define mkArg(x,y)        ((Expr*)mkExprList(x,y))
#define mkArgList1(x)     ((Expr*)mkExprList(0,x))
#define mkArgList2(x,y)   ((Expr*)mkExprList(mkExprList(0,y),x))
#define mkArgList3(x,y,z) ((Expr*)mkExprList(mkExprList(mkExprList(0,z),y),x))

VRegnum cg_exprvoid(Expr *x)
{
    return cg_expr1(x, NO);
}

VRegnum cg_expr(Expr *x)
{
    return cg_expr1(x, YES);
}

static VRegnum cg_diadvoid(Expr *x)
{   cg_expr1(arg1_(x), NO);
    return cg_expr1(arg2_(x), NO);
}

static VRegnum cg_multiply(TypeExpr *type, Expr *a1, Expr *a2)
{
#ifdef TARGET_HAS_MULTIPLY
    IGNORE(type);
    return cg_binary(J_MULR, a1, a2, 1, INTREG);
#else
    return cg_binary_or_fn(J_MULR, type, sim.mulfn, a1, a2, 1);
#endif
}

static VRegnum cg_unary_i(J_OPCODE op, RegSort rsort, Expr *x)
{
    VRegnum r, r1;
#ifdef TARGET_HAS_SCALED_OPS
    if (op == J_NOTR && is_shifted(x, 0, 0, 0)) {
        r1 = cg_expr(shift_operand(x));
        r = fgetregister(rsort);
        emitshift(op, r, GAP, r1, shift_amount(x));
    } else
#endif
    {   r1 = cg_expr(x);
        r = fgetregister(rsort);
        emitreg(op, r, GAP, r1);
    }
    bfreeregister(r1);
    return r;
}

/* @@@ what about LNGREG? */
static J_OPCODE floatyop(RegSort rsort, J_OPCODE j_i, J_OPCODE j_f, J_OPCODE j_d) {
    return rsort == DBLREG ? j_d :
           rsort == FLTREG ? j_f :
                             j_i;
}

/* Maybe the following routine will subsume cg_expr2 one day.          */
static VRegnum cg_exprreg(Expr *x, VRegnum r)
/* Used to save (virtual) registers for simple expressions which must  */
/* then be moved to a specified register (e.g. cond/fn_arg/fn_result). */
        /* Note that targetreg here is only 'reserved' not 'got'.  The  */
        /* caller of cg_cond will getreservedreg() on return to avoid   */
        /* overestimating temporary register use.                       */
{   switch (h0_(x))
    {
case s_integer:
        if (usrdbg(DBG_LINE) && exprfileline_(x) != 0)
            emitfl(J_INFOLINE, *exprfileline_(x));
        emit(J_MOVK, r, GAP, intval_(x));
        break;
case_s_any_string
        emitstring(J_STRING, r, exs_(x)->strseg);
        break;
#ifdef EVEN_FINER_DAY
case s_binder: ...
        break;
#endif
case s_cond:
        {   LabelNumber *l3 = nextlabel();
/* Previous phases of the compiler must have arranged that the two arms  */
/* of the condition each have the same mode. In particular they must     */
/* either be both integer or both floating point values. This has to     */
/* include the possibility of them being voided. Structure values are    */
/* not legal here.                                                       */
            (void)cg_cond(x, 1, r, l3, 0);
            start_new_basic_block(l3);
        }
        break;
/* n.b. do not use with with s_addrof due to loadadcon() slaving */
default:
        {   VRegnum r2 = cg_expr1(x, 1);
            RegSort rsort = vregsort(r2);
            emitreg(floatyop(rsort, J_MOVR, J_MOVFR, J_MOVDR), r, GAP, r2);
            bfreeregister(r2);
        }
        break;
    }
    return r;   /* may be useful */
}

#ifdef TARGET_HAS_DIVIDE
#ifdef TARGET_LACKS_REMAINDER

/* Use this if the target has divide but not remainder opcodes */
static VRegnum simulate_remainder(TypeExpr *t, Expr *a1, Expr *a2)
{
    Binder *gen1 = gentempbinder(t);
    Binder *gen2 = gentempbinder(t);
/* { int a1= arg1, a2 = arg2;
     a1 - (a1/a2)*a2;
   }
*/
    Expr *x = mk_exprlet(s_let, t,
        mkSynBindList(mkSynBindList(0, gen1), gen2),
        mk_expr2(s_comma, t,
            mk_expr2(s_assign, t,
                (Expr *)gen1,
                a1),
            mk_expr2(s_comma, t,
                mk_expr2(s_assign, t,
                    (Expr *)gen2,
                    a2),
                mk_expr2(s_minus, t,
                    (Expr *)gen1,
                    mk_expr2(s_times, t,
                        mk_expr2(s_div, t, (Expr *)gen1, (Expr *)gen2),
                        (Expr *)gen2)))));
    return cg_expr(x);
}

#endif
#endif

#ifdef ADDRESS_REG_STUFF
static VRegnum ensure_regtype(VRegnum r, RegSort rsort)
{
   if (vregsort(r) != rsort)
   {  if (rsort == ADDRREG)
      {  VRegnum r1 = fgetregister(rsort);
         emitreg(J_MOVR, r1, GAP, r);
         bfreeregister(r);
         r = r1;
      }
      else if (rsort == INTREG);
         /* do nothing -- AM presumes that this is because the          */
         /* back end can always use a D as an A but not vice-versa.     */
         /* Or is it the other way round?                               */
      else
         syserr(syserr_regtype, (long)rsort);
   }
   return r;
}
#endif

#ifdef TARGET_FP_LITS_FROM_MEMORY

void emitfloat1(J_OPCODE op, VRegnum r1, VRegnum r2, FloatCon *m)
{
    J_OPCODE op1;
    VRegnum r99;
    if (op == J_ADCOND || op == J_ADCONF)
    {   emitfloat(op, r1, r2, m);
        return;
    }
    r99 = fgetregister(ADDRREG);
    if (op == J_MOVDK) op = J_LDRDK|J_ALIGN8, op1 = J_ADCOND;
    else if (op == J_MOVFK) op = J_LDRFK|J_ALIGN4, op1 = J_ADCONF;
    else syserr(syserr_emitfloat1);
    emitfloat(op1, r99, GAP, m);
    emit(op, r1, r99, 0);
    bfreeregister(r99);
}

#else
#  define emitfloat1(a,b,c,d) emitfloat(a,b,c,d)
#endif

static VRegnum cg_loadfpzero(RegSort rsort, Expr *e)
{   /* void e if !=NULL and return 0 - used for things like f()*0     */
    VRegnum r;
    if (e) (void)cg_exprvoid(e);
    r = fgetregister(rsort);
    if (rsort == FLTREG)
        emitfloat1(J_MOVFK, r, GAP, fc_zero.s);
    else
        emitfloat1(J_MOVDK, r, GAP, fc_zero.d);
    return r;
}

#ifdef RANGECHECK_SUPPORTED
/* It would seem that this routine is a special case of cg_binary_1().  */
static void boundcheck(J_OPCODE op, VRegnum r, Expr *x)
{
    if (x == NULL)
        /* nothing */;
    else if (integer_constant(x))
        emit(J_RTOK(op), GAP, r, result2);
    else {
        VRegnum r1 = cg_expr(x);
        emitreg(op, GAP, r, r1);
        bfreeregister(r1);
    }
}
#endif

/* note that 'valneeded' and 'RegSort rsort' really tell similar stories */
/* Maybe a VOIDREG version of RegSort subsumes both                      */
static VRegnum cg_expr2(Expr *x, bool valneeded)
{
    AEop op;
    VRegnum r, r1;
    int32 mclength = mcrepofexpr(x);
    int32 mcmode = mclength >> MCR_SORT_SHIFT;
    RegSort rsort = (mclength &= MCR_SIZE_MASK,
         (mcmode!=2) ? INTREG : (mclength==4 ? FLTREG : DBLREG));
#ifdef ADDRESS_REG_STUFF
    if( rsort == INTREG )
    {
/* Work out further if the result is to be used as an address            */
/* If it is the specialise further to an ADDRREG                         */
      TypeExpr *te = princtype(typeofexpr(x));
      /* The t_subscript case is to include strings which       */
      /* have had their implicit '&' removed by simplify().     */
      if (h0_(te) == t_content || h0_(te) == t_subscript)
         rsort = ADDRREG;
    }
#endif

/* The next line will not catch cases where loading a one-word struct    */
/* occurs improperly if that gets treated as an integer. I have to let   */
/* this case slip through since in places I really want to treat such    */
/* structs as ints. Anyway all I lose is an internal check that should   */
/* never really fail anyway.                                             */
    if (mcmode==3 && valneeded)
        syserr(syserr_struct_val);
    if (x == 0) { syserr(syserr_missing_expr); return GAP; }

    op = h0_(x);
    if (usrdbg(DBG_LINE) && hasfileline_(op) && exprfileline_(x) != 0)
        emitfl(J_INFOLINE, *exprfileline_(x));

    switch (op)
    {
case s_throw:
        /* simplify.c has inserted a function call as arg1_(x).         */
        cg_exprvoid(arg1_(x));
        /* Should end a basic block (for dead-code loss here).          */
        return GAP;

case s_binder:
            if (!valneeded && !isvolatile_expr(x)) return GAP;
            {   Binder *b = exb_(x);
                if ((x = bindconst_(b)) != NULL)
                {   if (LanguageIsCPlusPlus)
                        syserr("bindconst $b got to cg.c", b);
                    return cg_expr2(x, valneeded);
                }
                r = ensure_regtype(cg_var(GAP, b, s_content, mcmode, mclength,
                                          rsort==ADDRREG),
                                   rsort);
                if (!valneeded) bfreeregister(r), r = GAP;
                return r;
            }
case s_integer:
            if (!valneeded) return GAP;
#ifdef TARGET_HAS_CONST_R_ZERO
            if (intval_(x) == 0) return R_ZERO;
#endif
            emit(J_MOVK, r = fgetregister(rsort), GAP, intval_(x));
            return r;

case s_floatcon:
            if (!valneeded) return GAP;
            if (software_floats_enabled && rsort != DBLREG)
            /* single precision values treated as ints */
            {   emit(J_MOVK, r = fgetregister(INTREG), GAP,
                             exf_(x)->floatbin.irep[0]);
                return r;
            }
#ifdef TARGET_HAS_CONST_R_FZERO
            if (is_fpzero(x)) return R_FZERO;
#endif
            r = fgetregister(rsort);
            emitfloat1(rsort==DBLREG ? J_MOVDK:J_MOVFK, r, GAP, exf_(x));
            return r;

case_s_any_string
            if (!valneeded) return GAP;
            emitstring(J_STRING, r=fgetregister(ADDRREG),
                                 exs_(x)->strseg);
            return r;

#ifdef EXTENSION_VALOF
case s_valof:
            {   struct ValofInfo saver;

                saver = valofinfo;

                valofinfo.binders = active_binders;
                valofinfo.lab = nextlabel();
                valofinfo.r = reserveregister(rsort);
            /* Valof blocks will not work (a syserr will occur via cg_addr */
            /* or cg_exprreg) for structure results and would need code    */
            /* here and at s_valof (and cg_addr &c) to make them work.     */
                cg_cmd(expr1c_(x));
                r = getreservedreg(valofinfo.r);
                /* The next line does nothing much but waste space usually */
                /* but is needed in case the valof may (or appear to) have */
                /* a route through without a resultis.                     */
                /* See the other uses of J_INIT.                           */
                emitbinder(floatyop(rsort, J_INIT, J_INITF, J_INITD),
                           r, gentempvar(type_(x), r));
                start_new_basic_block(valofinfo.lab);
                valofinfo = saver;
                return r;
            }
#endif

#ifdef RANGECHECK_SUPPORTED
case s_rangecheck:
            /* rangecheck  i, l, u: check that l<=i<=u, taking
               target-dependent action if not.
               Either l or u may be NULL, meaning don't check.
               value is i.
             */
            {   r = cg_expr2(arg1_(x), YES);
                boundcheck(J_CHKLR, r, arg2_(x));
                boundcheck(J_CHKUR, r, arg3_(x));
                return r;
            }

case s_checknot:
            /* check i, k: check that the value of i is not k,
               taking target-dependent action if not.
             */
            {   r = cg_expr2(arg1_(x), YES);
                if (integer_constant(arg2_(x)))
                    emit(J_CHKNEK, GAP, r, result2);
                else if (isintregtype_(rsort))
                    syserr(syserr_checknot);
                else {
                    VRegnum r2 = cg_expr2(arg2_(x), YES);
                    emitreg(rsort==FLTREG ? J_CHKNEFR: J_CHKNEDR,
                             GAP, r, r2);
                    bfreeregister(r2);
                }
                return r;
            }
#endif

case s_let:
            {   BindList *sl = active_binders;
                int32 d = current_stackdepth;
                cg_bindlist(exprletbind_(x), 0);
                r = cg_expr1(arg2_(x), valneeded);
                emitsetsp(J_SETSPENV, sl);
                current_stackdepth = d;
            }
            return r;
case s_fnap:
            if (mcmode == 3) syserr(syserr_fnret_struct);
            /* struct-valued functions should now never be seen here:    */
            /* optimise1 should always have fabricated an assignment     */
            /* (often to a temporary) which turns the s_fnap (via        */
            /* structure_assign()) into s_fnapstruct.                    */

            if (resultinflags_fn(x))
            {
                x = mk_expr3(s_cond, te_int, x, mkintconst(te_int, 1, 0), mkintconst(te_int, 0, 0));
                return cg_expr1(x, valneeded);
            }
            /* drop through */
/*
 * s_fnapstruct is an artefact introduced when a structure returning
 * function call is mapped from
 *        v = f(a,b);
 * onto   (void)f(&v,a,b);
 * so that the converted function application is marked as having been
 * subjected to this transformation.  This is so that cg_fnap can (for
 * some machines) pass the implicit extra address in some way other than
 * making it a new first argument.  Corresponding special treatment
 * is needed in function definitions - here that is achieved by inspection
 * of result_variable (NULL if not used) with funny treatment only
 * activated if TARGET_STRUCT_RESULT_REGISTER is defined.
 */
case s_fnapstructvoid:
case s_fnapstruct:
/* Some functions have special rules re compilation. open_compilable()   */
/* returns -2 if it is handed anything other than one of these.          */
/* NB open_compilable is now handed a pointer to the fnap expression,    */
/* for which it may generate a replacement to be given to cg_fnap        */
            r = open_compilable(&x, rsort, valneeded);
            return (r != NOT_OPEN_COMPILABLE) ? r :
                    cg_fnap(x, V_resultreg(rsort), valneeded);
case s_cond:
            {   LabelNumber *l3 = nextlabel();
/* Previous phases of the compiler must have arranged that the two arms  */
/* of the condition each have the same mode. In particular they must     */
/* either be both integer or both floating point values. This has to     */
/* include the possibility of them being voided. Structure values are    */
/* only legal here if the conditional expression as a whole is voided.   */
                r = cg_cond(x, valneeded, reserveregister(rsort), l3, 0);
                start_new_basic_block(l3);
                return getreservedreg(r);
            }

case s_cast:
            return cg_cast1(arg1_(x), mclength, mcmode);
case s_addrof:
            return cg_addr(arg1_(x), valneeded);

case s_notequal:
case s_equalequal:          /* (a==b)  -->  ((a==b) ? 1 : 0)             */
case s_greater:             /* and similarly for these others.           */
case s_greaterequal:
case s_less:
case s_lessequal:
            if (!valneeded) return cg_diadvoid(x);

            /* boolnot is unary, but is treated the same */
case s_boolnot:
            if (!valneeded) return cg_exprvoid(arg1_(x));

case s_andand:
case s_oror:
            x = mk_expr3(s_cond, te_int, x, lit_one, lit_zero);
            return cg_expr(x);

case s_comma:
            cg_exprvoid(arg1_(x));
            return cg_expr1(arg2_(x), valneeded);

case s_init:
#ifdef NARROW_FORMALS_REUSE_ARG_BINDER
            if ( (h0_(arg2_(x)) == s_binder && arg2_(x) == arg1_(x)) ||
                 (h0_(arg2_(x)) == s_cast && h0_(arg1_(x)) == s_binder && arg1_(arg2_(x)) == arg1_(x))) {
              TypeExpr *wt = widen_formaltype(bindtype_(exb_(arg1_(x))));
              int32 mcr = mcrepoftype(wt);
              int32 mcr1 = mcrepofexpr(arg2_(x));
              return cg_storein(cg_cast1_(cg_var(GAP, exb_(arg1_(x)), s_content, mcr >> MCR_SORT_SHIFT, mcr & MCR_SIZE_MASK, NO),
                                          mcr1 & MCR_SIZE_MASK, mcr1 >> MCR_SORT_SHIFT, mcr),
                                NULL, arg1_(x), s_assign);
            }
#endif
            op = s_assign;
case s_assign:
            if (mcmode == 3)
            {
                if (valneeded)
                    syserr(syserr_structassign_val);
                else
                {   structure_assign(arg1_(x), arg2_(x), mclength);
                    return GAP;
                }
            }
            goto ass_disp;
case s_displace:
            {   Expr *v = arg1_(x), *x3 = arg2_(x);
                if (valneeded && isintregtype_(rsort) && h0_(x3) == s_plus &&
                    is_same(arg1_(x3),v) && integer_constant(arg2_(x3)))
                {   /* a little optimisation... */
                    int32 n = result2;
                    VRegnum rx = cg_expr(v);
                    VRegnum r1 = fgetregister(ADDRREG);
                    emit(J_ADDK, r1, rx, n);
                    cg_storein(r1, NULL, v, s_assign);
                    bfreeregister(r1);
                    return rx;
                }
            }
ass_disp:
            if (nastiness(arg1_(x)) == ISHARD && nastiness(arg2_(x)) != ISHARD)
              return cg_storein(GAP, arg2_(x), arg1_(x),
                                valneeded ? op : s_assign);
            else
              return cg_storein(cg_expr(arg2_(x)), NULL, arg1_(x),
                                valneeded ? op : s_assign);

case s_content:
case s_content4:
        {   bool volatileorunaligned = isvolatile_expr(x) | (isunaligned_expr(x) << 1);
            if (!valneeded && !(volatileorunaligned & IsVolatile))
                return cg_exprvoid(arg1_(x));
            if (op == s_content4) volatileorunaligned |= BaseIsWordAligned;
            x = arg1_(x);
            verify_integer(x);
            if (memory_access_checks)
            {   Expr *fname =
                     mclength==1 ? sim.readcheck1 :
                     mclength==2 ? sim.readcheck2 :
                                   sim.readcheck4;
                x = mk_expr2(s_fnap, typeofexpr(x), fname, mkArgList1(x));
            }
            r = ensure_regtype(cg_stind(GAP, NULL, x, s_content, NULL, mcmode, mclength,
                                        rsort==ADDRREG, volatileorunaligned),
                               rsort);
            if (!valneeded) bfreeregister(r), r = GAP;
            return r;
        }

case s_monplus:
/* Monadic plus does not have to generate any code                       */
            return cg_expr1(arg1_(x), valneeded);

case s_neg:
            if (!valneeded) return cg_exprvoid(arg1_(x));
            if (isintregtype_(rsort))
                return cg_unary_i(J_NEGR, rsort, arg1_(x));
            r1 = cg_expr(arg1_(x));
            r = fgetregister(rsort);
            emitreg((rsort==FLTREG ? J_NEGFR : J_NEGDR), r, GAP, r1);
            bfreeregister(r1);
            return r;

case s_bitnot:
            if (!valneeded) return cg_exprvoid(arg1_(x));
            verify_integer(x);
            return cg_unary_i(J_NOTR, rsort, arg1_(x));

case s_times:
        if (!valneeded) return cg_diadvoid(x);
        else if (!isintregtype_(rsort)) {
            if (is_fpzero(arg1_(x))) return cg_loadfpzero(rsort, arg2_(x));
            if (is_fpzero(arg2_(x))) return cg_loadfpzero(rsort, arg1_(x));
            return(cg_binary(rsort==FLTREG ? J_MULFR : J_MULDR,
                             arg1_(x), arg2_(x), 1, rsort));
        }
        {   int32 p;
            if ((p = ispoweroftwo(arg2_(x))) != 0)
                /* change to SIGNED shift if mcmode=0 and overflow checked */
                return cg_binary(J_SHLR+J_UNSIGNED, arg1_(x),
                                 mkintconst(te_int,p,0), 0, rsort);
            if ((p = ispoweroftwo(arg1_(x))) != 0)
                /* change to SIGNED shift if mcmode=0 and overflow checked */
                return cg_binary(J_SHLR+J_UNSIGNED, arg2_(x),
                                 mkintconst(te_int,p,0), 0, rsort);
            return cg_multiply(type_(x), arg1_(x), arg2_(x));
        }

case s_plus:
        if (!valneeded) return cg_diadvoid(x);
            /* Code that used to be here to turn a+-b into a-b etc now    */
            /* resides in simplify.c (where it also gets argument of      */
            /* s_content                                                  */
        return(cg_binary(isintregtype_(rsort) ? J_ADDR :
                         rsort==FLTREG ? J_ADDFR : J_ADDDR,
                         arg1_(x), arg2_(x), 1, rsort));

case s_minus:
        if (!valneeded) return cg_diadvoid(x);
        return(cg_binary(isintregtype_(rsort) ? J_SUBR :
                         rsort==FLTREG ? J_SUBFR : J_SUBDR,
                         arg1_(x), arg2_(x), 0, rsort));

case s_div:
/* Even if voiding this I calculate it in case there is a division error */
/* that ought to be reported.                                            */
/* But I arrange that the numerator is voided in this odd case, since    */
/* that can save me some effort.                                         */
        if (!valneeded)
        {   cg_exprvoid(arg1_(x));
            x = mk_expr2(s_div, type_(x), lit_one, arg2_(x));
        }
        if (!isintregtype_(rsort))
/* @@@ AM: tests like the following can probably be hit with a feature  */
/* bit within the JOPCODE property table when AM re-arranges them.      */
#ifdef TARGET_LACKS_FP_DIVIDE
/* N.B. in this version I make (p/q) turn into divide(q,p) since that    */
/* seems to make register usage behave better (see cg_binary_or_fn)      */
            r = cg_expr(mk_expr2(s_fnap, type_(x),
                        rsort==FLTREG ? sim.fdiv : sim.ddiv,
                        mkArgList2(arg2_(x), arg1_(x))));
#else
            r = cg_binary(rsort==FLTREG ? J_DIVFR : J_DIVDR,
                             arg1_(x), arg2_(x), 0, rsort);
#endif
/* can't the unsignedness property get in rsort? */
        else if (mcmode==1)
        {   int32 p;
            r = ((p = ispoweroftwo(arg2_(x))) != 0) ?
                cg_binary(J_SHRR+J_UNSIGNED, arg1_(x),
                          mkintconst(te_int,p,0), 0, rsort) :
                cg_divrem(J_DIVR+J_UNSIGNED, type_(x), sim.udivfn,
                          arg1_(x), arg2_(x));
        }
        else
        {
#if !defined(TARGET_HAS_DIVIDE) && !defined(TARGET_HAS_NONFORTRAN_DIVIDE)
            int32 p;
            if ((p = ispoweroftwo(arg2_(x))) != 0)
            {   /* e.g. (signed)  z/8 == (z>=0 ? z:z+7) >> 3 (even MIN_INT) */
                /* Do not forge such an expression since (a) we cannot      */
                /* re-use VRegs as we do below (this saves a resource AND   */
                /* forces and MOVR first which can often be combined with   */
                /* the zero test) and (b) profile counting is unwanted here.*/
                /* This code may be better as a procedure.                  */
                r = cg_expr(arg1_(x));
#ifdef TARGET_HAS_SCALED_OPS         /* even more cunning trick for n/2 ... */
                if (p == 1)
                    emitshift(J_ADDR, r, r, r, SHIFT_RIGHT | 31);   /* unsigned */
                else
#endif
                {   LabelNumber *l = nextlabel();
                    blkflags_(bottom_block) |= BLKREXPORTED;
                    emit(J_CMPK+Q_GE, GAP, r, 0);
                    emitbranch(J_B+Q_GE, l);
                    emit(J_ADDK, r, r, lowerbits(p));
                    start_new_basic_block(l);
                }
                if (p != 31)
                    emit(J_SHRK+J_SIGNED, r, r, p);
                else
                    emit(J_SHRK+J_UNSIGNED, r, r, p);
            }
            else
#endif
            r = cg_divrem(J_DIVR+J_SIGNED, type_(x), sim.divfn,
                          arg1_(x), arg2_(x));
        }
        if (!valneeded) bfreeregister(r), r = GAP;
        return r;

case s_rem:
        verify_integer(x);
        if (iszero(arg1_(x))) return cg_loadzero(arg2_(x));
        else if (isone(arg2_(x))) return cg_loadzero(arg1_(x));
/* can't the unsignedness property get in rsort? */
        else if (mcmode==1)
        {   int32 p;
            if ((p = ispoweroftwo(arg2_(x))) != 0)
                return cg_binary(J_ANDR, arg1_(x),
                                 mkintconst(te_int,lowerbits(p),0),
                                 0, rsort);
#ifdef TARGET_LACKS_REMAINDER
            return simulate_remainder(type_(x), arg1_(x), arg2_(x));
#else
            return(cg_divrem(J_REMR+J_UNSIGNED, type_(x), sim.uremfn,
                             arg1_(x), arg2_(x)));
#endif
        }
        else
        {
#if !defined(TARGET_HAS_DIVIDE) && !defined(TARGET_HAS_NONFORTRAN_DIVIDE)
            int32 p;
            if ((p = ispoweroftwo(arg2_(x))) != 0)
            {   /* see above code and comments for s_div too                */
                /* e.g. (signed)  z%8 == (z>=0 ? z&7 : -((-z)&7))           */
                VRegnum r = cg_expr(arg1_(x));
                LabelNumber *l = nextlabel(), *m = nextlabel();
                blkflags_(bottom_block) |= BLKREXPORTED;
                emit(J_CMPK+Q_GE, GAP, r, 0);
                emitbranch(J_B+Q_GE, l);
                if (p != 1) /* marginally better code for % 2 */
                    emitreg(J_NEGR, r, GAP, r);
                emit(J_ANDK, r, r, lowerbits(p));
                emitreg(J_NEGR, r, GAP, r);
                emitbranch(J_B+Q_AL, m);
                start_new_basic_block(l);
                emit(J_ANDK, r, r, lowerbits(p));
                start_new_basic_block(m);
                return r;
            }
#endif
            if (isminusone(arg2_(x)))
                return cg_loadzero(arg1_(x));   /* required by s_div defn */
#ifdef TARGET_LACKS_REMAINDER
            return simulate_remainder(type_(x), arg1_(x), arg2_(x));
#else
            return(cg_divrem(J_REMR+J_SIGNED, type_(x), sim.remfn,
                             arg1_(x), arg2_(x)));
#endif
        }

case s_leftshift:
        if (!valneeded) return cg_diadvoid(x);
        verify_integer(x);
        if (iszero(arg2_(x))) return(cg_expr(arg1_(x)));
        else if (iszero(arg1_(x))) return cg_loadzero(arg2_(x));
        else return(cg_binary(mcmode==1 ? J_SHLR+J_UNSIGNED : J_SHLR+J_SIGNED,
                              arg1_(x), arg2_(x), 0, rsort));

case s_rightshift:
        if (!valneeded) return cg_diadvoid(x);
        verify_integer(x);
        if (iszero(arg2_(x))) return(cg_expr(arg1_(x)));
        else if (iszero(arg1_(x))) return cg_loadzero(arg2_(x));
#ifdef TARGET_LACKS_RIGHTSHIFT   /* vax, clipper */
        else if (!integer_constant(arg2_(x)))
        {   Expr *a2 = arg2_(x);
/* The difference between signed and unsigned left shifts shows here */
            return cg_binary(mcmode==1 ? J_SHLR+J_UNSIGNED : J_SHLR+J_SIGNED,
                             arg1_(x), mk_expr1(s_neg, typeofexpr(a2), a2),
                             0, rsort);
        }
#endif /* TARGET_LACKS_RIGHTSHIFT */
/* Note that for right shifts I need to generate different code for      */
/* signed and unsigned operations.                                       */
        else return cg_binary(mcmode==1 ? J_SHRR+J_UNSIGNED : J_SHRR+J_SIGNED,
                              arg1_(x), arg2_(x), 0, rsort);

case s_and:
        if (!valneeded) return cg_diadvoid(x);
        verify_integer(x);
        return cg_binary(J_ANDR, arg1_(x), arg2_(x), 1, rsort);

case s_or:
        if (!valneeded) return cg_diadvoid(x);
        verify_integer(x);
        return(cg_binary(J_ORRR, arg1_(x), arg2_(x), 1, rsort));

case s_xor:
        if (!valneeded) return cg_diadvoid(x);
        verify_integer(x);
        return(cg_binary(J_EORR, arg1_(x), arg2_(x), 1, rsort));

default:
        syserr(syserr_cg_expr, (long)op, op);
        return GAP;
    }
}

/* things for swapping (virtual-) register contexts ...                    */

static SynBindList *bindlist_for_temps(RegList *regstosave,
                                       RegList *fpregstosave)
{   RegList *p1;
    SynBindList *things_to_bind = NULL;
/* CPLUSPLUS: note that we cannot handle anything in things_to_bind     */
/* which has a destructor.                                              */
    for (p1=regstosave; p1!=NULL; p1 = p1->rlcdr)
    {   Binder *bb = gentempvar(te_int, GAP);
        things_to_bind = mkSynBindList(things_to_bind, bb);
    }
    for (p1=fpregstosave; p1!=NULL; p1 = p1->rlcdr)
    {   RegSort tt = vregsort(p1->rlcar);
        Binder *bb = gentempvar(tt==FLTREG ? te_float : te_double, GAP);
        things_to_bind = mkSynBindList(things_to_bind, bb);
    }
    return (SynBindList *)dreverse((List *)things_to_bind);
}

static void stash_temps(RegList *regstosave, RegList *fpregstosave,
                        SynBindList *p2, J_OPCODE j_i, J_OPCODE j_f,
                        J_OPCODE j_d)
{   RegList *p1;
    for (p1=regstosave; p1!=NULL; p1 = p1->rlcdr)
    {   emitbinder(j_i, p1->rlcar, p2->bindlistcar);
        p2 = p2->bindlistcdr;
    }
    for (p1=fpregstosave; p1!=NULL; p1 = p1->rlcdr)
    {   VRegnum r = p1->rlcar;
        emitbinder((vregsort(r)==FLTREG ? j_f : j_d),
                   r, p2->bindlistcar);
        p2 = p2->bindlistcdr;
    }
}

static RegList *rl_discard(RegList *x)
{   return (RegList *)discard2((List *)x);
}

#define toplevel_alignment(b) \
  ((bindstg_(b) & bitofstg_(s_auto)) ? alignof_toplevel_auto :\
                                       alignof_toplevel_static)

#define expr_alignment(e) \
  ((h0_(e) == s_binder) ? toplevel_alignment((Binder *)e) : 1)

#define AddUsedReg(r) (usedregs = mkRegList(usedregs, (r)), ++nusedregs)

/* The effect of calling flush_arg_usedregs is to set usedregs to 0     */
/* and either dispose of its pointed to list or to pass it on to        */
/* someone else who will.   @@@ REVIEW?                                 */
static void flush_arg_usedregs(int32 argaddr)
{   /* 'argaddr' is the stack offset (counting arg1 as 0) of where      */
    /* the first register (if any) in usedregs is to go.                */
    argaddr += alignof_toplevel_auto * length((List *)usedregs);
    for (usedregs = (RegList *)dreverse((List *)usedregs);
             usedregs != NULL;
             usedregs = rl_discard(usedregs))
    {   VRegnum r = usedregs->rlcar;
        if (!((unsigned32)((r)-R_A1) < (unsigned32)NARGREGS))
            syserr(syserr_bad_reg, (long)r);
/* @@@ perhaps J_PUSHR should mean "push alignof_toplevel size binder.  */
        emit(J_PUSHR, r, GAP, argaddr -= alignof_toplevel_auto);
        active_binders = mkBindList(active_binders, integer_binder);
        current_stackdepth += alignof_toplevel_auto;
    }
    if (usedfpregs!=NULL) syserr(syserr_bad_fp_reg);
    nusedregs = nusedfpregs = 0;
}

static void flush_fparg(VRegnum r, int32 rep, int32 argaddr)
{   if (rep == MCR_SORT_FLOATING + 4)
    {   if (alignof_toplevel_auto==8) syserr("ALPHA flt arg confusion");
        /* currently float args are widened to doubles.                 */
        emit(J_PUSHF, r, GAP, argaddr);
        active_binders = mkBindList(active_binders, integer_binder);
    }
    else
    {   emit(J_PUSHD, r, GAP, argaddr);
        active_binders = mkBindList(active_binders, integer_binder);
        if (alignof_toplevel_auto != 8)
            active_binders = mkBindList(active_binders, integer_binder);
    }
    current_stackdepth = padtomcrep(current_stackdepth, rep) +
                          padsize(rep & MCR_SIZE_MASK, alignof_toplevel_auto);
}

/* ECN: Handle case where R_IP is defined to be an arg register */
#if R_IP < NARGREGS
#if R_IP != NARGREGS-1
#error "Can't handle this definition of R_IP"
#else
#define NARGREGS1 3
#endif
#else
#define NARGREGS1 (NARGREGS==0 ? 1 : NARGREGS)
#endif

#ifdef TARGET_HAS_RISING_STACK
#  define FlushPrevArgRegs(arg, n) flush_arg_usedregs((arg)[(n)-1].addr);
#else
#  define FlushPrevArgRegs(arg, n) flush_arg_usedregs((arg)[(n)+1].addr);
#endif

/* The following typedef is local to cg_fnargs() and cg_fnap() */
typedef struct ArgInfo {
    Expr *expr;
    int info;       /* nastiness(expr) */
    uint8 regoff,   /* offset of first argument register from R_A1 */
          nreg;     /* number of integer argument registers */
    int32 rep,      /* mcrepof(expr) */
          addr;     /* stack offset from base of argument list */
} ArgInfo;

static void cg_fnargs_stack(ArgInfo arg[], int32 regargs, int32 n, bool firstsplit)
/* Evaluate arguments described by arg[regargs] up to arg[n-1] and place */
/* them on the stack. If TARGET_HAS_RISING_STACK, the order is ascending */
/* and a gap is left for those passed in registers. Otherwise, the order */
/* is descending.                                                        */
/* However, ensure the stack is always correctly aligned if necessary.   */

/* The arguments handled by this function are not necessarily intended   */
/* to be passed on the stack - they (or some part of them) may be popped */
/* into integer registers before the call.                               */
/* This behaviour is BROKEN if STACK_MOVES_ONCE.                         */
{   int32 narg;
    int32 nargregs1 = NARGREGS1;
    int32 stackargs = firstsplit ? regargs-1 : regargs;
#ifdef TARGET_IS_ARM_OR_THUMB
/* this really means "TARGET_IMPLEMENTS_UnalignedLoadMayUse" */
    bool unaligned_arg = NO;
    for (narg = stackargs; narg != n; narg++)
        if (ContainsUnalignedSubExpr(arg[narg].expr)) {
            unaligned_arg = YES;
            break;
        }
    if (unaligned_arg)
      for (; ; nargregs1--)
        if (!UnalignedLoadMayUse(R_A1+nargregs1-1))
          break;
#endif
#ifdef TARGET_HAS_RISING_STACK
    for (narg = stackargs; narg != n; narg++ )
    {   int32 rep = arg[narg].rep;
#else
    for (narg = n; narg != stackargs; )
    {   int32 rep = arg[--narg].rep;
#if (alignof_double > alignof_toplevel_auto)
/* pad beyond last int arg --- hmm think */
        if (arg[narg].addr + padsize(rep & MCR_SIZE_MASK, alignof_toplevel_auto) !=
              arg[narg+1].addr)
        {   BindList *nb = active_binders;
            /* @@@ note that the next line of code assumes that         */
            /* (alignof_double/alignof_int) == 1 or 2.                  */
            nb = mkBindList(nb, integer_binder);
            current_stackdepth += alignof_toplevel_auto;
            emitsetsp(J_SETSPENV, nb);
        }
#endif
#endif /* TARGET_HAS_RISING_STACK */
/* Major fun is called for here in case an actual argument is something  */
/* other than a 32-bit integer-like quantity.                            */
        switch (rep & MCR_SORT_MASK)
        {
        default:
          syserr(syserr_cg_fnarg, (long)rep);
          break;
        case MCR_SORT_SIGNED:
        case MCR_SORT_UNSIGNED:
/* Maybe the next use of 'nusedregs' is nasty.                           */
          if (nusedregs == nargregs1 || arg[narg].info == ISHARD)
              /* The following line avoids silly (n**2) code on fn call. */
              FlushPrevArgRegs(arg, narg);

          {   Expr *a = arg[narg].expr;
#ifdef TARGET_HAS_RISING_STACK
              VRegnum argr = R_A1 + nusedregs;
#else
              VRegnum argr = R_A1 + nargregs1-1 - nusedregs;
#endif
              (void)cg_exprreg(a, argr);
              AddUsedReg(argr);
          }
          break;
        case MCR_SORT_FLOATING:
          FlushPrevArgRegs(arg, narg);
          if (!firstsplit || narg != stackargs)
          {   VRegnum r = cg_expr(arg[narg].expr);
              int32 argaddr = arg[narg].addr;
              flush_fparg(r, rep, argaddr);
              bfreeregister(r);
              break;
          }
          /* Otherwise (fp argument split between stack and registers)   */
          /* fall through to handle as though struct. The argument is    */
          /* guaranteed by cg_fnargs() to be store-like.                 */
        case MCR_SORT_STRUCT:
          /* There used to be a check here that the size of the struct   */
          /* is a multiple of align_of_struct. It's been retired as      */
          /* inadequate (alignof_struct may be less than sizeof_int);    */
          /* moreover, we need to handle packed structs                  */
          /* The code guarded by !defined(TARGET_HAS_BLOCKMOVE) below    */
          /* must take care not to try to handle cases which aren't      */
          /* adequately aligned.                                         */
          if (nusedregs == nargregs1 || arg[narg].info == ISHARD
                                     || MEMCPYREG == DBLREG)
              FlushPrevArgRegs(arg, narg);
          { int32 start = 0,
                  structsize = rep & MCR_SIZE_MASK;
            if (firstsplit && narg == stackargs)
                start = arg[narg].nreg * alignof_toplevel_auto;
/*
 * We now pretend that the ARM has a BLOCKMOVE instruction because that
 * makes it possible for gen.c to expand blockmoves into sequences of
 * loads or stores, or maybe procedure calls, exploiting knowledge of
 * how many registers are free.
 */
/* ECN: Thumb does not support blockmove for the following as is does not
 *      have a proper set of LDMIA/STMIA instructions for use with SP.
 *      Also, its peepholer does not yet support J_PUSHC.
 */
#if !defined(TARGET_HAS_BLOCKMOVE) || defined(TARGET_IS_THUMB)
/* The following code needs to know struct alignment as well as size:    */
            if (alignoftype(typeofexpr(arg[narg].expr)) >= MEMCPYQUANTUM
                && structsize < 5*MEMCPYQUANTUM)
/* The case of a (small) structure argument (now guaranteed by simplify  */
/* not to involve a function call) can be compiled using a sequence of   */
/* PUSH (or PUSHD) operations.                                           */
/* We expect that to be cheaper than the synthetic assignment used in    */
/* the more general case below.                                          */
/* This special case code is inhibited if size is not a multiple of 4.   */
            {   Expr *e = take_address(arg[narg].expr);
                Binder *b = is_local_adcon(e);
                VRegnum r = GAP;
                if (b == NULL)
                {   r = cg_expr(e);
/* Hmm: I have to do a bfreeregister on r before any flush_arg_usedregs() */
/* This is not dangerous as flow analysis will regard r as alive up to    */
/* the last member.                                                       */
                    bfreeregister(r);
                }
#ifdef TARGET_HAS_RISING_STACK
                structsize = start;
                while (structsize != (rep & MCR_SIZE_MASK))
#else
                while (structsize != start)
#endif
                {   VRegnum argr;
                    if (nusedregs == nargregs1)
                        flush_arg_usedregs(arg[narg].addr + structsize);
#ifdef TARGET_HAS_RISING_STACK
                    argr = R_A1 + nusedregs;
#else
                    argr = MEMCPYREG==DBLREG ? R_FA1
                                             : R_A1 + nargregs1-1 - nusedregs;
                    structsize -= MEMCPYQUANTUM;
#endif
                    if (b != NULL)
                        emitvk(J_memcpy(J_LDRVK|J_ALIGN4), argr, structsize, b);
                    else
                        emit(J_memcpy(J_LDRK|J_ALIGN4), argr, r, structsize);
#ifdef TARGET_HAS_RISING_STACK
                    structsize += MEMCPYQUANTUM;
#endif
                    if (MEMCPYREG==DBLREG)
                        flush_fparg(argr, MCR_SORT_FLOATING+sizeof_double,
                                    arg[narg].addr+structsize);
                    else
                        AddUsedReg(argr);
                }
/* The bfreeregister(r) above notionally belongs here.                   */
            }
            else
#endif
/* The general case of an argument that can involve a function call      */
/* returning a structure is dealt with here... (Oct 92: fn can't happen) */
            {
              FlushPrevArgRegs(arg, narg);
              { TypeExpr *t;
#ifdef NEVER
/* The following preferable code is beaten by cg_fnargs.                */
/*  (in the case when a struct spans the reg/memory boundary.).         */
                Binder *gen = gentempbinder(t);
                bindstg_(gen) |= b_spilt;
/* Forge an address-taken struct variable to fit on the stack in the    */
/* usual position for the actual parameter.                             */
                cg_bindlist(mkSynBindList(0, gen), 0);
#else /* ALWAYS */
/* We add a number of integer binders to the stack, whose total size is */
/* the same as that of the argument object. But we assign to a          */
/* temporary binder of the correct type (not added to the stack). The   */
/* address of this binder is made correct by forging its bindbl_()      */
/* field to be the same as if it had been added to the stack rather     */
/* than the integers. b_unbound in bindstg_() is used to mark precisely */
/* this disgusting situation, so that later dataflow analysis has some  */
/* chance.                                                              */
                Binder *gen;
                BindList *nb = active_binders;
                int32 i, size = padsize(structsize-start, alignof_toplevel_auto);
                current_stackdepth += size;
                for (i = size; i != 0; i -= alignof_toplevel_auto)
                    nb = mkBindList(nb, integer_binder);
                t = (start == 0) ? typeofexpr(arg[narg].expr)
                                 : mk_typeexpr1(t_subscript, te_char,
                                                mkintconst(te_int, size, 0));
                gen = gentempvar(t, GAP);
                if (target_stack_moves_once) {
                    bindstg_(gen) |= b_spilt|b_unbound;
/* BEWARE: the next line is in flux (Nov89) and is only OK because      */
/* 'gen' never gets to be part of 'active_binders'.                     */
                    bindaddr_(gen) = (arg[narg].addr + start) | BINDADDR_NEWARG;
                } else {
                    bindstg_(gen) |= b_spilt|b_bindaddrlist|b_unbound;
                    bindbl_(gen) = nb;
                }
                emitsetsp(J_SETSPENV, nb);
#endif
                if (start == 0)
                    structure_assign((Expr *)gen, arg[narg].expr, structsize);
                else
                {   Expr *e = mk_expr2(s_plus, ptrtotype_(te_int),
                                               take_address(arg[narg].expr),
                                               mkintconst(te_int, start, 0));
                    e = mk_expr2(s_fnap, te_void, sim.memcpyfn,
                            mkArgList3(take_address((Expr *)gen), e,
                                       mkintconst(te_int,size,0)));
                    cg_exprvoid(e);
                }
                if (usedregs != 0) syserr(syserr_fnarg_struct);
              }
            }
          }
          break;
        }                 /* end of switch */
#if defined(TARGET_HAS_RISING_STACK) && (alignof_double > alignof_toplevel_auto)
        if (arg[narg].addr + padsize(rep & MCR_SIZE_MASK, alignof_toplevel_auto) !=
              arg[narg+1].addr)
        {   BindList *nb = active_binders;
            /* @@@ note that the next line of code assumes that         */
            /* (alignof_double/alignof_int) == 1 or 2.                  */
            nb = mkBindList(nb, integer_binder);
            current_stackdepth += alignof_toplevel_auto;
            emitsetsp(J_SETSPENV, nb);
        }
#endif
    }                     /* end of for */
    flush_arg_usedregs(arg[regargs].addr);
}

/* ECN: If R_IP < NARGREGS below we must assign the R_IP register to a virtual
 * register, return this, and perform the assignment to R_IP after we have
 * calculated the function address (in the case of a fn pointer) as calculating
 * this address may in itself use R_IP
 */
/* HCM: On reflection, it appears always to be at least no worse to    */
/* evaluate all arguments to virtual registers, then to move them to   */
/* the correct argument registers (rather than having a number of      */
/* (evaluate to virtual register; move to argument register) pairs.    */
#define ArgDeferred(r, fn) ((r) < R_FA1)

#if 0
#ifdef TARGET_IS_ARM_OR_THUMB
/* this really means "TARGET_IMPLEMENTS_UnalignedLoadMayUse" */
#  define ArgDeferred(r, fn) \
    ((isunaligned_expr(fn) && UnalignedLoadMayUse(r)) ||\
     (R_A1 <= R_IP && R_IP < R_A1+NARGREGS && r == R_IP))
#else
#    define ArgDeferred(r, fn) 0
#endif
#endif

/* Structure representing the value of a register argument which has   */
/* not been fully evaluated by cg_fnargs_regs(): either it has been    */
/* evaluated into a virtual register, not into the physical argument   */
/* register (r != GAP), or it has not been evaluated at all (e != NULL)*/
/* : constants only!.                                                  */
/* Only one of r and e may be set, of course.                          */
typedef struct {
  VRegnum r;
  Expr *e;
} DeferredArg;

typedef struct {
  int32 resultregs;
  VRegnum specialarg;
  Expr *fn;
  uint32 resultrep;
  uint16 auxflags;
  /* out ... (of cg_fnargs) */
  VRegnum fnreg;
  SynBindList *fnsave;
  DeferredArg deferred[NINTREGS-R_A1];
} FnargStruct;

static void cg_fnargs_regs(ArgInfo arg[], int32 intregargs, int32 fltregargs,
                           FnargStruct *argstruct, int splitarg)
/* Finally do the first NARGREGS (or less) 'int' args to registers:    */
/* Do the hardest first to avoid moving easier things around.          */
/* Also, save and restore explicitly all function results except the   */
/* last to avoid recursive cg_fnap making a quadratic mess of          */
/* f() { g(a(),b(),c(),...); }                                         */
/* Oct 92: this code has been extended so that 'intregargs' can also   */
/* include struct/fp regs, which are loaded directly (instead of       */
/* going through cg_fnargs_stack() and J_POP).  Hence (addressable)    */
/* float values can be loaded to int regs directly.    ***SOON***      */
/* The code behaves as before unless cg_fnargs() takes the opportunity */
/* to increase 'intregargs' from before.                               */
{   BindList *save_binders = active_binders;
    int32 d = current_stackdepth;
    int32 regargs = intregargs+fltregargs;
/* the +1 in the next lines is for the possible hidden argument.       */
    VRegnum argregs[NANYARGREGS+1];        /* arg virt regs   */
    SynBindList *argsaves[NANYARGREGS+1];  /* for previous fn call results */
    int hardness;
    int32 firsthard = -1;
    {   int32 i;
        for (i = NARGREGS; --i >= 0;) {
            argstruct->deferred[i].r = GAP;
            argstruct->deferred[i].e = NULL;
        }
        for (i = regargs; --i >= 0; )
        {   if (arg[i].info == ISHARD) firsthard = i;
            argsaves[i] = (SynBindList *) DUFF_ADDR, argregs[i] = GAP;
        }
    }
    for (hardness = ISHARD; hardness >= ISCONST; hardness--)
    {   int32 i;
#ifdef TARGET_FP_ARGS_IN_FP_REGS
#define callregsort(n, f) \
  ((n)<(f) ? ((arg[n].rep & MCR_SIZE_MASK)==sizeof_float ? FLTREG : DBLREG)\
           : INTREG)
#define callreg(n, f) ((n)<(f) ? R_FA1+(n) : \
                        argstruct->specialarg != GAP && (n)==(f) ? argstruct->specialarg : \
                        R_A1+arg[n].regoff)
#else
#define callregsort(n, f) INTREG
#define callreg(n, f) (R_A1+arg[n].regoff)
#endif
        for (i = regargs; --i >= 0; )
            if (arg[i].info == hardness)
            {   Expr *a = arg[i].expr;
                int32 repsort = arg[i].rep & MCR_SORT_MASK;
                if (hardness == ISHARD && i != firsthard
                    && argstruct->fnreg != GAP && argstruct->fnsave == NULL)
                {   SynBindList *b = bindlist_for_temps(usedregs, usedfpregs);
                    /* b should have at most 1 elt */
                    cg_bindlist(b, 1);
                    if (b->bindlistcdr != NULL)
                        syserr(syserr_cg_fnarg1);
                    emitbinder(J_STRV|J_ALIGN4V, argstruct->fnreg, b->bindlistcar);
                    usedregs = 0; nusedregs = 0;
                    usedfpregs = 0; nusedfpregs = 0;
                    argstruct->fnsave = b;
                }
                if (hardness == ISCONST) {
                    VRegnum argr = callreg(i, fltregargs);
                    if (ArgDeferred(argr, argstruct->fn))
                      argstruct->deferred[argr - R_A1].e = a;
                    else
                      (void)cg_exprreg(a, argr);
                }
                else if (i == splitarg
                         || (repsort == MCR_SORT_STRUCT
                             && (alignoftype(typeofexpr(a)) >= MEMCPYQUANTUM
                                 || expr_alignment(a) >= MEMCPYQUANTUM)))
                {   if (h0_(a) != s_fnap && h0_(a) != s_let)
                        argregs[i] = cg_expr(take_address(a));
                    else {
                        TypeExpr *t = typeofexpr(a);
                        Binder *gen = gentempbinder(t);
                        Expr *fnap = NULL;
                        if (h0_(a) == s_fnap)
                          fnap = a;
                        else if (h0_(arg2_(a)) == s_fnap)
                          fnap = arg2_(a);
                        if (fnap == NULL || !returnsstructinregs(arg1_(fnap)))
                            bindstg_(gen) |= b_spilt;
/* Forge an address-taken struct variable to fit on the stack in the    */
/* usual position for the actual parameter.                             */
                        cg_bindlist(mkSynBindList(0, gen), 0);
                        cg_exprvoid(mk_expr2(s_assign, t, (Expr*)gen, a));
                        arg[i].expr = (Expr *)gen;
                        arg[i].info = ISBIND;
                    }
                }
                else /* (we'll get a syserr for structs) */
                    argregs[i] = cg_expr(a);

                if (hardness == ISHARD)
                {   SynBindList *b = i == firsthard ? 0 : /* first is easy */
                                  bindlist_for_temps(usedregs, usedfpregs);
                    /* b should have at most 1 elt */
                    cg_bindlist(b, 1);
                    if (b != 0)
                    {   J_OPCODE j_saveop =
                              (repsort == MCR_SORT_STRUCT) ? J_STRV|J_ALIGN4V :
                   (callregsort(i, fltregargs) == FLTREG)  ? J_STRFV|J_ALIGN4V :
                   (callregsort(i, fltregargs) == DBLREG ||
                             repsort == MCR_SORT_FLOATING) ? J_STRDV|J_ALIGN8 :
                                                             J_STRV|J_ALIGN4V;
                        if (b->bindlistcdr != NULL)
                            syserr(syserr_cg_fnarg1);
                        emitbinder(j_saveop, argregs[i], b->bindlistcar);
                        usedregs = 0; nusedregs = 0;
                        usedfpregs = 0; nusedfpregs = 0;
                    }
                    argsaves[i] = b;
                }
            }
    }
    {   int32 i;
        for (i = 0; i < regargs; i++)
        {   SynBindList *b;
            bool done = arg[i].info == ISCONST; /* we did these above.  */
            int32 repsort = arg[i].rep & MCR_SORT_MASK;
            VRegnum realargr = callreg(i, fltregargs);
            VRegnum argr = realargr;
            if (!done && ArgDeferred(argr, argstruct->fn)) {
                VRegnum ar = argregs[i];
                if (isany_realreg_(ar) || ar == GAP || vregsort(ar) != INTREG)
                    ar = vregister(INTREG);
                argr = argstruct->deferred[argr - R_A1].r = ar;
            }
            if (repsort == MCR_SORT_STRUCT) {
                int32 j, limit = arg[i].nreg;
                for (j = 0; j<limit; j++)
                    if (ArgDeferred(realargr+j, argstruct->fn))
                        argstruct->deferred[realargr + j - R_A1].r = vregister(INTREG);
            }
/* @@@ This can be usedfpregs?    Yes, fix!!!                           */
/* Unclear the nusedregs/fregs do anything at all here.                 */
            AddUsedReg(argr);
            if (arg[i].info == ISHARD && (b = argsaves[i]) != 0)
            {   if (b->bindlistcdr != NULL)
                    syserr(syserr_cg_fnarg1);
/* Logically, the following code just reloads argregs[i], but we        */
/* try to reload from spill directly to arg regs: OK for int->intreg    */
/* dble->dblereg, but dble/struct->intreg needs careful code...         */
/* The order of tests below follows that in the (!done) case.           */
                if (repsort == MCR_SORT_STRUCT)
                    emitbinder(J_LDRV|J_ALIGN4V, argregs[i], b->bindlistcar);
                else if (callregsort(i, fltregargs) == FLTREG)
                    emitbinder(J_LDRFV|J_ALIGN4V, argr, b->bindlistcar),
                    done = 1;
                else if (callregsort(i, fltregargs) == DBLREG)
                    emitbinder(J_LDRDV|J_ALIGN8, argr, b->bindlistcar),
                    done = 1;
                else if (repsort == MCR_SORT_FLOATING)
                    emitbinder(J_LDRDV|J_ALIGN8, argregs[i], b->bindlistcar);
                else
                {   emitbinder(J_LDRV|J_ALIGN4V, argr, b->bindlistcar);
                    done = 1;
                }
                (void)freeSynBindList(b);
            }
            if (!done && argregs[i] != GAP
                && (argregs[i] != argr || repsort > MCR_SORT_UNSIGNED))
            {   /* argregs[i] will be GAP when the actual argument is  */
                /* a call to an inlined function returning a structure */
                /* result in registers                                 */
                VRegnum r = argregs[i];
                if (repsort == MCR_SORT_STRUCT || i == splitarg)
                {   int32 j, limit = arg[i].nreg;
/* The usedregs/nusedregs code needs a better interface!               */
                    int32 load = isunaligned_type(typeofexpr(arg[i].expr)) ?
                                   J_LDRK|J_ALIGN1 :
                                   J_LDRK|J_ALIGN4;
                    usedregs = usedregs->rlcdr; nusedregs--;
                    for (j = 0; j<limit; j++)
                    {
                        VRegnum thisr = realargr + j;
                        if (ArgDeferred(thisr, argstruct->fn))
                            thisr = argstruct->deferred[thisr - R_A1].r;
                        AddUsedReg(thisr);
                        emit(load, thisr, r, 4*j);
                    }
                }
                else if (callregsort(i, fltregargs) == FLTREG)
                    emitreg(J_MOVFR, argr, GAP, r);
                else if (callregsort(i, fltregargs) == DBLREG)
                    emitreg(J_MOVDR, argr, GAP, r);
#ifdef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
                else if (repsort == MCR_SORT_FLOATING)   /* [am] */
                    emitreg(vregsort(r) == DBLREG ? J_MOVDR : J_MOVFR,
                            argr, GAP, r);
#else
                else if (arg[i].rep == MCR_SORT_FLOATING + sizeof_float)
                    emitreg(J_MOVFIR, argr, GAP, r);
                else if (repsort == MCR_SORT_FLOATING)   /* [am] */
                {   VRegnum argr2 = realargr+1;
                    /* We can't defer the loads of the real argunent    */
                    /* registers here (for ARM), because the expansion  */
                    /* of MOVDIR requires r2 > r1, and we have no way   */
                    /* to constrain the result of register allocation.  */
                    argstruct->deferred[realargr - R_A1].r = GAP;
                    argstruct->deferred[argr2 - R_A1].r = GAP;
                    AddUsedReg(argr2);
                    emitreg(J_MOVDIR, realargr, argr2, r);
                }
#endif
                else
                    emitreg(J_MOVR, argr, GAP, r);
                bfreeregister(r);
            }
        }
        if (argstruct->fnsave != NULL) {
            argstruct->fnreg = fgetregister(ADDRREG);
            emitbinder(J_LDRV|J_ALIGN4V, argstruct->fnreg, argstruct->fnsave->bindlistcar);
        }
        emitsetsp(J_SETSPENV, save_binders);
        current_stackdepth = d;
    }
}

#define intregable(rep, e) \
     (((rep) & MCR_SORT_MASK) != MCR_SORT_STRUCT \
      || alignoftype(typeofexpr(e)) >= alignof_int \
      || expr_alignment(e) >= alignof_int)

static int32 cg_fnargs(ExprList *a, ArgInfo arg[], int32 n,
                       FnargStruct *argstruct)
/* specialarg is non-GAP if there is an implicit extra (first,integer)  */
/* arg (e.g. for swi_indirect or 88000 struct return value pointer).    */
{
    int32 intargwords, intregargs = 0, intregwords = 0, fltregargs = 0;
    int32 splitarg = -1;
#ifdef TARGET_HAS_RISING_STACK
    Binder *arg0;
#endif
    {   int32 argoff = 0, narg = 0;
        SynBindList *newtemps = NULL;
        Expr *tempinits = NULL;
#ifdef TARGET_FP_ARGS_IN_FP_REGS
        if ((config & CONFIG_FPREGARGS) &&
            !(argstruct->auxflags & f_nofpregargs))
        {   ExprList *p, *q = NULL;
/* Reorder the argument list, by destructively extracting the first     */
/* up to NFLTARGREGS float args, and then dropping through to handle    */
/* int args.  This code needs better TARGET parameterisation.           */
/* On the MIPS we only allow LEADING fp args in fp regs.                */
/* Moreover such fp args inhibit the corresponding 2 int reg args!      */
            for (p = a; p != NULL; p = cdr_(p))
            {   Expr *ae = exprcar_(p);
                int32 repsort = mcrepofexpr(ae) >> MCR_SORT_SHIFT;
                if (repsort == 2 && narg < NFLTARGREGS)
                {   arg[narg++].expr = ae;
                    fltregargs++;
                    if (q == NULL)
                        a = cdr_(p);
                    else
                        cdr_(q) = cdr_(p);
                }
                else
                    q = p;
            }
        }
#endif
/* The following code determines in which (int)reg an arg is going to   */
/* be passed.  In general this is the same as determining its address   */
/* (see below '.addr') since register alignment of doubles passed in    */
/* int regs usually matches that of doubles passed in storage.          */
/* It could probably be merged into to the 'argoff' loop.               */
        if (argstruct->specialarg != GAP) intregwords--;
/* intregargs can include specialarg, intregwords never does.           */
        for (; a != NULL; a = cdr_(a), narg++)
        {   Expr *ae = exprcar_(a);
            int32 rep = mcrepofexpr(ae);
#if alignof_double > alignof_int && !defined(TARGET_IS_SPARC) && \
    !defined(TARGET_IS_ALPHA)
            int32 rbase = padsize(intregwords, rep & MCR_ALIGN_DOUBLE ? 2:1L);
#else
            int32 rbase = intregwords;
#endif
            int32 nreg = padsize((rep & MCR_SIZE_MASK), alignof_toplevel_auto)
                         / alignof_toplevel_auto;
            int32 rlimit = rbase + nreg;
            arg[narg].expr = ae;
            arg[narg].nreg = (uint8)nreg;
            if (rbase < NARGREGS)
            {   /* Some of the argument can be passed in registers       */
                bool loadable = intregable(rep, ae);
                if (rlimit > NARGREGS || !loadable)
                {   Binder *gen;
                    Expr *thisinit;
                    if (!target_stack_moves_once)
                        break;
                    /* if !loadable, ae is a struct with alignment <     */
                    /* alignof_int. Any object on the stack has          */
                    /* alignment >= alignof_int Thus, copying to a temp  */
                    /* is sufficient to allow this argument to be        */
                    /* directly loaded into argument registers.          */
                    /* If loadable, the argument is wider than an intreg */
                    /* and is to be passed partly in registers and partly*/
                    /* on the stack.                                     */
                    if (!loadable
                        || (h0_(ae) != s_binder
                            && nastiness(ae) != ISXCONST))
                    {
                        gen = gentempbinder(typeofexpr(ae));
                        newtemps = mkSynBindList(newtemps, gen);
                        thisinit = mk_expr2(s_assign, bindtype_(gen), (Expr *)gen, ae);
                        if (tempinits == NULL)
                            tempinits = thisinit;
                        else
                            tempinits = mk_expr2(s_comma, te_void, thisinit, tempinits);
                        arg[narg].expr = (Expr *)gen;
                    }
                    if (rlimit > NARGREGS)
                    {   arg[narg].nreg = (uint8)(NARGREGS - rbase);
                        splitarg = narg;
                    }
                }
                intregargs++; intregwords = rlimit;
                arg[narg].regoff = (uint8)rbase;
            } else
                break;
        }
        arg[narg].regoff = (uint8)intregwords;   /* useful sentinel below?     */
        for (; a != NULL; a = cdr_(a), narg++)
            arg[narg].expr = exprcar_(a);
        if (narg != n) syserr(syserr_cg_argcount);

        for (narg = 0; narg < n; narg++)
        {   Expr *ae = arg[narg].expr;
            int32 rep = mcrepofexpr(ae);
            if (h0_(ae) == s_binder && bindconst_(exb_(ae)) != NULL)
            {   if (LanguageIsCPlusPlus)
                    syserr("bindconst $b got to cg.c", exb_(ae));
                ae = arg[narg].expr = bindconst_(exb_(ae));
            }
            argoff = padtomcrep(argoff, rep);
            arg[narg].info = nastiness(ae);
            arg[narg].rep = rep;
            arg[narg].addr = argoff;
/* Do not increment 'argoff' for specialarg (hidden argument).          */
            if (!(narg == fltregargs && argstruct->specialarg != GAP))
                argoff += padsize(rep & MCR_SIZE_MASK, alignof_toplevel_auto);
        }
        if (newtemps != NULL) {
            cg_bindlist(newtemps, 0);
            cg_exprvoid(tempinits);
        }

#if !defined(TARGET_HAS_RISING_STACK) && (alignof_double > alignof_toplevel_auto)
/* The next line pads the offset of the last arg exactly in the case    */
/* it will be handled by cg_fnargs_stack.  If all the args are int-like */
/* and go directly to regs (i.e. <NARGREGS) then we do not have to pad  */
/* after the last of an odd number of args.                             */
        if (n != fltregargs+intregargs)
            argoff = padtomcrep(argoff, bindmcrep_(double_pad_binder));
#endif
        arg[narg].addr = argoff;        /* sentinel for cg_fnargs_stack */
        intargwords = (argoff - arg[fltregargs].addr)/alignof_toplevel_auto;
        /* Note that any hidden arg is not counted in intargwords.      */
    }
#if (alignof_double > alignof_toplevel_auto) || defined(TARGET_IS_ALPHA)
    /* Pre-align stack to double alignment -- maybe one day         */
    /* suppress the alignment if there are no double args and the   */
    /* called proc can be seen to be floating-free and leaf-like.   */
    /* Note, by considering "f() { int x; g(0.0, &x); }", that this */
    /* may waste stack space -- i.e.                                */
    /*   [ half of 0.0, half of 0.0, &x, pad, pad, x, f-linkage..]  */
    /* perhaps double_antipad_binder would help.                    */
    {   BindList *nb = active_binders;
        nb = mkBindList(nb, double_pad_binder);
        current_stackdepth = padtomcrep(current_stackdepth,
                                        bindmcrep_(double_pad_binder));
        emitsetsp(J_SETSPENV, nb);
    }
#endif
#ifdef TARGET_HAS_RISING_STACK
    /* Leave gap on stack for those args which are passed in regs, but */
    /* only if some are also (possibly unnecessarily) on the stack.    */
    if (intargwords > intregwords) {
      BindList *nb = active_binders;
      int32 i;
      for (i=0; i<intregargs; i++) {
        current_stackdepth += alignof_toplevel_auto;
        if (i==0) {
          nb = mkBindList(nb, gentempvar(te_int, GAP));
          arg0 = nb->bindlistcar; /* needed later!! */
          bindstg_(arg0) |= b_spilt;
          if (target_stack_moves_once)
          /* BEWARE: the next line is in flux (Nov89) and is only OK because */
          /* 'arg0' never gets to be part of 'active_binders'.               */
              bindaddr_(arg0) = arg[0].addr | BINDADDR_NEWARG;
          else
              bindaddr_(arg0) = (current_stackdepth + arg[0].addr) | BINDADDR_LOC;
        }
        else
            nb = mkBindList(nb, integer_binder);
      }
      emitsetsp(J_SETSPENV, nb);
    }
#endif
    cg_fnargs_stack(arg, intregargs+fltregargs, n, splitarg >= 0);
    if (nastiness(argstruct->fn) == ISHARD)
        argstruct->fnreg = cg_expr(argstruct->fn);
#ifdef TARGET_IS_ARM_OR_THUMB
/* this really means "TARGET_IMPLEMENTS_UnalignedLoadMayUse" */
    else if (ContainsUnalignedSubExpr(argstruct->fn)) {
        int i;
        for (i = 0; i < intregwords; i++)
          if (UnalignedLoadMayUse(R_A1+i)) {
            argstruct->fnreg = cg_expr(argstruct->fn);
            break;
          }
    }
#endif
    cg_fnargs_regs(arg, intregargs, fltregargs, argstruct, splitarg);

#if (alignof_double > alignof_toplevel_auto)
/* The next few lines deal with the trickiness of handling a call like  */
/* f(1,2.3) which, if alignof_double==8 (excepting SPARC) can load      */
/* regs a1, a3, a4.  Keep regalloc happy by undefining a2 explicitly.   */
/* Code above ensures we only pad at end of regs if also stack args.    */
/* Beware: not tested with alignment AND specialarg != GAP.             */
/* @@@ we should probably have done intregargs-- here if specialarg...  */
/* @@@ (or used .regoff since very similar to .addr.)                   */
    {   int32 i = fltregargs + (argstruct->specialarg==GAP ? 0:1), r = 0;
        int32 ibase = arg[i].addr;
        while (intregwords < NARGREGS &&
                 ibase + 4*intregwords < arg[fltregargs+intregargs].addr)
            intregwords++;
        while (r < intregwords && i < fltregargs+intregargs)
          if (ibase + 4*r >= arg[i+1].addr) i++;
          else
          {   if (ibase + 4*r >= arg[i].addr +
                      padsize(arg[i].rep & MCR_SIZE_MASK, alignof_toplevel_auto))
                emitbinder(J_INIT, R_A1 + r, 0);
              r++;
          }
    }
#endif

    if (current_stackdepth > greatest_stackdepth)
        greatest_stackdepth = current_stackdepth;

/* Now if some of the first few args were floating there are values on   */
/* the stack that I want to have in registers. Ditto structure values.   */

    {   RegList *q = NULL;
        int32 i;
        BindList *nb = active_binders;
        for (i=intregwords; i<intargwords && i<NARGREGS; i++) {
            VRegnum r = R_A1+i;
            if (ArgDeferred(r, argstruct->fn))
              argstruct->deferred[i].r = r = vregister(INTREG);
#ifdef TARGET_HAS_RISING_STACK
          if (intargwords > NARGREGS)
            emitvk(J_LDRVK|J_ALIGN4, r, 4*i, arg0);
          else
#endif
          { q = mkRegList(q, r);
            /* @@@ The next line explains the contorted alternative */
            /* to the #ifdef NEVER code in cg_fnargs_stack.         */
            if (nb->bindlistcar != integer_binder)
                syserr(syserr_padbinder, nb->bindlistcar);
            current_stackdepth -= alignof_toplevel_auto;
            intregwords++;
          }
          if (nb == NULL) syserr(syserr_null_nb);
          nb = nb->bindlistcdr;
        }
        if (q != NULL)
        {   int32 i = 0;
            Binder *b = gentempbinder(te_void);         /* @@@ hack     */
            bindstg_(b) |= b_spilt;
            cg_bindlist(mkSynBindList(0, b), 0);
#define J_LDRLVKxx J_LDRLVK
            for (q = (RegList *)dreverse((List *)q);
                    q != NULL; q = rl_discard(q))
            {   emitvk(alignof_toplevel_auto==8 ? J_LDRLVKxx|J_ALIGN8 :
                                                  J_LDRVK|J_ALIGN4,
                       q->rlcar, i, b);
                i += alignof_toplevel_auto;
            }
            emitsetsp(J_SETSPENV, nb);
            current_stackdepth -= i;
        }
        /* Recreate the list of used registers to keep life safe */
        /* @@@ Redo soon? */
        while (usedregs) usedregs = rl_discard(usedregs);
        while (usedfpregs) usedfpregs = rl_discard(usedfpregs);
        nusedregs = nusedfpregs = 0;

        if (argstruct->specialarg != GAP)
            usedregs = mkRegList(usedregs, argstruct->specialarg);

        for (i=0; i<intregwords; i++)
        {   VRegnum r = R_A1+i;
            if (ArgDeferred(r, argstruct->fn) && argstruct->deferred[i].r != GAP)
              r = argstruct->deferred[i].r;
            AddUsedReg(r);
        }
#ifdef TARGET_FP_ARGS_IN_FP_REGS
        for (i=0; i<fltregargs; i++)
            AddUsedReg(R_FA1+i);
/* @@@ AM: why on earth does this code not use 'usedfpregs?'.           */
/* answer: only one call of cg_expr for odd machine before discarded.   */
#endif
    }
/* Marker in argwords if a special register was used for a struct result */
    return k_argdesc_(arg[n].addr/alignof_toplevel_auto, argfpmask,
                      intregwords, fltregargs, argstruct->resultregs,
                      argstruct->specialarg != GAP ? K_SPECIAL_ARG : 0L);
}

static void LoadDeferredArgReg(FnargStruct const *argstruct, int32 i)
{   VRegnum r = argstruct->deferred[i].r;
    if (r != GAP) {
        emitreg(J_MOVR, R_A1+i, GAP, r);
        bfreeregister(r);
    } else if (argstruct->deferred[i].e != NULL)
        (void)cg_exprreg(argstruct->deferred[i].e, R_A1+i);
}

static void LoadDeferredArgRegs(FnargStruct const *argstruct)
{   int32 i = NARGREGS;
    while (--i >= 0)
        LoadDeferredArgReg(argstruct, i);

    if (argstruct->specialarg != GAP)
        LoadDeferredArgReg(argstruct, argstruct->specialarg-R_A1);
}

/* For functions of 10 args or less, C stack is used, not SynAlloc space: */
#define STACKFNARGS 10  /* n.b. this is *not* a hard limit on no. of args */
/* NB also that I need STACKFNARGS to be at least as large as the no of   */
/* registers for passing args if I have an 88000 as target.               */
static void cg_fnap_1(AEop op, Expr *fn, TypeExpr *fnt,
                      ExprList *a, VRegnum resreg, FnargStruct *argstruct)
{
    int32 argdesc;
    VRegnum structresultp = GAP;
    Expr *structresult = NULL;
    Binder *structresultbinder = NULL;
    int32 resultwords = 0;
    uint16 fnflags;
    argstruct->resultregs = 0;

    argstruct->auxflags = fnflags = typefnaux_(fnt).flags;
    argstruct->resultrep = mcrepoftype(typearg_(fnt));

    if ((op == s_fnapstruct || op == s_fnapstructvoid) &&
        returnsstructinregs_t(fnt))
    {   resultwords = sizeoftype(typearg_(fnt)) / MEMCPYQUANTUM;
        structresult = exprcar_(a);
        a = cdr_(a);
        /* The +resreg term below accounts for the built-in             */
        /* divide+remainder functions, which are lyingly described as   */
        /* returning a single result (because that's easier for the     */
        /* front end to handle). resreg is always 0 for user-defined    */
        /* functions.                                                   */
        argstruct->resultregs = resultwords + resreg;
    }

    {   ArgInfo v[STACKFNARGS];
        int32 n = length(a);
/* The n+1 on the next line gives a sentinel to cg_fnargs.              */
        ArgInfo *p = (n+1) > STACKFNARGS ?
                       (ArgInfo *)SynAlloc((n+1)*sizeof(ArgInfo)) : v;
        argstruct->specialarg =
#ifdef TARGET_SPECIAL_ARG_REG
                            (fnflags & f_specialargreg
#  ifdef TARGET_STRUCT_RESULT_REGISTER
                             || op == s_fnapstruct
                             || op == s_fnapstructvoid
#  endif
                             ) ? TARGET_SPECIAL_ARG_REG :
#endif
                            GAP;
        argstruct->fn = fn; argstruct->fnreg = GAP; argstruct->fnsave = NULL;
        argdesc = cg_fnargs(a, p, n, argstruct);
    }

/* Now the arguments are all in the right places - call the function     */

    if (structresult != NULL && op != s_fnapstructvoid)
    {   if (h0_(structresult) == s_addrof &&
            h0_(arg1_(structresult)) == s_binder)
            structresultbinder = exb_(arg1_(structresult));
        else
            structresultp = cg_expr(structresult);
/* /* this call to cg_expr() is wrong if specialarg or there may be a fn? */
/* it should probably go via the specialreg-like interface?               */
    }

    if (fntypeisvariadic(fnt)) argdesc |= K_VACALL;
#if TARGET_SUPPRESS_VARIADIC_TAILCALL || TARGET_FLAGS_VA_CALLS
    /* WD: TARGET_FLAGS_VA_CALLS obsolete now: original meaning was not to use
       tailcalls on variadic function calls by 'faking' a normal function call.
       TARGET_SUPPRESS_VARIADIC_TAILCALL now does exactly that - without cheating */
    if (fntypeisvariadic(fnt)) argdesc |= K_NOTAILCALL;
#endif

    {   Expr *temp;
        if (vregsort(resreg) == DBLREG && (fnflags & f_resultinintregs))
        {   /* returning fp result in integer registers (using hardfp) */
            resreg = R_A1;
            argdesc = k_setresultregs_(argdesc, (argstruct->resultrep & MCR_SIZE_MASK) >> 2);
        }
        if (h0_(fn) == s_addrof && h0_(temp=arg1_(fn)) == s_binder)
        {   TypeExpr *tt = princtype(bindtype_(exb_(temp)));
/* The next next few lines represent an enthusiastic sanity check.      */
/* We want to check that the Binder fn-type, esp. its typefnaux_()      */
/* (which includes details of inline/reg-use/side-effectness) matches   */
/* that in the s_addrof node (which is used above for struct-return-    */
/* reg-use etc).  Pointer equality (fnt==tt) used to work, but this is  */
/* thwarted by globalize_expr() for C++ static initialisation.          */
/* Note also that simplify.c:optimise_cast(isfntype) conspires too.     */
            LoadDeferredArgRegs(argstruct);
            if (fnt != tt)
              /* this memcmp is dubious, but the 'holes' should match.  */
              if (h0_(tt) != t_fnap ||
                  memcmp(&typefnaux_(fnt), &typefnaux_(tt),
                         sizeof(TypeExprFnAux)) != 0)
                syserr(syserr_cg_fnap_1);
            if (fnflags & bitoffnaux_(s_pure)) argdesc |= K_PURE;
            if (fnflags & bitoffnaux_(s_commutative)) argdesc |= K_COMMUTATIVE;
            if (fnflags & f_resultinflags) argdesc |= K_RESULTINFLAGS;
/* We could imagine code which emits several jopcodes here (saved in    */
/* in-linable form in typefnaux_(fnt)) for in-line JOP expansion.       */
            if (fnflags & bitoffnaux_(s_swi))
                emitcall(J_OPSYSK, resreg, argdesc,
                          (Binder *)(IPtr)(typefnaux_(fnt).inlinecode));
            else {
                emitcall(J_CALLK, resreg,
                         argdesc | ((fnflags & f_notailcall) ? K_NOTAILCALL : 0),
                         exb_(temp));
            }
        }
        else switch (mcrepofexpr(fn))
        {
        case 0x00000004: case 0x01000004:
        case 0x00000008: case 0x01000008:
            {   VRegnum r = argstruct->fnreg;
                if (r == GAP) r = cg_expr(fn);
                LoadDeferredArgRegs(argstruct);
                emitcallreg(J_CALLR, resreg, argdesc, r);
                bfreeregister(r);
                break;
            }
        default:
                syserr(syserr_cg_fnap);
        }
    }
    if (structresult != NULL && op != s_fnapstructvoid)
    {   int32 i;
        if (structresultbinder != NULL &&
            !(bindstg_(structresultbinder) & bitofstg_(s_auto)))
            structresultp = cg_expr(structresult);
        for (i = 0; i < resultwords; i++) {
            if (structresultp != GAP)
                emit(J_memcpy(J_STRK|J_ALIGN4), resreg+i,
                     structresultp, i * MEMCPYQUANTUM);
            else
                emitvk(J_memcpy(J_STRVK|J_ALIGN4), resreg+i,
                       i * MEMCPYQUANTUM, structresultbinder);
        }
        bfreeregister(structresultp);
    }
}

static VRegnum cg_fnap(Expr *x, VRegnum resreg, bool valneeded)
{
  SynBindList *sm1temps = NULL;
  Expr *sm1ass = NULL;
  if (target_stack_moves_once)
/* If TARGET_STACK_MOVES_ONCE then we have to put all arglists in the   */
/* same place.  To avoid overwriting in f(g(1,2),g(3,4)) we transform   */
/* this to "let (t0,t1) in (t0=g(1,2), t1=g(3,4), f(t0,t1))".           */
/* We only do this transformation for ISHARD (= function containing)    */
/* terms.  This transformation is sometimes pessimistic (e.g. last      */
/* arg to a procedure being a fn), but regalloc should be able to       */
/* produce the code we first thought of.                                */
/* Before 'improving' the last arg. treatment, consider the case of     */
/* it being a structure returning function, and thus overlap occurring. */
/* Note that this code destructively updates the aetree.                */
  { ExprList *a = exprfnargs_(x);
    for (; a != NULL; a = cdr_(a))
      {   Expr *ae = exprcar_(a);
          if (ae != NULL && nastiness(ae) == ISHARD)
          {   /* ae == NULL for the return pointer for struct-in-regs   */
              /* functions                                              */
              TypeExpr *t = typeofexpr(ae);
              Binder *gen = gentempbinder(t);
              Expr *ass = mk_expr2(s_assign, t, (Expr *)gen, ae);
              exprcar_(a) = (Expr *)gen;
              sm1temps = mkSynBindList(sm1temps, gen);
              if (sm1ass == NULL)
                  sm1ass = ass;
              else
                  sm1ass = mk_expr2(s_comma, te_void, ass, sm1ass);
          }
      }
  }
  {
/* Compile a call to a function - being tidied!                          */
    RegSort rsort = vregsort(resreg);
    int32 spint = spareregs, spfp = sparefpregs;
    RegList *regstosave = usedregs, *fpregstosave = usedfpregs;
    int32 savebits = nusedregs, savefpbits = nusedfpregs;
    BindList *save_binders = active_binders;
    int32 d = current_stackdepth;
    SynBindList *things_to_bind = bindlist_for_temps(regstosave, fpregstosave);
    Expr *fn = arg1_(x);
    TypeExpr *fnt = princtype(typeofexpr(fn));
    FnargStruct argstruct;
/* Calling a function must preserve all registers - here I push any that */
/* are in use onto the stack.                                            */
    cg_bindlist(things_to_bind, 1);
    stash_temps(regstosave, fpregstosave, things_to_bind,
                J_STRV|J_ALIGN4V, J_STRFV|J_ALIGN4V, J_STRDV|J_ALIGN8);

    nusedregs = nusedfpregs = 0;        /* new 20-6-87 */
    usedregs = usedfpregs = NULL;
    spareregs = sparefpregs = 0;

    if (!((h0_(fnt) == t_content || h0_(fnt) == t_ref) &&
           (h0_(fnt = princtype(typearg_(fnt))) == t_fnap ||
             (h0_(fnt) == t_coloncolon &&         /* C++ ptr-to-mem fns */
              h0_(fnt = princtype(typearg_(fnt))) == t_fnap))))
    {   pr_expr(fn); cc_msg(" of type ");
        pr_typeexpr(princtype(typeofexpr(fn)), 0);
        syserr(syserr_cg_fnap);
    }

    if (sm1temps != NULL) {
        cg_bindlist(sm1temps, 0);
        cg_exprvoid(sm1ass);
    }
    cg_fnap_1(h0_(x), fn, fnt, exprfnargs_(x), resreg, &argstruct);

    if (LanguageIsCPlusPlus)
      { /* need to know if we are inside a try{} block, but note
           that auto variables with destructors are also stored
           on currentExceptionEnv. */
        ExceptionEnv* exenv = currentExceptionEnv;
        while (exenv!=NULL)
          {
            if (exenv->type == ex_handlerblock)
              {
                /* would be better to fiddle with the block flags so as to avoid having to fool the optimiser with bogus code*/
                emit(J_CMPR , GAP, 0, 0);/*compare always true*/
                emitbranch(J_B + Q_NE, exenv->handlers.henv.handlerblock);
                start_new_basic_block(nextlabel());
                break;
              }
            exenv=exenv->cdr;
          }
      }

    if (rsort == DBLREG && (argstruct.resultrep & MCR_SIZE_MASK) == sizeof_float)
        rsort = FLTREG;
/* All registers are now free - work out what the args to the fn are      */
/* Switch back to the outer context of registers.                        */
    while (usedregs) usedregs = rl_discard(usedregs);
    while (usedfpregs) usedfpregs = rl_discard(usedfpregs);
    usedregs = regstosave, usedfpregs = fpregstosave;
    nusedregs = savebits,  nusedfpregs = savefpbits;
    spareregs = spint, sparefpregs = spfp;
    {   VRegnum resultr = GAP;
        if (valneeded) {
            if (returnsstructinregs_t(fnt) && argstruct.resultregs > 1)
                resultr = resreg;
            else {
                resultr = fgetregister(rsort);
                if (rsort == FLTREG) {
                    if (argstruct.auxflags & f_resultinintregs)
                        emitreg(J_MOVIFR, resultr, GAP, R_A1);
                    else
                        emitreg(J_MOVFR, resultr, GAP, resreg);
                } else if (rsort == DBLREG) {
                    if (argstruct.auxflags & f_resultinintregs)
                        emitreg(J_MOVIDR, resultr, R_A1, R_A1+1);
                    else
                        emitreg(J_MOVDR, resultr, GAP, resreg);
                } else
                    emitreg(J_MOVR, resultr, GAP, resreg);
            }
        }
        stash_temps(regstosave, fpregstosave, things_to_bind,
                    J_LDRV|J_ALIGN4V, J_LDRFV|J_ALIGN4V, J_LDRDV|J_ALIGN8);
        while (things_to_bind)
            things_to_bind = freeSynBindList(things_to_bind);
        emitsetsp(J_SETSPENV, save_binders);
        current_stackdepth = d;
        return resultr;
    }
  }
}

static ExceptionEnv *mkExceptionEnv(ExceptionEnv* cdr, ex_enum type, void* destructee)
{
  ExceptionEnv* ExEnv =  (ExceptionEnv *) BindAlloc (sizeof (ExceptionEnv));
  ExEnv->cdr = cdr;
  ExEnv->type = type;
  if (type==ex_destructor)
    ExEnv->handlers.destructee = (Binder*) destructee;
  else /*type==ex_handlerblock*/
    ExEnv->handlers.henv.handlerblock = (LabelNumber*) destructee;
  return ExEnv;
}

static HandlerList *mkHandlerList(HandlerList *cdr, int type, LabelNumber *handler)
{
  HandlerList *h = BindAlloc(sizeof(HandlerList));
  h->cdr =  cdr;
  h->type = type;
  h->handler = handler;
  return h;
}

/* jopcode generation for commands ...                                      */

static void cg_cmd(Cmd *x)
{
    Cmd *oldcmd = cg_current_cmd;
    AEop op;
    while (x != 0)
    {
        cg_current_cmd = x;
        if (cmdfileline_(x).f != 0)
        {   /* This (outer) 'if' block could be a proc as appears below too */
            if (!cg_infobodyflag)
            {
#ifdef TARGET_HAS_PROFILE
                if (profile_option) emitfl(J_COUNT, cmdfileline_(x));
#endif
                if (usrdbg(DBG_PROC)) emit(J_INFOBODY, GAP, GAP, 0);
                cg_infobodyflag = 1;
            }
            if (usrdbg(DBG_LINE)) emitfl(J_INFOLINE, cmdfileline_(x));
        }
        switch (op = h0_(x))
        {

default:    syserr(syserr_cg_cmd, (long)op, op);
            break;

case s_endcase:    /* those 'break's meaning "exit switch" */
            if (switchinfo.endcaselab==NOTINSWITCH) syserr(syserr_cg_endcase);
            else
            {   emitsetspandjump(switchinfo.binders, switchinfo.endcaselab);
            }
            break;

case s_break:      /* those 'break's meaning "exit loop" */
            if (loopinfo.breaklab==NOTINLOOP) syserr(syserr_cg_break);
            else
            {   if (loopinfo.breaklab == 0)
                    loopinfo.breaklab = nextlabel();
                emitsetspandjump(loopinfo.binders, loopinfo.breaklab);
            }
            break;

case s_continue:
            if (loopinfo.contlab==NOTINLOOP) syserr(syserr_cg_cont);
            else
            {   if (loopinfo.contlab == 0)
                    loopinfo.contlab = nextlabel();
                emitsetspandjump(loopinfo.binders, loopinfo.contlab);
            }
            break;

#ifdef EXTENSION_VALOF
case s_resultis:
            /* Valof blocks will not work (a syserr will occur via cg_addr */
            /* or cg_exprreg) for structure results and would need code    */
            /* here and at s_resultis (and cg_addr &c) to make them work.  */
            {   Expr *val = cmd1e_(x);
                if (val != 0) /* In case of 'resultis <errornode>' */
                    (void)cg_exprreg(val, valofinfo.r);
            }
            emitsetspandjump(valofinfo.binders, valofinfo.lab);
            break;

#endif

case s_return:
            cg_count(cmdfileline_(x));
            cg_return(cmd1e_(x), NO);
            break;

case s_do:
            cg_loop(0, 0, 0, cmd1c_(x), cmd2e_(x));
            break;

case s_for: cg_loop(cmd1e_(x), cmd2e_(x), cmd3e_(x), cmd4c_(x), 0);
            break;

case s_if:  {   LabelNumber *l1 = nextlabel();
                Cmd *cc;
                cg_test(cmd1e_(x), 0, l1);
                cc = cmd2c_(x);
                if (cc != NULL)
/* This mess is because we can properly have a null consequence for a */
/* condition, but then it does not have a count field to pass down to */
/* cg_count!                                                          */
                {   cg_count(cmdfileline_(cc));
                    cg_cmd(cc);
                }
                if ((x = cmd3c_(x))==0) start_new_basic_block(l1);
                else
                {   LabelNumber *l2 = nextlabel();
                    emitbranch(J_B, l2);
                    start_new_basic_block(l1);
                    cg_cmd(x);
                    start_new_basic_block(l2);
                    cg_count(cmdfileline_(x));
                }
            }
            break;

case s_switch:
            if ((mcrepofexpr(cmd1e_(x)) >> MCR_SORT_SHIFT) > 1)
                syserr(syserr_cg_switch);
            cg_count(cmdfileline_(x));
            {   VRegnum r = cg_expr(cmd1e_(x));
                struct SwitchInfo oswitchinfo;
                int32 ncases = 0, i;
                CasePair *casevec;
                Cmd *c;
                oswitchinfo = switchinfo;
                switchinfo.endcaselab = nextlabel();
                switchinfo.binders = active_binders;
                switchinfo.defaultlab =
                    switch_default_(x) ? nextlabel() : switchinfo.endcaselab;
                for (c = switch_caselist_(x); c != 0; c = case_next_(c))
                    ncases++;                /* count cases */
/* n.b. SynAlloc is used in the next line -- the store will die very soon */
/* we should use a 'C' auto vector for small amounts here                 */
                casevec = (CasePair *) SynAlloc(ncases*sizeof(casevec[0]));
                i = ncases;
                for (c = switch_caselist_(x); c != 0; c = case_next_(c))
                {   LabelNumber *ln = nextlabel();
                    if (h0_(c) != s_case) syserr(syserr_cg_caselist);
                    i--;    /* syn sorts them backwards */
                    casevec[i].caseval = evaluate(cmd1e_(c));
                    casevec[i].caselab = ln;
                    /* case_lab_(c) */ cmd4c_(c) = (Cmd *)ln;
                }
                /* previous phases guarantee the cases are sorted by now */
                blkflags_(bottom_block) |= BLKREXPORTED;
                casebranch(r, casevec, ncases, switchinfo.defaultlab);
                bfreeregister(r);
                cg_cmd(cmd2c_(x));
                start_new_basic_block(switchinfo.endcaselab);
                switchinfo = oswitchinfo;
            }
            break;

case s_try:
        {
          LabelNumber *l, *handler_exit_label, *handlerblock_label;
          ExceptionEnv* ExEnv = currentExceptionEnv;/* remember ExceptionEnv*/
          Handler* handler_list = (Handler*) cmd2e_ (x);
          List* hl;
          currentExceptionEnv = mkExceptionEnv(currentExceptionEnv, ex_handlerblock, 0);
          hl = (List*) handler_list;
          for(currentExceptionEnv->handlers.henv.handlercount=0;hl!=NULL;hl=hl->cdr)
            {
              currentExceptionEnv->handlers.henv.handlerlist =
                mkHandlerList(currentExceptionEnv->handlers.henv.handlerlist,
                              0, /*should be handler type*/
                              nextlabel());
              currentExceptionEnv->handlers.henv.handlercount++;
            }
          handlerblock_label = nextlabel();
          currentExceptionEnv->handlers.henv.handlerblock = handlerblock_label;
          cg_cmd(cmd1c_(x)); /* body of 'try' */
          ExEnv = currentExceptionEnv;
          currentExceptionEnv = currentExceptionEnv->cdr;
          l = nextlabel();
          emitbranch(J_B, l);
          if (cmd3c_(x)!=NULL) /* cmd3c is handler_exit */
            handler_exit_label = nextlabel();
          else handler_exit_label = l;

          {       /* set blk_table from HandlerEnv*/
            int i = ExEnv->handlers.henv.handlercount;
            LabelNumber** ll = BindAlloc (sizeof (LabelNumber*) * i);

            start_new_basic_block(handlerblock_label);
            emitcasebranch(J_TYPECASE, GAP, ll, i);
            i = 0;
            for (;handler_list!=NULL; handler_list=handler_list->handcdr)
            /* if (h0_(handler_list->handbody) != s_throw) this is wrong; there is currently no easy way to distinguish a handler which just does throw;*/
              { ll[i]=nextlabel();
                start_new_basic_block(ll[i++]);
                cg_cmd(handler_list->handbody);
                emitbranch(J_B, handler_exit_label);
              }
          }
         if (cmd3c_(x)!=NULL)
           {
             start_new_basic_block(handler_exit_label);
             cg_cmd(cmd3c_(x));
             emitbranch(J_B, l);
           }
         else if (debugging(DEBUG_CG))
           printf("this try has no handler_exit block\n");

         start_new_basic_block(l);
        }
        break;

case s_catch:
            {   Handler *unused_handler = cmdhand_(x);
                /* syn.c has given an error for this June 1993.         */
                IGNORE(unused_handler);
                x = cmd1c_(x);
                continue;
            }
/* I wonder if this is the way to do it, or to pass this structure      */
/* on to later stages of the compiler.  The key thing is to ensure      */
/* that all back-ends see: ORG n; ADD a1,delta; TAILCALLK fn.           */
case s_thunkentry:
            {   VfnList *l = (VfnList *)cmd1e_(x), *p;
                int32 ncases = 0, i;
                LabelNumber **table;
                for (p = l; p != 0; p = p->vfcdr) ncases++;
                table = (LabelNumber **) BindAlloc(
                                            ncases * sizeof(LabelNumber *));
                for ((i = 0, p = l); p != 0; p = p->vfcdr)
                    table[i++] = nextlabel();
#ifdef TARGET_HAS_DATA_VTABLES
                if (target_has_data_vtables || ncases > 1)
#else
                if (ncases > 1)
#endif
                    emitcasebranch(J_THUNKTABLE, GAP, table, ncases);
                for ((i = 0, p = l); p != 0; (i++, p = p->vfcdr))
                {   start_new_basic_block(table[i]);
                    if (TARGET_VTAB_ELTSIZE > 4)
                        emit(J_ORG, GAP, GAP, i*TARGET_VTAB_ELTSIZE);
                    emit(J_ADDK, R_P1, R_P1, p->vfdelta);
                    /* ECN: Set 'K_THUNK' bit so we can differentiate these
                     * from ordinary J_CALLK later
                     */
                    emitcall(J_CALLK, V_resultreg(INTREG),
                             k_argdesc_(1, 0, 1, 0, 0, 0)|K_THUNK, p->vfmem);
                    cg_return(0,0);
                }
            }
            break;

case s_case:
            if (switchinfo.defaultlab==NOTINSWITCH) syserr(syserr_cg_case);
            {   LabelNumber *l1 = case_lab_(x);
                if (l1 == NULL) syserr(syserr_unset_case);
                cg_case_or_default(l1);
            }
            x = cmd2c_(x);
            continue;

case s_default:
            if (switchinfo.defaultlab==NOTINSWITCH) syserr(syserr_cg_default);
            cg_case_or_default(switchinfo.defaultlab);
            x = cmd1c_(x);
            continue;

case s_colon:
            {   LabBind *labbinder = cmd1lab_(x);
                LabelNumber *ln = labbinder->labinternlab;
                if (ln == NULL) ln = labbinder->labinternlab = nextlabel();
                start_new_basic_block(ln);
            }
            cg_count(cmdfileline_(x));
            x = cmd2c_(x);
            continue;

case s_goto:
            {   LabBind *labbinder = cmd1lab_(x);
                LabelNumber *l = labbinder->labinternlab;
                if (l == NULL) l = labbinder->labinternlab = nextlabel();
                if (labbinder->labuses & l_defined)  /* else bind.c err msg */
                { emitsetspgoto(active_binders, l);
                  emitbranch(J_B, l);
                }
            }
            break;

case s_semicolon:
/* cmd1e_(x) should by non-NULL, but be gentle for error recovery.      */
            if (cmd1e_(x) != NULL) cg_exprvoid(cmd1e_(x));
            break;

case s_block:
            {   BindList *sl = active_binders;
                int32 d = current_stackdepth;
                CmdList *cl = cmdblk_cl_(x);
                SynBindList *bl = cmdblk_bl_(x);
                bool destructee = false;
                cg_bindlist(bl, 0);

                if (bl != NULL)
                  {
                  Binder* e =  bl->bindlistcar ;
                  if (isclasstype_(princtype(typeofexpr((Expr*)e))))
                    {
                    destructee = true;
                    currentExceptionEnv = mkExceptionEnv
                      (currentExceptionEnv, ex_destructor, e);
                    start_new_basic_block(nextlabel());
                    }
                  }
                if (usrdbg(DBG_VAR))
                {   current_env = (BindListList *)
                          binder_cons2(current_env, binderise(bl));
                    /* Hmm, this code is in flux pro tem. but the idea is   */
                    /* that we have to put debug scope info into block      */
                    /* heads so that is cannot get deadcoded away (discuss) */
                    (void)start_new_basic_block(nextlabel());
                }
                for (; cl!=NULL; cl = cdr_(cl))
                    cg_cmd(cmdcar_(cl));

                if (usrdbg(DBG_VAR))
                {   current_env = current_env->bllcdr;
                    (void)start_new_basic_block(nextlabel());
                }
                if (destructee)
                  {  currentExceptionEnv = currentExceptionEnv->cdr;
                    (void)start_new_basic_block(nextlabel());
                  }
                emitsetsp(J_SETSPENV, sl);
                current_stackdepth = d;
            }
            break;     /* from switch */
#ifdef TARGET_HAS_INLINE_ASSEMBLER
case s_asm:
            cg_asm (x);
            break;
#endif
        }
        break;         /* from loop */
    }
    cg_current_cmd = oldcmd;
}

static void cg_test1(Expr *x, bool branchtrue, LabelNumber *dest)
{
    VRegnum r;
    int32 bc, bcl;
    if (x == 0) { syserr(syserr_missing_expr); return; }
    verify_integer(x);
    if (usrdbg(DBG_LINE) && hasfileline_(h0_(x)) && exprfileline_(x) != 0)
        emitfl(J_INFOLINE, *exprfileline_(x));
    if (integer_constant(x))
    {   if ((result2==0 && !branchtrue) ||
            (result2!=0 && branchtrue)) emitbranch(J_B, dest);
        return;
    }
    else switch (h0_(x))
    {
case s_let:
        {   BindList *sl = active_binders;
            int32 d = current_stackdepth;
            LabelNumber *ltrue = nextlabel();
            LabelNumber *lfalse = nextlabel();
            cg_bindlist(exprletbind_(x), 0);
            cg_test1(arg2_(x), !branchtrue, lfalse);

            {   int32 d1 = current_stackdepth;
                BindList *sl1 = active_binders;
                start_new_basic_block(ltrue);
                emitsetsp(J_SETSPENV, sl);
                current_stackdepth = d;
                emitbranch(J_B, dest);

                active_binders = sl1;
                current_stackdepth = d1;
                start_new_basic_block(lfalse);
                emitsetsp(J_SETSPENV, sl);
                current_stackdepth = d;
                return;
            }
        }

default:    if (resultinflags_fn(x))
            {
                uint32 cond = typefnauxflags_(princtype(typearg_(princtype(typeofexpr(arg1_(x)))))) & Q_MASK;
                r = cg_fnap(x, V_resultreg(INTREG), NO);
                bfreeregister(r);
                emitbranch(J_B + (branchtrue ? cond : Q_NEGATE(cond)), dest);
                return;
            }
            r = cg_expr(x);
            emit(J_CMPK+ (branchtrue ? Q_NE : Q_EQ), GAP, r, 0);
            bfreeregister(r);
            emitbranch(J_B+ (branchtrue ? Q_NE : Q_EQ), dest);
            return;

case_s_any_string
            if (branchtrue) emitbranch(J_B, dest);
            return;

case s_andand:
            if (branchtrue)
            {   LabelNumber *l = nextlabel();
                cg_test1(arg1_(x), 0, l);
                cg_count(cmdfileline_(cg_current_cmd));
                cg_test1(arg2_(x), 1, dest);
                start_new_basic_block(l);
                return;
            }
            else
            {   cg_test1(arg1_(x), 0, dest);
                cg_count(cmdfileline_(cg_current_cmd));
                cg_test1(arg2_(x), 0, dest);
                return;
            }

case s_oror:
            if (!branchtrue)
            {   LabelNumber *l = nextlabel();
                cg_test1(arg1_(x), 1, l);
                cg_count(cmdfileline_(cg_current_cmd));
                cg_test1(arg2_(x), 0, dest);
                start_new_basic_block(l);
                return;
            }
            else
            {   cg_test1(arg1_(x), 1, dest);
                cg_count(cmdfileline_(cg_current_cmd));
                cg_test1(arg2_(x), 1, dest);
                return;
            }

case s_boolnot:
            cg_test1(arg1_(x), !branchtrue, dest);
            return;

case s_comma:
            cg_exprvoid(arg1_(x));
            cg_test1(arg2_(x), branchtrue, dest);
            return;

case s_monplus:
/* Monadic plus does not have to generate any code                       */
            cg_test1(arg1_(x), branchtrue, dest);
            return;

/*
case s_and:    may turn into J_BIT
*/

case s_equalequal:
            bc = Q_NE, bcl = Q_UNE;
            break;

case s_notequal:
            bc = Q_EQ, bcl = Q_UEQ;
            break;

case s_greater:
            bc = Q_LE, bcl = Q_LS;
            break;

case s_greaterequal:
            bc = Q_LT, bcl = Q_LO;
            break;

case s_less:
            bc = Q_GE, bcl = Q_HS;
            break;

case s_lessequal:
            bc = Q_GT, bcl = Q_HI;
            break;

    }
    {
        Expr *e1 = arg1_(x), *e2 = arg2_(x);
        int32 rep;

        if (resultinflags_fn(e1))
            e1 = mk_expr3(s_cond, te_int, e1, mkintconst(te_int, 1, 0), mkintconst(te_int, 0, 0));
        if (resultinflags_fn(e2))
            e2 = mk_expr3(s_cond, te_int, e2, mkintconst(te_int, 1, 0), mkintconst(te_int, 0, 0));
        rep = mcrepofexpr(e1);
        if (rep == MCR_SORT_FLOATING+8 ||
            rep == MCR_SORT_FLOATING+8+MCR_ALIGN_DOUBLE)
            cg_condjump(J_CMPDR, e1, e2, DBLREG,
                        (branchtrue ? Q_NEGATE(bc) : bc), dest);
        else if (rep == MCR_SORT_FLOATING+4)
            cg_condjump(J_CMPFR, e1, e2, FLTREG,
                        (branchtrue ? Q_NEGATE(bc) : bc), dest);
        else if ((rep & MCR_SORT_MASK) == MCR_SORT_UNSIGNED ||
                  rep == MCR_SORT_PLAIN+1)          /* plain char */
            cg_condjump(J_CMPR, e1, e2, INTREG,
                        (branchtrue ? Q_NEGATE(bcl) : bcl), dest);
        else if ((rep & MCR_SORT_MASK) == MCR_SORT_SIGNED)
            cg_condjump(J_CMPR, e1, e2, INTREG,
                        (branchtrue ? Q_NEGATE(bc) : bc), dest);
        else syserr(syserr_cg_badrep, (long)rep);
    }
    return;
}

static void cg_cast2(VRegnum r1, VRegnum r, int32 mcmode, int32 mclength)
{
    if (mcmode == 0) emit(J_EXTEND, r1, r, mclength);
                else emit(J_ANDK, r1, r, lowerbits(8*mclength));
}

static VRegnum cg_cast1_(VRegnum r, int32 mclength, int32 mcmode, int32 argrep)
{
    int32 argmode = argrep >> MCR_SORT_SHIFT,
          arglength = argrep & MCR_SIZE_MASK;
    VRegnum r1;
    RegSort rsort = (mcmode!=2) ? INTREG : mclength==4 ? FLTREG : DBLREG;
    if (mcmode==3 || argmode==3)
    {   if (mcmode==argmode && mclength==arglength) return r;
        else syserr(syserr_cg_cast);
    }

    if (mcmode==argmode) switch(mcmode)
    {
case 0:     /* change width of integer */
/* The test mclength==4 on the next and subsequent lines is a           */
/* temporary hack for TARGET_IS_ADENART on the way to full 64-bit ops.  */
        if (mclength>=arglength || mclength==4) return r;
        emit(J_EXTEND, r1=fgetregister(INTREG), r,
/* Yukky coding here 0 is EXTENDBW, 1 is EXTENDBL, 2 is EXTENDWL...
 * this oddity should be changed sometime later - or at the very least
 * lifted into some enumeration or set of #define constants.
 */
             mclength == 1 ?
               (arglength == 2 ? 0 : 1) : 2);
        bfreeregister(r);
        return r1;
case 1:     /* change width of (unsigned) */
/* The test mclength==4 on the next and subsequent lines is a           */
/* temporary hack for TARGET_IS_ADENART on the way to full 64-bit ops.  */
        if (mclength>=arglength || mclength==4) return r;
        emit(J_ANDK, r1=fgetregister(INTREG), r, lowerbits(8*mclength));
        bfreeregister(r);
        return r1;
case 2:     /* change width of float */
        if (mclength==arglength) return r;
        r1 = fgetregister(rsort);
        if (mclength==4 && arglength==8)
            emitreg(J_MOVDFR, r1, GAP, r);
        else if (mclength==8 && arglength==4)
            emitreg(J_MOVFDR, r1, GAP, r);
        else syserr(syserr_cg_fpsize, (long)arglength, (long)mclength);
        bfreeregister(r);
        return r1;
default:
        if (mclength==arglength) return r;
        syserr(syserr_cg_cast1, (long)mcmode);
        return GAP;
    }
    else if (mcmode==2)
    {   /* floating something */
/* @@@ LDS 23Aug89 - This comment used to say: */
/* "Earlier parts of the compiler ensure that it is only necessary to    */
/* cope with full 32-bit integral types here. Such things as (float) on  */
/* a character are dealt with as (float)(int)<char> with the inner cast  */
/* explicit in the parse tree."                                          */
/* This is no longer true (move of cast optimisation to optimise1()) and */
/* is clearly nonsense, as this function throws away integer widening    */
/* casts in cases 0 and 1 (signed and unsigned) of the if () above.      */
/*      if (arglength!=4) syserr(syserr_cg_cast3, (long)arglength); */
#ifdef TARGET_LACKS_UNSIGNED_FIX
        if (argmode != 0)    /* unsigned float - simulate with signed */
        {   VRegnum r2;
            emit(J_EORK, r2 = fgetregister(INTREG), r, 0x80000000);
            emitreg(J_FLTDR+J_SIGNED, r1 = fgetregister(DBLREG), GAP, r2);
            bfreeregister(r2);
/* N.B. fc_two_31 is double - but this trick won't work with single      */
/*      so I do it in double and then convert down to single precision   */
            emitfloat1(J_MOVDK, r2 = fgetregister(DBLREG), GAP, fc_two_31);
            emitreg(J_ADDDR, r1, r1, r2);
            bfreeregister(r2);
/* the next line should recursively call cg_cast() or cg_expr1() so we   */
/* check that we are not running out of regs.                            */
            if (mclength==4)
            {   VRegnum r3 = fgetregister(FLTREG);
                emitreg(J_MOVDFR, r3, GAP, r1); /* shorten */
                bfreeregister(r1);
                r1 = r3;
            }
        }
        else
#endif /* TARGET_LACKS_UNSIGNED_FIX */
        {   int32 w = (argmode==0) ? J_SIGNED : J_UNSIGNED;
            r1 = fgetregister(rsort);
            emitreg((rsort==FLTREG ? J_FLTFR : J_FLTDR) + w, r1, GAP, r);
        }
        bfreeregister(r);
        return r1;
    }
    else if (argmode==2)
    {   /* fixing something */
#ifdef TARGET_LACKS_UNSIGNED_FIX
/* N.B. the mclength==4 test in the next line is to produce shorter code */
/* for (unsigned short)(double)x.  It implies that this is calculated as */
/* (unsigned short)(int)(double)x.                                       */
        if (mcmode != 0 && mclength == 4)
        {
            VRegnum r2, r3;
/* Fixing to an unsigned result is done by subtracting 2^31, so that the
 * range is signed, and a signed FIX can be used with rounding to minus
 * infinite. After this, adding 2^31 again gives the correct result,
 * including positive/negative overflow.
 */
            if (arglength == 4)
            {
                /* cast to double, since float doesn't have enough precision */
                emitreg(J_MOVFDR, r3 = fgetregister(DBLREG), GAP, r);
                bfreeregister(r);
                r = r3;
            }
            emitfloat1(J_MOVDK, r2 = fgetregister(DBLREG), GAP, fc_two_31);
            emitreg(J_SUBDR, r, r, r2);   /* use 3-addr arm op one day? */
            emitreg(J_FIXDRM+J_SIGNED, r1 = fgetregister(INTREG), GAP, r);
            emit(J_EORK, r1, r1, 0x80000000);
            bfreeregister(r2);
        }
        else
            emitreg((arglength==4 ? J_FIXFR : J_FIXDR) + J_SIGNED,
                    r1 = fgetregister(INTREG), GAP, r);  /* see N.B. above */
#else  /* TARGET_LACKS_UNSIGNED_FIX */
        {   int32 w = (mcmode == 0) ? J_SIGNED : J_UNSIGNED;
            emitreg((arglength==4 ? J_FIXFR : J_FIXDR) + w,
                    r1 = fgetregister(INTREG), GAP, r);
        }
#endif /* TARGET_LACKS_UNSIGNED_FIX */
/* If I do something like (short)<some floating expression> I need to    */
/* squash the result down to 16 bits.                                    */
        if (mclength < 4)
            cg_cast2(r1, r1, mcmode, mclength);
        bfreeregister(r);
        return r1;
    }
    else if (arglength==4 && mclength==4) return r;
    else if (mcmode==0 || mcmode==1)
    {   if (mclength>=4) return r;
        cg_cast2(r1=fgetregister(INTREG), r, mcmode, mclength);
        bfreeregister(r);
        return r1;
    }
    else
    {   syserr(syserr_cg_cast2, (long)mcmode, (long)mclength,
                                (long)argmode, (long)arglength);
        return GAP;
    }
}

static VRegnum cg_cast1(Expr *x1, int32 mclength, int32 mcmode)
{
    if (mclength==0) return cg_exprvoid(x1);  /* cast to void */
    return cg_cast1_(cg_expr(x1), mclength, mcmode, mcrepofexpr(x1));
}

/* At some point we might be willing for a xxx/target.h to specify a    */
/* macro/fn for (a renamed) cg_limit_displacement to exploit machines   */
/* like ARM which do not have a proper notion of quantum/min/max.       */
static int32 cg_limit_displacement(int32 n, J_OPCODE op, int32 ld_align,
                                   int32 mclength, int32 flag) /* nasty arg! */
{
    int32 mink, maxk, span, w, offset;
    IGNORE(mclength);
    IGNORE(flag);

    mink = MinMemOffset(op + ld_align);
    maxk = MaxMemOffset(op + ld_align);
    span = maxk - mink + 1;

/* I insist that span be a power of two, so that the inserted offset   */
/* in the code given below has a neat machine representation.  On many */
/* machines all is OK already, but on the ARM span as defined above is */
/* one less than a power of two.  Fix it up...                         */
/* AM: I think 'neat' above means 'ARM-neat(8 bits)'.                  */

    w = 0;
    do
    {   span -= w;
        w = span & (-span);   /* least significant bit */
    } while (span != w);      /* stop when span has just 1 bit */

/* If n is between mink and maxk (and quantum accessible) we want to    */
/* return it directly, else generate a 'least bits' additive fixup.     */
/* The following expression is believed algebraically equivalent to     */
/* ACN's in the case quantum=1.  @@@ Unify with take_neat_address.      */
/* Note the assumption that (mink & -quantum) == mink!                  */

    offset = n;
    if (offset < mink || offset > maxk)
    {
        offset = (unsigned32)n % span;
        /* If this will do, it is bound to leave a remainder that   */
        /* is easier to handle (fewer bits) than n was, whereas the */
        /* numbers below have no such guarrantee                    */
        if (offset < mink || offset > maxk)
            offset = (n - mink > 0) ? mink + (n - mink) % span :
                     (maxk - n > 0) ? maxk - (maxk - n) % span :
                                      maxk + (maxk - n) % span;
    }
    return offset & (-MemQuantum(op + ld_align));
}

static VRegnum cg_stind(VRegnum r, Expr *val, Expr *x, const int32 flag, Binder *b,
                        const int32 mcmode, const int32 mclength,
                        bool address, int volatileorunaligned)
/* now combines effect of old cg_content.                                */
/* calculates:   *x       if flag==s_content                             */
/*               *x = r   if flag==s_assign                              */
/*      prog1(*x,*x = r)  if flag==s_displace                            */
/* In the latter two cases, if r==GAP the value to be stored is given by */
/* val (not yet given to cg_expr)                                        */
/* The above values are the ONLY valid values for flag                   */
{   J_OPCODE ld_op;
    int32 ld_align;
    Expr *x1, *x2 = NULL;
    int32 n = 0, shift = 0, postinc = 0, down = 0;
    /* n.b. could add down to addrmode sometime */
    enum Addr_Mode { AD_RD, AD_RR, AD_VD } addrmode = AD_RD;
    RegSort rsort = mcmode!=2 ? INTREG : (mclength==4 ? FLTREG : DBLREG);
    int32 signedness = mclength >= 4 ? 0 :
                         mcmode == 0 ? J_SIGNED : J_UNSIGNED;

    switch (mcmode)
    {
case 0: /* signed */
case 1: /* unsigned */
        switch (mclength)
        {
    case 1: ld_op = J_LDRBK; ld_align = J_ALIGN1; break;
    case 2: ld_op = J_LDRWK; ld_align = J_ALIGN2; break;
    case 4: ld_op = J_LDRK; ld_align = J_ALIGN4; break;
    case 8: ld_op = J_LDRLK; ld_align = J_ALIGN8; break;
    default: syserr(syserr_cg_bad_width, (long)mclength); ld_op = J_NOOP; ld_align = J_ALIGN1;
        }
        break;
case 2: if (rsort==FLTREG)
          ld_op = J_LDRFK, ld_align = J_ALIGN4;
        else
          ld_op = J_LDRDK, ld_align = J_ALIGN8;
        break;
default:
        syserr(syserr_cg_bad_mode, (long)mcmode); ld_op = J_NOOP; ld_align = J_ALIGN1;
        break;
    }
    if (volatileorunaligned & IsUnaligned)
        ld_align = J_ALIGN1;

#ifdef NEW_J_ALIGN_CODE             /* was TARGET_IS_ADENART */
/* Although this code is just for a special machine (which encourages   */
/* all 64-bit aligned loads to be done with J_LDRLK), the idea should   */
/* be generalisable (e.g. to improve the TARGET_LACKS_HALFWORD_STORE    */
/* code below).                                                         */
/* We convert ld/st 8/16/32 bits into 64-bit rd/wr, sign-/zero-         */
/* extending on load 8/16 bits and write beyond the item into           */
/* space which alignof_toplevel guarantees is junk.                     */
/* Note: the only reason we don't always enable this code is that it    */
/* might harm cross-jumping optimisation.                               */
    if (b != NULL)
    {   int32 newalign = toplevel_alignment(b);
        int32 new_j_align = newalign == 8 ? J_ALIGN8 :
                            newalign == 4 ? J_ALIGN4 :
                            newalign == 2 ? J_ALIGN2 :
                                            J_ALIGN1;
        if (new_j_align > ld_align)
            ld_align = new_j_align;
    }
#endif

#ifdef ADDRESS_REG_STUFF
    if (rsort==INTREG && address) rsort = ADDRREG;
#else
    IGNORE(address);
#endif
    while (h0_(x) == s_cast) {
        int32 rep = mcrepofexpr(arg1_(x));
        if (rep >= MCR_SORT_FLOATING
            || (rep & MCR_SIZE_MASK) != sizeof_ptr)
            break;
        x = arg1_(x);
    }

    switch (h0_(x))
    {
case s_plus:
        x1 = arg1_(x), x2 = arg2_(x);
#ifdef TARGET_HAS_SCALED_ADDRESSING
/* one might wonder whether the test for is_shifted or s_integer should  */
/* come first.  Observe that either is correct, and the sensible code    */
/* can never have both on an indirection.  E.g.  *(int *)(3 + (x<<7)).   */
/* Moreover, if the machine cannot support all these modes then some are */
/* killed below.                                                         */
        if (is_shifted(x1, mclength, signedness, ld_op | ld_align))
        {   Expr *x3 = x1;
            x1 = x2;
            x2 = shift_operand(x3);
            shift = shift_amount(x3);
            addrmode = AD_RR;
        }
        else if (is_shifted(x2, mclength, signedness, ld_op | ld_align))
        {   shift = shift_amount(x2);
            x2 = shift_operand(x2);
            addrmode = AD_RR;
        }
        else
#endif /* TARGET_HAS_SCALED_ADDRESSING */
             if (h0_(x1)==s_integer) n = intval_(x1), x1 = x2;
        else if (h0_(x2)==s_integer) n = intval_(x2);
        else addrmode = AD_RR;
        break;
case s_minus:
        x1 = arg1_(x), x2 = arg2_(x);
#ifdef TARGET_HAS_SCALED_ADDRESSING
        if (is_shifted(x1, mclength, signedness, ld_op | ld_align))
        {   Expr *x3 = x1;
            x1 = mk_expr1(s_neg, type_(x), x2);
            x2 = shift_operand(x3);
            shift = shift_amount(x3);
            addrmode = AD_RR;
        }
/* /* why on earth is it interesting if x2 is shifted if we don't have */
/* negative-indexing?                                                  */
/* ACN to check and move is_shifted test into conditional code?        */
        else if (is_shifted(x2, -mclength, signedness, ld_op | ld_align))
                      /* Negative mclength marks operand as subtracted */
#ifdef TARGET_HAS_NEGATIVE_INDEXING
        {   shift = shift_amount(x2);
            if ((shift & (SHIFT_RIGHT|SHIFT_ARITH)) == (SHIFT_RIGHT|SHIFT_ARITH))
                cc_rerr(cg_rerr_iffy_arithmetics);
            x2 = shift_operand(x2);
            down = J_NEGINDEX, addrmode = AD_RR;
        }
        else if (h0_(x2)==s_integer) n = -intval_(x2);
        else down = J_NEGINDEX, addrmode = AD_RR;
#else /* !TARGET_HAS_NEGATIVE_INDEXING */
        {   shift = shift_amount(x2);
            x2 = shift_operand(x2);
            x2 = mk_expr1(s_neg, typeofexpr(x2), x2);
            addrmode = AD_RR;
        }
        else if (h0_(x2)==s_integer) n = -intval_(x2);
        else x1 = x, x2 = 0;
#endif /* TARGET_HAS_NEGATIVE_INDEXING */
#else /* TARGET_HAS_SCALED_ADDRESSING */
        if (h0_(x2)==s_integer) n = -intval_(x2);
        else x1 = x, x2 = 0;
#endif /* TARGET_HAS_SCALED_ADDRESSING */
        break;
case s_displace:
        {   Expr *v = arg1_(x), *x3 = arg2_(x);
            if (h0_(x3) == s_plus &&
                is_same(arg1_(x3),v) && integer_constant(arg2_(x3)))
            {   postinc = result2;
                x = v;
            }
        }
        /* drop through */
default:
        x1 = x, x2 = 0;
        break;
    }
/* This code was, and may be better a procedure.                            */
/* Sample observations: x2 is valid only if addrmode == AD_RR (2 reg addr)  */

/* Now make allowance for the limited offsets available with LDRK/STRK      */
    if (addrmode == AD_RD)
    {   int32 n1;
        if (h0_(x1) == s_integer) {
            n += intval_(x1);
            n1 = cg_limit_displacement(n, ld_op, ld_align, mclength, flag);
            x1 = mkintconst(type_(x), n - n1, 0);
        } else {
            n1 = cg_limit_displacement(n, ld_op, ld_align, mclength, flag);
            if (n1 != n)
                x1 = mk_expr2(s_plus, type_(x), x1, mkintconst(te_int, n-n1, 0));
        }
        n = n1;
    }

/* The following line needs regularising w.r.t. machines, like ARM       */
/* where fp/halfword addressing differs from int/byte.                   */
    if (addrmode == AD_RR &&
        (0
#ifdef TARGET_LACKS_RR_STORE
         || (flag != s_content && mcmode != 2)
#endif
#ifdef TARGET_LACKS_RR_HALFWORD_STORE
         || (target_lacks_rr_halfword_store && flag != s_content && mcmode != 2 && mclength == 2)
#endif
#ifdef TARGET_LACKS_RR_FP_ACCESSES
         || mcmode == 2
#endif
#ifdef TARGET_LACKS_RR_UNALIGNED_ACCESSES
         || (volatileorunaligned & IsUnaligned)
#endif
        ))
/* Deal with data types which cannot support register indexed address    */
/* modes: convert back to something more simple.                         */
    {
#ifdef TARGET_HAS_SCALED_ADDRESSING
/* If what we have is *(a+(b+k)), it's a good idea to rewrite as *((a+b)+k) */
/* Not really dependent on TARGET_HAS_SCALED_ADDRESSING in principle,    */
/* but the code below would need to be slightly different if not (shift, */
/* down).                                                                */
        if ((shift & SHIFT_RIGHT) == 0 && (h0_(x2) == s_plus || h0_(x2) == s_minus)) {
            Expr *x3 = arg1_(x2), *x4 = arg2_(x2);
            if (h0_(x3) == s_integer && h0_(x2) == s_plus) {
                Expr *t = x4; x4 = x3, x3 = t;
            }
            if (h0_(x4) == s_integer) {
                int32 n1;
                int32 d = (h0_(x2) == s_plus) ? down : down ^ J_NEGINDEX;
                n = intval_(x4);
                if (shift != 0) n = n << (shift & SHIFT_MASK);
                if (d) n = -n;
                n1 = cg_limit_displacement(n, ld_op, ld_align, mclength, flag);
                if (n1 == n) {
                    addrmode = AD_RD;
                    x1 = mk_expr2((down != 0 ? s_minus : s_plus), type_(x), x1,
                                    mk_expr2(s_leftshift, type_(x3), x3, mkintconst(te_int, shift, 0)));
                }
            }
        }
#endif
        if (addrmode != AD_RD) {
            x1 = x;
            n = 0;                 /* just to make sure! */
            addrmode = AD_RD;
            down = 0;
        }
    }

  { VRegnum r1,r2,r99;
    Binder *x1b = 0;
/* The following test is probably in the wrong place.  Note that the      */
/* reduction to 4k boundaries above does not help if AD_VD then updates.  */
/* Further, use of AD_VD mode probably does not help at all if the binder */
/* is a long way from SP or FP.                                           */
/* @@@ For keeping IP sane, AM thinks we should mark IP as not-available  */
/* if stack frame size (plus largest offset in AD_VD) exceeds single      */
/* register addressability range.   Views?                                */
    if (addrmode == AD_RD && postinc == 0)
    {   x1b = is_local_adcon(x1);
/*            *(&<local> + n)   will use VD addressing mode                */
        if (x1b) addrmode = AD_VD;
    }
    if (addrmode != AD_VD)
    {   if (addrmode == AD_RD) r1 = cg_expr(x1), r2 = GAP;
/* is_same(x1,x2) is not worth testing for addresses                     */
        else if (nastiness(x1) < nastiness(x2))
            r2 = cg_expr(x2), r1 = cg_expr(x1);
        else
            r1 = cg_expr(x1), r2 = cg_expr(x2);
    }
    else r1 = r2 = GAP; /* To avoid dataflow anomalies */
    r99 = (flag == s_assign) ? GAP : fgetregister(rsort);
    ld_op |= ld_align;
    if (volatileorunaligned & BaseIsWordAligned) ld_op |= J_BASEALIGN4;
    if (val != NULL) r = cg_expr(val);
    if (flag != s_assign)
    {   int32 ld_op_su = ld_op | signedness;
        if (addrmode == AD_RD) emit(ld_op_su, r99, r1, n);
        else if (addrmode == AD_VD) emitvk(J_addvk(ld_op_su), r99, n, x1b);
        else emitshift(J_KTOR(ld_op_su) + down, r99, r1, r2, shift);
    }
    if (flag != s_content)
    {
#ifdef TARGET_LACKS_HALFWORD_STORE
/* It would be nice it we could make the back-end do this fabrication.     */
/* We do not do so yet as it is unclear how the work register 'rx' could   */
/* could be passed.                                                        */
        if (target_lacks_halfword_store && (ld_op & J_TABLE_BITS) == J_LDRWK)
        { if (b != NULL && target_lsbytefirst && toplevel_alignment(b) >= alignof_int)
          { /* new experimental ARM J_ALIGNMENT code:                      */
            ld_op = ld_op & ~J_ALIGNMENT | J_ALIGN4;
            goto elsecase;
          }
          else
          { int32 basealign = ld_op & J_BASEALIGN4;
            VRegnum rx = fgetregister(INTREG);
            int32 a_msb, a_lsb;
            if (addrmode == AD_RR)
                syserr(syserr_cg_indexword);
            if (target_lsbytefirst)
            {   a_lsb = n;  a_msb = n+1;}
            else
            {   a_msb = n;  a_lsb = n+1;}
            if (addrmode == AD_VD) emitvk(J_STRBVK|J_ALIGN1, r, a_lsb, x1b);
            else emit(J_STRBK|basealign|J_ALIGN1, r, r1, a_lsb);
            emit(J_SHRK+J_SIGNED, rx, r, 8);
            if (addrmode == AD_VD) emitvk(J_STRBVK|J_ALIGN1, rx, a_msb, x1b);
            else emit(J_STRBK|basealign|J_ALIGN1, rx, r1, a_msb);
            bfreeregister(rx);
          }
        }
        else
elsecase:
#endif
        {   J_OPCODE st_op = J_LDtoST(ld_op);
            if (addrmode == AD_RD) emit(st_op, r, r1, n);
            else if (addrmode == AD_VD) emitvk(J_addvk(st_op), r, n, x1b);
            else emitshift(J_KTOR(st_op) + down, r, r1, r2, shift);
        }
    }
/* Here there had been a s_displace within the indirection, and I do the */
/* update part of it.                                                    */
    if (addrmode != AD_VD)
    {   if (postinc != 0)
        {   emit(J_ADDK, r1, r1, postinc);
            cg_storein(r1, NULL, x, s_assign); /* really a call to cg_var so far */
        }
        bfreeregister(r1);
    }
    if (addrmode == AD_RR) bfreeregister(r2);
    if (flag == s_content)
    {   if (volatileorunaligned & IsVolatile) emituse(r99, rsort);
        return r99;
    }
    if (flag == s_displace)
    {   bfreeregister(r);
        if (volatileorunaligned & IsVolatile) emituse(r99, rsort);
        return r99;
    }
    return r;
  }
}

static VRegnum chroma_check(VRegnum v)
/* This code goes to some trouble to see if there would be a real register */
/* available for use, even though register allocation happens later. This  */
/* behaviour is so that I have something on which to base an heuristic     */
/* relating to spilling things to the stack.                               */
{   if (isintregtype_(vregsort(v)))
    {   if (AddUsedReg(v) <= NTEMPREGS+NARGREGS+NVARREGS) return v;
    }
    else
    {   usedfpregs = mkRegList(usedfpregs, v);
#ifdef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
        if ((nusedregs+=2) <= NTEMPREGS+NARGREGS+NVARREGS) return v;
#else
        if (++nusedfpregs <= NFLTTEMPREGS+NFLTARGREGS+NFLTVARREGS) return v;
#endif
    }
    /* The next line can happen either if:
     *  1. target.h gives NTEMPREGS=NARGREGS=NVARREGS=0  or
     *  2. an op like unsigned fix takes a number of temporaries larger
     *     that the 4 allowed for below (this is delicate, see cg_expr1()).
     */
    syserr(syserr_chroma);
    return v;
}

static VRegnum reserveregister(RegSort precision)
{   nreservedregs++;
    return vregister(precision);
}

static VRegnum getreservedreg(VRegnum r)
{   nreservedregs--;
    return chroma_check(r);
}

VRegnum fgetregister(RegSort rtype)
{
    return chroma_check(vregister(rtype));
}

void bfreeregister(VRegnum r)
{
    if (r == GAP) return;
    if (generic_member((IPtr)r, (List *)usedregs))
    {   nusedregs--;
        usedregs = (RegList *)generic_ndelete((IPtr)r, (List *)usedregs);
    }
    else if (generic_member((IPtr)r, (List *)usedfpregs))
    {
#ifdef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
        nusedregs -= 2;
#else
        nusedfpregs--;
#endif
        usedfpregs = (RegList *)generic_ndelete((IPtr)r, (List *)usedfpregs);
    }
/* There used to be a syserr() trap here that checked that registers were  */
/* discarded tidily - under the newer order of things it has gone away.    */
}

#define jop_iscmp_(op) (((op)&~Q_MASK)==J_CMPR || \
                        ((op)&~Q_MASK)==J_CMPFR || \
                        ((op)&~Q_MASK)==J_CMPDR)

J_OPCODE Q_swap(J_OPCODE op)
{   /* If the bit patterns for the codes were more sensible then this could */
    /* be cheaper.  As it stands more cases coalesce than the code admits.  */
    switch (op & Q_MASK)
    {   default: syserr(syserr_Q_swap, (long)op);
        case Q_AL: case Q_AL+Q_UBIT:
        case Q_UEQ: case Q_UNE:
        case Q_EQ: case Q_NE: return op;
        case Q_LT: case Q_GT: return op ^ (Q_LT ^ Q_GT);
        case Q_LE: case Q_GE: return op ^ (Q_LE ^ Q_GE);
        case Q_LO: case Q_HI: return op ^ (Q_LO ^ Q_HI);
        case Q_LS: case Q_HS: return op ^ (Q_LS ^ Q_HS);
    }
}

static Binder *is_local_adcon(Expr *a)
{   if (h0_(a) == s_addrof)
    {   Expr *w = arg1_(a);
        if (h0_(w) == s_binder)
        {   Binder *b = exb_(w);
            if ((bindstg_(b) & PRINCSTGBITS) == bitofstg_(s_auto))
                return b;
        }
    }
    return 0;
}

static Expr *take_address(Expr *e)
{
    if (h0_(e)==s_content) return arg1_(e);     /*   & * x   --->  x     */
    else if (h0_(e)==s_cast) return take_address(arg1_(e));  /* ignore casts */
    else return cg_optimise0(mk_expr1(s_addrof,
                                   ptrtotype_(typeofexpr(e)),
                                   e));
}

/* This routine forges 'Binder's and so MUST be done in one place.       */
/* It is arguable that is should be more opportunistic about re-using    */
/* pre-existing adcons (e.g. use FLT ones for INTs on the ARM).          */
static Expr *take_neat_address(Binder *b, RegSort rsort)
/* b is a static or extdef binder                                        */
{   int32 off = bindaddr_(b);
    BindList *bb = datasegbinders;
    Binder *bb_elt = NULL;
    int32 base = 0;
    int32 loctype = binduses_(b) & u_loctype;
    J_OPCODE op = isintregtype_(rsort) ? J_LDRK+J_ALIGN4 : J_LDRFK+J_ALIGN4;
    int32 mink, maxk, span;

    mink = MinMemOffset(op);
    maxk = MaxMemOffset(op);

    /* The alignof_max is needed on machines like the i860.     */
    /* alignof_max acts like quantum in cg_limit_displacement.  */
    span = (maxk+1-mink) & -(int32)4 & -(int32)alignof_max;

/* I find a binder for a variable at (&datasegment+nnn) where nnn is a   */
/* neat number and the variable I want now is close to it.               */
/* The following code should use xxx % span as in cg_limit_displacement. */
/* @@@ In fact this whole code probably should be a call to              */
/* cg_limit_displacement with possibly a flag arg (they do same job!).   */
/* @@@ more complication if LDRK_MAX == LDRK_MIN...                      */
    if (span == 0) return take_address((Expr *)b);

    while (off > maxk)
        base += span, off -= span;
    while (off < mink)
        base -= span, off += span;

/* Find a binder for the address involved...                             */
    for (; bb != NULL; bb = bb->bindlistcdr)
    {   bb_elt = bb->bindlistcar;
        if (bindaddr_(bb_elt) == base &&
            (binduses_(bb_elt) & u_loctype) == loctype) break;
    }
    if (bb == NULL)
    {   bb_elt = genglobinder(te_int);  /* MUST be global */
        bindaddr_(bb_elt) = base;
        binduses_(bb_elt) |= loctype;
        datasegbinders =
            (BindList *) global_cons2(SU_Other, datasegbinders, bb_elt);
    }
    if (off == 0) return take_address((Expr *)bb_elt);
    else return mk_expr2(s_plus, te_int,
            take_address((Expr *)bb_elt),
            mkintconst(te_int, off, 0));
}

static VRegnum loadadcon(Binder *b)
/* only used once from cg_addr()                                         */
{
    VRegnum r = fgetregister(ADDRREG);
    J_OPCODE op = J_ADCON;
    if (!(bindstg_(b) & b_fnconst)) {
        if ((bindstg_(b) & b_undef)
              ? (alignof_toplevel_static >= 4
                 || alignoftype(bindtype_(b)) >= 4)
              : (bindaddr_(b) & 3) == 0)
        op = J_ADCON+J_BASEALIGN4;
    }
    emitbinder(op, r, b);
    return r;
}

static void emituse(VRegnum r, RegSort rsort)
{
    if (isintregtype_(rsort)) emit(J_USE, r, GAP, 0);
    else if (rsort == FLTREG) emit(J_USEF, r, GAP, 0);
    else emit(J_USED, r, GAP, 0);
}

static VRegnum cg_var(VRegnum r, Binder *b, AEop flag,
                      int32 mcmode, int32 mclength,
                      bool address)
{
/* AM 22-10-86: New code amalgamating cg_var and (part of) cg_storein.    */
/*    flag is a member of {s_content,s_displace,s_assign}, see cg_stind(). */
/*    fixes bugs in &-locals and extern value fetch.                      */
/* variables can be of several flavours :                                */
/*    (a) local          reference offset from sp                        */
/*    (b) global         reference offset from &datasegment              */
/*    (c) constant       codegenerate associated value (done elsewhere)  */
/*    (d) external       indirect access necessary                       */
/* local vars (even char/short) are treated as possible register vars    */
/* (unless address taken - see below) and are treated as 4 byte values   */
/* with the top bits set up so that widening is done on STORE not on     */
/* load.  This seems a good strategy.                                    */
/* If they have address taken then this strategy does not work (consider */
/* signed short/char variables).  Hence they MUST be put on the stack,   */
/* and be properly accessed (this code fixed a bug in version 1.10)).    */
/* A related bug from extern loads loading (possibly incorrect) top bits */
/* is fixed at the same time.                                            */
/* Note that we must be extra careful with short/char vars whose address */
/* is taken on 370/68000 sex machines.                                   */

/* note that 'b' didn't ought to be a struct/union value.                */
    RegSort rsort = mcmode!=2 ? INTREG : (mclength==4 ? FLTREG : DBLREG);
    VRegnum r99 = GAP;  /* Never used but this saves dataflow anomaly */
    bool volatileorunaligned = isvolatile_type(bindtype_(b)) |
                               (isunaligned_type(bindtype_(b)) << 1);
#ifdef ADDRESS_REG_STUFF
    if (rsort==INTREG && address) rsort = ADDRREG;
#else
    IGNORE(address);
#endif

    switch (bindstg_(b) & PRINCSTGBITS)
    {
default:
        syserr(syserr_cg_stgclass, (long)bindstg_(b));
case b_globalregvar:
case bitofstg_(s_auto):
        if (!((bindstg_(b) & (b_addrof|b_spilt)) && mclength < 4))
        {   /* We use LDRxV/STRxV for variables either whose address is  */
            /* not taken or which occupy 1 or 2 whole stack word(s).     */
            /* Avoid this for short/char &-taken locals, consider        */
            /*    extern short x=0; *(&x+0) = -1; f(x);                  */
            /* The indirect assignment to x cannot affect the top bits   */
            /* (e.g. maybe in procedure) and so LDRV cannot be used to   */
            /* load a pre-(sign/zero) padded version of x as it would be */
            /* if x is in a register.  Also mutter about machine sex.    */
            if (flag != s_assign)
            {   r99 = fgetregister(rsort);
                emitbinder(floatyop(rsort, J_LDRV|J_ALIGN4V, J_LDRFV|J_ALIGN4V, J_LDRDV|J_ALIGN8), r99, b);
            }
/* N.B. local integer variables are ALWAYS stored in a 32-bit word even  */
/* if only 8 or 16 bits is needed. Hence STRV does not need length data  */
            if (flag != s_content)
                emitbinder(floatyop(rsort, J_STRV|J_ALIGN4V, J_STRFV|J_ALIGN4V, J_STRDV|J_ALIGN8), r, b);
            break;
        }
        /* else drop through to use J_ADCONV via s_extern case.          */
        /* This is certainly NOT optimal code, but better than bugs.     */
/* The previous code here was buggy, but on the other hand, I like the
 * idea of using STRV/STRK (32 bits) for storing simple short/char
 * vars made feasible by the padding performed on simple variables by
 * vargen.c.  Of course this is not possible in general in cg_stind()
 * because of array elements.  Worry a bit too about oddsex machines.
 */
jolly:
        r = cg_stind(r, NULL, take_address((Expr *)b), flag, b,
                     mcmode, mclength, NO, volatileorunaligned);
        if (flag == s_content) return r;
        flag = s_assign;
        break;
case bitofstg_(s_extern):
        if (bindstg_(b) & b_undef) goto jolly;
case bitofstg_(s_static):
        if ((binduses_(b) & u_bss) && bindaddr_(b) == BINDADDR_UNSET) goto jolly;
/* v1   ->    *(&datasegment + nnn)    when v1 is a static               */
/* See comment for s_extern above for possible improvement too.          */
        r = cg_stind(r, NULL, take_neat_address(b, rsort), flag, b,
                     mcmode, mclength, NO, volatileorunaligned);
        if (flag == s_content) return r;
        flag = s_assign;
        break;
    }
    if (flag == s_content)
    {   if (volatileorunaligned & IsVolatile) emituse(r99, rsort);
        return r99;
    }
    if (flag != s_displace && !(volatileorunaligned & IsVolatile))
    {   cgstate.juststored.var = b;
        cgstate.juststored.reg = r;
    }
    if (flag == s_displace)
    {   bfreeregister(r);
        if (volatileorunaligned & IsVolatile) emituse(r99, rsort);
        return r99;
    }
    return r;
}

VRegnum cg_storein(VRegnum r, Expr *val, Expr *e, AEop flag)
/* if flag is s_displace return old value,
   else flag is s_assign and return stored value (already coerced). */
{
    int32 mcrep = mcrepofexpr(e);
    int32 mcmode = mcrep >> MCR_SORT_SHIFT;
    int32 mclength = mcrep & MCR_SIZE_MASK;
    bool volatileorunaligned = isvolatile_expr(e) |
                               (isunaligned_expr(e) << 1);
    VRegnum res = GAP;

    switch (h0_(e))
    {
case s_binder:
        if (val != NULL) r = cg_expr(val);
        res = cg_var(r, exb_(e), flag, mcmode, mclength, 0);
        break;

case s_content4:
        volatileorunaligned |= BaseIsWordAligned;

case s_content:
        e = arg1_(e);
        if (memory_access_checks)
        {   Expr *fname = mclength==1 ? sim.writecheck1 :
                         mclength==2 ? sim.writecheck2 :
                         sim.writecheck4;
            e = mk_expr2(s_fnap, typeofexpr(e), fname, mkArgList1(e));
        }
        res = cg_stind(r, val, e, flag, NULL, mcmode, mclength, NO, volatileorunaligned);
        break;

/* The following case is caused by s.*m = 42; where s is a one-word     */
/* struct. Optimise1() changes to (m, s) = 42; !!!                      */
case s_comma:
        cg_exprvoid(arg1_(e));
        return cg_storein(r, val, arg2_(e), flag);

/* The following case is caused by 's.m = 42; where s is a one-word     */
/* struct.  The problem is that optimise0 changes s.m to (typeof_m)s.   */
/* The solution below is rather nasty and doesn't even try to fix the   */
/* way that { (char)a = 1; } warns and then syserrs in pcc mode!        */
case s_cast:
        if ((mcrep & ~0x01000000) == (mcrepofexpr(arg1_(e)) & ~0x01000000))
            return cg_storein(r, val, arg1_(e), flag);
        /* drop through */
default:
        syserr(syserr_cg_storein, (long)h0_(e));
    }
    if (volatileorunaligned & IsVolatile) emit(J_VSTORE, GAP, GAP, 0);
    return res;

}

static VRegnum cg_addr(Expr *sv, bool valneeded)
{
    VRegnum r;
    Expr *e;
    for (;;) switch (h0_(sv))
    {
case s_comma:   /* can occur in structure manipulation code */
        cg_exprvoid(arg1_(sv));
        sv = arg2_(sv);
        continue;

case s_cast:
        /*  & ((cast)x)    --->   & x               */
        sv = arg1_(sv);
        continue;

case s_cond:
        /*  & (p ? x : y)  --->   p ? (&x) : (&y)   */
        arg2_(sv) = take_address(arg2_(sv));
        arg3_(sv) = take_address(arg3_(sv));
        type_(sv) = typeofexpr(arg2_(sv));
        return cg_expr1(sv, valneeded);

case s_assign:
/* this can happen with structure assignments - it is essentially an     */
/* artefect of transformations made here in the codegenerator but seems  */
/* fairly convenient.                                                    */
/* In particular this is used in the case of                             */
/*      (a = b) . c                                                      */
/* which in effect turns into                                            */
/*      ((a = b), a . c)                                                 */
/* but with need for special care if a is an expression that might have  */
/* side effects when being evaluated.                                    */
        e = arg1_(sv);
        switch (h0_(e))
        {
    default:
            syserr(syserr_cg_addr);
    case s_content:
    case s_content4:
           {    TypeExpr *t = typeofexpr(arg1_(e));
                Binder *gen = gentempbinder(t);
/*     & (*p=q)                                                          */
/*                turns into                                             */
/*     (let g;  g = p,  *g = q,  g)                                      */
/*  where the temp var is to ensure that p gets evaluated just once.     */
                sv = mk_exprlet(s_let,
/* @@@ The semantic analyser should export such a function ... */
                              t,
                              mkSynBindList(0, gen),
                              mk_expr2(s_comma,
                                       t,
                                       mk_expr2(s_assign,
                                                t,
                                                (Expr *)gen,
                                                arg1_(e)),
                                       mk_expr2(s_comma,
                                                t,
                                                mk_expr2(s_assign,
                                                         typeofexpr(arg2_(sv)),
                                                         mk_expr1(h0_(e),
                                                                  t,
                                                                  (Expr *)gen),
                                                arg2_(sv)),
                                       (Expr *)gen)));
                if (debugging(DEBUG_CG))
                {   eprintf("& p = q  ---> ");
                    pr_expr_nl(sv);
                }
            }
            return cg_expr1(sv, valneeded);
    case s_binder:
            cg_exprvoid(sv);  /* get the assignment done, voiding the result */
            sv = e;           /* then take address of the lhs variable       */
        }
        /* drop through */
case s_binder:
      { Binder *b = exb_(sv);
        switch (bindstg_(b) & PRINCSTGBITS)
        {
    default:
            syserr(syserr_cg_stgclass, (long)bindstg_(b));
    case bitofstg_(s_auto):
            if (valneeded)
            {   emitbinder(J_ADCONV, r = fgetregister(ADDRREG), b);
                return (r);
            }
            else return GAP;
    case bitofstg_(s_static):
    case bitofstg_(s_extern):
            if (valneeded) return loadadcon(b);
            else return GAP;
        }
      }
case s_int64con:
        if (!valneeded) return GAP;
        emitint64(J_ADCONLL, r = fgetregister(ADDRREG), GAP, exi64_(sv));
        return r;
case s_floatcon:
      { FloatCon *f = exf_(sv);
        if (is_float_(f->floatlen)) {
            if (!valneeded) return GAP;
            emitfloat(J_ADCONF, r = fgetregister(ADDRREG), GAP, f);
            return r;
        } else if (is_anydouble_(f->floatlen)) {
            if (!valneeded) return GAP;
            emitfloat(J_ADCOND, r = fgetregister(ADDRREG), GAP, f);
            return r;
        }
      }
default:
        syserr(syserr_cg_addr1, (long)h0_(sv));
    }
}

#if defined TARGET_HAS_SCALED_OPS || defined TARGET_HAS_SCALED_ADD
static VRegnum cg_opshift(J_OPCODE jop, Expr *arg1, Expr *arg2,
                          int32 shift)
/*
 * Note that the scheme we have here can only cope with constant scale
 * quantities - the ARM can support dynamic shift-amounts, as in
 *     ORR  r1, r2, r3, LSL r4
 * but same will not fit in with the limitations os Jopcode formats.
 */
{
    bool same = 0;
    VRegnum r, r2, targetreg;
    if (is_same(arg1,arg2)) (same = 1, r = r2 = cg_expr(arg1));
    else if (nastiness(arg1) < nastiness(arg2))
        r2 = cg_expr(arg2), r = cg_expr(arg1);
    else
        r = cg_expr(arg1), r2 = cg_expr(arg2);
    targetreg = (jop_iscmp_(jop) ? GAP : fgetregister(INTREG));
    emitshift(jop, targetreg, r, r2, shift);
    bfreeregister(r);
    if (!same) bfreeregister(r2);
    return targetreg;
}
#endif /* TARGET_HAS_SCALED_OPS */

static void verify_integer(Expr *x)
/* @@@ probably overcautious and underused nowadays.                    */
{
    switch(mcrepofexpr(x))
    {
case 0x00000001:    /* signed integers are OK */
case 0x00000002:
case 0x00000004:
case 0x00000008:
case 0x01000001:    /* unsigned integers are OK */
case 0x01000002:
case 0x01000004:
case 0x01000008:
case 0x03000001:    /* structures/unions up to 4 bytes long are OK */
case 0x03000002:
case 0x03000003:
case 0x03000004:
case 0x04000001:    /* plain, short integers are OK */
case 0x04000002:
        return;
default:
        syserr(syserr_integer_expected);
    }
}

static VRegnum cg_binary_or_fn(J_OPCODE op, TypeExpr *type,
                               Expr *fname, Expr *a1, Expr *a2,
                               bool commutesp)
{
/* commutesp is used to control selection of special cases on integer    */
/* args as well as commutativity.                                        */
/* This code is only ever activated on integerlike things                */
    if (commutesp && nastiness(a1)<nastiness(a2))
    {   Expr *t = a1;
        a1 = a2;
        a2 = t;
    }
#if defined TARGET_HAS_MULTIPLY || defined TARGET_IS_SPARC
    if (commutesp && integer_constant(a2))   /* really just allow MULK */
        return cg_binary(op, a1, a2, commutesp, INTREG);
#endif
/* Fortunately I can somewhat fudge the creation of a function call node */
/* since it will only be looked at be this codegenerator and in the      */
/* restricted context of function calls only little bits of type info    */
/* are looked at.                                                        */

/* N.B. in this version I make (p/q) turn into divide(q,p) since that    */
/* seems to make register usage behave better. This is an incompatible   */
/* change from some earlier versions of this compiler - BEWARE           */

/* Detection of special case of divide, remainder by 10 moved to cse.c   */
    a1 = mk_expr2(s_fnap, type, fname, mkArgList2(a2, a1));
    return cg_expr(a1);
}

static VRegnum cg_binary_1(J_OPCODE op, Expr *a1, Expr *a2,
                           bool commutesp, J_OPCODE *condP,
                           RegSort fpp)
{   /* This routine has been grossly uglified by CMP's having conds */
    J_OPCODE cond = condP==0 ? 0 : *condP;
    if (is_same(a1, a2))
    {   VRegnum r, targetreg;
        r = cg_expr(a1);    /* Do this BEFORE allocating targetreg */
        targetreg = jop_iscmp_(op) ? GAP : fgetregister(fpp);
        emitreg(op+cond, targetreg, r, r);
        bfreeregister(r);
        return(targetreg);
    }
/* This first swap is entirely looking for constant arg cases,           */
/* possible evaluation order swap comes later.                           */
    if (commutesp && nastiness(a1)<nastiness(a2))
    {   Expr *t = a1;
        a1 = a2;
        a2 = t;
        if (condP) *condP = cond = Q_swap(cond);
    }
#ifdef TARGET_HAS_SCALED_ADD
    if (op == J_ADDR || op == J_SUBR)
    { if (op == J_ADDR && is_shifted(a2, 0, 0, 0))
        return cg_opshift(op+cond, a1, shift_operand(a2), shift_amount(a2));
      if (is_shifted(a1, 0, 0, 0))
      { if (condP) *condP = cond = Q_swap(cond);
        return cg_opshift((op==J_SUBR ? J_RSBR : op) + cond,
                              a2, shift_operand(a1), shift_amount(a1));
      }
    }
#endif /* TARGET_HAS_SCALED_ADD */
  { VRegnum targetreg;
#ifdef TARGET_HAS_SCALED_OPS
/* The following code has come here as the best place for it.             */
/* One might wonder whether the test for is_shifted or s_integer should   */
/* come first.  Observe that either is correct.  Consider:                */
/*   if ((x>>7) == 27) ...                                                */
/* We can either do    MOVK r,27;        CMPR r, x LSR 7                  */
/* or                  MOVR r, x LSR 7;  CMPK r, 27                       */
/* The former is preferable if loop invariants are optimised.             */
/* The former is what we do here...                                       */
    if (op == J_ADDR || op == J_SUBR ||
        op == J_ANDR || op == J_ORRR || op == J_EORR ||
        (op & ~Q_MASK) == J_CMPR)
    { if (is_shifted(a2, 0, 0, 0))
        return cg_opshift(op+cond, a1, shift_operand(a2), shift_amount(a2));
      if (is_shifted(a1, 0, 0, 0))
      { if (condP) *condP = cond = Q_swap(cond);
        return cg_opshift((op==J_SUBR ? J_RSBR : op) + cond,
                              a2, shift_operand(a1), shift_amount(a1));
      }
    }
#endif /* TARGET_HAS_SCALED_OPS */
    if (jop_canRTOK(op) && integer_constant(a2)) /* floating case below */
    {   int32 n = result2;
        VRegnum r1 = cg_expr(a1);
/* Compare instructions do not need a real destination.                  */
        targetreg = jop_iscmp_(op) ? GAP : fgetregister(fpp);
#define jop_isregshift_(op) \
   (((op) & ~(J_SIGNED+J_UNSIGNED)) == J_SHLR || \
    ((op) & ~(J_SIGNED+J_UNSIGNED)) == J_SHRR)
        if (jop_isregshift_(op))
        {
            if (n == 0)   /* this case should not currently happen */
            {   bfreeregister(targetreg);  /* i.e. don't use reg */
                return r1;
            }
            if ((0xffffffff & (unsigned32)n) >= (unsigned32)32)
            {
/* The following optimisations of errors are overzealous (warned in sem.c)  */
/* but ensure compatible behaviour of constants and expressions.            */
                VRegnum r2 = fgetregister(INTREG);
#ifdef TARGET_LACKS_RIGHTSHIFT
                if ((op & ~(J_SIGNED+J_UNSIGNED)) == J_SHRR)
                    op ^= (J_SHRR^J_SHLR), n = -n;
#endif /* TARGET_LACKS_RIGHTSHIFT */
                emit(J_MOVK, r2, GAP, n);
                emitreg(op+cond, targetreg, r1, r2);
                bfreeregister(r2);
                op = J_NOOP;
            }
        }
        /* @@@ do similar things for div/rem by 0? */
        if (op != J_NOOP) emit(J_RTOK(op+cond), targetreg, r1, n);
        bfreeregister(r1);
        return targetreg;
    }
#ifdef TARGET_HAS_FP_LITERALS
    if (h0_(a2) == s_floatcon && fpliteral(exf_(a2), J_RTOK(op)))
    {   VRegnum r1 = cg_expr(a1);
        targetreg = jop_iscmp_(op) ? GAP : fgetregister(fpp);
/* The next line is just emitfloat because it is illegal to have FP_LITERALS
 * and also needing the literals in store.
 */
        emitfloat(J_RTOK(op+cond), targetreg, r1, exf_(a2));
        bfreeregister(r1);
        return targetreg;
    }
#endif /* TARGET_HAS_FP_LITERALS */
    {   VRegnum r1, r2;
        if (nastiness(a1) < nastiness(a2))
            r2 = cg_expr(a2),
            (!isintregtype_(fpp) ? sparefpregs++ : spareregs++),
            r1 = cg_expr(a1),    /* Do this BEFORE allocating targetreg */
            (!isintregtype_(fpp) ? sparefpregs-- : spareregs--);
        else
            r1 = cg_expr(a1),
            (!isintregtype_(fpp) ? sparefpregs++ : spareregs++),
            r2 = cg_expr(a2),    /* Do this BEFORE allocating targetreg */
            (!isintregtype_(fpp) ? sparefpregs-- : spareregs--);
        targetreg = jop_iscmp_(op) ? GAP : fgetregister(fpp);
        emitreg(op+cond, targetreg, r1, r2);
        bfreeregister(r1);
        bfreeregister(r2);
    }
    return(targetreg);
  }
}

static VRegnum cg_binary(J_OPCODE op, Expr *a1, Expr *a2,
                         bool commutesp, RegSort fpp)
{
    return cg_binary_1(op, a1, a2, commutesp, 0, fpp);
}

static void cg_condjump(J_OPCODE op, Expr *a1, Expr *a2, RegSort rsort,
                        J_OPCODE cond, LabelNumber *dest)
{   bfreeregister(cg_binary_1(op, a1, a2, 1, &cond, rsort));
    emitbranch(J_B+cond, dest);
}

static void cg_count(FileLine fl)
{
#ifdef TARGET_HAS_PROFILE
    if (full_profile_option && fl.f != 0)
        emitfl(J_COUNT, fl);
#else
    IGNORE(fl);
#endif
}

static void cg_test(Expr *x, bool branchtrue, LabelNumber *dest)
{
/* I wonder if the count-point that was here was really useful? ...
    cg_count(cmdfileline_(cg_current_cmd));
 ... end of commented out code */
    cg_test1(x, branchtrue, dest);
}

static bool at_least_once(Expr *init, Expr *endtest)
{
/* This should return true if the boolean formula endtest is certain to  */
/* return false if obeyed straight after the execution of init. This is  */
/* used to map 'for' loops onto 'do .. while' ones where the test is a   */
/* little cheaper.                                                       */
/* The cases I recognize at present are where the initializer is an      */
/* expression (possibly with commas) ending with a form 'var=int' for    */
/* a simple variable, and the end test is an expression 'var op int' or  */
/* 'int op var' for the same variable and a relational operator. Then    */
/* by comparing the two integers I can see if the endtest will fail on   */
/* entry to the loop & if so move it to the end. It might be worth       */
/* extending this code to identify the forms 'var', 'var++', 'var--',    */
/* '++var' and '--var' in the end test position, depending somewhat on   */
/* the perception we have of what sorts of loop are commonly written.    */
    int32 i1, i2;
    int32 unsignedp;
    Expr *var, *x1, *x2;
    AEop tst;
    if (endtest==0) return(1);  /* no endtest => this does not matter    */
    if (init==0) return(0);     /* no init for => I can't tell           */
    while (h0_(init) == s_comma) init = arg2_(init);
    while (h0_(init) == s_cast)  init = arg1_(init);
    if (!(h0_(init)==s_assign)) return(0);
    var = arg1_(init);
    if (!(h0_(var)==s_binder)) return(0);
    i1 = mcrepofexpr(var);
    if (i1!=4 && i1!=0x01000004) return(0); /* int or unsigned int OK    */
    init = arg2_(init);
    if (!integer_constant(init)) return(0);
    i1 = result2;
/* Now I know that the initializer is 'var = i1'                         */
    if (!isrelational_(tst = h0_(endtest))) return(0);
    x1 = arg1_(endtest);
    x2 = arg2_(endtest);
    {   Expr *v = 0;
        if (integer_constant(x2) &&
            (x1 == var || (h0_(x1) == s_cast && arg1_(x1) == var)))
            v = x1, i2 = result2;
        else if (integer_constant(x1) &&
                 (x2 == var || (h0_(x2) == s_cast && arg1_(x2) == var)))
            v = x2, i2 = i1, i1=result2;
        else
            return 0;

        if (h0_(v) == s_cast) {
            /* ok if both types are effectively the same, or if they are
               the same width and one is signed and the other unsigned
             */
            int32 repdiff = mcrepofexpr(var) ^ mcrepofexpr(v);
            if ((repdiff & MCR_SIZE_MASK) != 0 ||
                ((repdiff >> MCR_SORT_SHIFT) & ~1) != 0)
                return 0;
        }
        unsignedp = unsigned_expression_(v);
    }
/* NB the tests here are done in signed or unsigned mode                 */
/* depending on the character of the variable v.                         */
    {   unsigned32 i1u = i1 & 0xffffffff, i2u = i2 & 0xffffffff;
    switch (tst)
    {
default:
        return(0);
case s_equalequal:
        return(i1==i2);
case s_notequal:
        return(i1!=i2);
case s_greater:
        if (unsignedp) return (i1u>i2u);
        else return(i1>i2);
case s_greaterequal:
        if (unsignedp) return (i1u>=i2u);
        return(i1>=i2);
case s_less:
        if (unsignedp) return (i1u<i2u);
        return(i1<i2);
case s_lessequal:
        if (unsignedp) return (i1u<=i2u);
        return(i1<=i2);
    }
    }
}

static int32 alignofpointee(Expr *x, int32 knownalign)
{   int32 a1 = 1, a2 = 1;
/* Compute maximum of type-based alignment and layout-based alignment.  */
/* Maybe it would help if previous stages could have done this.         */
/* Note that it is better that optimise() has removed any possible      */
/* outer (e.g. arg) cast to (void *) from a more aligned pointer type.  */
    TypeExpr *t = princtype(typeofexpr(x));
    if (h0_(t) == t_content || h0_(t) == t_ref)
    {   TypeExpr *tt = typearg_(t);
        if (isunaligned_type(tt))
            return 1;
        /* the (amusingly named) test on next line seems overkeen...    */
        /* ... but it protects for memcpy applied to (void *).          */
        if (sizeoftypelegal(tt)) a1 = alignoftype(tt);
    }
    if (isstring_(h0_(x)))
        a2 = alignof_literal;
    else if (h0_(x) == s_addrof && h0_(arg1_(x)) == s_binder)
        a2 = toplevel_alignment(exb_(arg1_(x)));
    if (a1 > knownalign) knownalign = a1;
    if (a2 > knownalign) knownalign = a2;
    return knownalign;
}

static int32 sizeofpointee(Expr *x, int32 *padding)
{
/* @@@ Beware: sizeofpointee() is now a constraint on how strings       */
/* are stored (and even shared!) in memory.  Hence more of the string   */
/* stuff which some back-ends (including ARM) manage needs to move to   */
/* MIP so we can see that it is consistent.                             */
    int32 len = 0, pad = 0;
    if (h0_(x) == s_string) {
        len = stringlength(exs_(x)->strseg)+1;    /* isstring_()? */
        pad = padsize(len, alignof_literal) - len;
    } else if (h0_(x) == s_addrof) {
        x = arg1_(x);
        if (h0_(x) == s_binder &&
            sizeoftypelegal(bindtype_(exb_(x)))) {
            len = sizeoftype(bindtype_(exb_(x)));
            pad = padsize(len, toplevel_alignment(exb_(x))) - len;
        }
    }
    *padding = pad;
    return len;
}

#define symisctor(s)  (LanguageIsCPlusPlus ? strncmp(symname_(s), "__ct", 4) == 0 : 0)

static void emitcopy(Icode *ic) {
    if (ic->op == J_SETSPENV) {
        active_binders = ic->r2.bl;
        emitsetsp(ic->op, ic->r3.bl);;
    } else
        emitic(ic);
}

static Inline_ArgSubstList *New_Inline_ArgSubstList(Inline_ArgSubstSort sort) {
    Inline_ArgSubstList *sl = (Inline_ArgSubstList *)SynAlloc(sizeof(Inline_ArgSubstList));
    sl->notnull = NO;
    sl->sort = sort;
    return sl;
}

static VRegnum TryInlineRestore(
  Binder *fname, ExprList *args, Expr *structresult, RegSort rsort, bool valneeded) {
    VRegnum resultr = GAP;
    Inline_RestoreControl rc;
    BindList *oactive = active_binders;
    Inline_SavedFn px;
    Inline_SavedFn *p = Inline_FindFn(fname);
    VRegnum structresultp = GAP;
    Binder *structresultbinder = NULL;
    bool resultisstruct = NO;
    int32 narg = length((List *)args);
    if (structresult != NULL && !returnsstructinregs_t(bindtype_(fname))) narg++;
    if (p == NULL || narg != length((List *)p->fndetails.argbindlist))
      return NOT_OPEN_COMPILABLE;

    px = *p;
    rc.exitlabel = nextlabel();
    rc.env = oactive;
    rc.argreplace = NULL;
    {   TypeExpr *fntype = bindtype_(fname);
        TypeExpr *restype = typearg_(fntype);
        if (returnsstructinregs_t(fntype)
            && (mcrepoftype(restype) & MCR_SORT_MASK) == MCR_SORT_STRUCT) {
            /* Note that returnsstructinregs() but structresult==NULL is    */
            /* possible: it occurs precisely when the function being called */
            /* here provides the return value for the calling function.     */
            /* (also, in this case the call is s_fnapstructvoid rather than */
            /* s_fnapstruct). But we mustn't let Inline_Restore think the   */
            /* call is voided in this case, or it will kill instructions    */
            /* loading the result                                           */
            VRegnum r = V_resultreg(INTREG);
            unsigned i, n = (unsigned)sizeoftype(restype) / MEMCPYQUANTUM;
            resultisstruct = YES;
            for (i = 0; i < n; i++) {
              rc.resultregs[i] = r;
              rc.newresultregs[i] = fgetregister(INTREG);
              r++;
            }
            rc.nresults = n;
            if (structresult != NULL) {
                if (h0_(structresult) == s_addrof &&
                    h0_(arg1_(structresult)) == s_binder)
                    structresultbinder = exb_(arg1_(structresult));
                else
                    structresultp = cg_expr(structresult);
            }
        } else if (isvoidtype(restype)) {
            rc.nresults = 0;
        } else {
            rc.nresults = 1;
            rc.resultregs[0] = V_resultreg(rsort);
            if (!valneeded)
                rc.newresultregs[0] = GAP;
            else
                resultr = rc.newresultregs[0] = fgetregister(rsort);
        }
    }
    /* Arrange to do inline substitution for suitable arguments, rather than
     * assignment to an argument binder. CSE can achieve the same effect, but
     * doing it here is a significant time saver for both CSE and regalloc;
     * also, by direct sustitution of &arg into *par, we can hope to remove
     * the spurious address-taken attribute from arg and improve generated
     * code significantly: this can't be done after CSE (address-taken-ness
     * has then already been used to determine aliasing).
     */
    if (!(var_cc_private_flags & 1048576L)) {
        Inline_ArgSubstList **slp = &rc.argreplace;
        ExprList *a = args;
        Inline_ArgBinderList *argl;
        for (argl = px.args;
             argl != NULL;
             argl = cdr_(argl), a = cdr_(a)) {
            Binder *b = argl->globarg;
            Expr *ex = exprcar_(a);
            Expr *rest = NULL;
            bool byreference = NO;
            Inline_ArgSubstList *sl = NULL;
            if (h0_(ex) == s_comma) {
                rest = arg1_(ex);
                ex = arg2_(ex);
            }
            if (h0_(ex) == s_addrof) {
                byreference = YES;
                ex = arg1_(ex);
            }
            if (!byreference && h0_(ex) == s_integer) {
                sl = New_Inline_ArgSubstList(T_Int);
                if (argl->narrowtype != NULL) b = argl->globnarrowarg;

            } else if (argl->narrowtype != NULL) {
                if ( h0_(ex) == s_binder && !byreference
                     && !(bindstg_(exb_(ex)) & b_addrof)
                     && (bindstg_(exb_(ex)) & bitofstg_(s_auto))
                     && mcrepofexpr(ex) == mcrepoftype(argl->narrowtype)) {
                    sl = New_Inline_ArgSubstList(T_Binder);
                    b = argl->globnarrowarg;
                }
            } else if (h0_(ex) == s_binder
                  /* a variable is only substitutable if it's not updated in
                     the function to be inlined. Local to the calling function
                     and not also passed by reference is sufficient to ensure
                     this. The latter is checked later.
                   */
                       && !( (bindstg_(exb_(ex)) & b_addrof)
                             && sizeoftypelegal(bindtype_(exb_(ex)))
                             && (mcrepofexpr(ex) & MCR_SIZE_MASK) < sizeof_int)
                       && (byreference
                           || (bindstg_(exb_(ex)) & bitofstg_(s_auto)))) {
                if (!byreference) {
                  if (bindstg_(exb_(ex)) & b_addrof) continue;
                  sl = New_Inline_ArgSubstList(T_Binder);
                  if (symisctor(currentfunction.symstr) && symisctor(bindsym_(fname))
                      && exb_(ex) == currentfunction.argbindlist->bindlistcar)
                    sl->notnull = YES;
                } else if (!(bindstg_(exb_(ex)) & bitofstg_(s_auto))) {
                  sl = New_Inline_ArgSubstList(T_Adcon);
                  if (!(bindstg_(exb_(ex)) & bitofstg_(s_weak)))
                    sl->notnull = YES;
                } else {
                  int32 rep = mcrepofexpr(ex);
                  int32 sort = rep & MCR_SORT_MASK,
                        len = rep & MCR_SIZE_MASK;
                  sl = New_Inline_ArgSubstList(T_AdconV);
                  sl->size = sort == MCR_SORT_FLOATING ?
                                (len == 4 ? MEM_F :
                                            MEM_D) :
                             sort < MCR_SORT_FLOATING ?
                                (len == 1 ? MEM_B :
                                 len == 2 ? MEM_W :
                                 len == 4 ? MEM_I :
                                            MEM_LL) :
                                MEM_NONE;
                  sl->notnull = YES;
                }
            } else if (h0_(ex) == s_plus && h0_(arg1_(ex)) == s_binder
                       && h0_(arg2_(ex)) == s_integer
                       && symisctor(currentfunction.symstr)
                       && symisctor(bindsym_(fname))
                       && exb_(arg1_(ex)) == currentfunction.argbindlist->bindlistcar) {
                sl = New_Inline_ArgSubstList(T_Plus);
                sl->notnull = YES;
            }
            if (sl != NULL) {
                cdr_(sl) = NULL;
                sl->arg = b; sl->replacement.ex = ex;
                sl->refsleft = NO;
                sl->rest = rest;
                *slp = sl; slp = &cdr_(sl);
            }
        }
    }
    if (debugging(DEBUG_CG))
        cc_msg("\ninlined $b\n", fname);
    Inline_Restore(&px, &rc);
    {   typedef struct ArgValList ArgValList;
        struct ArgValList {
            ArgValList *cdr;
            Expr *init;
        };
        ArgValList *argvals = NULL;
        Inline_ArgSubstList *sl = rc.argreplace;
        Inline_ArgBinderList *argl = px.args;
        BindList *bl = px.fndetails.argbindlist;
        ExprList *a = args;
        for (; argl != NULL; argl = cdr_(argl), a = cdr_(a)) {
            Expr *ex = exprcar_(a);
            TypeExpr *t;
            Binder *bglob = argl->narrowtype == NULL || argl->globnarrowarg == NULL
                                                     ? argl->globarg
                                                     : argl->globnarrowarg;
            if (sl != NULL && sl->arg == bglob) {
                bool refsleft = sl->refsleft;
                Expr *rest = sl->rest;
                sl = cdr_(sl);
                if (!refsleft) {
                    if (rest != NULL)
                        argvals = (ArgValList *)syn_list2(argvals, rest);
                    continue;
                }
            }
            {   Binder *b = bl->bindlistcar;
                if (bindsym_(b) != bindsym_(bglob))
                    syserr("Inline_Restore: argument substitution confused");
                if (argl->globnarrowarg != NULL) {
                    b = argl->instantiatednarrowarg;
                    t = argl->narrowtype;
                    /*/* this optimise0 is questionable -- Harry will improve */
                    ex = optimise0(mkcast(s_assign, ex, t));
                } else if (h0_(ex) != s_string)
                    t = typeofexpr(ex);
                else
                    t = mk_typeexpr1(s_content, primtype_(bitoftype_(s_char)), 0);
                bindtype_(b) = t;
                argvals = (ArgValList *)
                          syn_list2(argvals,
                                    mk_expr2(s_assign, t, (Expr *)b, ex));
                bl = bl->bindlistcdr;
            }
        }
        emitsetsp(J_SETSPENV, rc.env);
        if (px.ix_narrowspenv >= 0) {
            BlockHead *insert = blkdown_(px.top_block);
            emitsetsp(J_SETSPENV, blkcode_(insert)[px.ix_narrowspenv].r3.bl);
        }
        argvals = (ArgValList *)dreverse((List *)argvals);
        for (; argvals != NULL; argvals = (ArgValList *)discard2(argvals))
            cg_exprvoid(argvals->init);
    }
    local_binders = (BindList *)nconc((List *)local_binders,
                                      (List *)px.var_binders);
    regvar_binders = (BindList *)nconc((List *)regvar_binders,
                                       (List *)px.reg_binders);
    { /* We now try to merge both the first and last blocks of an inlined
       * function with blocks from the caller: if the inlined function has just
       * one block, it can be inlined without introducing any extra blocks
       * (we _have_ created the labels for the blocks we won't be introducing,
       * which will make the labels for real blocks sparser. Let's hope it
       * doesn't matter.
       * (firstblockmergeable and lastblockmergeable tell us whether we can)
       */
        BlockHead *insert = blkdown_(px.top_block);
        BlockHead *end_insert = px.bottom_block;
        if (insert == end_insert
            || (px.firstblockmergeable
                && blklab_(blkdown_(insert)) == blknext_(insert)
                && !(blkflags_(insert) & BLKSWITCH))) {
            Icode *ic = blkcode_(insert);
            uint32 i = 0,
                   len = blklength_(insert);
            uint8 *ignoremap = px.firstblockignore;
            for (; i < len; i++, ic++)
                if (ignoremap == NULL)
                  emitcopy(ic);
                else {
                  /* The narrowing store into an argument binder is turned into
                   * a load, to guard against cg's desire to reuse a register
                   * just stored rather than to load from the place just stored
                   * to.
                   */
                  if ((ignoremap[(i+px.ix_max)/8] & regbit((i+px.ix_max)%8)) &&
                      stores_r1(ic->op))
                  { ic->op = J_XtoY(ic->op, J_STRK, J_LDRK);
                    emitcopy(ic);
                  }
                  else if (!(ignoremap[i/8] & regbit(i%8)))
                    emitcopy(ic);
                }
            if (blkflags_(insert) & BLK2EXIT)
                emitbranch(J_B+(blkflags_(insert) & Q_MASK), blknext1_(insert));
            if (insert == end_insert)
                insert = NULL;        /* just one block to be inlined */
            else
                insert = blkdown_(insert);
        }
        if (insert != NULL) {
            BlockHead *insert_after = bottom_block;
            BlockHead *insert_before;
            BlockHead *endblock = px.lastblockmergeable ? end_insert : NULL;
            emitbranch(J_B, blklab_(insert));
            if (debugging(DEBUG_CG)) {
                BlockHead *b = insert;
                for (; b != endblock; b = blkdown_(b))
                    flowgraf_printblock(b, NO);
            }
            if (px.lastblockmergeable) {
                Icode *ic = blkcode_(endblock);
                unsigned32 i = 0, len = blklength_(endblock);
                active_binders = blkstack_(end_insert);
                start_new_basic_block(blklab_(endblock));
                for (; i < len; i++, ic++)
                    emitcopy(ic);
                if (insert == end_insert)
                  end_insert = blkup_(bottom_block);
                else
                  end_insert = blkup_(endblock);
            } else {
                active_binders = blkstack_(blkdown_(px.top_block));
                start_new_basic_block(rc.exitlabel);
            }
            insert_before = bottom_block;  /* (the new block just started) */
            blkdown_(insert_after) = insert; blkup_(insert) = insert_after;
            blkdown_(end_insert) = insert_before;
            blkup_(insert_before) = end_insert;
        }
    }
    emitsetsp(J_SETSPENV, oactive);
    if (debugging(DEBUG_CG))
        cc_msg("\nend inlined $b\n", fname);

    if (structresult != NULL) {
        int32 i;
        if (structresultbinder != NULL
            && !(bindstg_(structresultbinder) & bitofstg_(s_auto)))
            structresultp = cg_expr(structresult);
        for (i = 0; i < rc.nresults; i++) {
            VRegnum r = rc.newresultregs[i];
            if (structresultp != GAP)
                emit(J_memcpy(J_STRK|J_ALIGN4), r, structresultp,
                     i * MEMCPYQUANTUM);
            else
                emitvk(J_memcpy(J_STRVK|J_ALIGN4), r,
                       i * MEMCPYQUANTUM, structresultbinder);
            bfreeregister(r);
        }
        bfreeregister(structresultp);
    } else if (resultisstruct) {
        /* but structresult == NULL : move renamed result registers */
        /* to result registers                                      */
        int32 i;
        for (i = 0; i < rc.nresults; i++) {
            VRegnum r = rc.newresultregs[i];
            emitreg(J_MOVR, rc.resultregs[i], GAP, r);
            bfreeregister(r);
        }
    }
    return resultr;
}

#define ptrtofn_(f) (mk_expr1(s_addrof, ptrtotype_(typeofexpr(f)), (f)))

static int32 LengthOfString(String *p) {
    int32 n = 0;
    StringSegList *s = p->strseg;
    for ( ; s != NULL ; s = s->strsegcdr) {
      size_t l = (size_t)s->strseglen;
      if (l > 0) {
        size_t l1 = strlen(s->strsegbase);
        if (l1 < l) {
          n += l1;
          break;
        }
        n += l;
      }
    }
    return n;
}

static VRegnum open_compilable(Expr **xp, RegSort rsort, bool valneeded)
{
    Expr *x = *xp;
    Expr *fname = arg1_(x);
    Expr *a1 = NULL, *a2 = NULL, *a3 = NULL;
    int32 narg = 0, n;
    ExprList *a = exprfnargs_(x);

    if (h0_(fname) != s_addrof) return NOT_OPEN_COMPILABLE;
    fname = arg1_(fname);
    if (fname == NULL || h0_(fname) != s_binder) return NOT_OPEN_COMPILABLE;
/* Only consider this call if the function is a direct function name */
    if (a != NULL)
    {   a1 = exprcar_(a);
        narg++;
        a = cdr_(a);
        if (a != NULL)
        {   a2 = exprcar_(a);
            narg++;
            a = cdr_(a);
            if (a != NULL)
            {   a3 = exprcar_(a);
                narg++;
                a = cdr_(a);
                if (a != NULL) narg++;
            }
        }
    }
#ifdef TARGET_INLINES_MONADS    /* distinctly special case-ish          */
    if (narg == 1) {
        int32 i = target_inlinable(exb_(fname), narg);
        if (i) {
            VRegnum r1 = cg_expr(a1);
            VRegnum targetreg = fgetregister(rsort);
            emit(floatyop(rsort, J_INLINE1, J_INLINE1F, J_INLINE1D),
                 targetreg, r1, i);
            bfreeregister(r1);
            return targetreg;
        }
    }
#endif

#ifdef TARGET_HAS_DIVREM_FUNCTION
/* The idea here is that if we are doing both divide and remainder,
   CSE can eliminate one call.  To do this, it and regalloc need to
   understand that div & udiv return two results.
 */
/* Should we invent a V_resultreg2 macro for R_A1+1?                    */
    if (fname == arg1_(sim.remfn) && narg == 2)
        return cg_fnap(mk_expr2(s_fnap, te_int, sim.divfn, (Expr *)exprfnargs_(x)),
                       R_A1+1, YES);
    else if (fname == arg1_(sim.uremfn) && narg == 2)
        return cg_fnap(mk_expr2(s_fnap, te_uint, sim.udivfn, (Expr *)exprfnargs_(x)),
                       R_A1+1, YES);
#endif
    if (fname == sim.llsrem && narg == 3)
        return cg_fnap(mk_expr2(h0_(x), te_llint, ptrtofn_(sim.llsdiv), (Expr *)exprfnargs_(x)),
                       R_A1+2, YES);
    else if (fname == sim.llurem && narg == 3)
        return cg_fnap(mk_expr2(h0_(x), te_ullint, ptrtofn_(sim.lludiv), (Expr *)exprfnargs_(x)),
                       R_A1+2, YES);
    else if (fname == sim.llsrrem && narg == 3)
        return cg_fnap(mk_expr2(h0_(x), te_llint, ptrtofn_(sim.llsrdv), (Expr *)exprfnargs_(x)),
                       R_A1+2, YES);
    else if (fname == sim.llurrem && narg == 3)
        return cg_fnap(mk_expr2(h0_(x), te_ullint, ptrtofn_(sim.llurdv), (Expr *)exprfnargs_(x)),
                       R_A1+2, YES);

    if (bindsym_(exb_(fname)) == sim.strcpysym) {
      if (narg == 2 && h0_(a2) == s_string) {         /* isstring_()? */
        int32 n = LengthOfString(exs_(a2));
        *xp = mk_expr2(s_fnap, type_(x), sim.realmemcpyfn,
                       mkArgList3(a1, a2, mkintconst(te_int, n+1, 0)));
        return open_compilable(xp, rsort, valneeded);
      } else
        return NOT_OPEN_COMPILABLE;
    }

    if (bindsym_(exb_(fname)) == sim.strlensym) {
      if (narg == 1 && h0_(a1) == s_string) {         /* isstring_()? */
        int32 n = LengthOfString(exs_(a1));
        return cg_expr(mkintconst(te_int, n, 0));
      } else
        return NOT_OPEN_COMPILABLE;
    }

/* Next macro tests if translating 'memcpy' to '_memcpy' is worthwhile  */
/* It must be still in flux...                                          */
#define structptrlike(e) ((alignofpointee(e,1) & (MOVC_ALIGN_MIN-1)) == 0)
#ifdef TARGET_HAS_BLOCKMOVE
#  define cg_inlineable_size(n) (((n) & (MEMCPYQUANTUM-1)) == 0)
#else
/* Currently the non-J_MOVC expansion below only works for mults of 4,   */
/* and then only if guaranteed 4-byte aligned.                           */
#  define cg_inlineable_size(n) (alignof_struct >= 4 && (n & 3) == 0)
#endif

    if (bindsym_(exb_(fname)) == bindsym_(exb_(arg1_(sim.realmemcpyfn))) &&
        !valneeded && narg == 3 &&
        h0_(a3) == s_integer &&
        ((n = intval_(a3)) < MEMCPYQUANTUM ||
         (structptrlike(a1) && structptrlike(a2))))
    {   Expr *x1;
        Expr *args = (Expr *)exprfnargs_(x);
        if (!cg_inlineable_size(n)) {
            int32 padding;
            int32 destsize = sizeofpointee(a1, &padding);
            if (n == destsize && padding != 0 && cg_inlineable_size(destsize+padding))
                args = mkArgList3(a1, a2, mkintconst(te_int, destsize+padding, 0));
            else if (n >= MEMCPYQUANTUM)
                return NOT_OPEN_COMPILABLE;
        }
        x1 = mk_expr2(s_fnap, type_(x), sim.memcpyfn, args);
        return open_compilable(&x1, rsort, valneeded);
    }
    if (bindsym_(exb_(fname)) == bindsym_(exb_(arg1_(sim.realmemsetfn))) &&
        narg == 3 &&
        h0_(a2) == s_integer && intval_(a2) == 0 &&
        h0_(a3) == s_integer &&
        ((n = intval_(a3)) < MEMCPYQUANTUM ||
         structptrlike(a1)) && 0)         /* coming to exist */
    {   Expr *x1;
        Expr *args = (Expr *)exprfnargs_(x);
        if (!cg_inlineable_size(n)) {
            int32 padding;
            int32 destsize = sizeofpointee(a1, &padding);
            if (n == destsize && padding != 0 && cg_inlineable_size(destsize+padding))
                args = mkArgList3(a1, a2, mkintconst(te_int, destsize+padding, 0));
            else if (n >= MEMCPYQUANTUM)
                return NOT_OPEN_COMPILABLE;
        }
        x1 = mk_expr2(s_fnap, type_(x), sim.memsetfn, args);
        return open_compilable(&x1, rsort, valneeded);
    }

/* At present the main thing that we do open compilation for is          */
/* _memcpy() and _memset() and then only if it has just 3 args, the      */
/* last of which is an integer with value >= 0 & a multiple of           */
/* alignof_struct (@@@ this last comment becoming out-of-date).          */
    if (bindsym_(exb_(fname)) == bindsym_(exb_(arg1_(sim.memcpyfn))) &&
        narg == 3 && h0_(a3) == s_integer &&
        (n = intval_(a3)) >= 0 &&
        (n < MEMCPYQUANTUM || cg_inlineable_size(n)))
    { VRegnum r1, r2;
      int32 align = alignofpointee(a1, 1);
      int32 al2 = alignofpointee(a2, 1);
      if (al2 < align) align = al2;
      if (align > MOVC_ALIGN_MAX) align = MOVC_ALIGN_MAX;
      if (n < MEMCPYQUANTUM || align >= MOVC_ALIGN_MIN)
      { int32 j_align = align & 1 ? J_ALIGN1 :
                        align & 2 ? J_ALIGN2 :
                        align & 4 ? J_ALIGN4 : J_ALIGN8;
/*
 * Here we break pay the penalty for having pretended that the ARM has
 * a block move instruction - we have to deny it at this stage.
 */
        {
/* ARM experiment with MOVC underway.  Copy of a single word is turned into
   LOAD+STORE, as easier for CSE to optimise away if appropriate.  Actually,
   I suppose that this is a good idea for all targets. Longer moves
   get turned into a MOVC (which destroys its argument registers if the move
   is longer than the number of registers I'm prepared to guarantee available).
   WD: should we do this for 2 words (doubles) too?
 */
          if (n >= 8) {
            procflags |= PROC_HASMOVC;
            spareregs += 2;
            r1 = cg_expr(a1);
            r2 = cg_expr(a2);
            spareregs -= 2;
            if (n <= 12)
            /* If there are enough spare registers, the expansion of
               MOVC needn't alter r1 and r2.  (2 dedicated registers,
               plus the one holding the source address).
             */
              emit(J_MOVC|j_align, r1, r2, n);   /* must NOT corrupt r1 */
            else {
              VRegnum r3 = fgetregister(INTREG);
              emitreg(J_MOVR, r3, GAP, r1);
              emit(J_MOVC|j_align, r3, r2, n);
              bfreeregister(r3);
            }
          }
          else
          { Binder *loadv = is_local_adcon(a2),
                   *storev = is_local_adcon(a1);
            r1 = GAP; r2 = GAP;
            spareregs += 2;
            if (n < MEMCPYQUANTUM) {
                VRegnum r3;
                if (storev == NULL ||
                    (mcrepofexpr((Expr *)storev) & MCR_SORT_MASK) < MCR_SORT_FLOATING)
                    r1 = cg_expr(a1);
                if (loadv == NULL ||
                    (mcrepofexpr((Expr *)loadv) & MCR_SORT_MASK) < MCR_SORT_FLOATING)
                    r2 = cg_expr(a2);
                spareregs -= 2;
                r3 = fgetregister(MEMCPYREG);
                while (--n >= 0)
                {   if (r2 != GAP)
                        emit(J_LDRBK|J_ALIGN1, r3, r2, n);
                    else
                        emitvk(J_LDRBVK|J_ALIGN1, r3, n, loadv);
                    if (r1 != GAP)
                        emit(J_STRBK|J_ALIGN1, r3, r1, n);
                    else
                        emitvk(J_STRBVK|J_ALIGN1, r3, n, storev);
                }
                bfreeregister(r3);
            } else if (n == sizeof_int && !valneeded) {
                Expr *e = mk_expr2(s_assign, te_int,
                                    mk_expr1(s_content, te_int,
                                      optimise0(mk_expr1(s_cast, ptrtotype_(te_int), a1))),
                                    mk_expr1(s_content, te_int,
                                      optimise0(mk_expr1(s_cast, ptrtotype_(te_int), a2))));
                cg_exprvoid(e);

            } else {
                VRegnum r3, r4;
                bool load_notvk = NO,
                     store_notvk = NO;
                if (storev != NULL) {
                    if ((mcrepofexpr((Expr *)storev) & MCR_SORT_MASK) < MCR_SORT_FLOATING)
                        store_notvk = YES;
                } else
                    r1 = cg_expr(a1);
                if (loadv != NULL) {
                    if ((mcrepofexpr((Expr *)loadv) & MCR_SORT_MASK) < MCR_SORT_FLOATING)
                        load_notvk = YES;
                } else
                    r2 = cg_expr(a2);
                spareregs -= 2;
                /* WD - experiment: generate result delay scheduled code */
                r3 = fgetregister(MEMCPYREG);
                r4 = fgetregister(MEMCPYREG);
                while ((n -= 2 * MEMCPYQUANTUM) >= 0)
                {   if (loadv == NULL) {
                        emit(J_memcpy(J_LDRK|J_ALIGN4), r3, r2, n);
                        emit(J_memcpy(J_LDRK|J_ALIGN4), r4, r2, n + MEMCPYQUANTUM);
                    } else if (load_notvk) {
                        emitbinder(J_LDRV|J_ALIGN4, r3, loadv);
                        emitbinder(J_LDRV|J_ALIGN4, r4, loadv);
                    } else {
                        emitvk(J_memcpy(J_LDRVK|J_ALIGN4), r3, n, loadv);
                        emitvk(J_memcpy(J_LDRVK|J_ALIGN4), r4, n + MEMCPYQUANTUM, loadv);
                    }
                    if (storev == NULL) {
                        emit(J_memcpy(J_STRK|J_ALIGN4), r3, r1, n);
                        emit(J_memcpy(J_STRK|J_ALIGN4), r4, r1, n + MEMCPYQUANTUM);
                    } else if (store_notvk) {
                        emitbinder(J_STRV|J_ALIGN4, r3, storev);
                        emitbinder(J_STRV|J_ALIGN4, r4, storev);
                    } else {
                        emitvk(J_memcpy(J_STRVK|J_ALIGN4), r3, n, storev);
                        emitvk(J_memcpy(J_STRVK|J_ALIGN4), r4, n + MEMCPYQUANTUM, storev);
                    }
                }
                bfreeregister(r4);
                n += 2 * MEMCPYQUANTUM;
                while ((n -= MEMCPYQUANTUM) >= 0)
                {   if (loadv == NULL)
                        emit(J_memcpy(J_LDRK|J_ALIGN4), r3, r2, n);
                    else if (load_notvk)
                        emitbinder(J_LDRV|J_ALIGN4, r3, loadv);
                    else
                        emitvk(J_memcpy(J_LDRVK|J_ALIGN4), r3, n, loadv);

                    if (storev == NULL)
                        emit(J_memcpy(J_STRK|J_ALIGN4), r3, r1, n);
                    else if (store_notvk)
                        emitbinder(J_STRV|J_ALIGN4, r3, storev);
                    else
                        emitvk(J_memcpy(J_STRVK|J_ALIGN4), r3, n, storev);
                }
                bfreeregister(r3);
            }
          }
        }
        bfreeregister(r2);
        return r1;
      }
    }
/*
 * The following code does open compilation of "_memset" in the case
 * were there are 3 args and the second and third args are
 * zero and divisible by alignof_struct exactly.
 */
    if (bindsym_(exb_(fname)) == bindsym_(exb_(arg1_(sim.memsetfn))) &&
        narg == 3 &&
        h0_(a2) == s_integer && intval_(a2) == 0 &&
        h0_(a3) == s_integer &&
        (n = intval_(a3)) >= 0 &&
        (n < MEMCPYQUANTUM || cg_inlineable_size(n)))
    { VRegnum r1;
        /* @@@ currently _memset/J_CLRC implies at least J_ALIGN4.      */
      int32 align = alignofpointee(a1, 1);
      if (n < MEMCPYQUANTUM || !(align & 3))
      { VRegnum r2;
#if defined (TARGET_HAS_BLOCKMOVE) && !defined(TARGET_IS_ARM)
        if (n >= MEMCPYQUANTUM) {
          spareregs += 1;                 /* duh?                         */
          r1 = cg_expr(a1);
          spareregs -= 1;
          emit(J_CLRC|J_ALIGN4, r1, GAP, n);      /* must NOT corrupt r1? */
        }
#else  /* TARGET_HAS_BLOCKMOVE */
/* For very short memset's I just do STORE sequences. For longer ones  */
/* I synthesize a loop.                                                */
#ifdef TARGET_IS_ARM
        if (n >= 8) {
          procflags |= PROC_HASMOVC;
          r1 = cg_expr(a1);
          if (n == 8)
            emit(J_CLRC|J_ALIGN4, r1, GAP, n);  /* must NOT corrupt r1  */
          else {
            r2 = fgetregister(INTREG);
            emitreg(J_MOVR, r2, GAP, r1);
            emit(J_CLRC|J_ALIGN4, r2, GAP, n);
            bfreeregister(r2);
          }
        }
#else /* TARGET_IS_ARM */
        if (n >= 10*MEMCPYQUANTUM)
        {
            LabelNumber *ll = nextlabel();
            VRegnum r3;
            spareregs += 2;
            r1 = cg_expr(a1);
            r2 = MEMCPYREG==DBLREG ? cg_loadfpzero(DBLREG,0) : cg_expr(a2);
            spareregs -= 2;
            r3 = fgetregister(INTREG);
            emit(J_MOVK, r3, GAP, n-MEMCPYQUANTUM);
#ifdef TARGET_LACKS_RR_STORE
                emit(J_ADDK, r1, r1, n);
#endif
            start_new_basic_block(ll);
#ifdef TARGET_LACKS_RR_STORE
                emit(J_SUBK, r1, r1, MEMCPYQUANTUM);
                emit(J_memcpy(J_STRK|J_ALIGN4), r2, r1, 0);
#else
                emitreg(J_memcpy(J_STRR|J_ALIGN4), r2, r1, r3);
#endif
            emit(J_SUBK, r3, r3, MEMCPYQUANTUM);
            emit(J_CMPK + Q_GE, GAP, r3, 0);
            emitbranch(J_B + Q_GE, ll);
            bfreeregister(r3);
            bfreeregister(r2);
        }
#endif
#endif  /* TARGET_HAS_BLOCKMOVE */
        else
        {   Binder *storev = is_local_adcon(a1);
            r1 = GAP;
            spareregs += 2;
            if (n < MEMCPYQUANTUM) {
                if (storev == NULL ||
                    (mcrepofexpr((Expr *)storev) & MCR_SORT_MASK) < MCR_SORT_FLOATING)
                    r1 = cg_expr(a1);
                r2 = cg_expr(a2);
                spareregs -= 2;
                while (--n >= 0) {
                    if (r1 != GAP)
                        emit(J_STRBK|J_ALIGN1, r2, r1, n);
                    else
                        emitvk(J_STRBVK|J_ALIGN1, r2, n, storev);
                }
            } else {
                bool store_notvk = NO;
                if (storev != NULL) {
                    if ((mcrepofexpr((Expr *)storev) & MCR_SORT_MASK) < MCR_SORT_FLOATING)
                        store_notvk = YES;
                } else
                    r1 = cg_expr(a1);
                r2 = MEMCPYREG==DBLREG && !store_notvk ? cg_loadfpzero(DBLREG,0) :
                                                         cg_expr(a2);
                spareregs -= 2;
                while ((n -= MEMCPYQUANTUM) >= 0) {
                    if (storev == NULL)
                        emit(J_memcpy(J_STRK|J_ALIGN4), r2, r1, n);
                    else if (store_notvk)
                        emitbinder(J_STRV|J_ALIGN4, r2, storev);
                    else
                        emitvk(J_memcpy(J_STRVK|J_ALIGN4), r2, n, storev);
                }
            }
            bfreeregister(r2);
        }
        return r1;
      }
    }
    if (bindsym_(exb_(fname)) == bindsym_(exb_(arg1_(sim.memcpyfn)))) {
      /* _memcpy which has failed to be expanded in-line (length or alignment
         wrong - can only happen with __packed structs).
       */
        *xp = mk_expr2(s_fnap, type_(x), sim.realmemcpyfn, (Expr *)exprfnargs_(x));
        return NOT_OPEN_COMPILABLE;
    }
    if (bindsym_(exb_(fname)) == bindsym_(exb_(arg1_(sim.memsetfn)))) {
      /* _memset which has failed to be expanded in-line (see above) */
        *xp = mk_expr2(s_fnap, type_(x), sim.realmemsetfn, (Expr *)exprfnargs_(x));
        return NOT_OPEN_COMPILABLE;
    }
    if (bindsym_(exb_(fname)) == bindsym_(exb_(arg1_(sim.inserted_word)))
        && narg == 1 && h0_(a1) == s_integer)
    {
/* _word(nnn) will plant nnn in the code - for EXPERT/lunatic use only! */
        emit(J_WORD, GAP, GAP, intval_(a1));
        return R_A1; /* /* Resultregister wanted here? */
    }

    if ((bindstg_(exb_(fname)) & bitofstg_(s_inline)) &&
        !(var_cc_private_flags & 8192L)) {
        Expr *structresult = NULL;
        ExprList *args = exprfnargs_(x);
        if (returnsstructinregs_t(bindtype_(exb_(fname))))
            if (h0_(x) != s_fnap) {
                structresult = exprcar_(args);
                args = cdr_(args);
            }
        return TryInlineRestore(exb_(fname), args, structresult, rsort, valneeded);
    }

    return NOT_OPEN_COMPILABLE;
}

/* jopcode generation for binding vars and args ...                         */

static Binder *gentempvar(TypeExpr *t, VRegnum r)
{   /* like gentempbinder, but pretends set_local_vregister called */
    /* bindaddr_() is not set at this point, but will get filled   */
    /* in later (by cg_bindlist or explicit code) if it might be   */
    /* needed. There will be a syserr if an attempt is made to     */
    /* reference a spilt temporary that has not been completed     */
    /* properly.                                                   */
    Binder *bb = gentempbinder(t);
    bindxx_(bb) = r;
    bindmcrep_(bb) = mcrepofexpr((Expr *)bb);
    return bb;
}

static TypeExpr *teofsort(RegSort sort)
{   switch (sort)
    {   case FLTREG: return te_float;
        case DBLREG: return te_double;
#ifdef ADDRESS_REG_STUFF
        case ADDRREG:return te_int;
#endif
        default:     return te_int;
    }
}

Binder *gentempvarofsort(RegSort sort)
{
    return gentempvar(teofsort(sort), vregister(sort));
}

static Binder *gentempvarwithname(TypeExpr *t, VRegnum r, char *name)
{   /* As gentempvar(), but prescribes the name to be given to the */
    /* generated binder                                            */
    Binder *bb = gentempbinderwithname(t, name);
    bindxx_(bb) = r;
    bindmcrep_(bb) = mcrepofexpr((Expr *)bb);
    return bb;
}

Binder *gentempvarofsortwithname(RegSort sort, char *name)
{
    return gentempvarwithname(teofsort(sort), vregister(sort), name);
}

static void set_local_vregister(Binder *b, int32 rep, bool isarg)
{   VRegnum r = GAP;
    int32 mode = rep >> MCR_SORT_SHIFT, len = rep & MCR_SIZE_MASK;
    if (isvolatile_type(bindtype_(b)))
    {   /* treat volatile locals as 'address taken' for setjmp.             */
        bindstg_(b) = (bindstg_(b) & ~bitofstg_(s_register)) | b_spilt;
    }
    if (!(bindstg_(b) & b_spilt))
    {   /* try to put in a register */
        if (mode == 0 || mode == 1)   /* ADENART, was "&& len<=4".    */
        {
#ifdef ADDRESS_REG_STUFF
           TypeExpr *t = princtype(bindtype_(b));
           r = vregister(h0_(t) == t_content || h0_(t) == t_subscript ?
                              ADDRREG : INTREG);
#else
           r = vregister(INTREG);
#endif
/* J_INIT never generates code: it can be thought of as meaning          */
/* "load this register with an undefined value" and it helps register    */
/* allocation in the case that the user seems not to initialise the      */
/* variable properly. E.g. it controls the trouble I get in code like:   */
/*    { int x; <thing not using x>; if (tautology) x = 1; <use x>; }     */
            if (!isarg) emitbinder(J_INIT, r, b);
        }
        else if (mode == 2 && len==4)
        {   r = vregister(FLTREG);
            if (!isarg) emitbinder(J_INITF, r, b);
        }
        else if (mode == 2 && len==8)
        {   r = vregister(DBLREG);
            if (!isarg) emitbinder(J_INITD, r, b);
        }
    }
    bindxx_(b) = r;
    bindmcrep_(b) = rep;
    if ((bindstg_(b) & bitofstg_(s_register)) &&
/* @@@ LDS 23Aug89 - Temporary: to be rationalised soon. Sorry */
        !(var_cc_private_flags & 1L))
    {   regvar_binders = mkBindList(regvar_binders, b);
        /* discouragement of spilling now in regalloc */
    }
    else local_binders = mkBindList(local_binders, b);
}

static void init_slave_reg(
    Binder *b, int32 argno, int32 nfltregwords, int32 nintregargs)
/* b is the binder for a potentially registered argument variable. Load  */
/* its initial value from the place where the relevant argument was      */
/* passed - register a1 to a4 for simple cases and the stack otherwise.  */
/* Oct 92: this code is in need of re-parameterisation.                  */
{
    /* bindaddr_(b) is known to be BINDADDR_ARG.                        */
    int32 addr = bindaddr_(b) & ~BINDADDR_MASK;
    int32 n = addr / alignof_toplevel_auto;
    VRegnum v = bindxx_(b);
    if (v != GAP)
    {   int32 ni = n - nfltregwords;
        int32 ir = ni;
        RegSort rsort = vregsort(v);
#ifdef TARGET_STRUCT_RESULT_REGISTER
        if (b == result_variable)
            emitreg(J_MOVR, v, GAP, TARGET_STRUCT_RESULT_REGISTER);
        else
#endif
        if (isintregtype_(rsort))
        {
/* @@@ The following lines need tidying (remember adenart stops         */
/* collecting args when it sees a struct (parameterise!)).              */
/* @@@ Are the other NARGREGS's below OK too?                           */
            if (0 <= ni && ni < nintregargs)
              emitreg(J_MOVR, v, GAP, R_P1+ir);
            else emitbinder(J_LDRV1|J_ALIGN4V, v, b);
        }
        else if (rsort == FLTREG)
/* This case does not currently happen in standard Norcroft compilers,  */
/* since 'float' args are passed as double and callee-narrowed.         */
/* J_MOVIFR has to copy a bit-pattern from an integer register into one */
/* of the FP registers.                                                 */
        {   if (ni < 0)
              emitreg(J_MOVFR, v, GAP, R_FP1+argno);
            else if (ir < NARGREGS)
#ifdef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
              emitreg(J_MOVFR, v, GAP, R_P1+ir);
#else
              emitreg(J_MOVIFR, v, GAP, R_P1+ir);
#endif
            else
                emitbinder(J_LDRFV1|J_ALIGN4V, v, b);
        }
        else
/* If I have a double-precision arg the value is passed in two integers  */
/* and here I must be prepared to move it into a doubleprecision FP      */
/* register.                                                             */
        {   if (ni < 0)
/* The following line assumes FPREGARGS are arranged to appear first...  */
              emitreg(J_MOVDR, v, GAP, R_FP1+argno);
            else
            if (ir < NARGREGS-1)
                emitreg(J_MOVIDR, v, R_P1+ir, R_P1+ir+1);
            else
/* If a floating point arg straddles the boundary between where args are */
/* passed in registers & where they come on the stack I know that there  */
/* are at least 5 words of args, so if I suppress the leaf-procedure     */
/* optimisation I know that the args will get written to the stack as    */
/* contiguous words. Then I can load the FP value easily.                */
            {   if (ir == NARGREGS-1) procflags |= PROC_ARGPUSH;
                emitbinder(J_LDRDV1|J_ALIGN8, v, b);
            }
        }
    }
}

static void cg_bindlist(SynBindList *x, bool initflag)
{   /* initflag is 1 if J_INIT is not needed due to later explicit init. */
    BindList *new_binders = active_binders;
    for (; x!=NULL; x = x->bindlistcdr)
    {   Binder *b = x->bindlistcar;
        if (bindstg_(b) & bitofstg_(s_auto))        /* ignore statics    */
        /* N.B. register vars must also have auto bit set                */
        {   int32 rep = mcrepofexpr((Expr *)b);
            set_local_vregister(b, rep, initflag);
            new_binders = mkBindList(new_binders, b);
            b->bindaddr.bl = new_binders;
            bindstg_(b) |= b_bindaddrlist;
/* the next 3 line calculation should be done after regalloc, not here */
            current_stackdepth = padtomcrep(current_stackdepth, rep) +
                                 padsize(rep & MCR_SIZE_MASK, alignof_toplevel_auto);
            if (current_stackdepth > greatest_stackdepth)
                greatest_stackdepth = current_stackdepth;
        }
    }
    emitsetsp(J_SETSPENV, new_binders);
}

static int32 cg_bindargs_size(BindList *args)
{   int32 argoff = 0;
    for (; args!=NULL; args=args->bindlistcdr)
    {   Binder *b = args->bindlistcar;
        int32 rep = mcrepofexpr((Expr *)b);
/* Things in an argument list can only have s_auto storage class     */
        if (!(bindstg_(b) & bitofstg_(s_auto))) syserr(syserr_nonauto_arg);
        argoff = padtomcrep(argoff, rep);
        set_local_vregister(b, rep, 1);
        bindaddr_(b) = argoff | BINDADDR_ARG;
        argoff += padsize(rep & MCR_SIZE_MASK, alignof_toplevel_auto);
    }
    return argoff;
}


/* One might worry here about functions that specify their formals with  */
/* a type such as char, short or float.  For language independence sem.c */
/* arranges that such things never occur by generating an explicit       */
/* narrowing assignment in this case.                                    */

static int32 cg_bindargs(BindList *args, bool ellipsis)
/* Ellipsis is true if this function was defined with a '...' at the end */
/* of the list of formal pars it should accept.                          */
/* Returns number of argwords for possible use by codeseg_function_name(). */
/* Note that on some machines (e.g. the 88000) very strange things have to */
/* be done to support va_args (i.e. if '...' is indicated).  Also in some  */
/* cases integer, floating and structure args may be passed in different   */
/* ways.                                                                   */
{
    BindList *x;
    int32 argoff, lyingargwords;
    int32 nfltregargs = 0, nintregargs = 0, nfltregwords = 0;
    int32 argno = 0;

/* If ANY argument has its address taken I mark ALL arguments as having  */
/* their address taken, unless the user has declared them as registers.  */
    for (x = args; x!=NULL; x=x->bindlistcdr)
    {   Binder *b = x->bindlistcar;
        if (bindstg_(b) & b_addrof)
        {   for (x = args; x!=NULL; x=x->bindlistcdr)
            {   b = x->bindlistcar;
                if (!(bindstg_(b) & bitofstg_(s_register)))
                    bindstg_(b) |= b_addrof;
            }
            break;
        }
    }
#ifdef TARGET_FP_ARGS_IN_FP_REGS
    if ((config & CONFIG_FPREGARGS)) {
        BindList *intargs = NULL, **intargp = &intargs,
                 *fltregargs = NULL, **fltregargp = &fltregargs;
        for (x = args; x != NULL; x = x->bindlistcdr) {
            Binder *b = x->bindlistcar;
            BindList *newbl = mkBindList(NULL, b);
            int32 rep = mcrepofexpr((Expr *)b);
            if ((rep & MCR_SORT_MASK) == MCR_SORT_FLOATING
                && nfltregargs < NFLTARGREGS
               )
            {   int32 bytes = rep & MCR_SIZE_MASK;
                nfltregwords += (bytes > alignof_toplevel_auto ? bytes : alignof_toplevel_auto) /
                                sizeof_int;
                nfltregargs++,
                *fltregargp = newbl, fltregargp = &newbl->bindlistcdr;
            } else
                *intargp = newbl, intargp = &newbl->bindlistcdr;
        }
        if (intargs != NULL) *fltregargp = intargs;
        args = fltregargs;
        argoff = cg_bindargs_size(args);
        nintregargs = intargs == NULL ? 0 :
            (argoff - (bindaddr_(intargs->bindlistcar) & ~BINDADDR_MASK))/4;
    } else
#endif /* TARGET_FP_ARGS_IN_FP_REGS */
    {   argoff = cg_bindargs_size(args),
        nintregargs = argoff/alignof_toplevel_auto;
    }

    currentfunction.fltargwords = nfltregwords;
    if (nintregargs > NARGREGS) nintregargs = NARGREGS;
    max_argsize = argoff;
#ifdef TARGET_STRUCT_RESULT_REGISTER
    if (result_variable != NULL)
    {   int32 rep = mcrepofexpr((Expr *)result_variable);
        set_local_vregister(result_variable, rep, 1);
/*
 * The bindaddr field would be inspected in init_slave_reg, but that
 * takes special action on result_variable so I can put junk in here.
 */
        bindaddr_(result_variable) = BINDADDR_ARG;
    }
#endif
    /* Note that with '...' a cautious entry sequence is needed:          */
    /* it suffices to tell the back-end that we need many arg words.      */
    /* The value 0x7fff is chosen for backwards compatibility and easy    */
    /* visibility in masks.  It is subject to change and backends should  */
    /* check for a value outwith 0..255.                                  */
    lyingargwords = ellipsis ? K_ARGWORDMASK : argoff/alignof_toplevel_auto;
    /* The operand of J_ENTER is used to determine addressing of args     */
    /* on machines such as the ARM.                                       */
    emit(J_ENTER, GAP, GAP,
        /* note the first zero is dubious -- rely on regalloc.c not       */
        /* using it!                                                      */
        k_argdesc_(lyingargwords, 0, nintregargs, nfltregargs,
        (int32)currentfunction.nresultregs, ellipsis ? K_VAFUNC : 0));
#ifdef TARGET_STRUCT_RESULT_REGISTER
    if (result_variable != NULL) init_slave_reg(result_variable, 0, 0, 0);
#endif
    for (x=args; x!=NULL; x=x->bindlistcdr)
        init_slave_reg(x->bindlistcar, argno++, nfltregwords, nintregargs);
    active_binders = NULL;
    current_stackdepth = greatest_stackdepth = 0;
    start_new_basic_block(nextlabel());
    return lyingargwords;
}

static void loadresultsfrombinder(Binder *x) {
    int32 n;
    for (n = 0; n < currentfunction.nresultregs; n++)
        emitvk(J_memcpy(J_LDRVK|J_ALIGN4), V_Presultreg(INTREG)+n, n*MEMCPYQUANTUM, x);
}

static void cg_return(Expr *x, bool implicitinvaluefn)
{
    LabelNumber *retlab = (implicitinvaluefn ? RetImplLab : RetVoidLab);
    if (x!=0)
    {   int32 mcrep = mcrepofexpr(x);
/* Structure results are massaged here to give an assignment via a       */
/* special variable.                                                     */
/* @@@ This all need updating for C++, but in the meantime note that     */
/* CPLUSPLUS constructors in return statements give a non-omitted        */
/* return expr of VOID type.                                             */
        if ((mcrep >> MCR_SORT_SHIFT) == 3)
        {   TypeExpr *t = typeofexpr(x);
            if (currentfunction.nresultregs > 0) {
                if (h0_(x) == s_fnap && returnsstructinregs(arg1_(x))) {
                    VRegnum r = cg_expr(mk_expr2(s_fnapstructvoid, te_void, arg1_(x),
                                                 mkArg(exprfnargs_(x), NULL)));
                    if (r != R_A1 && r != GAP) {
                        int n;
                        for (n = 0; n < currentfunction.nresultregs; n++)
                            emitreg(J_MOVR, R_A1+n, GAP, r+n);
                    }

                } else if (h0_(x) == s_binder && (bindstg_(exb_(x)) & bitofstg_(s_auto)))
                    loadresultsfrombinder(exb_(x));
                else {
                    if (h0_(x) != s_fnap) {
                        t = ptrtotype_(t);
                        x = cg_optimise0(mk_expr1(s_addrof, t, x));
                    }
                    if (h0_(t) != t_content) {
                        BindList *sl = active_binders;
                        int32 d = current_stackdepth;
                        Binder *temp = gentempbinder(t);
                        cg_bindlist(mkSynBindList(0, temp), 0);
                        x = mk_expr2(s_assign, t, (Expr *)temp, x);
                        cg_exprvoid(x);
                        loadresultsfrombinder(temp);
                        emitsetsp(J_SETSPENV, sl);
                        current_stackdepth = d;
                    } else {
                        VRegnum r = cg_expr(x);
                        int32 n;
                        for (n = 0; n < currentfunction.nresultregs; n++)
                            emit(J_memcpy(J_LDRK|J_ALIGN4), V_Presultreg(INTREG)+n, r,
                                 n * MEMCPYQUANTUM);
                        bfreeregister(r);
                    }
                }
                retlab = RetIntLab;
            } else {
                if (result_variable==NULL) syserr(syserr_struct_result);
/* Return the result of a struct-returning fn. The result expn is a var, */
/* a fn call, or (let v in expn) if expn involves a struct-returning fn. */
                if (h0_(x) == s_fnap)
/* return f(...), so use the reult variable directly to get whizzy code. */
                    cg_exprvoid(mk_expr2(s_fnapstruct, te_void, arg1_(x),
                                         mkArg(exprfnargs_(x), result_variable)));
                else if (h0_(x) == s_let)
/* Here we have a return (expn involving a struct-fn call). It's a pity */
/* that multiple such things can't be commoned up to share a single     */
/* result copy operation. The problem is the scope of the binder in the */
/* let, absence of return expressions, and failure to distribute the    */
/* missing return expressions through the tree appropriately (Sigh).    */
                {   arg2_(x) = mk_expr2(s_assign, t,
                        mk_expr1(s_content, t, (Expr *)result_variable),
                        arg2_(x));
                    cg_exprvoid(x);
                } else
/* There is some hope of commoning up the result copies, for example in */
/* return i ? x : y, where x and y are binders. Do this by using a ptr  */
/* to the result value until a common tail of code in which *res = *val */
                {   TypeExpr *pt = ptrtotype_(t);
                    cg_exprvoid(
                        mk_expr2(s_assign, pt, (Expr *)result_temporary,
/* @@@ LDS 22-Sep-89: use of optimise0() here is iffy, and anticipates  */
/* the evolution of simplify into a properly specified tree transformer */
                            cg_optimise0(mk_expr1(s_addrof, pt, x))));
                    if (structretlab == NOTALABEL)
                    {   structretlab = nextlabel();
                        start_new_basic_block(structretlab);
                        cg_exprvoid(mk_expr2(s_assign, t,
                            mk_expr1(s_content, t, (Expr *)result_variable),
                            mk_expr1(s_content, t, (Expr *)result_temporary)));
                    }
                    else
                    {   emitsetspgoto(active_binders, structretlab);
                        emitbranch(J_B, structretlab);
                        return;
                    }
                }
            }
        }
        else
        {   int32 mcmode = mcrep >> MCR_SORT_SHIFT;
            RegSort rsort =
                 mcmode!=2 ? INTREG : (mcrep==0x02000004 ? FLTREG : DBLREG);
            /* The next line takes care of compiling 'correct' code for */
            /* void f() { return g();}                                  */
            /* It now deals with C++ class returning functions (syn.c)  */
            if ((mcrep & MCR_SIZE_MASK) == 0)
            {   cg_exprvoid(x);
                retlab = RetVoidLab;
            }
            else
            {   VRegnum r = cg_expr(x);
                emitreg(floatyop(rsort, J_MOVR, J_MOVFR, J_MOVDR),
                        V_Presultreg(rsort), GAP, r);
                bfreeregister(r);
                retlab = (rsort == DBLREG ? RetDbleLab :
                          rsort == FLTREG ? RetFloatLab : RetIntLab);
            }
        }
    }
    else if (defining_main)
    {
        /* Within main() any return; is treated as return 0; - this   */
        /* is done because the value returned by main() is used as    */
        /* a success code by the library, but on some other C systems */
        /* the value of main() is irrelevant...                       */
        /* Users who go                                               */
        /*      struct foo main(int argc, char *argv[]) { ... }       */
        /* are not protected here!                                    */
        /* AM: unfortunately this stops implicit return warnings...   */
        emit(J_MOVK, V_Presultreg(INTREG), GAP, 0);
        retlab = RetIntLab;
    }
    emitsetspenv(active_binders, (BindList *)NULL);
    /* Not emitsetsp, because we don't want to allow it to be optimised out */
    /* See comments in the CSE code for the need for a SETSP just before    */
    /* every RETURN.  function modifycode()....                             */
    /* Do not optimise this away lightly!                                   */
    /* Note also that 'active_binders = NULL;' is, in some sense, missed    */
    /* out here, but because of the emitbranch() this is NECESSARY!         */

    emitbranch(J_B, retlab);
}

static bool SimpleTest(Expr const *test) {
    while (h0_(test) == s_boolnot) test = arg1_(test);
    return isrelational_(h0_(test));
    /* (x) has already been turned into (x != 0) */
}

static void cg_loop(Expr *init, Expr *pretest, Expr *step, Cmd *body,
                    Expr *posttest)
{
/* Here I deal with all loops. Many messy things are going on!           */
    struct LoopInfo oloopinfo;
    bool once = at_least_once(init, pretest);
/* A large amount of status belongs with loop constructs, and gets saved */
/* here so that it can be restored at the end of compiling the loop.     */
    oloopinfo = loopinfo;
    loopinfo.breaklab = loopinfo.contlab = 0;
    loopinfo.binders = active_binders;

    if (init != 0) cg_exprvoid(init);  /* the initialiser (if any)       */

    cg_count(cmdfileline_(cg_current_cmd));

/* The variable once has been set true if, on the basis if looking at    */
/* the initialiser and the pretest I can tell that the loop will be      */
/* traversed at least once. In that case I will use the pretest as a     */
/* posttest for better generated code.                                   */

    if (!usrdbg(DBG_LINE) || (pretest == 0 && step == 0))
    {   LabelNumber *bodylab = nextlabel(), *steplab = 0;
        if (!once) {
             if (body != NULL && h0_(body) != s_continue &&
                 SimpleTest(pretest) && !(config & CONFIG_OPTIMISE_SPACE))
                 cg_test(pretest, NO, loopinfo.breaklab = nextlabel());
             else
                 emitbranch(J_B, steplab = nextlabel());
        }
        start_new_basic_block(bodylab);
        if (body != NULL)
        {   cg_count(cmdfileline_(body));
            cg_cmd(body);
        }
        if (loopinfo.contlab != 0) start_new_basic_block(loopinfo.contlab);
        if (step != 0) cg_exprvoid(step);
        if (steplab != 0) start_new_basic_block(steplab);

/* When cg_loop is called there can NEVER be both a pretest and a post-  */
/* test specified. Here I put out the (conditional) branch back up to    */
/* the top of the loop.                                                  */
        cg_count(cmdfileline_(cg_current_cmd));
        if (pretest != 0) cg_test(pretest, YES, bodylab);
        else if (posttest != 0) cg_test(posttest, YES, bodylab);
        else emitbranch(J_B, bodylab);
    } else {
        LabelNumber *steplab, *bodylab = nextlabel();
        LabelNumber *testlab = pretest == 0 ? 0 : nextlabel();
        loopinfo.contlab = steplab = (step != 0) ? nextlabel() : testlab;
        if (pretest != 0)
        {   start_new_basic_block(testlab);
            loopinfo.breaklab = nextlabel();
            if (step == 0)
                cg_test(pretest, NO, loopinfo.breaklab);
            else {
                cg_test(pretest, YES, bodylab);
                emitbranch(J_B, loopinfo.breaklab);
            }
        }
        if (step != 0) {
            if (pretest == 0) emitbranch(J_B, bodylab);
            start_new_basic_block(steplab);
            if (exprfileline_(step) != 0)
                emitfl(J_INFOLINE, *exprfileline_(step));
            cg_exprvoid(step);
            if (testlab != 0) emitbranch(J_B, testlab);
        }
        start_new_basic_block(bodylab);
        if (body != NULL)
        {   cg_count(cmdfileline_(body));
            cg_cmd(body);
        }
        cg_count(cmdfileline_(cg_current_cmd));
        if (posttest != 0)
            cg_test(posttest, YES, steplab);
        else
            emitbranch(J_B, steplab);
    }
    if (loopinfo.breaklab != 0) start_new_basic_block(loopinfo.breaklab);
    loopinfo = oloopinfo;
}

static int32 dense_case_table(CasePair *v, int32 ncases)
{
/* This function provides a criterion for selection of a test-and-branch */
/* or a jump-table implementation of a case statement. Note that it is   */
/* necessary to be a little careful about arithmetic overflow in this    */
/* code, and that the constants here will need tuning for the target     */
/* computer's instruction timing characteristics.                        */
    int32 low_value = v[0].caseval,
          high_value = v[ncases-1].caseval;
    int32 halfspan = high_value/2 - low_value/2;     /* cannot overflow  */
#ifdef TARGET_SWITCH_isdense
    if (TARGET_SWITCH_isdense(ncases,halfspan)) return 1;   /* tuneable  */
#else
    if (halfspan < ncases &&
            /* The next line reflects SUB required on many targets.     */
            /* Should the test be on span, not ncases?                  */
            (ncases > 4 || ncases==4 && low_value==0))
        return 1;            /* good try? */
    {   int32 shift; int32 val = ~low_value;
        int32 n = ncases;
        while (--n != 0) val &= ~v[n].caseval;
        val += 1;
        shift = logbase2(val & (-val));
        if (shift > 1) {
            if (low_value < 0 && high_value > 0) {
                unsigned32 uhigh;
                for (n = 0; n < ncases; n++)
                    if (v[n].caseval >= 0) break;
                uhigh = just32bits_(v[n-1].caseval);
                if (uhigh >> (shift+1) < (uint32)ncases &&
                    ncases >= 4+3)
                    return shift+1+J_UNSIGNED;
            }
            if ((halfspan >> shift) < ncases &&
                /* 3 here reflects the required test that bottom <shift>     */
                /* bits are zero                                             */
                (ncases > 4+3 || (ncases == 4+3 && low_value == 0)))
                return shift+1;
        }
    }
#endif
    return 0;
}

static void linear_casebranch(VRegnum r, CasePair *v, int32 ncases,
                              LabelNumber *defaultlab)
{
    while (--ncases >= 0)
    {   emit(J_CMPK + Q_EQ, GAP, r, v->caseval);
        emitbranch(J_B + Q_EQ, v->caselab);
        v++;
    }
    emitbranch(J_B, defaultlab);
}

static void table_casebranch(VRegnum r, CasePair *v, int32 ncases,
                             LabelNumber *defaultlab, int32 shift)
{
    int32 m, n, i, size;
    LabelNumber **table;
    VRegnum r1 = r;
    int32 shtype = J_SIGNED;
    int32 casex = 0;
    if (shift & J_UNSIGNED) {
        shtype = J_UNSIGNED; shift &= ~J_UNSIGNED;
        for (; casex < ncases; casex++)
            if (v[casex].caseval >= 0) break;
        m = 0, n = just32bits_((unsigned32)v[casex-1].caseval) >> (shift-1);
    } else {
        m = v[0].caseval, n = v[ncases-1].caseval;
        if (shift > 1)
        {   m = signed_rightshift_(m, (shift-1));
            n = signed_rightshift_(n, (shift-1));
        }
    }
    size = n - m + 1;
    if (m == 1)
    { /* Avoid a subtraction (and maybe need for an extra register) by
         making the switch table one larger
       */
        size++;
        m = 0;
    }
    table = (LabelNumber **) BindAlloc((size+1) * sizeof(LabelNumber *));
    if (m != 0 || shift > 1)
    {   VRegnum r2 = r;
        r1 = fgetregister(INTREG);
        if (shift > 1)
        {   emit(J_ANDK, r1, r, (1L << (shift-1)) - 1);
            emit(J_CMPK + Q_NE, GAP, r1, 0);
            emitbranch(J_B + Q_NE, defaultlab);
            bfreeregister(r1);
            r1 = fgetregister(INTREG);
            emit(J_SHRK + shtype, r1, r, shift-1);
            r2 = r1;
        }
        if (m != 0) emit(J_SUBK, r1, r2, m);
    }
    table[0] = defaultlab;
    for (i = 0; i < size; i++)
       if (just32bits_((i+m) << (shift-1)) == just32bits_(v[casex].caseval)) {
           table[i+1] = v[casex].caselab;
           /* arrange wraparound for unsigned case */
           if (++casex == ncases) casex = 0;
       } else
           table[i+1] = defaultlab;

    /* It is important that literals are not generated so as to break up */
    /* the branch table that follows - J_CASEBRANCH requests this.       */
    /* Type check kluge in the next line...                              */
    emitcasebranch(J_CASEBRANCH, r1, table, size + 1);
    if (r1 != r) bfreeregister(r1);
}

static void casebranch(VRegnum r, CasePair *v, int32 ncases,
                       LabelNumber *defaultlab)
{
    if (ncases<5) linear_casebranch(r, v, ncases, defaultlab);
    else {
        int32 n = dense_case_table(v, ncases);
        if (n != 0)
            table_casebranch(r, v, ncases, defaultlab, n);
        else
        {   int32 mid = ncases/2;
            LabelNumber *l1 = nextlabel();
#ifdef TARGET_LACKS_3WAY_COMPARE
            emit(J_CMPK + Q_GE, GAP, r, v[mid].caseval);
            emitbranch(J_B + Q_GE, l1);
            casebranch(r, v, mid, defaultlab);
            start_new_basic_block(l1);
            casebranch(r, &v[mid], ncases-mid, defaultlab);
#else
/*
 * CSE is told here not to move things which might set the condition code
 * between the two conditional branches below by setting BLKCCLIVE.
 */
            /* The following line is a nasty hack.                          */
            /* It is also not always optimal on such machines.              */
            emit(J_CMPK + Q_UKN, GAP, r, v[mid].caseval);
            blkflags_(bottom_block) |= BLKCCEXPORTED;
            emitbranch(J_B + Q_EQ, v[mid].caselab);
            blkflags_(bottom_block) |= BLKCCLIVE;
            emitbranch(J_B + Q_GT, l1);
            casebranch(r, v, mid, defaultlab);
            start_new_basic_block(l1);
            casebranch(r, &v[mid+1], ncases-mid-1, defaultlab);
#endif
        }
    }
}

static void cg_case_or_default(LabelNumber *l1)
/* Produce a label for a case or default label in a switch.  Note that in   */
/* general we must jump round a stack adjusting jopcode, but to save jop    */
/* and block header space we test for the common case.                      */
{   if (active_binders == switchinfo.binders)
        start_new_basic_block(l1);
/* the next few lines of code take care of 'case's within blocks with       */
/* declarations:  switch(x) { case 1: { int v[10]; case 2: foo(); }}        */
    else
    {   LabelNumber *l = nextlabel();
        BindList *bl = active_binders;
        emitbranch(J_B, l);
        start_basic_block_at_level(l1, active_binders = switchinfo.binders);
/* Amazing amount of fiddling about in case ICODE section may overflow. */
        emitsetsp(J_SETSPENV, bl);
        start_new_basic_block(l);
    }
    cg_count(cmdfileline_(cg_current_cmd));
}

static VRegnum cg_loadconst(int32 n, Expr *e)
{   /* void e if !=NULL and return n - used for things like f()*0     */
    VRegnum r;
    if (e) (void)cg_exprvoid(e);
#ifdef TARGET_HAS_CONST_R_ZERO
    if (n == 0) return R_ZERO;
#endif
    emit(J_MOVK, r=fgetregister(INTREG), GAP, n);
    return r;
}

static void cg_cond1(Expr *e, bool valneeded, VRegnum targetreg,
                     LabelNumber *l3, bool structload)
{   for (; h0_(e)==s_comma; e = arg2_(e))
        cg_exprvoid(arg1_(e));

    if (h0_(e)==s_cond)
        (void)cg_cond(e, valneeded, targetreg, l3, structload);
    else if (!valneeded)
         bfreeregister(cg_expr1(e, valneeded));
    else
    {   if (structload)
        {   VRegnum r;
            emitreg(J_MOVR, targetreg, GAP, r = load_integer_structure(e));
            bfreeregister(r);
        } else
            (void)cg_exprreg(e, targetreg);
        blkflags_(bottom_block) |= BLKREXPORTED;
    }
    emitbranch(J_B, l3);
}

static VRegnum cg_cond(Expr *c, bool valneeded, VRegnum targetreg,
                       LabelNumber *l3, bool structload)
{
    Expr *b = arg1_(c), *e1 = arg2_(c), *e2 = arg3_(c);
    LabelNumber *l1 = nextlabel();
    if (usrdbg(DBG_LINE) && exprfileline_(c) != 0)
        emitfl(J_INFOLINE, *exprfileline_(c));
    cg_test(b, 0, l1);
    cg_cond1(e1, valneeded, targetreg, l3, structload);
    start_new_basic_block(l1);
    cg_cond1(e2, valneeded, targetreg, l3, structload);
    return targetreg;
}

static int32 ispoweroftwo(Expr *x)
{
    unsigned32 n, r;
    if (!integer_constant(x)) return 0;
    n = result2;
    r = n & (0-n);
    if (n == 0 || r != n) return 0;
    r = 0;
    while (n != 1) r++, n >>= 1;
    return r;
}

static void structure_assign(Expr *lhs, Expr *rhs, int32 length)
{
    Expr *e;

/* In a void context I turn a structure assignment into a call to the    */
/* library function memcpy().                                            */
/* Note that casts between structure types are not valid (and so will    */
/* have been filtered out earlier), but casts to the same structure type */
/* can be present (particularly around (a ? b : c) expressions) as an    */
/* artefact of the behaviour of sem. Prune them off here.                */
/* AM Nov 89: The present arrangement of forgeing a call to _memcpy() is */
/* not very satisfactory -- there are problems with tail recursion if    */
/* not TARGET_HAS_BLOCKMOVE and problems with stack addresses if         */
/* TARGET_STACK_MOVES_ONCE (being fixed).                                */
/* To this end, note that 'lhs' ultimately has take_address() and        */
/* typeofexpr() applied to it (but beware the s_assign ref. below).      */
    while (h0_(rhs) == s_cast) rhs = arg1_(rhs);
    switch (h0_(rhs))
    {
case s_let:
        {   BindList *sl = active_binders;
            int32 d = current_stackdepth;
            cg_bindlist(exprletbind_(rhs), 0);
            structure_assign(lhs, arg2_(rhs), length);
            emitsetsp(J_SETSPENV, sl);
            current_stackdepth = d;
            return;
        }
case s_comma:
        /* Maybe this recursive call should just be the expansion:       */
        /*  (a = (b,c)) ---> (b, a=c).                                   */
        cg_exprvoid(arg1_(rhs));
        structure_assign(lhs, arg2_(rhs), length);
        return;
case s_assign:
/* A chain of assignments as in    p = q = r   get mapped as follows:    */
/*    (  LET struct *g,                                                  */
/*       g = &q,                                                         */
/*       *g = r,                                                         */
/*       p = *g )                                                        */
/*                 thus &q gets evaluated only once                      */
/* or to ( q = r, p = q ) if q is simple                                 */

        {   TypeExpr *t = typeofexpr(rhs);
            if (!isvolatile_type(t) && issimplelvalue(arg1_(rhs))) {
                e = mk_expr2(s_comma,
                             t,
                             rhs,
                             mk_expr2(s_assign,
                                      t,
                                      lhs,
                                      arg1_(rhs)));
            } else {
                Binder *gen = gentempbinder(ptrtotype_(t));
                e = mk_exprlet(s_let,
                         t,
                         mkSynBindList(0, gen),
                         mk_expr2(s_comma,
                                  t,
                                  mk_expr2(s_assign,
                                           ptrtotype_(t),
                                           (Expr *)gen,
                                           take_address(arg1_(rhs))),
                                  mk_expr2(s_comma,
                                           t,
                                           mk_expr2(s_assign,
                                                    t,
                                                    mk_expr1(s_content,
                                                             t,
                                                             (Expr *)gen),
                                                    arg2_(rhs)),
                                           mk_expr2(s_assign,
                                                    t,
                                                    lhs,     /* @@@rework */
                                                    mk_expr1(s_content,
                                                             t,
                                                             (Expr *)gen)))));
            }
        }
        break;
case s_fnap:
        e = mk_expr2(s_fnapstruct, te_void, arg1_(rhs),
                     mkArg(exprfnargs_(rhs), take_address(lhs)));
        break;
case s_cond:
/* Convert    a = (b ? c : d)                                            */
/*    (LET struct *g,                                                    */
/*       g = &a,                                                         */
/*       b ? (*g = c) : (*g = d))                                        */
/*                                                                       */
/*  or to b ? (a = c) : (a = d) if a is simple                           */

        {   TypeExpr *t = typeofexpr(lhs);
            if (issimplelvalue(lhs)) {
                e = mk_expr3(s_cond,
                             t,
                             arg1_(rhs),
                             mk_expr2(s_assign,
                                      t,
                                      lhs,
                                      arg2_(rhs)),
                             mk_expr2(s_assign,
                                      t,
                                      lhs,
                                      arg3_(rhs)));
            } else {
                Binder *gen = gentempbinder(ptrtotype_(t));
                e = mk_exprlet(s_let,
                         t,
                         mkSynBindList(0, gen),
                         mk_expr2(s_comma,
                                  t,
                                  mk_expr2(s_assign,
                                           ptrtotype_(t),
                                           (Expr *)gen,
                                           take_address(lhs)),
                                  mk_expr3(s_cond,
                                           t,
                                           arg1_(rhs),
                                           mk_expr2(s_assign,
                                                    t,
                                                    mk_expr1(s_content,
                                                             t,
                                                             (Expr *)gen),
                                                    arg2_(rhs)),
                                           mk_expr2(s_assign,
                                                    t,
                                                    mk_expr1(s_content,
                                                             t,
                                                             (Expr *)gen),
                                                    arg3_(rhs)))));
            }
        }
        break;
case s_binder:
        if (bindconst_(exb_(rhs)) != NULL)
        {   if (LanguageIsCPlusPlus)
                syserr("bindconst $b got to cg.c", exb_(rhs));
            rhs = bindconst_(exb_(rhs));
        }
default:
        e = mk_expr2(s_fnap, te_void, sim.memcpyfn,
                     mkArgList3(take_address(lhs), take_address(rhs),
                                mkintconst(te_int,length,0)));
        break;
    }
    if (debugging(DEBUG_CG))
    {   eprintf("Structure assignment: ");
        pr_expr_nl(e);
    }
    cg_exprvoid(e);
}

static VRegnum load_integer_structure(Expr *e)
{
/* e is a structure-valued expression, but one where the value is a      */
/* one-word integer-like quantity. Must behave like cg_expr would but    */
/* with special treatment for function calls.                            */
    switch (h0_(e))
    {
case s_comma:
        cg_exprvoid(arg1_(e));
        return load_integer_structure(arg2_(e));
case s_assign:
        return cg_storein(load_integer_structure(arg2_(e)),
                          NULL, arg1_(e), s_assign);
case s_fnap:
        {   TypeExpr *t = type_(e);
            Binder *gen = gentempbinder(ptrtotype_(t));
            bindstg_(gen) |= b_addrof;
            e = mk_expr2(s_fnap, te_void, arg1_(e),     /* /* AM: s_fnapstruct here? */
                         mkArg(exprfnargs_(e), take_address((Expr *)gen)));
            e = mk_exprlet(s_let, t, mkSynBindList(0, gen),
                    mk_expr2(s_comma, t, e, (Expr *)gen));
            return cg_expr(e);
        }
/* Since casts between structure-types are illegal the only sort of cast   */
/* that can be present here is just one re-asserting the type of the       */
/* expression being loaded. Hence I skip over the cast. This certainly     */
/* happens with a structure version of (a = b ? c : d) where the type gets */
/* inserted to give (a = (structure)(b ? c : d)).                          */
case s_cast:
            return load_integer_structure(arg1_(e));
case s_cond:
        {   LabelNumber *l3 = nextlabel();
            VRegnum r = cg_cond(e, 1, reserveregister(INTREG), l3, 1);
            start_new_basic_block(l3);
            return getreservedreg(r);
        }

default:
        return cg_expr(e);
    }
}

static VRegnum cg_expr1(Expr *x, bool valneeded)
{
    AEop op = h0_(x);
/* See the discussion in chroma_check() above.                          */
/* @@@ AM thinks that spilling probably oughtn't to start so late --    */
/* the code here allows 1 single expression to preempt many reg vars.   */
/*          *** RETHINK HERE ***                                        */
/* To avoid running out of registers I do dreadful things here:         */
#ifdef TARGET_IS_THUMB
/* ECN: 3 is better for Thumb as 4 means it has no free V registers
 * when calling a function with 4 args. Maybe 2 would be even better
 */
    if ((nusedregs >= (NTEMPREGS+NARGREGS+NVARREGS-spareregs-3)
#else
    if ((nusedregs >= (NTEMPREGS+NARGREGS+NVARREGS-spareregs-4)
#endif
#ifndef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
/* AM has unilaterally decided that 2 spare FP regs should always be enough */
/* here (after he has changed the unsigned FIX code).  Anyway, using 3 for  */
/* for 2 on the next line hurts the 370 code generator as EVERY integer     */
/* operation spills!  Suggestion - only spill FP regs when we have a FP     */
/* result - however beware machines like the VAX where FP=INT reg!          */
         || nusedfpregs >= (NFLTTEMPREGS+NFLTARGREGS+NFLTVARREGS-sparefpregs-2)
#endif
         ) &&
        (op!=s_binder && op!=s_integer && op!=s_floatcon &&
         !isstring_(op)))
    {
/* Here I seem a bit short on working registers, so I take drastic steps */
/* and flush all current registers to the stack, do this calculation and */
/* then reload things. Keeping everything straight is a bit of a mess    */
/* since this breaks the usual abstractions about register allocation    */
/* and usage.                                                            */
        BindList *save_binders = active_binders;
        int32 d = current_stackdepth;
        RegList *saveused = usedregs, *saveusedfp = usedfpregs;
        int32 savebits = nusedregs, savefpbits = nusedfpregs;
        int32 spint = spareregs, spfp = sparefpregs;
        VRegnum r;
        SynBindList *things_to_bind = bindlist_for_temps(saveused, saveusedfp);
#ifndef REGSTATS
/*
 * REGSTATS is defined when ACN is building a private system to investigate
 * register allocation behaviour
 */
        if (debugging(DEBUG_SPILL))
        {   cc_msg("Usedregs = %ld, spareregs = %ld\n",
                     (long)nusedregs, (long)spareregs);
#ifndef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
            cc_msg("FP count = %ld, sparefpregs = %ld\n",
                     (long)nusedfpregs, (long)sparefpregs);
#endif
        }
#endif
/* First I must allocate binders on the stack & save all current         */
/* register contents away.                                               */
        cg_bindlist(things_to_bind, 1);
        stash_temps(saveused, saveusedfp, things_to_bind,
                    J_STRV|J_ALIGN4V, J_STRFV|J_ALIGN4V, J_STRDV|J_ALIGN8);

        nusedregs = nusedfpregs = 0;
        usedregs = usedfpregs = NULL;
        spareregs = sparefpregs = 0;

/* Then compute the value of this expression.                            */
        if (valneeded)
        {   r = cg_expr2(x, 1);
/* I must free the register here because I am about to monkey about with */
/* the tables that show what registers are where. Ugh.                   */
            bfreeregister(r);
        }
        else
        {   r = cg_expr2(x, 0);
            bfreeregister(r);
            r = GAP;
        }

/* Switch back to the outer context of registers.                        */
        usedregs = saveused, usedfpregs = saveusedfp;
        nusedregs = savebits, nusedfpregs = savefpbits;
        spareregs = spint, sparefpregs = spfp;

/* The result of evaluating this expression must be moved to a newly     */
/* allocated register to make sure it does not clash with anything.      */
        if (r != GAP)
        {   RegSort rsort = vregsort(r);
            VRegnum r1 = fgetregister(rsort);
/* Register r is no longer formally allocated (by the chromaticity count */
/* code) but it will still exist!                                        */
            emitreg(floatyop(rsort, J_MOVR, J_MOVFR, J_MOVDR), r1, GAP, r);
            r = r1;
        }

/* Now restore register values                                           */
        stash_temps(saveused, saveusedfp, things_to_bind,
                    J_LDRV|J_ALIGN4V, J_LDRFV|J_ALIGN4V, J_LDRDV|J_ALIGN8);
        while (things_to_bind)
            things_to_bind = freeSynBindList(things_to_bind);

/* adjust stack pointer as necessary.                                    */
        emitsetsp(J_SETSPENV, save_binders);
        current_stackdepth = d;

        return r;
    }
    else if (valneeded) return cg_expr2(x, 1);
    else
    {   VRegnum r = cg_expr2(x, 0);
        bfreeregister(r);
        return GAP;
    }
}

void cg_sub_reinit(void) {
    codebuf_reinit2();
    flowgraph_reinit();
    cse_reinit();
    regalloc_reinit();
}

static void topdec_init(void)
{
    cg_sub_reinit();

    local_binders = regvar_binders = NULL;
    integer_binder = gentempvarwithname(te_int, GAP, "IntBinder");
    bindstg_(integer_binder) |= b_spilt;
    bindmcrep_(integer_binder) = MCR_SORT_SIGNED | alignof_toplevel_auto;
    double_pad_binder = gentempvarwithname(te_double, GAP, "PadBinder");
    bindstg_(double_pad_binder) |= b_spilt;
    bindmcrep_(double_pad_binder) = MCR_SORT_STRUCT | MCR_ALIGN_DOUBLE | 0;

    active_binders = NULL;

    loopinfo.breaklab = loopinfo.contlab = NOTINLOOP;
    switchinfo.endcaselab = switchinfo.defaultlab = NOTINSWITCH;
    structretlab = NOTALABEL;
#ifdef EXTENSION_VALOF
    valofinfo.binders = NULL;
    valofinfo.lab = NULL;
    valofinfo.r = 0;
#endif
    top_block = start_new_basic_block(nextlabel());
    procflags = 0;
    cg_infobodyflag = 0;
    cg_current_cmd = (Cmd *)DUFF_ADDR;
    usedregs = usedfpregs = NULL;
    nusedregs = nusedfpregs = 0;
    spareregs = sparefpregs = 0;
    nreservedregs = 0;
}

static void forcetostore(BindList *bl)
{   for (; bl != NULL; bl = bl->bindlistcdr) {
        Binder *b = bl->bindlistcar;
        /* Force all user-visible variables in bl to be in store,
           so that longjmp by register jamming has the pcc semantics.
         */
        if (!isgensym(bindsym_(b))) bindxx_(b) = GAP;
    }
}

void cg_topdecl2(BindList *local_binders, BindList *regvar_binders)
{
    BindList *split_binders = NULL,
             *invariant_binders = cse_eliminate();
    /* Corrupt regvar_binders and local_binders to get */
    /* a spill_order list for allocate_registers()     */
    drop_local_store();   /* what loopopt used */
    split_binders = splitranges(local_binders, regvar_binders);
    drop_local_store();
    lose_dead_code();     /* before regalloc   */
    if ((procflags & BLKSETJMP) &&
        HasFeature(Feature_UnixStyleLongjmp))
    {
        forcetostore(local_binders);
        if (!HasFeature(Feature_LetLongjmpCorruptRegVars))
            forcetostore(regvar_binders);
    }
    allocate_registers(
        (BindList *)nconc((List *)invariant_binders,
             nconc((List *)split_binders,
                nconc((List *)local_binders,
                      (List *)regvar_binders))));

    drop_local_store();   /* what regalloc used */

    phasename = "machinecode";
/* If (after register allocation etc) an argument is left active in      */
/* memory (rather than being slaved in a register) I will do the full    */
/* entry sequence. Force this by setting PROC_ARGPUSH in that case.      */
/* Note that PROC_ARGADDR will thereby imply PROC_ARGPUSH, but they are  */
/* different in that PROC_ARGADDR suppresses tail recursion (flowgraph.c)*/
/* Also if a big stack frame is needed I tell xxxgen.c to be cautious.   */
    if (greatest_stackdepth > 256) procflags |= PROC_BIGSTACK;
    {   BindList *fb = argument_bindlist;
        for (; fb != NULL; fb = fb->bindlistcdr) {
            Binder *b1 = fb->bindlistcar;
            if (bindxx_(b1) == GAP) procflags |= PROC_ARGPUSH;
        }
    }
/* Now, also set PROC_ARGPUSH if debugging of local variables is         */
/* requested -- this will ensure that FP is set up.                      */
/* N.B. We could probably optimise this if no vars spill, i.e. the       */
/* debugger *probably* does not need FP, but why bother??                */
    if (usrdbg(DBG_VAR) && dbg_needsframepointer())
      procflags |= PROC_ARGPUSH;

/* This is the place where I put tables into the output stream for use   */
/* by debugging tools - here are the names of functions.                 */
#ifndef TARGET_IS_ARM
    cg_fnname_offset_in_codeseg = HasFeature(Feature_SaveName) ?
                        codeseg_function_name(currentfunction.symstr, currentfunction.argwords) : -1;
    show_entry(currentfunction.symstr, currentfunction.xrflags);
#else
/* This work is now done in arm/gen.c so that fn names are only dumped   */
/* for functions which have stack frames.                                */
    cg_fnname_offset_in_codeseg = -1;
#endif
    linearize_code();
    dbg_xendproc(currentfunction.fl);

    show_code(currentfunction.symstr);

    if (cgstate.block_cur > max_block) max_block = cgstate.block_cur;
    if (cgstate.icode_cur > max_icode) max_icode = cgstate.icode_cur;
}

/* After all code has been generated, we inspect it to remove b_addrof from
   binders which are not actually address-taken. This happens with arguments
   to inline functions, where eg __inline f(int *p) { *p = 1; } f(&x);
   turns into x = 1 but x has been marked address-taken. We go to this trouble
   in order to avoid the aliasing implications of address-taken.
 */

#define b_vk_addressed b_maybeinline
#define b_really_addresstaken b_fnconst

static void check_addrof2(BindList *bl) {
    for (; bl != NULL; bl = bl->bindlistcdr)
        if (bindstg_(bl->bindlistcar) & (b_vk_addressed|b_really_addresstaken))
            syserr("check_addrof2");
}

static void clear_addrof2(BindList *bl) {
    for (; bl != NULL; bl = bl->bindlistcdr) {
        Binder *b = bl->bindlistcar;
        if (bindstg_(b) & b_really_addresstaken)
          /* Address actually taken: leave addrof on the binder if it's there
             (need not be).
           */
            bindstg_(b) &= ~b_really_addresstaken;
          /* Marked address taken, but address not in fact taken.
             Clear the mark.
           */
        else if (bindstg_(b) & b_addrof) {
            bindstg_(b) &= ~b_addrof;
            if (debugging(DEBUG_CG))
                cc_msg("Removing address-taken from $b:%p\n", b, b);
        }
    }
}

static void spill_addrof(BindList *bl) {
    for (; bl != NULL; bl = bl->bindlistcdr) {
        Binder *b = bl->bindlistcar;
        if (bindstg_(b) & (b_addrof | b_spilt | b_vk_addressed)) {
            if (bindstg_(b) & b_addrof)
              bindstg_(b) &= ~(b_spilt | b_vk_addressed);
            else
              bindstg_(b) &= ~b_vk_addressed;
            bindxx_(b) = GAP;
        }
    }
}

static void correct_addrof(BindList *local_binders, BindList *regvar_binders) {
    BindList *bl;
    BlockHead *b;
    check_addrof2(local_binders);
    check_addrof2(regvar_binders);
    for (b = top_block; b != NULL; b = blkdown_(b)) {
        int32 n = blklength_(b);
        Icode *ip = blkcode_(b);
        for (; --n >= 0; ip++)
            if ((ip->op & J_TABLE_BITS) == J_ADCONV)
                bindstg_(ip->r3.b) |= b_really_addresstaken;
            else if (vkformat(ip->op))
                bindstg_(ip->r3.b) |= b_vk_addressed;
    }
    clear_addrof2(local_binders);
    clear_addrof2(regvar_binders);

/* Now propagate address taken-ness across all args (unless register)    */
    for (bl = argument_bindlist; bl != NULL; bl = bl->bindlistcdr)
    {   Binder *b = bl->bindlistcar;
        if (bindstg_(b) & b_addrof)
/* Furthermore since in that case I will always need to write arguments  */
/* in place on that stack it makes sense to use a full entry sequence.   */
/* This of course must, in general, kill tail recursion optimisation.    */
        {   procflags |= PROC_ARGADDR;
            for (bl = argument_bindlist; bl != NULL; bl = bl->bindlistcdr)
            {   b = bl->bindlistcar;
                if (!(bindstg_(b) & bitofstg_(s_register)))
                    bindstg_(b) |= b_addrof;
            }
            break;
        }
    }
    spill_addrof(local_binders);
    spill_addrof(regvar_binders);
}

void cg_topdecl(TopDecl *x, FileLine fl)
{
        if (x == NULL || h0_(x) != s_fndef)
            syserr(syserr_cg_unknown, x == NULL ? 0L : (long)h0_(x));
        {   Binder *b = x->v_f.fn.name;
            SynBindList *formals = x->v_f.fn.formals;
            Cmd *body = x->v_f.fn.body;
            Symstr *name = bindsym_(b);
            TypeExpr *t = prunetype(bindtype_(b)), *restype;
            int32 resrep, old_profile_option = 0;
            fl.p = dbg_notefileline(fl);
            currentfunction.fl = fl;
/* Object module generation may want to know if this module defines
   main() so that it can establish an entry point. Also while defining
   main() we should ensure that return; is mapped onto return 0;
   N.B. this latter really be done so that regalloc can warn first!! */
            if (name == mainsym &&
                (bindstg_(b) & bitofstg_(s_extern)) != 0)
                defining_main = has_main = YES;
            else defining_main = NO;
            /* disable profiling for compiler generated functions, vtables included */
            if (bindstg_(b) & b_generated)
            {   old_profile_option = var_profile_option;
                var_profile_option = 0;
            }
            if (h0_(t)!=t_fnap)
            {   syserr(syserr_cg_topdecl);
                return;
            }
            procauxflags = typefnaux_(t).flags;
            topdec_init();
            restype = prunetype(typearg_(t));
            resrep = mcrepoftype(restype);
            currentfunction.nresultregs = 0;
            currentfunction.baseresultreg = GAP;
            result_variable = NULL;
            if ((resrep & MCR_SORT_MASK) == MCR_SORT_STRUCT)
            {
                if (returnsstructinregs_t(t)) {
                    currentfunction.baseresultreg = R_P1result;
                    currentfunction.nresultregs =
                       (int)(((resrep & MCR_SIZE_MASK) + MEMCPYQUANTUM - 1)/ MEMCPYQUANTUM);

                } else {
/* If a function returns a structure result I give it a hidden extra     */
/* first argument that will point to where the result must be dumped.    */
                    result_variable = currentfunction.structresult;
                    if (result_variable == 0) syserr(syserr_cg_return_struct);
                    if (usrdbg(DBG_VAR))
                        dbg_locvar(result_variable, cmdfileline_(body));
#ifndef TARGET_STRUCT_RESULT_REGISTER
                    formals = mkSynBindList(formals, result_variable);
#endif
                    {   TypeExpr *pt = bindtype_(result_variable);
                        Binder *b = gentempbinder(pt);
                        set_local_vregister(b, mcrepoftype(pt), 0);
                        result_temporary = b;
                    }
                }

            } else if ((resrep & MCR_SIZE_MASK) != 0) {
                int32 resmode = resrep & MCR_SORT_MASK;
                RegSort rsort = resmode != MCR_SORT_FLOATING ? INTREG :
                               resrep == MCR_SORT_FLOATING+4 ? FLTREG :
                                                               DBLREG;
                currentfunction.baseresultreg = V_Presultreg(rsort);
            }
/* Here is a ugly mess - 'formals' has SynAlloc store, which is         */
/* corrupted by drop_local_store().  It needs copying for both for the  */
/* use below (PROC_ARGPUSH) and for its use in regalloc.c.              */
            argument_bindlist = (BindList *)binderise(formals);
            if (usrdbg(DBG_VAR))
            {   /* for the basic block started by J_ENTER in cg_bindargs() */
                current_env = (BindListList *) binder_cons2(0, argument_bindlist);
            }
            currentfunction.argwords = cg_bindargs(argument_bindlist, x->v_f.fn.ellipsis);
            currentfunction.symstr = bindsym_(b);
            cg_cmd(body);
#ifdef never
            /* the following code is maybe what AM would like */
            if (!deadcode && !isprimtype_(restype, s_void))
                cc_warn(cg_warn_implicit_return, symname_(name));
#endif
            /* we know here that fl.f != 0 */
            if (!cg_infobodyflag)
            {
#ifdef TARGET_HAS_PROFILE
                if (profile_option) emitfl(J_COUNT, fl);
#endif
                if (usrdbg(DBG_PROC)) emit(J_INFOBODY, GAP, GAP, 0);
                cg_infobodyflag = 1;
            }
            if (usrdbg(DBG_LINE)) emitfl(J_INFOLINE, fl);
            cg_return(0, !isprimtype_(restype, s_void));

            drop_local_store();
            phasename = "loopopt";
/* Force inline functions to have internal linkage... the argument as to */
/* why this is a Good Thing is long and complicated...                   */
            currentfunction.xrflags =
                bindstg_(b) & (bitofstg_(s_static) | bitofstg_(s_inline)) ?
                                      xr_code+xr_defloc : xr_code+xr_defext;

            correct_addrof(local_binders, regvar_binders);
            if ( !(bindstg_(b) & bitofstg_(s_inline)) ||
                 usrdbg(DBG_ANY) ||
                 !Inline_Save(b, local_binders, regvar_binders)) {

                cg_topdecl2(local_binders, regvar_binders);
                symext_(currentfunction.symstr)->usedregs = regmaskvec;
            }
            /* enable profile option, if necessary */
            if (old_profile_option)
                var_profile_option = old_profile_option;
        }
}

void cg_init(void)
{
    obj_init();                 /* MUST precede codebuf_init() */
    Inline_Init();
    regalloc_init();
    codebuf_init();
    mcdep_init();             /* code for system dependent module header */
    datasegbinders = (BindList *)global_cons2(SU_Other, 0, datasegment);
    max_icode = 0; max_block = 0;
    cse_init();
    splitrange_init();
    has_main = NO;

#ifndef NO_OBJECT_OUTPUT
      if (objstream) obj_header();
#endif
#ifndef NO_ASSEMBLER_OUTPUT
      if (asmstream) asm_header();
#endif

    dbg_init();

    show_entry(bindsym_(codesegment), xr_code+xr_defloc);  /* nasty here */
    show_code(bindsym_(codesegment));                      /* nasty here */
}

void cg_reinit(void)
{
    codebuf_reinit();
}

void cg_tidy(void)
{
    Inline_Tidy();
    codebuf_tidy();
    if (debugging(DEBUG_STORE)) {
        cc_msg("Max icode store %ld, block heads %ld bytes\n",
                (long)max_icode, (long)max_block);
    }
    regalloc_tidy();
    cse_tidy();

/* Pad data segment to at least 4 byte multiple (to flush vg_wbuff),    */
/* but pad to multiple of alignof_max if bigger.                        */
/* Do this irrespective of object module format.                        */
    {  int32 alignto = alignof_max > 4 ? alignof_max : 4;
       padstatic(alignto);
#ifdef TARGET_HAS_BSS
       padbss(alignto);
#endif
#ifdef CONST_DATA_IN_CODE
       SetDataArea(DS_Const);
       padstatic(alignto);
       SetDataArea(DS_ReadWrite);
#endif
    }

    /* maybe do dreverse(CodeXrefs+DataXrefs here one day? */
#ifndef NO_OBJECT_OUTPUT
    if (objstream) obj_trailer();
#endif
#ifndef NO_ASSEMBLER_OUTPUT
    if (asmstream) asm_trailer();
#endif
    localcg_tidy();
}

/* End of cg.c */
