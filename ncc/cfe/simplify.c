/*
 * simplify.c: tree optimisation phase of C compiler
 * Copyright (C) Codemist Ltd, 1988-1992.
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright 1991-1997 Advanced Risc Machines Limited. All rights reserved
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$  Codemist 13
 * Checkin $Date$
 * Revising $Author$
 */

#include <setjmp.h>

#include "globals.h"
#include "simplify.h"
#include "sem.h"
#include "bind.h"
#include "aetree.h"
#include "builtin.h"
#include "store.h"
#include "aeops.h"
#include "errors.h"

/* AM nov-88: add code to allow mcrep fns to return a flag if the     */
/* object requires double alignment (e.g. some structs)               */
/* As a transition this is only enabled if alignof_double > alignof_int. */
/* AM 24-sep-87: created from sem.c, but the idea is soon to put tree */
/* replacement bits of cg.c in here too.                              */
/* Fix (unreleased) bug in *(int *)&x caused by over-keen optimisation */
/* Re-fix to kill bug in (LDS's) extern int a[]; return *a;            */

/* optimise0() is called after parsing an expression (generally by syn.c) */
/* which has been type-checked on the way by sem.c.  It does tree-like    */
/* optimisations, such as removing casts between objects which have the   */
/* same run-time representation (e.g. char* -> int* -> long)          */

/* expression optimiser:
 * Current aims for optimise():
 *  0) Remove s_invisible nodes introduced while parsing for error messages.
 *  1) reduce constant operations.  Most (e.g. 1+2) is done when
 *     building tree nodes, however, this is a good place to spot
 *     (x+1)+2, or (x.a).b.  Unfortunately this is not done yet so
 *     genpointer() in vargen.c and the CG both do similar things with the
 *     result of optimise().  Also turn x+0 to x soon.
 *  2) Transform &*x to x, and &x.a to &x + a.
 *  3) Regroup certain arithmetic expressions so as to allow more
 *     constant folding to occur.
 * The resultant tree is normalised to some extent.  E.g. & is only
 * applied to s_binder's.
 */

/* forward references... */
static Expr *optimisefnap(Expr *);

static jmp_buf optimise0_jb;


/* The following routine fixes LDS's bug (in 1.57) alluded to above.  */
/* It is not the final word, since we can clearly sometimes do better */
/* at detecting same pointers, but is intended to keep LDS happy with */
/* 'minimal change to code'.                          */
static bool same_pointedto_types(Expr *e, Expr *e1)
{   TypeExpr *x = prunetype(typeofexpr(e));
    TypeExpr *x1 = prunetype(typeofexpr(e1));
    if (x == x1) return 1;
    /* Careful not to pass arrays/structs/fns to mcrepofexpr()      */
    /* (and thence sizeoftype which can issue error messages).      */
    /* The next line duplicates previous behaviour on t_fnap types. */
    if (h0_(x) == t_fnap && h0_(x1) == t_fnap)
        return 1;
    if (h0_(x) == t_subscript || h0_(x) == t_fnap || isclasstype_(x))
        return 0;
    if (h0_(x1) == t_subscript || h0_(x1) == t_fnap || isclasstype_(x1))
        return 0;
    return mcrepofexpr(e) == mcrepofexpr(e1);
}

bool is_same(Expr *a, Expr *b)
/* Expressions are considered the same if they compute the same value    */
/* and do not have any side-effects.                     */
{
    AEop op;
    for (;;)
    {   if ((op = h0_(a)) != h0_(b))
        {   AEop opb = h0_(b);
            if (isrelational_(op) && isrelational_(opb)
                && integer_constant(arg2_(a)))
            {   int32 ka = result2;
                if (integer_constant(arg2_(b)))
                {   int32 kb = result2;
                    int32 asort = mcrepofexpr(arg1_(a)) & MCR_SORT_MASK,
                          bsort = mcrepofexpr(arg1_(a)) & MCR_SORT_MASK;
                    if (asort == bsort)
                        switch (op)
                        {
                        case s_less:
                            return (opb == s_lessequal && ka == kb+1
                                    && (asort == MCR_SORT_UNSIGNED ? ka != 0 : ((ka ^ kb) > 0 || ka == 0)));
                        case s_lessequal:
                            return (opb == s_less && kb == ka+1
                                    && (asort == MCR_SORT_UNSIGNED ? kb != 0 : ((ka ^ kb) > 0 || kb == 0)));
                        case s_greater:
                            return (opb == s_greaterequal && kb == ka+1
                                    && (asort == MCR_SORT_UNSIGNED ? kb != 0 : ((ka ^ kb) > 0 || kb == 0)));
                        case s_greaterequal:
                            return (opb == s_greater && ka == kb+1
                                    && (asort == MCR_SORT_UNSIGNED ? ka != 0 : ((ka ^ kb) > 0 || ka == 0)));
                        }
                }
            }
            return NO;
        }
        if (isvolatile_expr(a) || isvolatile_expr(b)) return NO;
        switch (op)
        {
    case s_binder:
            return a == b;  /* volatile attribute already checked */
    case s_integer:
            return intval_(a) == intval_(b);
    case_s_any_string
    case s_floatcon:
            return a == b;  /* improve? */
    case s_dot:
            if (exprdotoff_(a) != exprdotoff_(b)) return NO;
            a = arg1_(a), b = arg1_(b);
            continue;
    case s_cast:
/* equivtype is probably too strong on the next line (we should         */
/* probably use a more machine-oriented test on types) but, before      */
/* changing it to the logical mcrepofexpr()=mcrepofexpr(), note that    */
/* casts on empty arrays to pointers can cause mcrepofexpr() to cc_err. */
/* @@@ Then again, perhaps is_same should be elided by cse.c now?       */
            if (!equivtype(type_(a), type_(b))) return NO;
    case s_addrof:
    case s_bitnot:
    case s_boolnot:
    case s_neg:
    case s_content:
    case s_monplus:
            a = arg1_(a);
            b = arg1_(b);
            continue;
    case s_equalequal:
    case s_notequal:
    case s_times:
    case s_plus:
    case s_and:
    case s_or:
    case s_xor:
            if (is_same(arg1_(a), arg1_(b)))
            {   a = arg2_(a);
                b = arg2_(b);
                continue;
            } else if (is_same(arg2_(a), arg1_(b)))
            {   a = arg1_(a);
                b = arg2_(b);
                continue;
            }
            return NO;
    case s_andand:
    case s_oror:
    case s_greater:
    case s_greaterequal:
    case s_less:
    case s_lessequal:
    case s_comma:
    case s_minus:
    case s_div:
    case s_leftshift:
    case s_rem:
    case s_rightshift:
            if (!is_same(arg1_(a), arg1_(b))) return NO;
            a = arg2_(a);
            b = arg2_(b);
            continue;
    case s_cond:
            if (!is_same(arg1_(a), arg1_(b))) return NO;
            if (!is_same(arg2_(a), arg2_(b))) return NO;
            a = arg3_(a);
            b = arg3_(b);
            continue;

    default:
            return NO;
        }
    }
}

static Expr *optimise_cast(Expr *e)
{   Expr *a1 = arg1_(e);
    int32 e_mode = mcrepofexpr(e), e_len;
    int32 a_mode = mcrepofexpr(a1), a_len;
    TypeExpr *destntype = typeofexpr(e);
    TypeExpr *sourcetype = typeofexpr(a1);
    TypeExpr *te = princtype(typeofexpr(e));
    if (h0_(te) == t_content) te = typearg_(te);
    if (isfntype(te)) return e;  /* leave in casts to fn type */

/* a cast to the same type is ineffectual                             */
    if (e_mode == a_mode &&
        !((recursivequalifiers(destntype) | recursivequalifiers(sourcetype))
           & bitoftype_(s_volatile)))
        return a1;

    e_len = e_mode & MCR_SIZE_MASK;
    e_mode >>= MCR_SORT_SHIFT;
    a_len = a_mode & MCR_SIZE_MASK;
    a_mode >>= MCR_SORT_SHIFT;

/* A cast is ineffectual if it does not change the m/c representation.   */
    if (e_mode < 2 && a_mode < 2)        /* cast of integral to integral */
    {
        if (e_mode == a_mode && e_len > a_len)
            return a1;         /* vacuous signedness-preserving widening */

/* Things like (int)(unsigned char)x are NOT vacuous, even though cg     */
/* will generate no code for them, because (double)(int)(unsigned char)x */
/* (double)(unsigned char)x and (double)(signed char)x are all different.*/
/* Even (unsigned int)(int) has a role: consider:-                       */
/* double d;  (double)(unsigned)(int)d; - what can be elided? Nothing!   */
    }

    if (h0_(a1) == s_cast)
    {
/* The inner casts are irrelevant in the following cases:                */
/*     (float) (double) x                                                */
/*     (double) (float) x where x is shorter than int                    */
/*     (char)  (short)  x   (char) (int) x   (short) (int) x             */
/* So are the corresponding unsigned cases.                              */
        if (   (e_mode <  2 && a_mode <  2 && e_len < a_len)
            || (e_mode == 2 && a_mode == 2
                && (e_len < a_len
                    || (mcrepofexpr(arg1_(a1)) & MCR_SIZE_MASK) < 2)))
/* /* Revisit this code to handle short longer than a float's mantissa   */
/*    (or int shorter, for that matter)                                  */
        {
            arg1_(e) = arg1_(a1);
        }
    }
    return e;
}
/*
   AM: expressions such as  structfn().a[i]  are odd -- the ANSI spec seems
   to be very unclear about whether they illegally require the address
   of a function result.  To ease implementation all calls to structfn()
   are mapped to  (let t; t=structfn(),t)  but this transformation is
   undone if we know where the result is going, e.g. x = structfn().
*/

static SynBindList *new_binders;

static bool Div_SignBitClear(Expr *x, int32 rep) {
 /* We don't try too hard here at present: look for just widening of an
    unsigned type and positive constants.
  */
    if (h0_(x) == s_cast) {
        int32 xrep = mcrepofexpr(arg1_(x));
        return (xrep >> MCR_SORT_SHIFT) == 1 &&
               (xrep & MCR_SIZE_MASK) < (rep & MCR_SIZE_MASK);
    } else if (h0_(x) == s_integer)
        return intval_(x) > 0;
    else
        return NO;
}

static Expr *Div_CastToUnsigned(Expr *x, TypeExpr *t) {
/* (signbitclear(x, ..) is true) */
    return (h0_(x) == s_cast) ?
        mk_expr1(s_cast, t, arg1_(x)) :
        mkintconst(t, intval_(x), 0);
}

static Expr *IgnoreSignednessChange(Expr *e) {
    int32 e_mode = mcrepofexpr(e);
    int32 e_len = e_mode & MCR_SIZE_MASK;
    e_mode &= MCR_SORT_MASK;
    if (e_mode == MCR_SORT_SIGNED || e_mode == MCR_SORT_UNSIGNED)
        while (h0_(e) == s_cast) {
            int32 a_mode = mcrepofexpr(arg1_(e));
            int32 a_len = a_mode & MCR_SIZE_MASK;
            a_mode &= MCR_SORT_MASK;
            if (a_len == e_len &&
                (a_mode == MCR_SORT_SIGNED || a_mode == MCR_SORT_UNSIGNED))
                e = arg1_(e);
            else
                return e;
        }
    return e;
}

static Expr *RemovableSignOrZeroExtension(Expr *a, uint32 mask) {
    if (h0_(a) == s_and && h0_(arg2_(a)) == s_integer &&
        (~intval_(arg2_(a)) & mask) == 0)
        return arg1_(a);

    a = IgnoreSignednessChange(a);
    if (h0_(a) == s_rightshift && h0_(arg2_(a)) == s_integer) {
        int32 sl = 0, sr = intval_(arg2_(a));
        if ((((unsigned32)-1 >> sr) & mask) == mask) {
            a = IgnoreSignednessChange(arg1_(a));
            if (h0_(a) == s_leftshift) {
                if (h0_(arg2_(a)) != s_integer)
                    return NULL;
                sl = intval_(arg2_(a));
                a = arg1_(a);
            }
            if (sl < sr) {
                TypeExpr *t = typeofexpr(a);
                return mk_expr2(s_rightshift, t, a, mkintconst(t, sr - sl, 0));
            } else if (sl == sr)
                return a;
        }
    }
    return NULL;
}

/* Beware highly: optimise currently side-effects the tree.
   Moreover, s_invisible and (more serious) nodes for ++, += etc can
   share sub-structure.  Only binders I believe in the latter case
   so that all should be OK.  Also the use of recursive use of optimise()
   in case s_addrof requires it to be idempotent.
*/

static Expr *EvalBinaryOp(AEop op, TypeExpr *t, Expr *e1, Expr *e2) {
/* e1 and e2 known to be of sort s_integer. This is not a call to mkbinary()
 * because that may generate unwanted warnings about overflow. Also, we would
 * need to fiddle with the types of constants in pointer expressions to avoid
 * incorrect extra scaling.
 */
    int32 k1 = intval_(e1),
          k2 = intval_(e2);
    switch (op) {
    case s_times: k1 *= k2; break;
    case s_plus:  k1 += k2; break;
    case s_minus: k1 -= k2; break;
    case s_and:   k1 &= k2; break;
    case s_or:    k1 |= k2; break;
    case s_xor:   k1 ^= k2; break;
    default:      syserr("EvalBinaryOp %ld", op);
    }
    return mkintconst(t, k1, 0);
}

static int in_args = 0;

static Expr *optimise1(Expr *e, bool valneeded, bool *pure);
static Expr *optimise1b(Expr *e, Expr *a1, Expr *a2,
                        bool purea1, bool purea2, bool valneeded);

static Expr *mkb(AEop op, TypeExpr *t, Expr *a1, Expr *a2, bool valneeded) {
    Expr *e = mk_expr2(op, t, a1, a2);
    if (debugging(DEBUG_AETREE) && syserr_behaviour > 0) {
        pr_exproftype("optimise1b: ", e);
    }
    e = optimise1b(e, a1, a2, NO, NO, valneeded);
    if (debugging(DEBUG_AETREE) && syserr_behaviour > 0) {
        pr_exproftype("optimise1b= ", e);
    }
    return e;
}

static bool HasIntegralType(Expr *e)
{   int32 rep = mcrepofexpr(e) & MCR_SORT_MASK;
    return rep < MCR_SORT_FLOATING;
}

static Expr *DistributedOp(
  AEop op1, AEop op2, TypeExpr *type,
  Expr *a1, Expr *a21, Expr *a22, bool valneeded) {
    bool pure;
    return optimise1(mk_expr2(op1, type, a1, mk_expr2(op2, type, a21, a22)),
                     valneeded, &pure);
}

static Expr *optimise1b(Expr *e, Expr *a1, Expr *a2,
                        bool purea1, bool purea2, bool valneeded) {
    AEop op = h0_(e);
    TypeExpr *te = type_(e);
/* floating point tree optimisations moved here from cfe/sem.c    */
/* beware IEEE conformance, in that we optimise X+0.0 to X (NaN/-0).    */
    if (purea1 && purea2 && HasIntegralType(a1) && h0_(a1) == h0_(a2))
      if (((op == s_minus || op == s_plus) && h0_(a1) == s_times)
          || ((op == s_or || op == s_xor) && h0_(a1) == s_and)) {
        Expr *a11 = arg1_(a1),
             *a21 = arg2_(a1),
             *a12 = arg1_(a2),
             *a22 = arg2_(a2);
        if (is_same(a11, a12))
          return DistributedOp(h0_(a1), op, type_(e), a11, a21, a22, valneeded);
        else if (is_same(a21, a12))
          return DistributedOp(h0_(a1), op, type_(e), a21, a11, a22, valneeded);
        else if (is_same(a11, a22))
          return DistributedOp(h0_(a1), op, type_(e), a11, a21, a12, valneeded);
        else if (is_same(a21, a22))
          return DistributedOp(h0_(a1), op, type_(e), a21, a11, a12, valneeded);
      }
    if (op == s_minus) {
      if (is_fpzero(a1)) { h0_(e) = s_neg; arg1_(e) = a2; return e; }
      if (is_fpzero(a2)) return a1;
      if (is_intzero(a2)) return a1;
      if (is_intzero(a1)) return mk_expr1(s_neg, te, a2);
      if (purea1 && purea2 && HasIntegralType(e) && is_same(a1, a2))
        return mkintconst(te, 0, 0);
      if (h0_(a2) == s_neg) {
          /* a - -b => a + b */
        h0_(e) = s_plus;
        a2 = arg1_(a2);
      } else
      /* should also do -a - b => -(a + b)? */
      if (h0_(a2) == s_integer) {
        h0_(e) = op = s_plus;
        a2 = mkintconst(type_(a2), -intval_(a2), 0);
      } else if (h0_(a1) == s_plus && h0_(a2) == s_plus) {
        Expr *a12 = arg2_(a1),
             *a22 = arg2_(a2);
        if (h0_(a12) == s_integer) {
          if (h0_(a22) == s_integer) {
            /* (a+k) - (b+k1) => (a-b) + (k1-k) */
            a1 = mk_expr2(s_minus, te, arg1_(a1), arg1_(a2));
            a2 = EvalBinaryOp(s_minus, te, a12, a22);
          } else {
            /* (a+k) - b => (a-b) + k */
            a1 = mk_expr2(s_minus, te, arg1_(a1), a2);
            a2 = a12;
          }
        } else if (h0_(a22) == s_integer) {
            /* a - (b+k) => (a-b) + -k */
            a1 = mk_expr2(s_minus, te, a1, arg1_(a2));
            a2 = mkintconst(te, -intval_(a22), 0);
        } else
          goto symmetric_done;
        h0_(e) = op = s_plus;
      } else
        goto symmetric_done;
    } else if (op == s_div || op == s_rem) {
    /* We deliberately avoid doing anything with 0/x here  */
    /* else a divide by zero could go undetected at runtime*/
    /* (we could turn it into (divcheck(x), 0), but        */
    /* probably to little gain)                            */
      TypeExpr *t = prunetype(te);
      int32 rep = mcrepoftype(t);
      /* Turn a signed division whose operands are both  */
      /* known to be positive into an unsigned division  */
      /* whose result is cast to signed. Rationale: s/w  */
      /* implementations of unsigned divide are likely to*/
      /* be a little faster, and if the divisor is a     */
      /* constant power of two the improvement is        */
      /* substantial                     */
      if ((rep & MCR_SORT_MASK) == MCR_SORT_SIGNED &&
        Div_SignBitClear(a1, rep) &&
        Div_SignBitClear(a2, rep) &&
        h0_(t) == s_typespec) {
        TypeExpr *t1 = primtype_(typespecmap_(t) | bitoftype_(s_unsigned));
        bool dummy;
        a1 = Div_CastToUnsigned(a1, t1);
        a2 = Div_CastToUnsigned(a2, t1);
        return optimise1(mk_expr1(s_cast,
                                  t,
                                  mk_expr2(op, t1, a1, a2)),
                         valneeded,
                         &dummy);
      }
      if (op == s_div && h0_(a2) == s_integer) {
        if (h0_(a1) == s_div && h0_(arg2_(a1)) == s_integer) {
          /* (a/k)/k1 => a/(k*k1) */
          a2 = EvalBinaryOp(s_times, te, arg2_(a1), a2);
          a1 = arg1_(a1);
        }
        if (intval_(a2) == 1) return a1;
        if (intval_(a2) == -1 &&
            (rep & MCR_SORT_MASK) == MCR_SORT_SIGNED) {
          return mkunary(s_neg, a1);
        }
      }
      goto symmetric_done;
    }
/* N.B. symmetric things only until symmetric_done...         */
    if (h0_(a1) == s_integer || h0_(a1) == s_floatcon)
    { Expr *w = a1;       /* move any const to arg2    */
      a1 = a2;      /* note both can't be consts.   */
      a2 = w;
    }
    if (h0_(a2) == s_integer && h0_(a1) == s_cond
        && (h0_(arg2_(a1)) == s_integer || h0_(arg3_(a1)) == s_integer)) {
      Expr *newa1, *newa2;
      if (h0_(arg2_(a1)) == s_integer)
        newa1 = EvalBinaryOp(op, te, arg2_(a1), a2);
      else
        newa1 = optimise1(mk_expr2(op, type_(a1), arg2_(a1), a2), valneeded, &purea1);
      if (h0_(arg3_(a1)) == s_integer)
        newa2 = EvalBinaryOp(op, te, arg3_(a1), a2);
      else
        newa2 = optimise1(mk_expr2(op, type_(a1), arg3_(a1), a2), valneeded, &purea1);
      return mk_expr3(s_cond, te, arg1_(a1), newa1, newa2);
    }
    if (op == s_and)
    { if (is_intzero(a2) && purea1) return mkintconst(te, 0, 0);
      if (is_intminusone(a2)) return a1;
      if (purea1 && purea2) {
        if (is_same(a1, a2))
          return a1;
        else if (h0_(a2) == s_bitnot) {
          if (is_same(a1, arg1_(a2)))
            return mkintconst(te, 0, 0);
        } else if (h0_(a1) == s_bitnot) {
          if (is_same(a2, arg1_(a1)))
            return mkintconst(te, 0, 0);
        }
      }
    }
    if (op == s_or)
    { if (is_intzero(a2)) return a1;
      if (is_intminusone(a2) && purea1) return mkintconst(te, -1, 0);
      if (purea1 && purea2) {
        if (is_same(a1, a2))
          return a1;
        else if (h0_(a2) == s_bitnot) {
          if (is_same(a1, arg1_(a2)))
            return mkintconst(te, -1, 0);
        } else if (h0_(a1) == s_bitnot) {
          if (is_same(a2, arg1_(a1)))
            return mkintconst(te, -1, 0);
        }
      }
    }
    if (op == s_xor)
    { if (is_intzero(a2)) return a1;
      if (is_intminusone(a2)) {
        if (h0_(a1) == s_bitnot)
          return arg1_(a1);
        else
          return mk_expr1(s_bitnot, te, a1);
      }
      if (purea1 && purea2) {
        if (is_same(a1, a2))
          return mkintconst(te, 0, 0);
        else if (h0_(a2) == s_bitnot) {
          if (is_same(a1, arg1_(a2)))
            return mkintconst(te, -1, 0);
        } else if (h0_(a1) == s_bitnot) {
          if (is_same(a2, arg1_(a1)))
            return mkintconst(te, -1, 0);
        }
      }
    }
    if (op == s_plus)
    { if (is_fpzero(a2)) return a1;
      if (is_intzero(a2)) return a1;
    }
    if (op == s_times)
    { if (is_fpone(a2)) return a1;
      if (is_fpminusone(a2))
          { h0_(e) = s_neg; arg1_(e) = a1; return e; }
      if (is_intzero(a2) && purea1) return mkintconst(te, 0, 0);
      if (is_intone(a2)) return a1;
      if (is_intminusone(a2)) return mk_expr1(s_neg, te, a1);
      /* -a * -b => a*b */
      if (h0_(a1) == s_neg) {
        if (h0_(a2) == s_neg)
          return mk_expr2(s_times, te, arg1_(a1), arg1_(a2));
        else if (h0_(a2) == s_times) {
          if (h0_(arg1_(a2)) == s_neg)
            return mk_expr2(s_times, te,
                    arg1_(a1),
                    mk_expr2(s_times, te, arg1_(arg1_(a2)), arg2_(a2)));
          else if (h0_(arg2_(a2)) == s_neg)
            return mk_expr2(s_times, te,
                    arg1_(a1),
                    mk_expr2(s_times, te, arg1_(a2), arg1_(arg2_(a2))));
        }
      } else if (h0_(a2) == s_neg && h0_(a1) == s_times) {
        if (h0_(arg1_(a1)) == s_neg)
          return mk_expr2(s_times, te,
                  mk_expr2(s_times, te, arg1_(arg1_(a1)), arg2_(a1)),
                  arg1_(a2));
        else if (h0_(arg2_(a1)) == s_neg)
          return mk_expr2(s_times, te,
                  mk_expr2(s_times, te, arg1_(a1), arg1_(arg2_(a1))),
                  arg1_(a2));
      }
    }
    if (h0_(a1) == op && h0_(arg2_(a1)) == s_integer) {
      Expr *k1 = arg2_(a1);
      if (h0_(a2) == s_integer) {
      /* ((a op n) op m)  => a op (n op m) */
        a1 = arg1_(a1);
        a2 = EvalBinaryOp(op, te, a2, k1);
/* This can convert (e.g.)  (a + 1) + (-1) into  (a + 0) which does not  */
/* get simplified further here. The codegenerator will treat this as     */
/* just a, and the seemingly spurious +0 will serve to preserve the      */
/* proper type of the expression.                                    */
      } else if (h0_(a2) == op && h0_(arg2_(a2)) == s_integer) {
      /* ((a op n) op (b op m)) => (a op b) op (m op n)) */
        a1 = mkb(op, te, arg1_(a1), arg1_(a2), valneeded);
        a2 = EvalBinaryOp(op, te, arg2_(a2), k1);
      } else {
        a1 = mkb(op, te, arg1_(a1), a2, valneeded);
        a2 = k1;
      }
    }
    if (h0_(a2) == op && h0_(arg2_(a2)) == s_integer) {
    /* a op (b op n) => (a op b) op n */
      a1 = mkb(op, te, a1, arg1_(a2), valneeded);
      a2 = arg2_(a2);
    }
    if (h0_(a2) == s_integer) {
      if (op == s_and) {
        AEop op2 = h0_(a1);
        Expr *a, *a11 = arg1_(a1);
        int32 k = intval_(a2);
        /* ((a & k1) op b) & k  where (~k1 & k) == 0
         *    => (a op b) & k
         * (((a << n) >> n) op b) & k  (top n bits of k are 0)
         *    => (a op b) & k
         * (((a << n) >> m) op b) & k  (m > n, top m bits of k are 0)
         *    => ((a >> (m-n)) op b) & k
         *
         * additionally, for the first case and op == + or -,
         * k must be 2^p-2^q. For simplicity, at no great cost,
         * we require k = 2^p-1 for all cases.
         */

        if ((op2 == s_and || op2 == s_or || op2 == s_xor) &&
            (a = RemovableSignOrZeroExtension(a11, k)) != NULL)
          arg1_(a1) = a;

        else if (op2 == s_plus || op2 == s_minus) {
          int32 n = k+1;
          if ((n & -n) == n &&
              (a = RemovableSignOrZeroExtension(a11, k)) != NULL)
            arg1_(a1) = a;
        }
        /* ((a << n) >> n) & k  (top n bits of k are 0)
         *    => a & k
         * ((a << n) >> m) & k  (m > n, top m bits of k are 0)
         *    => (a >> (m-n)) & k
         * (the apparent transformation of (a & k) & k1 has already
         *  been handled above).
         */
        else if ((a = RemovableSignOrZeroExtension(a1, k)) != NULL)
          a1 = a;

      /* (a | k1) & k => (a & k) | (k & k1) */
        if (op2 == s_or && h0_(arg2_(a1)) == s_integer) {
          Expr *x1 = a1;
          a1 = mkb(s_and, type_(x1), arg1_(x1), a2, valneeded);
          a2 = EvalBinaryOp(s_and, te, arg2_(x1), a2);
          h0_(e) = op = s_or;
        }
      }
    /* (a & ~k) | k gets transformed here to a | k, to cheer up
     * a common bitfield-setting case
     */
      if (op == s_or &&
          h0_(a1) == s_and && h0_(arg2_(a1)) == s_integer &&
        intval_(a2) == ~intval_(arg2_(a1)))
        a1 = arg1_(a1);

      if (op == s_times) {
      /* (a << n) * m =>  a * (m << n)
       *  if (m << n) doesn't overflow
       */
        if (h0_(a1) == s_leftshift && h0_(arg2_(a1)) == s_integer) {
          int32 shift = intval_(arg2_(a1));
          int32 n1 = intval_(a2), n2 = ((unsigned32)1 << shift);
          int32 n3 = n1 * n2;
          if ((n1 ^ n3 >= 0) && (n3 / n2 == n1)) {
            a1 = arg1_(a1);
            a2 = mkintconst(te_int, n3, 0);
          }
        }
        if (h0_(a1) == s_plus && h0_(arg2_(a1)) == s_integer) {
        /* (a + m) * n => (a * n) + (m * n) */
          Expr *x1 = a1;
          a1 = mk_expr2(s_times, type_(x1), arg1_(x1), a2);
          a2 = EvalBinaryOp(s_times, te, arg2_(x1), a2);
          h0_(e) = op = s_plus;
        } else if (h0_(a1) == s_neg) {
        /* (- a) * n => - (a * n) */
          int32 n = intval_(a2);
          if (n < 0)
            return mk_expr2(s_times, te, arg1_(a1), mkintconst(te_int, n, 0));
          else
            return mk_expr1(s_neg, te, mk_expr2(s_times, te, arg1_(a1), a2));
        }
      }
    }
    if (op == s_plus) {
    /* a + -b => a - b; -a + b => b-a */
        if (h0_(a2) == s_neg)
            h0_(e) = s_minus, a2 = arg1_(a2);
        else if (h0_(a1) == s_neg) {
            Expr *t = a2;
            h0_(e) = s_minus, a2 = arg1_(a1);
            a1 = t;
        }
    }
    if (op == s_or &&
        h0_(a1) == s_and && h0_(arg2_(a1)) == s_integer &&
        h0_(a2) == s_and && h0_(arg2_(a2)) == s_integer) {

      int32 k1 = intval_(arg2_(a1)),
            k = intval_(arg2_(a2));
      if (is_same(arg1_(a1), arg1_(a2))) {
      /* (x & k1) | (x & k) => x & (k1 | k)
       * Motivation: clean up expansion of bitfield &= k.
       */
        return mkb(s_and, te, arg1_(a1), mkintconst(te, k | k1, 0), valneeded);

      } else if (k1 == ~k) {
       /* (x & ~k) | ((x op y) & k) => x op (y & k)
        *  op = or, xor, or
        *  op = plus or minus and k is the top n bits (some n)
        *  *not* op = and, which will clear bits outside k.
        * Motivation: clean up expansion of bitfield op=.
        */
        AEop op2 = h0_(arg1_(a1));
        if (op2 == s_and || op2 == s_or || op2 == s_xor ||
            op2 == s_plus || op2 == s_minus) {
          Expr *t = a1; a1 = a2; a2 = t;
          k = k1;
        }
        op2 = h0_(arg1_(a2));
        if (( (op2 == s_and || op2 == s_or || op2 == s_xor) ||
              ( (op2 == s_plus || op2 == s_minus) &&
                k + (k & -k) == 0)
            ) &&
            is_same(arg1_(a1), arg1_(arg1_(a2)))) {
          Expr *y = arg2_(arg1_(a2));
          TypeExpr *t = type_(a2);
          h0_(e) = op2;
          a1 = arg1_(a1);
          if (op2 == s_and) {
          /* for op = and, the replacement is x & ~(~y & k)    */
          /* (equivalently, x & (y | ~k), but assuming k is    */
          /* compact and ~k isn't, the former is a better form.*/
            if (h0_(y) == s_bitnot)
              y = arg1_(y);

            else if (h0_(y) == s_leftshift && h0_(arg2_(y)) == s_integer &&
                     ((((int32)1 << intval_(arg2_(y))) - 1) & k) == 0 &&
                     h0_(IgnoreSignednessChange(arg1_(y))) == s_bitnot) {
              Expr *shval = arg2_(y);
              y = IgnoreSignednessChange(arg1_(y));
              y = mk_expr2(s_leftshift, t, arg1_(y), shval);

            } else
              y = mk_expr1(s_bitnot, t, y);

            a2 = mk_expr1(s_bitnot, t,
                   mk_expr2(s_and, t, y, arg2_(a2)));

          } else
#ifdef TARGET_HAS_SCALED_OPS
            /* if y has the form (z << n), change the transformation
             * result x op (y & k)  to  x op ((z & (k >> n)) << n)
             * (to allow the shift to be included in op)
             */
          if (h0_(y) == s_leftshift && h0_(arg2_(y)) == s_integer)
            a2 = mk_expr2(s_leftshift, t,
                   mk_expr2(s_and, t, arg1_(y),
                     mkintconst(t, (unsigned32)k >> intval_(arg2_(y)), 0)),
                   arg2_(y));
          else
#endif
          if (h0_(y) == s_integer)
            a2 = mkintconst(t, k & intval_(y), 0);
          else
            a2 = mk_expr2(s_and, t, y, arg2_(a2));
        }
      }
    }
symmetric_done:
    arg1_(e) = a1;
    arg2_(e) = a2;
    return e;
}

static int32 checkdotoff(Expr const *e) {
    int32 off = exprdotoff_(e);
    if (off == OFFSET_UNSET) { syserr("undefined dot offset"); off = 0; }
    return off;
}

typedef struct {
  AEop op;
  Expr *e;
  int32 n;
} CompKDesc;

static bool IsCompareK(Expr *e, CompKDesc *kd) {
  AEop op = h0_(e);
  if (isinequality_(op)) {
    int32 n;
    if (h0_(arg2_(e)) == s_integer) {
      kd->e = arg1_(e);
      n = intval_(arg2_(e));
    } else if (h0_(arg1_(e)) == s_integer) {
      switch (op) {
      case s_greater:      op = s_less; break;
      case s_greaterequal: op = s_lessequal; break;
      case s_less:         op = s_greater; break;
      case s_lessequal:    op = s_greaterequal; break;
      }
      kd->e = arg2_(e);
      n = intval_(arg1_(e));
    } else
      return NO;
    if (op == s_greater) {
      if ((mcrepofexpr(kd->e) & MCR_SORT_MASK) == MCR_SORT_UNSIGNED) {
        if (n == just32bits_(-1))
          return NO;
      } else {
        if (n == 0x7fffffff)
          return NO;
      }
      n++;
      op = s_greaterequal;
    }
    kd->op = op;
    kd->n = n;
    return YES;
  }
  return NO;
}

static Expr *OptimiseComparePair(CompKDesc const *k1, CompKDesc const *k2) {
  AEop op = s_nothing;
  int32 low, high;
  if (k1->op == s_greaterequal) {
    low = k1->n;
    if (k2->op == s_less || k2->op == s_lessequal) {
      op = k2->op;
      high = k2->n;
    }
  } else if (k1->op == s_less || k1->op == s_lessequal) {
    op = k1->op;
    high = k1->n;
    if (k2->op == s_greaterequal) {
      low = k2->n;
    }
  }
  if (op != s_nothing) {
    int32 mcr = mcrepofexpr(k1->e);
    if (((mcr & MCR_SORT_MASK) == MCR_SORT_UNSIGNED
         && (uint32)low < (uint32)high)
        || (high - low) > 0) {
      Binder *b = gentempbinder(te_uint);
      TypeExpr *t = typeofexpr(k1->e);
      Expr *a1 = low == 0 ? k1->e :
                            mk_expr2(s_minus, t, k1->e, mkintconst(t, low, 0));
      return mk_exprlet(s_let, te_int, mkSynBindList(0, b),
        mk_expr2(s_comma, te_int,
          mk_expr1(s_cast, te_void,
            mk_expr2(s_assign, te_uint, (Expr *)b,
              mk_expr1(s_cast, te_uint, a1))),
          mk_expr2(op, te_int, (Expr *)b,
            mkintconst(te_uint, high-low, 0))));
    }
  }
  return NULL;
}

static AEop NegateRelop(AEop op) {
  switch (op) {
  case s_equalequal:   return s_notequal;
  case s_notequal:     return s_equalequal;
  case s_greater:      return s_lessequal;
  case s_less:         return s_greaterequal;
  case s_greaterequal: return s_less;
  case s_lessequal:    return s_greater;
  default:             syserr("NegateRelop");
                       return s_nothing;
  }
}

static Expr *MkBoolNot(Expr *e) {
  if (isrelational_(h0_(e)))
    return mk_expr2(NegateRelop(h0_(e)), type_(e), arg1_(e), arg2_(e));
  else
    return mk_expr1(s_boolnot, type_(e), e);
}

static Expr *optimise1(Expr *e, bool valneeded, bool *pure)
{   AEop op = h0_(e);
    Expr *e1;
    bool purea1, purea2;
    *pure = YES;
    if (debugging(DEBUG_AETREE) && syserr_behaviour > 0) {
#ifndef NO_RETURN_EXPRESSIONS
      if (op != s_return)
#endif
        pr_exproftype("optimise1: ", e);
    }
    switch (op)
    {
#ifdef PASCAL /*ECN*/
        case s_error:
            return lit_zero;
#endif
        case s_integer:
        case s_int64con:
        case s_floatcon:
        case_s_any_string
#ifdef EXTENSION_VALOF
        case s_valof:
#endif
        case s_binder:
            {   Binder *b = exb_(e);
                /* Get rid of template arg binder */
                if (valneeded && is_template_arg_binder(e) && bindconst_(b) != NULL)
                    e = bindconst_(b);
                break;
            }
        case s_invisible:
            e = optimise1(arg2_(e), valneeded, pure);
            break;
        case s_evalerror:
            if (has_template_arg_scope() && arg3_(e) == NULL)
                /* silent mode */
                ;
            else
                cc_warn((msg_t)arg3_(e), h0_(arg2_(e)));
            e = optimise1(arg1_(e), valneeded, pure);
            break;
        case s_throw:
            *pure = NO;
            if (arg1_(e) != NULL) arg1_(e) = optimise1(arg1_(e), YES, &purea1);
            break;
#ifndef NO_RETURN_EXPRESSIONS  /* perhaps soon dropped for C too.       */
        case s_return:
            e = arg1_(e);
            if (h0_(e) != s_fnap) { e = optimise1(e, YES, pure); break; }
            /* drop through */
#endif
        case s_fnap:
            *pure = NO;
            e = optimisefnap(e);
#ifndef NO_RETURN_EXPRESSIONS
            if (op == s_return) break;
#endif
            /*
             * Does this function return a struct ?.  If so carry out a
             * transformation from 'fn()' to (let x; x=fn(),x)'.
             * Note: Temp binders are allocated in optimise0().
             * CPLUSPLUS: beware _ctor/_dtor and temps.
             * @@@ LDS 18-Oct-94: Partly fixed... reftemps() lifetimes wrong.
             */
            /* The condition following looks weird, but can be explained by
               the dualities:
               double <-> MCR_SORT_STRUCT
               single-word struct <-> int ie ~MCR_SORT_STRUCT
             */
            if ((mcrepofexpr(e) & MCR_SORT_MASK) == MCR_SORT_STRUCT)
            {   TypeExpr *t = typeofexpr(e);
                Binder *gen;
                bool usefancytemp = NO;
                if (LanguageIsCPlusPlus)
                {   TypeExpr *pt = princtype(t);
                    /* use a fancy C++ temp if this is an object of class type
                       that needs a ctor or has a dtor */
                    if (isclasstype_(pt) &&
                        tagbindbits_(typespectagbind_(pt)) & (TB_NEEDSCTOR|TB_HASDTOR))
                        usefancytemp = YES;
                }
                /* Note that this can't happen when optimise0 is called from
                 * cg, because then all structure-returning functions are on
                 * the rhs of assignments (assured by the call to optimise0
                 * before the tree is handed to cg), and for fn calls on the
                 * rhs of assignments optimise1 isn't called for the fn call,
                 * just optimisefnap (see below).
                 * If it could happen, the call to genreftemp / genexprtemp
                 * below would cause trouble, since the temporaries thus
                 * created wouldn't be bound.
                 */
                if (usefancytemp)
                    gen = (in_args || !valneeded) ? genexprtemp(t) : genreftemp(t);
                else
                {   gen = gentempbinder(t);
                    new_binders = mkSynBindList(new_binders, gen);
                }
                e = mk_expr2(s_assign, t, (Expr*)gen, e);
                if (valneeded)
                    e = mk_expr2(s_comma, t, e, (Expr*)gen);
            }
            break;
        case s_init:
        case s_assign:
            *pure = NO;
            e1 = optimise1(arg1_(e), YES, &purea1);
/* Nastiness here in C++: consider:                                     */
/*      class B: virtual A { ...};                                      */
/*      class D:B { ... };                                              */
/*      B f() { ... }                                                   */
/*      main() { D d; B &b = d; b = f(); }                              */
/* In general f() will CONSTRUCT a B in its implicit extra arg.         */
/* It must also construct vbases/vfns for a B since it does not know    */
/* the use the caller will make of it.  Hence eliding the b = f()       */
/* would corrupt b's and hence d's vbases/vfns.                         */
/* However, we could remove a 'struct_result = f()' copy ctor.          */
/* Use 'isproperclass()' to determine this.                             */
/* @@@ hmm, for such a b with a vbase, we would have generated a fncall */
/* instead of an assign already (or a partial assign).                  */

            /* Introduced by optimise1 for integer-like structs, but    */
            /* having no meaning on the lhs of an assignment            */
            if (h0_(e1) == s_cast) e1 = arg1_(e1);
            arg1_(e) = e1;
            if (h0_(e1) == s_cond) {
                TypeExpr *t1 = typeofexpr(e1);
                Binder *gen = gentempbinder(t1);
                e = optimise1(
                    mk_exprlet(s_let, t1, mkSynBindList(0, gen),
                        mk_expr2(s_comma, t1,
                            mk_expr1(
                                s_cast, te_void,
                                mk_expr2(s_init, t1, (Expr *)gen, arg2_(e))),
                            mk_expr3(s_cond, t1,
                                arg1_(e1),
                               mk_expr2(s_assign, t1, arg2_(e1), (Expr *)gen),
                               mk_expr2(s_assign, t1, arg3_(e1), (Expr *)gen)))),
                    YES, &purea1);
                break;
            }
            if (h0_(e1) == s_binder  ||
                h0_(e1) == s_content ||
                h0_(e1) == s_content4)
            /* s_dot is now impossible (it's been turned into *(a+k))   */
            {   Expr *a2 = arg2_(e);
                if (h0_(a2) == s_fnap)
/* Specifically avoid the temp introduction (case s_fnap above) for     */
/* struct-returning functions whose result is directly                  */
/* assigned to a binder or via s_content...                             */
                {   if (h0_(e1) != s_binder && HasFeature(Feature_Fussy)
                        && !returnsstructinregs(arg1_(a2)))
                    {   /* ...except in strict ANSI mode, if it is      */
                        /* possible that the assignment target may      */
                        /* overlap the source of the value returned by  */
                        /* the called function (when the result is      */
                        /* well-defined)                                */
                        arg2_(e) = optimise1(arg2_(e), YES, &purea1);
                        break;
                    }
                    arg2_(e) = optimisefnap(a2);
                    break;
                }
                if (h0_(a2) == s_let)
                {   Expr *a22 = arg2_(a2);
                    if (h0_(a22) == s_fnap)
                    {   arg2_(a2) = optimisefnap(a22);
                        break;
                    }
                }
            }
            {   Expr *a2 = optimise1(arg2_(e), YES, &purea1);
                if ( !valneeded &&
                     h0_(a2) == s_cast &&
                     mcrepofexpr(arg1_(a2)) < MCR_SORT_FLOATING &&
                     (mcrepofexpr(e1) & MCR_SIZE_MASK) == 1 &&
                     h0_(e1) != s_binder)
                  a2 = arg1_(a2);
                arg2_(e) = a2;
            }
            break;
        case s_addrof:
            e1 = optimise1(arg1_(e), YES, pure);
            if (h0_(e1) == s_comma || h0_(e1) == s_let)
            {   /* & (a, b) -> (a, & b); & (let x in e) -> (let x in & e) */
                e = mk_expr2(h0_(e1), type_(e), arg1_(e1),
                        optimise1(mk_expr1(s_addrof, type_(e), arg2_(e1)), YES, &purea1));
                break;
            } else  if (h0_(e1) == s_cond)
            {   /* &(a ? b: c) -> (a ? &b : &c) */
                e = mkcond(arg1_(e1), mkunary(s_addrof, arg2_(e1)),
                           mkunary(s_addrof, arg3_(e1)));
                break;
            } else if (h0_(e1) == s_assign || h0_(e1) == s_init)
            {   /* & a = b -> (a = b, & a) */
/* @@@ AM: this is wrong for side-effects in 'a'!!!?            */
                e = mk_expr2(s_comma, type_(e), e1,
                    optimise1(mk_expr1(s_addrof, type_(e), arg1_(e1)), YES, &purea1));
                break;
            }
/* The following line fixes a problem that shouldn't occur, as &(cast)   */
/* is illegal. However, it can occur because we recover from ++(type *)p */
/* even though ANSI disallow. Either way, a diagnostic has already been  */
/* issued (or a warning in -pcc mode) so there seems to be little excuse */
/* for generating a syserr(). Note that it also legitimises &(cast)var;  */
/* but not silently. Win some, lose some.                                */
            while (h0_(e1) == s_cast) e1 = arg1_(e1);
            arg1_(e) = e1;
            if (h0_(e1) == s_content || h0_(e1) == s_content4) { e = arg1_(e1); break; }
            if (isstring_(h0_(e1))) {
                e = e1;                     /* cg thinks addr already */
                break;
            }
            if (h0_(e1) == s_dot) syserr("s_dot output from optimise1");
            if (h0_(e1) != s_binder && h0_(e1) != s_comma && h0_(e1) != s_int64con
                && h0_(e1) != s_floatcon
                && !istypevar(typeofexpr(e1))
                && !(software_floating_point_enabled && h0_(e1) == s_floatcon)
               )
                /* Check that we have a binder for &.  However, beware we
                 * might have a structure returning function which will
                 * get transformed above.  Should test for this fully but
                 * testing for s_comma is probably ok !.
                 */
                syserr("optimise&(%ld,$s)", (long)h0_(e1), h0_(e1));
                /* syserr(syserr_optimise, (long)h0_(e1)); */
            break;

        case_content:
        case s_content4:
        case s_content:  /* get rid of extra &'s and *'s introduced above */
            arg1_(e) = e1 = optimise1(arg1_(e), YES, pure);
            if (h0_(e1) == s_addrof &&
                /* the next line ensures *(int*)&d -> d only if types match */
                same_pointedto_types(e, arg1_(e1)))
            {   e = arg1_(e1);
                if (valneeded && e && h0_(e) == s_binder
                    && bindconst_(exb_(e)) != NULL)
                    e = bindconst_(exb_(e));
            }
            break;
        case s_dot:     /* replace s_dot with s_content */
        case s_qualdot: /* always an error or syserr */
            e1 = arg1_(e);
            if (e1 == NULL)
                syserr("optimize1: bad null in dot expr");
            if (h0_(e1) == s_binder && bindsym_(exb_(e1)) == NULL)
            {   cc_err(simplify_err_illegal_use_of_mem_fn, exb_(arg2_(e)));
                longjmp(optimise0_jb, 1);
            }
            if (op == s_qualdot)
                syserr("optimize1: s_qualdot");
            /* NB. all s_dot code can be removed from cg.            */
            if ((mcrepofexpr(e1) & MCR_SORT_MASK) != MCR_SORT_STRUCT)
            {   /* Fetching a word from a single-word struct!.          */
                /* Probably just e (see cg_content_for_dot).        */
                /* @@@ Check 'volatile'.                                */
                /* Insert cast so types are right (e.g. for cg_fnap).   */
                /* This code wouldn't work for a byte in a union!       */
                if (mcrepofexpr(e1) == 0x00000004 && exprdotoff_(e)==0)
                {   e = optimise1(mk_expr1(s_cast, type_(e), e1), YES, pure);
                    break;
                }
                else
                    syserr("optimise(dot one word)");
            }
            else
            {   TypeExpr *tp = ptrtotype_(type_(e));
                Expr *e2 = mkintconst(te_int, checkdotoff(e), 0);
                TypeExpr *te1 = typeofexpr(e1);
                AEop op = ((config & CONFIG_STRUCT_PTR_ALIGN)
                           && sizeoftypelegal(te1)
                           && alignoftype(te1) >= 4) ? s_content4
                                                     : s_content;
/* Beware, assumes optimise(s_fnap(struct)) is address takeable!.       */
                e = mk_expr1(op, type_(e),
                      mk_expr2(s_plus, tp,
                        mk_expr1(s_addrof, tp, e1), e2));
            }
            goto case_content;
        case s_dotstar:
            e1 = arg1_(e);
            if ((mcrepofexpr(e1) & MCR_SORT_MASK) != MCR_SORT_STRUCT)
            {   /* Fetching a word from a single-word struct!.          */
                /* Replace with (e2, e1), i.e. eval e2 for side-effects */
                /* and return e1.  Implies p->*NULL == p->*(&S::s)!!    */
                if (mcrepofexpr(e1) == 0x00000004)
                {   e = optimise1(
                            mk_expr2(s_comma, type_(e), arg2_(e), e1),
                            YES, pure);
                    break;
                }
                else
                    syserr("optimise(dotstar one word)");
            }
            else
            {   TypeExpr *tp = ptrtotype_(type_(e));
                Expr *e2 = arg2_(e);
                /* follow [ES] suggestion for ptr-to-member rep.        */
                e2 = mk_expr2(s_minus, typeofexpr(e2), e2, lit_one);
/* Beware, assumes optimise(s_fnap(struct)) is address takeable!.       */
                e = mk_expr1(s_content, type_(e),
                      mk_expr2(s_plus, tp,
                        mk_expr1(s_addrof, tp, e1), e2));
            }
            goto case_content;
        case s_cond:
            e1 = e;
            arg1_(e) = optimise1(arg1_(e), YES, &purea1);
            if (is_intzero(arg3_(e)) && is_intone(arg2_(e))) {
              *pure = purea1;
              e = arg1_(e);
              break;
            } else if (is_intzero(arg2_(e)) && is_intone(arg3_(e))) {
              *pure = purea1;
              e = MkBoolNot(arg1_(e));
              break;
            }
            if ((mcrepofexpr(e) & MCR_SORT_MASK) == MCR_SORT_STRUCT)
            {   /* The expression is struct-valued */
                TypeExpr *te = type_(e);
                TypeExpr *pt = ptrtotype_(te);
                type_(e) = pt;
                e1 = mk_expr1(s_content, te, e);
                arg2_(e) = mk_expr1(s_addrof, pt, arg2_(e));
                arg3_(e) = mk_expr1(s_addrof, pt, arg3_(e));
            }
            arg2_(e) = optimise1(arg2_(e), valneeded, &purea2);
            purea1 = purea1 & purea2;
            arg3_(e) = optimise1(arg3_(e), valneeded, &purea2);
            *pure = purea1 & purea2;
            e = e1;
            break;
        case s_qualified|s_let:
        case s_let:
            arg2_(e) = optimise1(arg2_(e), valneeded, pure);
            break;
        case s_cast:
             arg1_(e) = optimise1(arg1_(e), valneeded && mcrepofexpr(e) != 0, pure);
            e = optimise_cast(e);
            break;
        case s_and:
        case s_times:
        case s_plus:
        case s_or:
        case s_xor:        /* these are both commutative and associative */
        case s_minus:      /* this isn't -- see goto below */
        case s_div:        /* nor this */
        case s_rem:
            {   Expr *a1 = optimise1(arg1_(e), YES, &purea1);
                Expr *a2 = optimise1(arg2_(e), YES, &purea2);
                e = optimise1b(e, a1, a2, purea1, purea2, valneeded);
                *pure = purea1 & purea2;
            }
            break;
#ifdef RANGECHECK_SUPPORTED
        case s_rangecheck:
            if (arg3_(e) != NULL) arg3_(e) = optimise1(arg3_(e), YES, pure);
            /* drop through */
        case s_checknot:
            arg1_(e) = optimise1(arg1_(e), YES, &purea1);
            if (arg2_(e) != NULL) arg2_(e) = optimise1(arg2_(e), YES, pure);
            *pure = *pure & purea1;
            break;
#endif
        case s_greater:
        case s_less:
        case s_greaterequal:
        case s_lessequal:
          { Expr *a1 = optimise1(arg1_(e), YES, &purea1);
            Expr *a2 = optimise1(arg2_(e), YES, &purea2);
            *pure = purea1 & purea2;
            if (*pure && HasIntegralType(a1) && is_same(a1, a2)) {
              e = mkintconst(te_int, op == s_greaterequal || op == s_lessequal, 0);
              break;
            }
            arg1_(e) = a1;
            arg2_(e) = a2;
            break;
          }
        case s_equalequal:
        case s_notequal:
          { Expr *a1 = optimise1(arg1_(e), YES, &purea1);
            Expr *a2 = optimise1(arg2_(e), YES, &purea2);
            *pure = purea1 & purea2;
            if (h0_(a1) == s_integer) { Expr *w = a1; a1 = a2; a2 = w; }
            if (*pure && HasIntegralType(a1) && is_same(a1, a2)) {
              e = mkintconst(te_int, op == s_equalequal, 0);
              break;
            } else if (h0_(a2) == s_integer) {
              int32 n = intval_(a2);
              if (isrelational_(h0_(a1))
                  || h0_(a1) == s_andand
                  || h0_(a1) == s_oror) {
                if ((op == s_notequal) != (n == 1))
                  e = a1;
                else
                  e = MkBoolNot(a1);
                break;
              }
              if (h0_(a1) == s_cond
                  && (h0_(arg2_(a1)) == s_integer || h0_(arg3_(a1)) == s_integer)) {
                Expr *newa1, *newa2;
                if (h0_(arg2_(a1)) == s_integer)
                  newa1 = mkintconst(type_(e), (intval_(arg2_(a1)) == n) ^ (op != s_equalequal), 0);
                else
                  newa1 = optimise1(mk_expr2(op, type_(e), arg2_(a1), a2), valneeded, &purea1);
                if (h0_(arg2_(a1)) == s_integer)
                  newa2 = mkintconst(type_(e), (intval_(arg3_(a1)) == n) ^ (op != s_equalequal), 0);
                else
                  newa2 = optimise1(mk_expr2(op, type_(e), arg3_(a1), a2), valneeded, &purea2);
                e = optimise1(mk_expr3(s_cond, type_(e), arg1_(a1), newa1, newa2), valneeded, &purea1);
                break;
              }
            /* in comparison of signed char for (in)equality against positive
             * constant <= SCHAR_MAX, cast the signed char to unsigned char
             * (in the belief that zero extension is cheaper than sign extn).
             */
              if (h0_(a1) != s_binder &&
                  n >= 0 && n < (1 << 7)) {
                TypeExpr *t = prunetype(typeofexpr(a1));
                if (h0_(t) == s_typespec) {
                  SET_BITMAP tm = typespecmap_(t);
                  if ((tm & (bitoftype_(s_char)|bitoftype_(s_signed))) ==
                            (bitoftype_(s_char)|bitoftype_(s_signed))) {
                    tm ^= (bitoftype_(s_signed)|bitoftype_(s_unsigned));
                    a1 = optimise1(mkcast(s_cast, a1, primtype_(tm)), YES, &purea1);
                  }
                }
              }
              if (h0_(a1) == s_or && h0_(arg2_(a1)) == s_integer) {
                int32 n1 = intval_(arg2_(a1));
                if (purea1 && (n & n1) != n1) {
                  e = mkintconst(te_int, op == s_notequal, 0);
                  break;
                }
              } else if (h0_(a1) == s_and && h0_(arg2_(a1)) == s_integer) {
                int32 n1 = intval_(arg2_(a1));
                if (purea1 && (n & n1) != n) {
                  e = mkintconst(te_int, op == s_notequal, 0);
                  break;
                }
              }
              if (n == 0) {
                a1 = IgnoreSignednessChange(a1);
                if (h0_(a1) == s_and && h0_(arg2_(a1)) == s_integer) {
                /* This is meant to improve comparisons of (unsigned) bitfields
                 * against 0. It turns the lh operand from (a shift n1) & n2
                 * into a & (n2 opposite_shift n1).
                 */
                  int32 n1 = intval_(arg2_(a1));
                  Expr *a11 = IgnoreSignednessChange(arg1_(a1));
                  if (h0_(a11) == s_rightshift &&
                    h0_(arg2_(a11)) == s_integer) {
                    int32 n2 = intval_(arg2_(a11));
                    if ((n1 & ((int32)-1 << (32 - n2))) == 0 ||
                        (mcrepofexpr(a11) & MCR_SORT_MASK) == MCR_SORT_UNSIGNED) {
                      arg1_(a1) = arg1_(a11);
                      arg2_(a1) = mkintconst(type_(a1), n1 << n2, 0);
                    }
                  } else if (h0_(a11) == s_leftshift &&
                             h0_(arg2_(a11)) == s_integer) {
                    int32 n2 = intval_(arg2_(a11));
                    arg1_(a1) = arg1_(a11);
                    arg2_(a1) = mkintconst(type_(a1), just32bits_((unsigned32)n1) >> n2, 0);
                  }
                } else if (h0_(a1) == s_rightshift && h0_(arg2_(a1)) == s_integer) {
                /* This is meant to improve comparisons of (signed) bitfields
                 * against 0. It turns the lh operand from (a << n2) >> n1
                 * (n1 >= n2) into (a & k) where k has n2 ms and (n1-n2) ls 0s
                 * and other bits 1.
                 */
                  int32 n1 = intval_(arg2_(a1)),
                        n2 = 0,
                        mask = 0;
                  Expr *a11 = IgnoreSignednessChange(arg1_(a1));
                  if (h0_(a11) == s_leftshift && h0_(arg2_(a11)) == s_integer) {
                    n2 = intval_(arg2_(a11));
                    a11 = arg1_(a11);
                    mask = (int32)1 << (32-n2);
                    /* relying on x<<0 having previously been transformed into x */
                    /* to avoid an undefined << 32.                              */
                  }
                  if (n2 <= n1) {
                    mask -= (int32)1 << (n1-n2);
                    h0_(a1) = s_and;
                    arg1_(a1) = a11;
                    arg2_(a1) = mkintconst(type_(a1), mask, 0);
                  }
                }
              }
            }
            arg1_(e) = a1;
            arg2_(e) = a2;
            break;
          }
        case s_leftshift:
        case s_rightshift:
          /* bitfield op=.
           * turns ((((x >> n) op y) & m) << n)
           * [already partly optimised from (((((x >> n) & m) op y) & m) << n)]
           * into (x op (y << n)) & (m << n)
           * (also ((((x >> n) & m) | y) << n), y constant, (y & m) == y, a
           *  mistaken transformation of the above)
           */
          { AEop op2 = s_nothing;
            Expr *e0l = optimise1(arg1_(e), YES, &purea1);
            Expr *e0r = optimise1(arg2_(e), YES, &purea2);
            Expr *e1l = NULL, *e1r = NULL, *e2l = NULL, *e3r;
            *pure = purea1 & purea2;

            /* convert (a op n) op m -> a op (n+m) */
            if (h0_(e0l) == op && h0_(e0r) == s_integer && h0_(arg2_(e0l)) == s_integer)
            {
                intval_(e0r) += intval_(arg2_(e0l));
                e0l = arg1_(e) = arg1_(e0l);
            }
            if (op == s_leftshift && h0_(e0r) == s_integer) {
              if (h0_(e0l) == s_and && h0_(e1r = arg2_(e0l)) == s_integer) {
                e1l = arg1_(e0l);
                op2 = h0_(e1l);
                if (op2 == s_plus || op2 == s_minus ||
                    op2 == s_and || op2 == s_or || op2 == s_xor)
                  e2l = arg1_(e1l);
                else if (op2 == s_rightshift)
                  e2l = e1l;
              } else if (h0_(e0l) == s_or && h0_(e1r = arg2_(e0l)) == s_integer &&
                         h0_(e1l = arg1_(e0l)) == s_and && h0_(arg2_(e1l)) == s_integer &&
                         (intval_(e1r) & intval_(arg2_(e1l))) == intval_(e1r)) {
                op2 = s_or;
                e2l = arg1_(e1l);
                e1r = arg2_(e1l);
                e1l = e0l;
              }
              if (e2l != NULL &&
                  h0_(e2l) == s_rightshift &&
                  h0_((e3r = arg2_(e2l))) == s_integer) {
                int32 nr = intval_(e3r),
                      nl = intval_(e0r);
                Expr *a21l = arg2_(e1l),
                     *a1 = op2 == s_rightshift ?
                             arg1_(e2l) :
                             mk_expr2(
                               op2, type_(e0l),
                               arg1_(e2l),
                               h0_(a21l) == s_integer ?
                                 mkintconst(type_(e0l), intval_(a21l) << nr, 0) :
                                 mk_expr2(s_leftshift, type_(e0l), a21l, e3r)),

                     *a2 = mkintconst(type_(e0l), intval_(e1r) << nr, 0);

                if (nl == nr) {
                  h0_(e) = s_and;
                  e0l = a1;
                  e0r = a2;
                } else if (nl > nr) {
                  e0l = mk_expr2(s_and, type_(e0l), a1, a2);
                  e0r = mkintconst(type_(e0r), nl - nr, 0);
                }
              }
            }
            arg1_(e) = e0l;
            arg2_(e) = e0r;
            break;
          }

        case s_plusplus: case s_minusminus:
        case s_displace:
            *pure = NO;
            arg1_(e) = optimise1(arg1_(e), YES, &purea1);
            arg2_(e) = optimise1(arg2_(e), YES, &purea1);
            break;

        case s_andand:
          { Expr *newe = NULL,
                 *a1 = optimise1(arg1_(e), YES, &purea1),
                 *a2 = optimise1(arg2_(e), YES, &purea2);
            *pure = purea1 & purea2;
            if (purea1 && purea2) {
              CompKDesc k1, k2;
              bool comp1 = IsCompareK(a1, &k1),
                   comp2 = IsCompareK(a2, &k2);
              if (comp1 && comp2 && is_same(k1.e, k2.e)) {
                newe = OptimiseComparePair(&k1, &k2);
                if (newe != NULL) {
                  e = newe;
                  break;
                }
              } else if (comp1 && h0_(a2) == s_andand) {
                if (IsCompareK(arg1_(a2), &k2) && is_same(k1.e, k2.e)) {
                  newe = OptimiseComparePair(&k1, &k2);
                  if (newe != NULL) {
                    a1 = newe;
                    a2 = arg2_(a2);
                  }
                } else if (IsCompareK(arg2_(a2), &k2) && is_same(k1.e, k2.e)) {
                  newe = OptimiseComparePair(&k1, &k2);
                  if (newe != NULL) {
                    a1 = newe;
                    a2 = arg1_(a2);
                  }
                }
              } else if (comp2 && h0_(a1) == s_andand) {
                if (IsCompareK(arg1_(a1), &k1) && is_same(k1.e, k2.e)) {
                  newe = OptimiseComparePair(&k1, &k2);
                  if (newe != NULL) {
                    a1 = arg2_(a1);
                    a2 = newe;
                  }
                } else if (IsCompareK(arg2_(a1), &k1) && is_same(k1.e, k2.e)) {
                  newe = OptimiseComparePair(&k1, &k2);
                  if (newe != NULL) {
                    a1 = arg1_(a1);
                    a2 = newe;
                  }
                }
              }
            }
            arg1_(e) = a1; arg2_(e) = a2;
            break;
          }
        case s_bitnot:
        case s_neg:
          { Expr *a1 = optimise1(arg1_(e), YES, pure);
            if (*pure && HasIntegralType(e)) {
              if (h0_(a1) == op) {
                e = arg1_(a1);
                break;
              }
            }
            arg1_(e) = a1;
            break;
          }
        case s_boolnot:
          { Expr *a1 = optimise1(arg1_(e), YES, pure);
            if (isrelational_(h0_(a1)))
              e = mk_expr2(NegateRelop(h0_(a1)), type_(e), arg1_(a1), arg2_(a1));
            else
              arg1_(e) = a1;
            break;
          }

        default:
            if (ismonad_(op))
                arg1_(e) = optimise1(arg1_(e), YES, pure);
            else if (isdiad_(op)) {
                arg1_(e) = optimise1(arg1_(e), YES, &purea1);
                arg2_(e) = optimise1(arg2_(e), YES, &purea2);
                *pure = purea1 & purea2;
            } else syserr(syserr_optimise1, (long)op);
            break;
    }
    if (debugging(DEBUG_AETREE) && syserr_behaviour > 0) {
#ifndef NO_RETURN_EXPRESSIONS
      if (op != s_return)
#endif
        pr_exproftype("optimise1= ", e);
    }
    return e;
}

static SynBindList *optimiselist(ExprList *x)
{   SynBindList *letbindings = NULL;
    bool dummy;
    for (; x != 0; x = cdr_(x)) {
        Expr *e = exprcar_(x);
        if (h0_(e) == s_fnap) {
        /* Avoid introduction of the temporary done by case s_fnap in        */
        /* optimise1 for structure-returning functions (produces an          */
        /* unnecessary and hard to remove structure copy). cg will cause the */
        /* called function to return its results directly to the argument    */
        /* place                                                             */
            e = optimisefnap(e);
        } else if (h0_(e) == s_let && h0_(arg2_(e)) == s_fnap) {
            arg2_(e) = optimisefnap(arg2_(e));
        } else {
            if ((mcrepofexpr(e) & MCR_SORT_MASK) == MCR_SORT_STRUCT &&
                h0_(e) == s_let && h0_(arg2_(e)) == s_comma) {
                SynBindList *bl = exprletbind_(e);
                Expr *a2 = arg2_(e);
                if (bl->bindlistcdr == NULL &&
                    (Expr *)bl->bindlistcar == arg2_(a2)) {
                    letbindings = mkSynBindList(letbindings, bl->bindlistcar);
                    e = a2;
                }
            }
            in_args++;
            e = optimise1(e, YES, &dummy);
            in_args--;
        }
        exprcar_(x) = e;
    }
    return letbindings;
}

static Expr *optimisefnap(Expr *e) {
    SynBindList *b;
    bool dummy;
    Expr *fn = arg1_(e) = optimise1(arg1_(e), YES, &dummy);
    b = optimiselist(exprfnargs_(e));
    /* Optimise away some casts for software floating point            */
    /* (cf optimisecast)                                               */
    if (h0_(fn) == s_addrof) {
        Expr *fnb = arg1_(fn);
        if (h0_(fnb) == s_binder && exprfnargs_(e) != NULL) {
            ExprList *args = exprfnargs_(e);
            Expr *arg = exprcar_(args);
            if (cdr_(args) == NULL
                && h0_(arg) == s_fnap
                && exprfnargs_(arg) != NULL && cdr_(exprfnargs_(arg)) == NULL
                && h0_(arg1_(arg)) == s_addrof
                && h0_(arg1_(arg1_(arg))) == s_binder) {
                Expr *fna = arg1_(arg1_(arg));
                ExprList *argsa = exprfnargs_(arg);
                if (fnb == sim.fnarrow) {
                    /* in (float)(double), the inner cast is redundant */
                    if (fna == sim.dwiden)
                        e = exprcar_(argsa);
                    else if (fna == sim.llstod)
                        e = mk1fnap(sim.llstof, argsa);
                    else if (fna == sim.llutod)
                        e = mk1fnap(sim.llutof, argsa);
                    else if (fna == sim.dfloat)
                        e = mk1fnap(sim.ffloat, argsa);
                    else if (fna == sim.dfloatu)
                        e = mk1fnap(sim.ffloatu, argsa);
                } else if (fnb == sim.dwiden && h0_(exprcar_(argsa)) == s_cast) {
                /* in (double)(float)(int), the cast to float is       */
                /* redundant if the thing cast to int is short or char */
                    int32 rep = mcrepofexpr(arg1_(exprcar_(argsa)));
                    if ((rep & MCR_SORT_MASK) < MCR_SORT_FLOATING
                        && (rep & MCR_SIZE_MASK) <= 2) {
                        if (fna == sim.ffloat)
                            e = mk1fnap(sim.dfloat, argsa);
                        else if (fna == sim.ffloatu)
                            e = mk1fnap(sim.dfloatu, argsa);
                    }
                }
            }
        }
    }
    return (b == NULL) ? e : mk_exprlet(s_let, type_(e), b, e);
}

#define U_Read 1
#define U_Write 2

typedef struct BindUseList BindUseList;
struct BindUseList {
     BindUseList *cdr;
     Binder *b;
     int use;
};

/* Very nice, AM had wanted to do something like this for some time!    */

static void warnifusage(BindUseList *bu, Binder *b, int flag) {
    for (; bu != NULL; bu = cdr_(bu))
        if (bu->b == b && (bu->use & flag)) {
            if (bu->use & flag & U_Read)
                cc_warn(warn_usage_rw, b);
            else
                cc_warn(warn_usage_ww, b);
            return;
        }
}

static BindUseList *mergeuselists(BindUseList *b1, BindUseList *b2, BindUseList *oldb) {
    if (b1 == oldb)
        return b2;
    else if (b2 != oldb) {
        BindUseList *p = b1, *next;
        for (; (next = cdr_(p)) != oldb; p = next) /* nothing */;
        cdr_(p) = b2;
     }
     return b1;
}

static BindUseList *checkvaruse(BindUseList *b, Expr *e)
{
    if (debugging(DEBUG_AETREE) && syserr_behaviour > 1)
    {   eprintf("checkvaruse "); pr_expr_nl(e);
    }

    switch (h0_(e)) {
    default:
        if (h0_(e) > s_binder)
            cc_warn(simp_warn_checkvar, h0_(e));
        break;
    case s_addrof:
        if (h0_(arg1_(e)) != s_binder)
            b = checkvaruse(b, arg1_(e));
        break;
/* Hmm, I'd rather do via isdiad_ ismonad_, possible? */
    case s_binder:
        warnifusage(b, exb_(e), U_Write);
        b = (BindUseList *)syn_list3(b, e, U_Read);
        break;

    case s_andequal: case s_orequal: case s_xorequal:
    case s_timesequal: case s_plusequal: case s_minusequal: case s_divequal:
    case s_idivequal: case s_remequal:
    case s_leftshiftequal: case s_rightshiftequal:
    case s_assign: case s_init:
        {   Expr *lhs = arg1_(e);
            b = checkvaruse(b, arg2_(e));
            if (h0_(lhs) != s_binder)
                b = checkvaruse(b, lhs);
            else {
                warnifusage(b, exb_(lhs), U_Write);
                b = (BindUseList *)syn_list3(b, lhs, U_Write);
            }
            break;
        }
    case s_plusplus: case s_minusminus:
    case s_displace:
        {   Expr *a1 = arg1_(e);
            if (h0_(a1) != s_binder)
                b = checkvaruse(b, a1);
            else {
                warnifusage(b, exb_(a1), U_Read+U_Write);
                b = (BindUseList *)syn_list3(b, a1, U_Write);
            }
            break;
        }
    case s_subscript:
    case s_equalequal: case s_notequal:
    case s_greater: case s_greaterequal: case s_less: case s_lessequal:
    case s_plus: case s_minus: case s_times: case s_div:
    case s_ptrdiff:
    case s_idiv: case s_rem: case s_power:
    case s_and: case s_or: case s_xor: case s_leftshift: case s_rightshift:
    case s_dotstar:
        b = checkvaruse(b, arg2_(e));
        /* drop though */

#ifndef NO_RETURN_EXPRESSIONS
    case s_return:
#endif
    case s_evalerror:
    case s_cast:
    case s_content4:
    case s_content:
    case s_monplus: case s_neg: case s_bitnot: case s_boolnot:
    case s_dot: case s_qualdot:
    case s_ctor:                /* a monad protecting a s_comma */
        b = checkvaruse(b, arg1_(e));
    case_s_any_string
        break;

    case s_invisible:
        b = checkvaruse(b, arg2_(e));
        break;

    case s_throw:
        if (arg1_(e)) b = checkvaruse(b, arg1_(e));
        break;

    case s_qualified|s_let:
    case s_let:
        b = checkvaruse(b, arg2_(e));
        break;

    case s_andand: case s_comma: case s_oror:
        {   BindUseList *b1 = checkvaruse(b, arg1_(e));
            BindUseList *b2 = checkvaruse(b, arg2_(e));
            b = mergeuselists(b1, b2, b);
            break;
        }
    case s_fnap:
        {   ExprList *args = exprfnargs_(e);
            for (; args != NULL; args = cdr_(args))
                b = checkvaruse(b, exprcar_(args));
            b = checkvaruse(b, arg1_(e));
            break;
        }
    case s_cond:
        {   BindUseList *b1 = checkvaruse(b, arg2_(e));
            BindUseList *b2 = checkvaruse(b, arg3_(e));
            BindUseList *b3 = checkvaruse(b, arg1_(e));
            b = mergeuselists(mergeuselists(b1, b2, b), b3, b);
            break;
        }
    }

if (debugging(DEBUG_AETREE) && syserr_behaviour > 1) {
  BindUseList *p;
  cc_msg("=>");
  for (p = b; p != NULL; p = cdr_(p))
    cc_msg(" $b,%s", p->b, (p->use-1)*3+"R\0\0W\0\0RW");
  cc_msg("\n");
}
    return b;
}

Expr *optimise0(Expr *e)
/* exported - yields 0 if a 'serious' error message has already been
   printed (we know this by the s_error at the top of the tree).
   The semantic routines *SHOULD* all be strict in s_error.
*/
{   Expr *res;
    bool dummy;
    if (h0_(e) == s_error) return NULL;
    checkvaruse(NULL, e);
    new_binders = NULL;
    if (setjmp(optimise0_jb) == 0)
        res = optimise1(e, YES, &dummy);
    else
    {   res = NULL;
        new_binders = NULL;
    }
    /*
     * If there are any structure returning functions allocate temp binders
     * here at the root of the expression tree.
     */
    return (new_binders == 0) ? res :
        mk_expr2(s_let, typeofexpr(res), (Expr*)new_binders, res);
}

/* The following routine detects when a struct/union has suitable members
   that it can be considered an integer and thus be slavable in a register.
   A first requirement is that all (union, total for struct) members are
   size 4 or less.  The total size of 4 has been checked by caller.
   However, not all such structs are suitable - consider
   struct { short a,b;}.  Moreover since C requires that the address of
   struct/union first element is the same as the address of the
   aggregate this poses problems (and that this problem extends to
   non-address-taken structs via assignment, this means that on some
   machines we cannot put  struct { char c; } in a register.
   However,  struct { int c:8;} is always OK.
   The rule is that every sub-object only contains int/enum/pointer.
   Return value is 1 if values of this type are allocatable to registers, 2
   if functions returning a value of this type should do so in an integer
   register (slightly looser conditions: this also requires that
   all subfields be integral and have offset zero, but allows shorter types
   than int).
*/
#define integerlikestruct(s) (slaveablestruct(s) == 1)

static int slaveablestruct(TagBinder *b)
{   ClassMember *l;
    int okres = 1;
    if (!integerlike_enabled) return 0;
    for (l = tagbindmems_(b); l != 0; l = memcdr_(l))
    {
        if (!is_datamember_(l))
        {   /* Reject non-static member functions (particularly ctors)  */
            /* since we can't just copy corresponding objects: consider */
            /* e.g. class A { A *p; A() { p = this; }};                 */
            if (!(bindstg_(l) & (bitofstg_(s_static)|bitofstg_(s_typedef))))
                /* need a macro for non-static member fn?              */
                return 0;
        }
#if 0
        else if (isbitfield_type(memtype_(l)))
        {   /* bits are OK (sem.c turns to int)                         */
            /* @@@ beware PCC mode/C++ char bitfields &c                */
        }
#endif
        else
        {   TypeExpr *t = princtype(memtype_(l));
            SET_BITMAP m;
            switch (h0_(t))
            {   default: return 0;                 /* array not OK      */
                case t_content: break;             /* pointers are OK   */
                case t_ref:     break;             /* and so are refs   */
                case t_fnap:    break;             /* so are mem fns    */
                case s_typespec:                 /* including bitfields */
                    if (memwoff_(l) != 0) return 0;
                    m = typespecmap_(t);
                    if (m & bitoftype_(s_enum))
                        m = typeofenumcontainer(typespectagbind_(t));
                    switch (m & -m)
                    {   default: return 0;
                        case bitoftype_(s_char):
                            okres = 2;
                            break;
                        case bitoftype_(s_int):
                            if (m & bitoftype_(s_short)) okres = 2;
                            break;                /* 4 bit int ok   */
                        case bitoftype_(s_double):
                           if ((m & bitoftype_(s_short))
                                && software_floats_enabled)
                                break;
                           return 0;
                        case bitoftype_(s_struct):
                        case bitoftype_(s_class):
                        case bitoftype_(s_union):
                            if (!slaveablestruct(typespectagbind_(t)))
                                return 0;
                            break;
                    }
                    break;
            }
        }
    }
    return okres;
}

static int32 mcrepofexpr1(Expr *e, bool container)
/* keep in step with sizeoftype */
{   TypeExpr *x = prunetype(typeofexpr(e));
    SET_BITMAP m;
    switch (h0_(x))
    {
case t_unknown:
    /* treated as void, see below. */
    return 0x0000000;
case s_typespec:
        m = typespecmap_(x);
        switch (m & -m)    /* LSB - unsigned/long etc. are higher */
        {
    case bitoftype_(s_enum):
            if (container)
                m = typeofenumcontainer(typespectagbind_(x));
            goto mcrepofint;
    case bitoftype_(s_char):
            if ((m & (bitoftype_(s_signed)|bitoftype_(s_unsigned))) == 0)
                m |= HasFeature(Feature_SignedChar) ?
                         bitoftype_(s_signed) : bitoftype_(s_unsigned);
            /* drop through */
    case bitoftype_(s_int):
    case bitoftype_(s_bool):
    mcrepofint:
            {   int32 n = sizeoftype(x);
                if (int_islonglong_(m))
                    return MCR_SORT_STRUCT + n;
                return n +
                    (m & bitoftype_(s_unsigned) ?
                          m & bitoftype_(s_signed) ? MCR_SORT_PLAIN :
                                                     MCR_SORT_UNSIGNED :
                                                  MCR_SORT_SIGNED);
            }
    case bitoftype_(s_double):
            {   int32 n = sizeoftype(x);
/* The tests here generate no code if alignof_double==alignof_int.      */
                return (alignof_double > alignof_int && n == sizeof_double) ?
                       MCR_SORT_FLOATING + MCR_ALIGN_DOUBLE + n :
                       MCR_SORT_FLOATING + n;
            }
    case bitoftype_(s_struct):
    case bitoftype_(s_class):
    case bitoftype_(s_union):
            {   int32 n = sizeoftype(x);
                if (n == 4 && integerlikestruct(typespectagbind_(x)))
                    return MCR_SORT_SIGNED + n;
                else
                    return (alignof_double > alignof_int &&
                            alignoftype(x) == alignof_double) ?
                           MCR_SORT_STRUCT + MCR_ALIGN_DOUBLE + n :
                           MCR_SORT_STRUCT + n;
            }
    case bitoftype_(s_void):
                /*
                 * BEWARE: Other parts of the compiler use mcrepoftype==0
                 * as a test for 'void' types.
                 */
                return 0x0000000;
    default: break;
            }
            /* drop through */
default:
/*      case t_fnap: */
            syserr(syserr_mcrepofexpr, (long)h0_(x),(long)typespecmap_(x));
case t_ovld:
            return MCR_SORT_SIGNED + sizeof_ptr;
case t_subscript:
/* The following checks that restriction that mcrepofexpr() spiritually     */
/* should never be applied to array typed expressions.  Two exceptions:     */
/* s_binder's (for flowgraf.c sizing) and s_strings (optimise removes their */
/* implicit '&').                                                           */
            if (h0_(e)!=s_binder && !isstring_(h0_(e)))
                syserr(syserr_mcreparray, (long)h0_(e));
            if (h0_(e) == s_binder)
            {   int32 n = sizeoftype(x);
                if (n & ~MCR_SIZE_MASK)
                    cc_err(simplify_err_outsizearray, exb_(e)),
                    n = MCR_SIZE_MASK;
                return (alignof_double > alignof_int &&
                        alignoftype(x) == alignof_double) ?
                       MCR_SORT_STRUCT + MCR_ALIGN_DOUBLE + n :
                       MCR_SORT_STRUCT + n;
            }
            /* s_string falls into pointer code */
case t_content:
case t_ref:
            return TARGET_ADDRESSES_UNSIGNED ? MCR_SORT_UNSIGNED + sizeof_ptr :
                                                 MCR_SORT_SIGNED + sizeof_ptr;
    }
}

static int32 mcrepofexpr2(Expr *e, bool container)
{   int32 r;
    /* temp. nasty hack for optimise(s_dot/s_dotstar) and cppfe/vargen  */
    /* solution: make type of datasegment struct-of-size 0x00ffffff?    */
        r = (e == (Expr *)datasegment || e == (Expr *)constdatasegment)
              ? MCR_SORT_STRUCT+0 : mcrepofexpr1(e, container);

/* Fake floating point values so that they are thought of as structures. */
    if (software_floats_enabled && r == MCR_SORT_FLOATING + 4)
        return MCR_SORT_SIGNED + 4;
    else if (software_doubles_enabled
             && (r == MCR_SORT_FLOATING + 8 ||
                 r == MCR_SORT_FLOATING + MCR_ALIGN_DOUBLE + 8))
        return MCR_SORT_STRUCT + 8;

    return r;
}

int32 mcrepofexpr(Expr *e)
{   return mcrepofexpr2(e, YES);
}

int32 mcrepoftype(TypeExpr *t)
{
/* This returns the machine representation of a type. Done by forgery of */
/* an expression and a call to mcrepofexpr().             */
    return mcrepofexpr(mk_expr2(s_invisible, t, 0, 0));
}

bool returnsstructinregs_t(TypeExpr *t) {
/* t is known to be a function type, but not necessarily one returning a */
/* structure value.                                    */
    TypeExpr *restype;
    t = prunetype(t);
    if (h0_(t) != t_fnap)
        syserr("non fnap in returnsstructinregs_t");
    restype = prunetype(typearg_(t));
    if (typefnaux_(t).flags & bitoffnaux_(s_structreg)) {
        int32 resultwords = sizeoftype(restype) / MEMCPYQUANTUM;
        return (resultwords >= 1 && resultwords <= NARGREGS);
    } else {
#ifdef SOFTWARE_FLOATING_POINT_RETURNS_DOUBLES_IN_REGISTERS
        if (software_doubles_enabled && isprimtype_(restype, s_double))
            return YES;
#endif
        if (h0_(restype) == s_typespec && int_islonglong_(typespecmap_(restype)))
            return YES;
        if (h0_(restype) == s_typespec && (typespecmap_(restype) & CLASSBITS) &&
            sizeoftype(restype) <= 4 && slaveablestruct(typespectagbind_(restype)) == 2)
                return YES;
        return NO;
    }
}

bool returnsstructinregs(Expr *fn) {
    TypeExpr *t = prunetype(typeofexpr(fn));
    if (h0_(t) != s_content) return NO; /* syserr will follow */
    t = princtype(typearg_(t));
    if (h0_(t) == t_coloncolon)
        t = typearg_(t);
    return returnsstructinregs_t(t);
}

/* end of simplify.c */
