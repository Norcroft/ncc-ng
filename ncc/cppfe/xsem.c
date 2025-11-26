/*
 * xsem.c: semantic analysis phase of the C++ compiler
 * Copyright (C) Codemist Ltd, 1988-1992
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Advanced RISC Machines Limited, 1991-1992, 1994
 * SPDX-Licence-Identifier: Apache-2.0
 * All rights reserved.
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#include <string.h>                            /* for memset and strcmp */
#include "globals.h"
#include "sem.h"
#include "bind.h"
#include "aetree.h"
#include "builtin.h"
#include "aeops.h"
#include "store.h"
#include "errors.h"
#include "util.h"     /* for padsize */
#include "simplify.h"
#include "syn.h"      /* for add_pendingfn() & recursing */

#define _SEM_H

static Expr *mkfnap_cpp(Expr *e, ExprList **l, bool *curried, Expr** let, Expr **firstarg);
static Expr *cpp_ptrcast(AEop op, Expr *e, TypeExpr *te, TypeExpr *tr,
                         AEop h0t);
static Expr *cpp_mkcast(AEop op, Expr **ep, TypeExpr *tr);
static Expr *nullptr(TagBinder *cl);
TypeExpr *lvalue_type(Expr *x);  /* isaddressablelvalue??        */
static ExprList *exprlist_of_default_args(FormTypeList *d, int);
static Binder *ovld_resolve_addr(Expr *e, BindList *bl);
static Binder *ovld_resolve_addr_2(AEop, TypeExpr *desttype, BindList *bl, Binder *generic);
static bool common_pointer_type(AEop op,
                TypeExpr *t1, Expr *e1, Expr **newe1,
                TypeExpr *t2, Expr *e2, Expr **newe2,
                TypeExpr **common);
static bool common_reference_type(AEop op,
                TypeExpr *t1, Expr *e1, Expr **newe1,
                TypeExpr *t2, Expr *e2, Expr **newe2,
                TypeExpr **common);

static bool call_dependency_type(TypeExpr *t, ScopeSaver tactuals);
static bool call_dependency_val(Expr *e, ScopeSaver tactuals);
static void sem_attempt_template_function(Binder *generic, Binder *specific);
static bool is_comparable_specialization(TypeExpr *t1, TypeExpr *t2);
static Binder *sem_instantiate_tmptfn(Binder *b, TypeExpr *bt, ExprList **l);

#define ensurelvalue_s_invisible \
                             /* a more general version of s_integer ...    */\
                             /* ... to replace that idea.                  */\
            if (h0_(orig_(x)) == s_ctor) { x = orig_(x); break; } /* tidy! */\
            /* taking the address of a t_ref behaves like s_content.       */\
            /* e.g. 'int &f(); ... return &f(); ...                        */\
            if (h0_(princtype(typeofexpr(orig_(x)))) == t_ref) return e;

#include "vargen.h"     /* for vg_note_vtable() */
#include "sem.c"

int env_size(Binder *b)
{   int i = 0;
    for (; b; b = bindcdr_(b)) i++;
    return i;
}

static Binder *ovld_resolve_addr(Expr *e, BindList *bl)
{
/* Taking the address of an ordinary or (possibly static) member fn.   */
/* For fn 'f', we treat &A::f, &a->f (and, in value ctxt) A::f, a->f   */
/* identically, returning type 't (A::*)(f())'.                        */
/* @@@ Well, at least we intend to!                                    */
    int len = length((List *) bl);
    if (h0_(e) == s_dot || h0_(e) == s_qualdot) e = exprdotmemfn_(e);
    if (h0_(e) != s_binder || (bl == NULL && bindactuals_(exb_(e)) == NULL
                               && bindftlist_(exb_(e)) == NULL))
        syserr("sem(odd ovld)");

    switch (len) {
    case 0:
        {   Binder *bspecific = NULL;
            if (bindactuals_(exb_(e)) != NULL)
            {   ExprList *l = NULL;
                ExprList *tactuals = bindactuals_(exb_(e));
                for (; tactuals; tactuals = cdr_(tactuals))
                    l = mkExprList(l, gentempbinder(typeofexpr(exprcar_(tactuals))));
                l = (ExprList *)dreverse((List *)l);
                bspecific = sem_instantiate_tmptfn(exb_(e), typeofexpr(e), &l);
            }
            return (bspecific != NULL) ? bspecific :
                (cc_err(sem_err_addr_template, e), (Binder *)errornode);
        }
    case 1:
        /* The rationale is that all use of a overloaded fn name refers to
           the generic binder. Overload resolution is performed again when
           usage is known i.e. mkcast.
        */
        {   Binder *bspecific = bl->bindlistcar;
            binduses_(bspecific) |= u_referenced;
            bindstg_(bindstg_(bspecific) & b_impl ? realbinder_(bspecific)
                     : bspecific) &= ~b_maybeinline;
            return bspecific;
        }
    default:
        return exb_(e);
    }
}

static Binder *ovld_resolve_addr_2(AEop op, TypeExpr *desttype, BindList *bl,
                                   Binder *generic)
{   Binder *bspecific = NULL;
    BindList *const origbl = bl;
    bool memtype = h0_(desttype) == t_coloncolon;
    if (op == s_cast && bl != NULL && bl->bindlistcdr == NULL &&
        memtype == ((bindstg_(bl->bindlistcar) & b_memfna) != 0))
        return bl->bindlistcar;

    if (memtype)
        desttype = typearg_(desttype);
    for (; bl != NULL; bl = bl->bindlistcdr)
    {   bspecific = bl->bindlistcar;
        if ((memtype == ((bindstg_(bspecific) & b_memfna) != 0)) &&
            equivtype(desttype, bindtype_(bspecific)) == 2)
        {   binduses_(bspecific) |= u_referenced;
            bindstg_(bindstg_(bspecific) & b_impl ? realbinder_(bspecific)
                                            : bspecific) &= ~b_maybeinline;
            return bspecific;
        }
    }
    if (!HasFeature(Feature_CFront) || origbl->bindlistcdr != NULL)
        cc_rerr(sem_rerr_noncallsite_ovld, bspecific, generic);
    return bspecific;
}

TagBinder *isclassenumorref_type(TypeExpr *t)
{   t = princtype(t);
    if (h0_(t) == t_ref) t = princtype(typearg_(t));
    return isclassorenumtype_(t) ? typespectagbind_(t) : 0;
}

Expr *thisify(Expr *e)
{   Binder *thisb = findbinding(thissym, NULL, LOCALSCOPES);
    if (thisb && h0_(thisb) == s_binder)
    {   binduses_(thisb) |= u_referenced;
        if (h0_(e) == s_member || h0_(e) == s_dot)
        {   ClassMember *member = (ClassMember *)e;
            return mkfieldselector(s_arrow, (Expr *)thisb, member);
        }
    }
    cc_err(sem_err_no_this_pntr);
    return errornode;
}

static Expr *nullptr(TagBinder *cl)
{   return mkintconst(ptrtotype_(tagbindtype_(cl)),
                      TARGET_NULL_BITPATTERN,
                      0);
}

typedef struct BinderCopyList {
    struct BinderCopyList *cdr;
    Binder *orig;
    Binder *copy;
} BinderCopyList;

static BinderCopyList *append_bl_copy(SynBindList *bl, SynBindList **copy)
{   BinderCopyList *bl_copy = NULL;
    for (; bl != NULL; bl = bl->bindlistcdr)
    {   Binder *b = bl->bindlistcar;
        bl_copy = binder_list3(bl_copy, b, gentempbinder(bindtype_(b)));
        *copy = mkSynBindList(*copy, bl_copy->copy);
    }
    return bl_copy;
}


static Expr *clone_expr_replace_exprtemps(Expr *e, BinderCopyList *bl_copy);

static ExprList *clone_exprlist_replace_exprtemps(ExprList *l, BinderCopyList *bl_copy)
{   return (ExprList *) (l == NULL) ? NULL :
        syn_cons2(clone_exprlist_replace_exprtemps(l->cdr, bl_copy),
                  clone_expr_replace_exprtemps(exprcar_(l), bl_copy));
}

/* Modelled on globalize_expr(), perhaps a generic tree-walker needed? */
static Expr *clone_expr_replace_exprtemps(Expr *e, BinderCopyList *bl_copy)
{   AEop op;
    if (e == NULL || h0_(e) == s_error)
        syserr("Null or error expr can't be cloned");
    switch (op = h0_(e)) {
    case s_fnapstruct:
    case s_fnap:
        return (Expr *)syn_list5(op, type_(e), exprfileline_(e),
                                 clone_expr_replace_exprtemps(arg1_(e), bl_copy),
                                 clone_exprlist_replace_exprtemps(exprfnargs_(e), bl_copy));
    case s_binder:
        for (; bl_copy != NULL; bl_copy = bl_copy->cdr)
            if (bl_copy->orig == exb_(e))
                return (Expr *)bl_copy->copy;
        return e;
#ifdef EXTENSION_UNSIGNED_STRINGS
    case s_ustring:
#endif
    case s_wstring:
    case s_string:
    case s_integer:
    case s_floatcon:
        return e;
    case s_let:
        return (Expr *)syn_list5(op, type_(e), exprfileline_(e), exprletbind_(e),
           clone_expr_replace_exprtemps(arg2_(e), bl_copy));
    case s_dot:
        {   bool is_bitfield = isbitfield_type(type_(e));
            Expr *r = (Expr *)SynAlloc(is_bitfield ? 7L*sizeof(int32) : 5L*sizeof(int32));
            h0_(r) = op;
            type_(r) = type_(e);
            exprfileline_(r) = exprfileline_(e);
            arg1_(r) = clone_expr_replace_exprtemps(arg1_(e), bl_copy);
            exprdotoff_(r) = exprdotoff_(e);
            if (is_bitfield)
            {   exprbsize_(r) = exprbsize_(e);
                exprmsboff_(r) = exprmsboff_(e);
            }
            return r;
        }
    case s_cond:
        return (Expr *)syn_list6(op, type_(e), exprfileline_(e),
                                 clone_expr_replace_exprtemps(arg1_(e), bl_copy),
                                 clone_expr_replace_exprtemps(arg2_(e), bl_copy),
                                 clone_expr_replace_exprtemps(arg3_(e), bl_copy));
    default:
        if (ismonad_(op) || op == s_cast)
        {   return (Expr *)syn_list4(op, type_(e), exprfileline_(e),
                                     clone_expr_replace_exprtemps(arg1_(e), bl_copy));
        } else if (isdiad_(op) || op == s_init
#ifdef RANGECHECK_SUPPORTED
                 || op == s_checknot
#endif
                )
            return (Expr *)syn_list5(op, type_(e), exprfileline_(e),
                                     clone_expr_replace_exprtemps(arg1_(e), bl_copy),
                                     clone_expr_replace_exprtemps(arg2_(e), bl_copy));
    }
    syserr("clone_expr_replace_exprtemps(%p:%.lu)", e, op);
    return NULL;
}

static Expr *clone_default_expr(Expr *e)
{   BinderCopyList *bl;
    SynBindList *tmps = NULL;
    if (h0_(e) != s_let+s_qualified) return e;
    bl = append_bl_copy(exprletbind_(e), &tmps);
    if (h0_(arg2_(e)) != s_comma) syserr("comma expr expected");
    add_to_saved_temps(tmps);
    add_expr_dtors(clone_expr_replace_exprtemps(arg2_(arg2_(e)), bl));
    return clone_expr_replace_exprtemps(arg1_(arg2_(e)), bl);
}

/* @@@ Perhaps we should mark these args so they avoid a 2nd optimise!  */
/* They certainly must not go via coerceunary (as type info may have    */
/* been changed by previous optimise0()).                               */
static ExprList *exprlist_of_default_args(FormTypeList *d, int argindex)
{   ExprList *p = 0, *q = 0;
    for (; d != NULL; d = d->ftcdr, ++argindex)
    {   Expr *e = d->ftdefault;
        if (e)
        {   ExprList *t;
            set_fnap_arg(argindex);
            t = mkExprList1(clone_default_expr(e));
            if (p) cdr_(q) = t, q = t;
            else p = q = t;
        }
        else if (p) syserr("non-contiguous default args!");
    }
    return p;
}

static Expr *pointerkeepnull(Expr *ee, Expr *e, Binder *gen)
{   /* 'ee' contains 'gen' as a subexpression.  Ensure that ee[e/gen]   */
    /* preserves NULL -- see [ES, p233].                                */
    /* @@@ arguably the 'if' here should be part of simplify.c where    */
    /* it could be of more general use.                                 */
    if (h0_(ee) == s_addrof)
    {   Expr *x = arg1_(ee);
        while (h0_(x) == s_dot && exprdotoff_(x) == 0) x = arg1_(x);
        if (h0_(x) == s_content && arg1_(x) == (Expr *)gen)
        {   arg1_(x) = e;
            return ee;
        }
    }
    return mklet(gen, typeofexpr(ee),
        mkbinary(s_comma,
            mkbinary(s_init, (Expr *)gen, e),
            mkcond((Expr *)gen, ee, lit_zero)));
}



/* AM memo: if just 1 v.fn then use fn itself (not table) for a base.   */
/* AM memo: vfntab in 1st phys base can be extended to derived class.   */

TypeExpr *core_type(TagBinder *base_tag)
{   ClassMember *p = tagbindmems_(base_tag);
    if (p != NULL && (attributes_(p) & CB_CORE))
        return memtype_(p);
    else
        return tagbindtype_(base_tag);
}

TagBinder *core_class(TagBinder *cl)
{   ClassMember *l = tagbindmems_(cl);
    if (l && attributes_(l) & CB_CORE)
    {   TypeExpr *t = princtype(memtype_(l));
        if (!isclasstype_(t)) syserr("core_class $c", cl);
        cl = typespectagbind_(t);
    }
    return cl;
}

ClassMember *type_derived_from(TypeExpr *tbase, TypeExpr *tderived)
{   TypeExpr *ptbase = princtype(tbase), *ptderived = princtype(tderived);
    return isclasstype_(ptbase) && isclasstype_(ptderived) ?
        derived_from(typespectagbind_(ptbase), typespectagbind_(ptderived)) :0;
}

Expr *commacons(Expr *a, Expr *b)
{   /* of more general use (NULL == optional, errornode == error).      */
    return a == 0 ? b : b == 0 ? a : mkbinary(s_comma, a, b);
}

static Expr *mkcommalist_1(Expr *a, va_list ap)
{   /* NULL == terminator, errornode = error */
    Expr *e = va_arg(ap, Expr *);
    if (e == NULL) return a;
    else
    {   Expr *rest;
        if (h0_(e) == s_error) return errornode;
        rest = mkcommalist_1(e, ap);
        if (h0_(rest) == s_error) return errornode;
        return mkbinary(s_comma, a, rest);
    }
}

Expr *mkcommalist(Expr *a, ...)
{   /* NULL == terminator, errornode = error */
    va_list ap;
    if (a == NULL) syserr("empty commaconsmany");
    va_start(ap, a);
    if (h0_(a) == s_error) return errornode;
    return mkcommalist_1(a, ap);
}

#define mkopapcheck(b) \
    if (h0_(b) != s_binder|| bindstg_(b) & bitofstg_(s_typedef)) \
            syserr("non fn operator")

#define prefer_tmptfn(a) (a != NULL && exprcar_(a) == NULL)

static bool match_non_type_args(ScopeSaver tformals, ExprList *actuals)
{   for (; tformals && actuals;
         tformals = bindcdr_(tformals), actuals = actuals->cdr)
        if (bindconst_(tformals) && exprcar_(actuals) &&
            (evaluate(bindconst_(tformals)) == evaluate(exprcar_(actuals))))
            continue;
        else
            return NO;
    return (!tformals && !actuals) ? YES : NO;
}

static Binder *sem_instantiate_tmptfn(Binder *b, TypeExpr *bt, ExprList **l)
{   Binder *fb = NULL;
    BindList *tmpts;

    if ((tmpts = temp_reduce(NULL, *l, NULL, b)) != NULL)
    {   Binder *ftemp = tmpts->bindlistcar;
        TypeExpr *t;
        BindList *bl;
        Symstr *sv;
        bool has_failed = NO;
        ScopeSaver env = bindformals_(ftemp);

        t = type_deduction(bindtype_(ftemp), *l, bindactuals_(b),
                           &env, NO, &has_failed);

        if (bindsym_(ftemp) == currentfunction.symstr)
        {
            /* Not really an instance if the call is made inside itself.
               It goes on the typeovldlist_ nonetheless for parsing purpose.
               Of course, template fn can't be code generated!
             */
            add_instance(ftemp, &typeovldlist_(bt), NO);
            has_failed = YES;
        }

        /* Is there already a suitable one around? Non-deduced types are the
           best.*/
        if (!prefer_tmptfn(bindactuals_(b)))
            for (bl = typeovldlist_(bt); bl && !has_failed; bl = bl->bindlistcdr)
                if ((bindenv_(bl->bindlistcar) == NULL) &&
                    !((bindstg_(bl->bindlistcar) & b_undef) &&
                      !(bindstg_(ftemp) & b_undef)) &&
                    equivtype(t, bindtype_(bl->bindlistcar)) &&
                    (bindactuals_(b) == NULL ||
                     match_non_type_args(bindformals_(bl->bindlistcar), bindactuals_(b))))
                    has_failed = YES;

        for (bl = bindinstances_(ftemp); bl && !has_failed; bl = bl->bindlistcdr)
            if (equivtype(t, bindtype_(bl->bindlistcar)) &&
                !((bindstg_(bl->bindlistcar) & b_undef) &&
                  !(bindstg_(ftemp) & b_undef)) &&
                (bindactuals_(b) == NULL ||
                 match_non_type_args(bindformals_(bl->bindlistcar), bindactuals_(b))))
            {   has_failed = YES;   /* pretends it's failed */
                fb = bl->bindlistcar;
            }

        if (!has_failed)
        {   Binder *fbind = NULL;
            Symstr *declname;
            binduses_(ftemp) |= u_referenced;
            fixup_template_arg_type(t, env);
            sv = ovld_tmptfn_instance_name(bindsym_(ftemp), env);
            declname = ovld_instance_name(sv, t);
            for (bl = typeovldlist_(bt); bl; bl = bl->bindlistcdr)
                if (bindsym_(bl->bindlistcar) == declname)
                {   fbind = bl->bindlistcar;
                    break;
                }
            if (!fbind)
            {   env = globalize_env(env);
                t = globalize_typeexpr(t);
                fixup_template_arg_type(t, env);
                fb = fbind =
                    instate_declaration(mkDeclRhsList(declname, t,
                                                      killstgacc_(bindstg_(ftemp))),
                                        TOPLEVEL|INSTANCE);
                attributes_(fbind) |= attributes_(ftemp);
                /* @@@ check temp type and non-type args are not extern */
                bindstg_(fbind) |= b_undef;
                bindenv_(fbind) = (!prefer_tmptfn(bindactuals_(b))) ?
                    globalize_template_arg_binders(env, bindactuals_(b)) : env;
                add_instance(fbind, &typeovldlist_(bt), NO);
                add_instance(fbind, &bindinstances_(ftemp), YES);
                if (bindstg_(ftemp) & (b_memfna+b_memfns))
                {   TagBinder *parent = bindparent_(ftemp);
                    Binder *btop;
                    SET_BITMAP stg;
                    DeclRhsList decl;

                    decl.declname = ovld_add_memclass(declname, parent,
                                                      (bindstg_(ftemp) & b_memfns) != 0);
                    stg = killstgacc_(bindstg_(ftemp));
                    if (stg & bitofstg_(s_static))
                        stg = (stg & ~bitofstg_(s_static))|bitofstg_(s_extern);
                    decl.declstg = stg;
                    decl.decltype = (stg & b_memfna) ?
                        memfn_realtype(t, parent) : t;
                    btop = instate_declaration(&decl, TOPLEVEL);
                    bindstg_(fbind) |= b_impl;
                    bindstg_(btop) |= b_undef;
                    bindenv_(btop) = bindenv_(fbind);
                    realbinder_(fbind) = btop;
                    fbind = btop;
                }
            }
            else
            {   fb = fbind;
                if (realbinder_(fbind) != NULL) fbind = realbinder_(fbind);
                if (!bindenv_(fb)) bindenv_(fb) = globalize_env(env);
                parameter_names_transfer(typefnargs_(t), typefnargs_(bindtype_(fb)));
            }
            if (!contains_typevars(bindtype_(fbind)) && (bindstg_(fbind) & b_undef)
                && !(bindstg_(ftemp) & b_undef))
            {   bool ismemtemp = (bindstg_(ftemp) & (b_memfns+b_memfna)) != 0;
                /* OK since overload resolution always chooses the exact match. */
                if (debugging(DEBUG_TEMPLATE))
                    cc_msg("instantiate $r -> $r\n", bindsym_(b), sv);
                add_pendingfn(ismemtemp ? bindsym_(fbind) : bindsym_(b),
                              ismemtemp ? NULL : sv,
                              globalize_typeexpr_no_default_arg_vals(bindtype_(fb)),
                              (bindstg_(fbind)&~b_undef),
                              bindparent_(ftemp),
                              NULL, bindtext_(ftemp), bindenv_(fbind), YES);
                bindstg_(fb) &= ~b_undef;
            }
        }
    }
    bindactuals_(b) = NULL;
    return fb;
}

static Expr *mkfnap_cpp(Expr *e, ExprList **l, bool *curried, Expr **let_, Expr **firstarg)
{
    Binder *thisb = 0;
    bool validobj = 0;
/* Rationale: if we have a s_dot or s_dotstar (s_arrow/s_arrowstar      */
/* have already gone) which gives a fn value (impossible in C)          */
/* then we have to add its LHS as a *potential* first arg for overload  */
/* resolution.  Potential because it only applies to non-static memfns. */
/* We also need to do this for 'Binder's (an implicit thisify() if      */
/* and only if there is a non-static memfn).                            */
/* We need to do this before coerceunary() can moan about unresolvable  */
/* overloadings (note this is OK because no refs to fns).               */
    Expr *let = 0;
    ExprList *ll = *l, *let_ll = 0;
/* We need a let to avoid double side->effects when making virtual      */
/* function calls because p->vf() will become (*(p + n)+ m)(p).  But we */
/* don't know if the function is virtual until after overload           */
/* resolution for which we need an argument list.  So we make the       */
/* argument list with (let_ll) and without (ll) the let and choose      */
/* whether or not to use the let down below.  We could always use the   */
/* let but the temporary elimination scheme in mkopap is confused by    */
/* it.                                                                  */
    Expr *ee = skip_invisible(e);
    bool may_be_virtual = h0_(ee) != s_qualdot;
    bool trivialfirstarg = NO;
    bool use_corefn = NO;
    /* Needed in C++ - A+B may generate an invisible node for,  */
    /* for example, A.operator+(B); also conversion fns...      */
    *curried = NO;
    *let_ = 0;
    if ((h0_(ee) == s_dot || h0_(ee) == s_qualdot) &&
           (h0_(type_(ee)) == t_ovld || h0_(type_(ee)) == t_fnap))
    {   /* C++ member function (e.g. explicit 'this')               */
        /* beware: vbase members maybe unrooted via a vbase ptr     */
        if (is_unrooted(arg1_(ee)) || (h0_(arg1_(ee)) == s_content &&
                is_unrooted(arg1_(arg1_(ee)))))
            /* just A::f() rather than a.A::f() */
            e = ee = exprdotmemfn_(ee);
        else
        {   Expr *thisobj = arg1_(ee);
            TypeExpr *pt = typeofexpr(thisobj);
            bool is_class = isclasstype_(princtype(pt));
            TypeExpr *bt = ptrtotype_(pt);
            Expr *thisptr = is_class ? mkaddr(thisobj) :
                mkunary(s_addrof, thisobj);
            Binder *tempthisb = gentempbinder(bt);
            validobj = 1;
            pt = princtype(pt);
            if (is_class &&
                (tagbindbits_(typespectagbind_(pt)) & TB_CORE))
                    use_corefn = YES;
            ll = mkExprList(*l, thisptr);
            let = mklet(tempthisb, bt,
                     mkbinary(s_init, (Expr *)tempthisb, thisptr));
            let_ll = mkExprList(*l, tempthisb);
            if (h0_(thisobj) == s_binder)
                bindstg_((exb_(thisobj))) |= b_addrof|u_referenced;
            e = exprdotmemfn_(ee);  /* s_binder of (generic) memfn. */
            /* make an s_invisible node?                            */
        }
    }
    if (h0_(ee) == s_binder && bindstg_(exb_(ee)) & b_fnconst)
    {   /* C++ member function (with implicit 'this').              */
        /* Invent this->f() or NULL->f() (in static memfn), then    */
        /* moan about NULL if f is b_memfna.                        */
        TagBinder *cl = bindparent_(exb_(ee));
        if (cl)
        {   thisb = findbinding(thissym, NULL, LOCALSCOPES);
            if (thisb == NULL ||
                !derived_fromeq(cl, typespectagbind_(typearg_(bindtype_(thisb)))))
              /* potential error (unless static memfn calls same).  */
              ll = mkExprList(*l, nullptr(cl));
            else if (h0_(thisb) == s_binder)
            {
              ll = mkExprList(*l, (Expr *)thisb),
              validobj = 1;
            }
            else syserr("mkfnap(thisb)");
            /* save unnecessary s_comma node in a fairly common case */
            trivialfirstarg = YES;
        }
    }
    if (h0_(ee) == s_dotstar)       /* see [ES, p71]                */
    {   Expr *thisobj = arg1_(ee);
        validobj = 1;
        *l = ll = mkExprList(*l, mkunary(s_addrof, thisobj));
        e = arg2_(ee);
        *curried = 1;
    }
/* The placing of the next line is tentative --- we should really       */
/* do the pre-overloading-resolution coercions on args (things like     */
/* array->pointer but not char->int) before it...                       */
/* @@@ well, what about "int v[10]; void f(int (&v)[10]); ... f(v);"?   */
/* Also, given "ovldfn(1)" valid, is "(*ovldfn)(1)" or "(&ovldfn)(1)"?  */
    else if (h0_(e) == s_binder)
    {   Binder *b = exb_(e), *b2;
        TypeExpr *bt = princtype(bindtype_(b));
        if (h0_(bt) == t_ovld || h0_(bt) == t_fnap)
        {   bool call_is_virtual;
            ExprList *arglist = *l;

            /* An arg with a dependent type or previous error
               indicates a no-call. */
            for (; arglist; arglist = cdr_(arglist))
                if (is_dependent_type(typeofexpr(exprcar_(arglist))) ||
                    h0_(exprcar_(arglist)) == s_error)
                    return errornode;

            /* An actual that's a s_evalerror or s_error indicates a no-call */
            for (arglist = bindactuals_(b); arglist; arglist = cdr_(arglist))
            {   Expr *e = exprcar_(arglist);
                if (e && (h0_(e) == s_evalerror || h0_(e) == s_error))
                    return errornode;
            }

            if (h0_(bt) == t_ovld)
            {   Binder *tmpt_bspecific = sem_instantiate_tmptfn(b, bt, l);
                b = (tmpt_bspecific) ? tmpt_bspecific :
                    ovld_resolve(b, typeovldlist_(bt), *l, ll, NO);
                if (h0_(b) == s_error) return errornode;
            }
            if ((bindstg_(b) & b_undef) && !contains_typevars(bindtype_(b)))
            {   if (bindparent_(b) != NULL)
                {   if (bindstg_(realbinder_(b)) & b_undef)
                        syn_attempt_template_memfn(exb_(e), b);
                    else
                        bindstg_(b) &= ~b_undef;
                }
                else
                    sem_attempt_template_function(exb_(e), b);
            }
/* here we should check access rights to the member before indirecting. */
            b2 = (bindstg_(b) & b_impl) ? realbinder_(b) : b;
/* @@@ are vfns really REFERENCED here?                                 */
            binduses_(b2) |= u_referenced;
            if (use_corefn && (attributes_(b2) & CB_HASCOREFN))
                b2 = realbinder_(b2);
            if ((bindstg_(b2) & STGBITS) == 0)
                syserr("mkfnap(bindstg %lx)\n", bindstg_(b2));
            call_is_virtual = may_be_virtual &&
                (bindstg_(b) & bitofstg_(s_virtual));
            if (bindstg_(b) & b_memfna)
            {   if (call_is_virtual && let)
                {    ll = let_ll;
                     *let_ = let;
                }
                *l = ll;              /* implicit first arg for 'this' */
                if (!validobj)  /* see thisify().                */
                    cc_err(sem_err_no_this_pntr2, e);
                if (thisb)
                    binduses_(thisb) |= u_referenced;
            }
            if (call_is_virtual)
            {   TagBinder *tb = bindparent_(b);
                Binder *thisvtab = findbinding(vtabsym, tb, INCLASSONLY);
                Expr *lv = exprcar_(*l);
                TypeExpr *te = typeofexpr(lv);
                TypeExpr *ttb = tagbindtype_(tb);
                TypeExpr *thist = indexable(te) ? ptrtotype_(ttb) : ttb;
                Expr *vtab = mkfieldselector(s_arrow,
                                mkcast(s_cast, lv,
        (bindstg_(thisvtab) & bitofstg_(s_typedef)) ? bindtype_(thisvtab) : thist),
                                    (ClassMember *)vtabsym);

                if (!SuppressDB_Has(Suppress_CFrontCaller))
                    cc_warn(sem_warn_virtual, b);
#ifdef TARGET_HAS_DATA_VTABLES
                if (target_has_data_vtables) {
                    e = mk_expr1(s_cast, ptrtotype_(bindtype_(b2)),
                         mk_expr1(s_content, ptrtotype_(te_int),
                          mk_expr2(s_plus, type_(vtab), vtab,
                           mkintconst(te_int, TARGET_VTAB_ELTSIZE*bindxx_(b2), 0))));
                } else
#endif
                {
                    e = mk_expr1(s_cast, ptrtotype_(bindtype_(b2)),
                         mk_expr2(s_plus, type_(vtab), vtab,
                          mkintconst(te_int, TARGET_VTAB_ELTSIZE*bindxx_(b2), 0)));
                }
                e = mkinvisible(type_(e), (Expr *)b2, e);
            }
            else
            {   bindstg_(b2) &= ~b_maybeinline;
                e = (Expr *)b2;
            }
        }
        if (!trivialfirstarg && *l != ll)
            *firstarg = exprcar_(ll);
    }
    return e;
}

/* mkopap() applies an operator.  Binary operators need to be           */
/* simultaneously overload resolved against in-scope diadic functions   */
/* and monadic member functions.                                        */
/* It returns 1. a s_fnap node, 2. an errornode or 3. NULL, the last    */
/* indicating no resolution possible (for operators like '&' '=', ','   */
/* which have predefined meaning on structs if not hidden.              */
Expr *mkopap(AEop op, TagBinder *cla, Expr *a, ExprList *l)
{   Symstr *opname = op == s_init ? ctorsym : operator_name(op);
    Binder *b1 = op == s_init ? 0 :
        findbinding(opname, NULL, FB_LOCALS+FB_GLOBAL);
    Binder *b2 = (cla == NULL || !isclasstagbinder_(cla)) ? NULL :
        findbinding(opname, cla,
            (op == s_assign || op == s_init) ? INCLASSONLY : INDERIVATION);
    ExprList *ll = mkExprList(l, a);
    int nargs = length((List *)ll);
    List *candidates = NULL;

    if (b1)
    {   mkopapcheck(b1);
        (void)sem_instantiate_tmptfn(b1, bindtype_(b1), &ll);
        candidates =
            mk_candidates(typeovldlist_(bindtype_(b1)), nargs, 0, candidates);
    }
    if (b2)
    {   mkopapcheck(b2);
        /* @@@ b2 is the generic, needs a specific for
           syn_attempt_template_memfn() */
        candidates =
            mk_candidates(typeovldlist_(bindtype_(b2)), nargs, 0, candidates);
    }

    switch (op)
    {
case s_fnap:    /* TEMPORARILY exclude fnaps... */
case s_init:
case s_assign:
case s_comma:
case s_addrof:  /* no built-in operators...     */
        break;
default:
        candidates = mk_operator_candidates(op, typeofexpr(a),
                    (l == 0) ? 0 : typeofexpr(exprcar_(l)), candidates);
    }

    if (candidates == 0) return 0;

    {   Binder bb, *b;
        bb.h0 = op;
        bb.bindparent = cla;
        b = ovld_reduce(&bb, candidates, l, ll);
        if (b == 0)
        {   if (op == s_assign && cla != 0 && (tagbindbits_(cla) & TB_NEEDSOPEQ))
            {   cc_err(sem_err_assign_ovld, cla);
                return errornode;
            }
            return 0;
        }
        if (h0_(b) == s_error) return errornode;
        if (h0_(b) == op)
        {    h0_(b) = s_operator;
             return (Expr *)b;
        }
        if (b->bindparent == 0)
            /* not a class member */
            return mkfnap((Expr *)b1, ll);
        else
        {   Expr *aa = 0;
            if (op == s_init)
/* lose const/volatile qualification for 'this' arg to s_init ctors...  */
/* if 'a' has type (<maybequalified> T *), cast to (<unqualified> T *); */
/* otherwise make *((<unqualified> T *)&a)...                           */
            {   TypeExpr *pta = princtype(typeofexpr(a));
                TypeExpr *pte = h0_(pta) != t_content ?
                        mkqualifiedtype_1(pta, 0, bitoftype_(s_const)) :
                        princtype(typearg_(pta));
                Expr *e = mkcast(s_cast|s_qualified,
                    h0_(pta) == t_content ? a : mkunary(s_addrof, a),
                    ptrtotype_(pte));
                aa = e;
                a = h0_(pta) == t_content ? e : mkunary(s_content, e);
            }
            a = mkfnap(mkfieldselector(s_dot, a, b), l);

/* /* this no longer works, 'cause mkfnap now returns a s_let node for  */
/* member function calls.  I can't quite bring myself to reanimate the  */
/* hack -- will think about the problem instead.                        */
            if (op == s_init && nargs == 2 && h0_(a) == s_fnap)
/* Here is a (generated) copy ctor; eliminate both the call and the     */
/* temp if (and only if) it is copying from a generated temp.           */
/* Effectively, cctor(&x, &(ctor(temp, y), temp)) ==> ctor(&x,y)        */
            {   ExprList *args = (ExprList *)arg2_(a);
                Expr *init = exprcar_(cdr_(args));
                if (h0_(init) == s_cast &&
                    h0_(init = skip_invisible_or_cast(arg1_(init))) == s_addrof &&
                    h0_(init = skip_invisible_or_cast(arg1_(init))) == s_comma &&
                    h0_(skip_invisible_or_cast(arg1_(init))) == s_fnap)
                {   Expr *e = skip_invisible_or_cast(arg1_(init));
                    Binder *t = exb_(arg2_(init));
                    if (equivtype(bindtype_(t), typearg_(typeofexpr(aa))) == 2)
                        if (killnexprtemp(t))
                            return mkfnap(arg1_(e),
                                mkExprList(cdr_(exprfnargs_(e)), aa));
                }
            }
            return a;
        }
    }
}

Expr *user_conversion(Expr *e, TagBinder *cl, TypeExpr *t)
{   Binder *b;
    /* enums don't have user conversions */
    if (cl == 0 || !isclasstagbinder_(cl)) return e;
    b = findbinding(conversion_name(t), cl, INDERIVATION);
    if (b == 0)
    {   cc_rerr("No conversion to type $t in $c", t, cl);
        return errornode;
    }
    return mkfnap(mkfieldselector(s_dot, e, b), /* NOARGS */0);

}

/* Cfront allows things like 'T* t; void** p = &t;' This checks if     */
/* Cfront allows implicit casting from ptr-to-te to a ptr-to-tr.       */
bool cfront_allows_pointercast(TypeExpr *te, TypeExpr *tr)
{   if (isvoidtype(tr)) return YES;
    else
        return h0_(te) == t_content && h0_(tr) == t_content &&
            cfront_allows_pointercast(typearg_(te), typearg_(tr));
}

static Expr *cpp_ptrcast(AEop op, Expr *e, TypeExpr *te, TypeExpr *tr,
                         AEop h0t)
{
/* Here we have a cast from pointer-to-te to a pointer-to-tr.           */
/* te and tr may both be non-pruned.  Return a suitable Expr (which     */
/* in C will always be 'e' but may be e+/-delta in C++).                */
/* Moan while doing so for unsuitable implicit casts.                   */
/* The Oct 88 draft clarifies that void pointers ARE required           */
/* to respect const/volatile qualification too.                         */
    int err = op != s_cast;
/* @@@ We need to enable EXPLICIT (and implicit with error msg) casts   */
/* from base type to (uniquely) derived type.                           */
/* The following code allows casts from derived type to unique base.    */
    TypeExpr *tep = princtype(te), *trp = princtype(tr);
    TagBinder *teb = 0;
    TagBinder *trb = 0;
    ClassMember *basemem = 0;
    bool is_ptrtomem = (h0_(tep) == t_coloncolon && h0_(trp) == t_coloncolon);
    SET_BITMAP q = 0;

    if ((isclasstype_(tep) && isclasstype_(trp)) || is_ptrtomem)
    {   teb = core_class(typespectagbind_(tep));
        trb = core_class(typespectagbind_(trp));
    }
/* Allow a pointer to CORE type to cast to pointer to its owning class: */
/* This code may be temporary!                                          */
    if (teb && trb && teb == trb)
    {   /* always 0 offset, so 'e' unchanged.                           */
        if (err && (q = qualifiers_lost(te,tr)) == 0) err = 0;
    }
    else if (teb && trb && !is_ptrtomem &&
                (basemem = derived_from(trb, teb)) != 0)
    {   /* Assert: (attributes_(basemem) & (CB_BASE|CB_VBPTR)) != 0     */
        /* Now check access by looking up the member...                 */
        path_to_member((ClassMember *)memsv_(basemem),
                typespectagbind_(tep), INDERIVATION);
        if (!accessOK)
            diagnose_access(bindsym_(typespectagbind_(trp)),
                typespectagbind_(tep));
        {   Binder *gen = 0;
/* op == s_this indicates virtual function invocation. There's no point */
/* keeping p==0, because if p==0 we can't locate the vtable anyway...   */
            Expr *g = h0t == t_ref || op == s_this ? e :
                  (Expr *)(gen = gentempbinder(typeofexpr(e)));
            Expr *ee = mkfieldselector(s_arrow, g, basemem);
            if (h0_(memtype_(basemem)) != t_content) ee = mkaddr(ee);
            e = gen == 0 ? ee : pointerkeepnull(ee,e,gen);
/* @@@ note this cannot affect qualifiers (no class A: const B {}).     */
/* Hmm, what about "typedef class X {} const B; class A:B {};"?         */
        }
        if (err && (q = qualifiers_lost(te,tr)) == 0) err = 0;
    }
    else if (teb && trb && (basemem = derived_from(teb, trb)) != 0)
    {   TypeExpr *tt = (is_ptrtomem) ? tagbindtype_(typespectagbind_(trp)) : tr;
        Expr *n = mkunary(s_content,
                    mkintconst(ptrtotype_(tt), TARGET_NULL_BITPATTERN, 0));
        Expr *f = mkfieldselector(s_dot, n, basemem);
        int32 off = 0;
/* BEWARE: relies on form of result of mkfieldselector().               */
        if (h0_(memtype_(basemem)) == t_content) f = mkunary(s_content,f);
        /* so 'f' is now an expression of type te.                      */
        if (err)
            err = (is_ptrtomem) ? 0 : 2;
        if (debugging(DEBUG_SYN))
            cc_msg("cast-to-derived: "), pr_expr_nl(f);
        if (!is_ptrtomem || h0_(tep) != t_fnap)
        for (;;)
        {   if (f == n)
            {   Expr *ee = mk_expr2((is_ptrtomem) ? s_plus : s_minus, ptrtotype_(tr), e,
                                    mkintconst(te_int, off, 0));
                if (h0t != t_ref && off != 0)
                {   if (is_ptrtomem)
                        e = ee;
                    else
                    {   Binder *gen = gentempbinder(typeofexpr(e));
                        arg1_(ee) = (Expr *)gen;
                        e = mklet(gen, type_(ee),
                              mkbinary(s_comma,
                                mkbinary(s_init, (Expr *)gen, e),
                                mkcond((Expr *)gen, ee, lit_zero)));
                    }
                }
                break;
            }
            else if (h0_(f) == s_dot)
            {   off += exprdotoff_(f);
                f = arg1_(f);
            }
            else
            {   cc_rerr(sem_rerr_cast_dtype_from_vbase);
                err = 0;        /* avoid repeated error messages.       */
                break;
            }
        }
    }
    else if (HasFeature(Feature_CFront) &&
              op != s_cast &&
              h0t == t_content &&
              !qualfree_equivtype(te, tr) &&
              cfront_allows_pointercast(te, tr))
        err = 0;
    else
    {   if (teb && trb &&
            (!(tagbindbits_(teb) & TB_DEFD) || !(tagbindbits_(trb) & TB_DEFD)))
            cc_warn(xsem_warn_cast_undef_struct, trb, teb);
        return pointercast(op, e, te, tr);             /* same as for C */
    }

    if (err && !SuppressDB_Has(Suppress_ImplicitCast))
    {   if (err & 2)
            cc_rerr(sem_rerr_implicit_cast1, op);
        else
            cc_rerr(sem_rerr_implicit_cast5, op, q);
    }
    return e;
}

static bool common_pointer_type(AEop op,
        TypeExpr *t1, Expr *e1, Expr **newe1,
        TypeExpr *t2, Expr *e2, Expr **newe2,
        TypeExpr **common)
/* Find a common pointer type for t1 and t2 which must be pointers to   */
/* (possibly qualified) class types, if any.  If found return newe1 and */
/* newe2 as the cast expressions as well as the common type chosen (t1  */
/* or t2).                                                              */
/* e1 == *newe1, e2 == *newe2, t1 == *common, t2 == *common are ok.     */
{   TypeExpr *t1x = typearg_(princtype(t1)), *t2x = typearg_(princtype(t2));
    if (type_derived_from(t1x, t2x))
    {   Expr *newe = cpp_ptrcast(op, e2, t2x, t1x, t_content);
        *newe1 = e1;
        *newe2 = newe;
        *common = h0_(*newe2) == s_error ? 0 : t1;
        return YES;
    }
    if (type_derived_from(t2x, t1x))
    {   Expr *newe = cpp_ptrcast(op, e1, t1x, t2x, t_content);
        *newe1 = newe;
        *newe2 = e2;
        *common = h0_(newe) == s_error ? 0 : t2;
        return YES;
    }
    return NO;
}

static bool common_reference_type(AEop op,
        TypeExpr *t1, Expr *e1, Expr **newe1,
        TypeExpr *t2, Expr *e2, Expr **newe2,
        TypeExpr **common)
/* Find a common reference type for t1 and t2 which must be             */
/* (possibly qualified) class types, if any.  If found return newe1 and */
/* newe2 as the cast expressions as well as the common type chosen (t1  */
/* or t2).                                                              */
/* e1 == *newe1, e2 == *newe2, t1 == *common, t2 == *common are ok.     */
{   if (type_derived_from(t1, t2))
    {   TypeExpr* reft1 = mk_typeexpr1(t_ref, t1, 0);
        Expr *newe = cpp_mkcast(op, &e2, reft1);
        if (h0_(newe) == s_error) return NO;
        *newe1 = e1;
        *newe2 = newe;
        *common = reft1;
        return YES;
    }
    if (type_derived_from(t2, t1))
    {   TypeExpr* reft2 = mk_typeexpr1(t_ref, t2, 0);
        Expr *newe = cpp_mkcast(op, &e1, reft2);
        if (h0_(newe) == s_error) return NO;
        *newe1 = newe;
        *newe2 = e2;
        *common = reft2;
        return YES;
    }
    return NO;
}

/* Handle casts involving refs, constructors and conversion fns.        */
/* Return non-0 to indicate all done; 0 to indicate that work remains   */
/* for sem.c::mkcast(), our caller.                                     */

static Expr *cpp_mkcast(AEop op, Expr **ep, TypeExpr *tr)
{   Expr *e = *ep;
    TypeExpr *x = princtype(tr);
    TypeExpr *te = typeofexpr(e);
    TypeExpr *y = princtype(te);

    if (h0_(x) == t_unknown)
        return (op == s_cast)?
            mk_expr1(s_cast, tr, coerceunary(e)) : coerceunary_2(e, COERCE_ASSIGN);
    if (h0_(y) == t_unknown) return mk_expr1(s_cast, tr, coerceunary(e));

    if (h0_(x) == t_ref)
    {   /* don't coerceunary yet, e.g. int a[5], (&x)[5] = a.           */
        /* are refs to fns/arrays allowed?  Unwritable!                 */
        /* but should we ref->content?                                  */
        TypeExpr *xr = typearg_(x);
/* Rationale: explicit casts to refs share an lvalue, but implicit      */
/* ones do not unless types match.  See [ES, p69, p155].  Whee(p).      */
/* The text on p154 differs from the examples: we allow a const ref     */
/* to refer to a non-const lvalue (as per 'rcd' in example).            */
        TypeExpr *lvt = lvalue_type(e);
        Binder *conv;
        bool is_ref_compatible_type = NO;
        if (lvt != NULL && (op == s_cast ||
#ifdef NEVER
/* consider:  volatile int i; const int &ri = i;  temp or not?          */
                            qualifier_subset(lvt, xr) &&
#endif
              ((is_ref_compatible_type = (qualfree_equivtype(lvt, xr) ||
                                         type_derived_from(xr, lvt)))
                            || h0_(xr) == t_fnap)))
/* The t_fnap case allows    int f(); int (&g)() = f;                   */
/* @@@ The following is sordid: lvalue_type considers all class values  */
/* to be ref-lvalues (q.v.) since they all have addresses               */
/* (@@@ modulo one-word structs) and rely on struct manipulation code   */
/* to have inserted temp locations were needed.  This seems necessary   */
/* so that complex x = sqrt(z); can make a ref to the result of sqrt    */
/* which can be passed to the copy constructor.  Hmmm.  Standard??      */
/* mkaddr() below skips the ensurelvalue test in mkunary(s_addrof).     */
/* It is not clear whether complex(3,4) is an lvalue.                   */
/* @@@ also maybe non optimal, given  'class D:A, B { ... };'.          */
/* (D *) => (B *) requires a NULL test, but (D &) => (B &) doesn't!     */
/* (pointercast() leaves type unchanged, but does any addition.)        */
        {   Expr *ea;
            TypeExpr *tea;
            if (isclasstype_(lvt))
            {   if (op == s_init &&
                    (!is_ref_compatible_type ||
                     (h0_(e) == s_invisible && h0_(orig_(e)) == s_ctor)))
                {   TypeExpr *plvt = ptrtotype_(lvt);
                    Binder *b = genreftemp(lvt);
                    ea = mkopap(s_init, typespectagbind_(lvt), (Expr *)b, mkExprList1(e));
                    ea = mk_expr2(s_comma, plvt, ea, mk_expr1(s_addrof, plvt, (Expr *)b));
                }
                else
                {   ea = mkaddr(coerceunary(e));
                    if (h0_(e) == s_binder)
                        bindstg_((exb_(e))) |= b_addrof|u_referenced;
                }
            }
            else
                ea = mkunary(s_addrof, e);
            tea = princtype(type_(ea)); /* differs from lvt if t_ovld->t_fnap. */
            if (h0_(tea) != t_content) syserr("mkcast(ref)");
            e = cpp_ptrcast(op, ea, typearg_(tea), xr, t_ref);
        }
        else if (op != s_cast && isclasstype_(y) &&
                (conv = class_has_conversion(typespectagbind_(y), x, YES)) != 0)
        {   e = mkfnap(mkfieldselector(s_dot, e, conv), 0);
            return mkcast(op, e, tr);
        }
        else
        {   Binder *b = (op == s_init) ? genreftemp(xr) : genexprtemp(xr);
            TypeExpr *pxr = ptrtotype_(xr);
            if (!(qualifiersoftype(xr) & bitoftype_(s_const)))
            {   cc_rerr(sem_rerr_valcasttoref, op);
                return errornode;
                    /* @@@ explicit/implicit casts differ?              */
                    /* beware refs to fns/arrays -- will syserr!?       */
            }

            {   TypeExpr *pt = princtype(xr);
                TagBinder *cla = isclasstype_(pt) ? typespectagbind_(pt) : 0;
                if (cla != 0) pt = primtype2_(
                    typespecmap_(pt) & ~bitoftype_(s_const), cla);

                e = mkcast(s_init, e, pt);
                if (cla == NULL)
                {   /* the following call caused tempbinders to be introduced into
                       scope such as s_fnap. Bad. But its purpose maybe related
                       to the comment below.
                     */
                    e = mkbinary(s_init, (Expr *)b, e);
                }
                else
                    e = mkopap(s_init, cla, (Expr *)b, mkExprList1(e));
                if (e == 0)
                    /* @@@ FW found this apprehensive, no diagnostics ehh!!! */
                    e = errornode;
                else if (e != errornode)
                {
                    e = mk_expr2(s_comma, pxr, e,
                            mk_expr1(s_addrof, pxr, (Expr *)b));
                    bindstg_(b) |= b_addrof|u_referenced;
                }
            }
#if 0
            e = mkcast(s_init, e, xr);
            if (e != errornode)
                e = mk_expr2(s_comma, pxr, e,
                        mk_expr1(s_addrof, pxr, (Expr *)b));
#endif
        }
/* The above Expr 'e' always has pointer type -- cast to ref type:      */
        return h0_(e) == s_error ? e : mk_expr1(s_cast, tr, e);
    }

    if (isvoidtype(x))
    {   if (h0_(y) == t_ovld || (h0_(y) == t_content && h0_(typearg_(y)) == t_ovld))
        {   cc_rerr(sem_rerr_noncallsite_ovld, NULL, exb_(e));
            return errornode;
        } else
            return 0 /* handle as in C */;
    }

    if (h0_(y) == t_ref)
    {   TypeExpr *tt = princtype(typearg_(y));
        if (isclasstype_(tt))
        /* ref class may involve conversions... */
        {   e = mkinvisible(typearg_(y), e, mk_expr1(s_content,typearg_(y),e));
            te = typearg_(y);
            y = tt;
        }
    }

    if (h0_(y) == t_ovld || (h0_(y) == t_content && h0_(typearg_(y)) == t_ovld))
    {   Binder *generic = NULL;
        Binder *specific;
        if (h0_(e) == s_addrof)
            generic = exb_(arg1_(e));
        else if (h0_(e) == s_dot || h0_(e) == s_qualdot)
            generic = exb_(arg2_(e));
        else if (h0_(e) == s_binder)
            generic = exb_(e);
        if (generic == NULL || h0_(generic) != s_binder)
            syserr("cpp_mkcast odd t_ovld expr");
        if (h0_(y) == t_content && h0_(x) != t_content)
            syserr("odd desttype for ovld fn");
        specific = ovld_resolve_addr_2(op, (h0_(x) == t_content) ? typearg_(x) : x,
               typeovldlist_(h0_(y) == t_content ? typearg_(y) : y), generic);
        if (specific == NULL)
            return errornode;
        if ((bindstg_(specific) & b_memfna) && h0_(e) != s_addrof)
        {   if (HasFeature(Feature_CFront))
                cc_warn(simplify_err_illegal_use_of_mem_fn, generic);
            else
                cc_rerr(simplify_err_illegal_use_of_mem_fn, generic);
        }
        e = mkaddr((Expr *)specific);
        if (op == s_cast)
        {   *ep = e;
            return NULL;        /* now handle as in 'C' */
        }
        return e;
    }

    if (isclasstype_(x) && isclasstype_(y) &&
        (core_class(typespectagbind_(x)) == core_class(typespectagbind_(y)) ||
         derived_from(typespectagbind_(x), typespectagbind_(y))))
    {   if (typespectagbind_(x) == typespectagbind_(y))
            /* identical class; handle as in C */
            return 0;
        else if (h0_(e) == s_binder)
        {   /* y is derived from tr, or core_class(x) is core_class(y)  */
            /* next line to handle: struct B {}; struct D : B {};       */
            /* const D d; B b; b = d;                                   */
            Expr *ea;
            TypeExpr *tea;
            tr = mkqualifiedtype(tr, qualifiersoftype(typeofexpr(e)));
            ea = mkaddr(e);
            tea = princtype(type_(ea));
            return mkunary(s_content,
                cpp_ptrcast(op, ea, typearg_(tea), tr, t_content));
        }
        else
        {   ClassMember *basemem = derived_from(typespectagbind_(x),
                                                typespectagbind_(y));
            return (!basemem) ? e : mkfieldselector(s_dot, e, basemem);
        }
    }
    else
    {   Binder *convfn = 0, *convctor = 0;
        if (isclasstype_(y))
            convfn = class_has_conversion(typespectagbind_(y), x, YES);
        if (isclasstype_(x))
            convctor = class_has_ctor(typespectagbind_(x), y, e, YES);

        if (convfn != 0 && convctor != 0)
        {   cc_err(syn_err_ambiguous_user_defined_conv, typespectagbind_(y),
                   typespectagbind_(x));
        }

        if (convfn != 0)
        {   e = mkfnap(mkfieldselector(s_dot, e, convfn), 0);
            return mkcast(op, e, tr);
        }
        else
        {   if (convctor != 0)
            {
    /* @@@ LDS 28-Sep-94: The following has been done above, I believe,     */
    /* first by ref stripping and then by checking for the same tagbinder.  */
    /* if (qualfree_equivtype(x, typeofexpr(coerceunary_2(e, COERCE_ARG)))) */
    /*              goto same_as_C;                                         */
                TypeExpr *bt = primtype2_(
                    typespecmap_(x) & ~bitoftype_(s_const),
                        typespectagbind_(x));
                Binder *b = genexprtemp(bt);

                Expr *init;
    /* beware the following line -- two deficiencies: 1. too much at    */
    /* run-time and doesn't alwyas require init.                        */
                attributes_(b) |= A_DYNINIT;
                if (op != s_cast)
                {   if (SuppressDB_Has(Suppress_ImplicitCtor)) xwarncount++;
                    else
                        /* see the discussion in [ES, p272]             */
                        cc_warn(sem_warn_implicit_constructor, x);
                }

                init = mk_expr2(s_comma, bt,
                                mkfnap(mkfieldselector(s_dot, (Expr *)b, convctor),
                                       mkExprList1(e)),
                                (Expr *)b);
                return mkinvisible(tr, mk_expr1(s_ctor, tr, e), mkcast(op, init, tr));
            }
        }
    }
    return 0;
}

/* Now stuff about constructors, first the virtual fn and base stuff... */

/* vfn_list() must keep in step with vtab_init().                       */
static VfnList *vfn_list_1(TagBinder *cl, int32 n, int32 off, VfnList *vfl,
                           TagBinder *derivation)
{   ClassMember *m;
    for (m = tagbindmems_(cl);  m != NULL;  m = memcdr_(m))
        if (h0_(m) == s_binder && bindstg_(m) & bitofstg_(s_virtual))
        /* Here, we really do want to search for the Symstr of the member */
        /* not for the member, or we won't find the most-derived vfn.     */
        {   Expr *e =
               path_to_member((ClassMember *)memsv_(m), derivation,
                            INDERIVATION+FB_FNBINDER+FB_KEEPI);
            int32 thisoffset = off;
            Binder *b = exb_(((h0_(e) == s_invisible) ?
                (thisoffset += arg3i_(e), arg2_(e)) : e));
            if (h0_(b) != s_binder)
                syserr("vfn $b not in class $b\n", m, derivation);
            if (bindstg_(b) & b_impl) b = realbinder_(b);
/* @@@ we shouldn't use 'b' here but lookup for the nearest b in the    */
/* derivation hierarchy.  But what about multiple (virtual) paths?      */
/* Oh, that's OK, use l-r algorithm (from vbase-init [ES])?             */
            if (debugging(DEBUG_BIND))
                cc_msg("vfn $b/$c,%ld, thisoff=%ld\n", b, cl, n, thisoffset);
            vfl = mkVfnList(vfl, b, thisoffset);
            n--;
        }
    /* left-most vtable sharing wrecked the following ...
    if (n != 0) syserr("vtable count $c", cl); */
    return vfl;
}

typedef List VtabList;
typedef struct VtabElt VtabElt;
struct VtabElt {
  TagBinder *cl;
  ClassMember *vtab;
  int32 offset;
};

static VtabList *lmost_derived, *rest;

#define mkVtabList(a,b)         ((VtabList *)syn_list2(a,b))
#define mkVtabElt(a,b,c)        ((int32 *)syn_list3(a,b,c))

static void vfn_list_r(TagBinder *cl, int32 off,
                       TagBinder *derivation)
{   ClassMember *m = tagbindmems_(cl);
    bool done = NO;

    if (m == NULL) return;
    if (attributes_(m) & (CB_CORE|CB_BASE))
    {   vfn_list_r(typespectagbind_(princtype(memtype_(m))), off, derivation);
        m = memcdr_(m);
    }
    {   ClassMember *tmp = m;
        for (; tmp != NULL; tmp = memcdr_(tmp))
        {   if (attributes_(tmp) & CB_VTAB)
            {   lmost_derived = mkVtabList(lmost_derived,
                        mkVtabElt(cl, tmp, off));
                done = YES;
                break;
            }
        }
    }
    for (;  m != NULL;  m = memcdr_(m))
    {   TypeExpr *t = princtype(memtype_(m));
        if (!is_datamember_(m)) continue;
/* In the next lines it is important to calculate the vbase 'this'      */
/* delta value from the base layout and not via vbase pointers (which   */
/* would arise when using mkcast(base-pointer to derived-pointer).      */
        if (attributes_(m) & CB_VTAB && !done)   /* i.e. vtabsym (for fgrep).    */
        {   int32 off1 = off == OFFSET_UNSET || memwoff_(m) == OFFSET_UNSET ?
                           OFFSET_UNSET :
                           off + memwoff_(m);
                rest = mkVtabList(rest, mkVtabElt(cl, m, off1));
        } else if (attributes_(m) & (CB_CORE|CB_VBASE|CB_BASE) &&
                    isclasstype_(t))
        {   int32 off1 = off == OFFSET_UNSET || memwoff_(m) == OFFSET_UNSET ?
                           OFFSET_UNSET :
                           off + memwoff_(m);
            vfn_list_r(typespectagbind_(t), off1, derivation);
        }
    }
}

/* vfn_list() collects a (reverse) list of the virtual functions and    */
/* their deltas for a class 'cl'.  'e' is NULL and 'off' 0 initially.   */
VfnList *vfn_list(TagBinder *cl)
{   VfnList *e = 0, *pe,  *last;
    List *vp;
    lmost_derived = 0, rest = 0;
    vfn_list_r(cl, 0, cl);
    lmost_derived = (VtabList *)dreverse(lmost_derived);
    rest = (VtabList *)dreverse(rest);
    for (vp = lmost_derived; vp != 0; vp = vp->cdr)
    {   VtabElt *tmp = (VtabElt *)car_(vp);
        e = vfn_list_1(tmp->cl, memvtablesize_(tmp->vtab), -tmp->offset, e, cl);
    }
    /* prefix preserving elimination of duplicates */
    e = (VfnList*)dreverse((List *)e);
    for (last = pe = e; pe != 0; pe = pe->vfcdr)
    {   VfnList *ppe;
        Symstr *sv = bindsym_(pe->vfmem);
        for (ppe = e; ppe != pe; ppe = ppe->vfcdr)
            if (bindsym_(ppe->vfmem) == sv && ppe->vfdelta == pe->vfdelta)
                break;
        if (ppe != pe)
            last->vfcdr = pe->vfcdr;
        else
            last = pe;
    }
    e = (VfnList *)dreverse((List *)e);
    for (vp = rest; vp != 0; vp = vp->cdr)
    {   VtabElt *tmp = (VtabElt *)car_(vp);
        e = vfn_list_1(tmp->cl, memvtablesize_(tmp->vtab), -tmp->offset, e, cl);
    }
/* do not refer to pure virtual fns, but catch calls through them...    */
    for (pe = e; pe != 0; pe = pe->vfcdr)
    {   if (bindstg_(pe->vfmem) & b_purevirtual)
            pe->vfmem = cppsim.xpvfn;
    }
    return e;
}

/* assert: vta = (s_addrof type binder).                                */
/* vto is the offset into the virtual function table.                   */
/* (currently done in the order of left-most derivation, core and       */
/* vbases)                                                              */
static Expr *vtab_init_1(TagBinder *cl, Expr *var, int32 off, Binder *vta,
                         int32 *vto)
{   ClassMember *m = tagbindmems_(cl);
    Expr *e = NULL;
    if (debugging(DEBUG_BIND))
        cc_msg("vtab($c+%ld, %ld)\n", cl, off, *vto);
    if (m == NULL) return e;

    if (attributes_(m) & (CB_CORE|CB_BASE))
    {   e = vtab_init_1(typespectagbind_(princtype(memtype_(m))),
                        var, off, vta, vto);
        m = memcdr_(m);
    }
    {   ClassMember *tmp = m;
        for (; tmp != NULL; tmp = memcdr_(tmp))
        {   if (attributes_(tmp) & CB_VTAB)
            {   if (!(bindstg_(tmp) & bitofstg_(s_typedef))) {
                    int32 off1 = off == OFFSET_UNSET || memwoff_(tmp) == OFFSET_UNSET ?
                                   OFFSET_UNSET : off + memwoff_(tmp);
                    Expr *e1 = mk_expr2(s_assign, bindtype_(vta),
                                        mk_exprwdot(s_dot, bindtype_(vta), var, off1),
                                        mk_expr2(s_plus, bindtype_(vta), (Expr *)vta,
                                                 mkintconst(te_int, TARGET_VTAB_ELTSIZE*(*vto),
                                                            0)));
                    e = commacons(e, e1);
                }
                *vto += memvtablesize_(tmp);
                break;
            }
        }
    }

    for (; m != NULL; m = memcdr_(m))
    {   TypeExpr *t = princtype(memtype_(m));
        if (!is_datamember_(m)) continue;
        if (attributes_(m) & (CB_VBASE|CB_BASE))
        {   int32 off1 = off == OFFSET_UNSET || memwoff_(m) == OFFSET_UNSET ?
                           OFFSET_UNSET : off + memwoff_(m);
            if (!isclasstype_(t)) syserr("what sort of base $b is this?", m);
            e = commacons(e, vtab_init_1(typespectagbind_(t), var, off1, vta, vto));
        }
    }
    return e;
}

static Binder *vtab_declare(Symstr *name)
{   DeclRhsList d;
/* the 'decltype' values in the following are rather a lie...           */
#ifndef TARGET_DATA_VTABLE
    TypeExprFnAux s;
    d.decltype = mkTypeExprfn(t_fnap, te_void, 0, 0,
                              packTypeExprFnAux(s, 0, 0, 0, 0, 0));
    /* NB: b_memfns forces a direct call instate_declaration_1() from   */
    /* instate_declaration_cpp(), with no further manging of name.      */
    d.declstg =
        bitofstg_(s_static) | b_undef | b_fnconst | b_memfns;
    /* soon to be COMMON,CODE on RISCOS.                                */
#else
    d.decltype = te_ulint;
    d.declstg = bitofstg_(s_static) | b_undef;
#endif
    d.declname = name;
    declinit_(&d) = 0;
    return instate_declaration(&d, TOPLEVEL);
}

/* AM: I think the best way to organise this is to arrange each class   */
/* which needs a vfntable (i.e. it, or one of its bases, has vfns)      */
/* has a static member which is vtb below.                              */
Expr *vtab_init(TagBinder *cl, Expr *var)
{   Symstr *name;
    Binder *vtb, *vta;
    int32 vto = 0;
    Expr *evta;
    Expr *r;
    if (!(tagbindbits_(cl) & TB_HASVTABLE))      /* lift to callers?     */
        return 0;
    name = ovld_instance_name(vtabsym, tagbindtype_(cl));
    vtb = bind_global_(name);                   /* nasty in this file!  */
    if (vtb == 0) vtb = vtab_declare(name);
    evta = mk_expr1(s_addrof, ptrtotype_(bindtype_(vtb)), (Expr *)vtb);
    vta = gentempbinder(type_(evta));
    r = vtab_init_1(cl, var, 0, vta, &vto);
    if (r)
        r = mklet(vta, bindtype_(vta),
                commacons(mkbinary(s_assign, (Expr *)vta, evta), r));
    if (vto == 0) syserr("empty vtable $c", cl);
    vg_note_vtable(cl, vto, bindsym_(vtb));
    return r;
}

/* vbase_init_1() walks a class looking for virtual base pointer fields.    */
/* On entry, 'var' is a side-effect-free object expression, which has       */
/* a sub-object of class 'cl' at offset 'off'.  'e' points initially to     */
/* the virtual base, but is extended to an assignment sequence:             */
/*    var.n1 = var.n2 = ... = var.nk = vbptr.                               */
/* On exit, e, now the augmented assignment sequence, is returned.          */
/* Assert: At least one assignment MUST be generated by each call.          */

static Expr *vbase_init_1(TagBinder *cl, Expr *var, int32 off, Expr *e)
{   ClassMember *m;

    for (m = tagbindmems_(cl);  m != NULL;  m = memcdr_(m))
    {   TypeExpr *t = princtype(memtype_(m));
        if (!is_datamember_(m)) continue;
/* @@@ beware: equivtype would fail for 'const' bases...                 */
        if ((attributes_(m) & CB_VBPTR) && equivtype(t, type_(e)))
        {   int32 off1 = off == OFFSET_UNSET || memwoff_(m) == OFFSET_UNSET ?
                           OFFSET_UNSET : off + memwoff_(m);
            e = mk_expr2(s_assign, type_(e),
                         mk_exprwdot(s_dot, type_(e), var, off1),
                         e);
        } else if (attributes_(m) & (CB_CORE|CB_VBASE|CB_BASE) &&
                    isclasstype_(t))
        {   int32 off1 = off == OFFSET_UNSET || memwoff_(m) == OFFSET_UNSET ?
                           OFFSET_UNSET : off + memwoff_(m);
            e = vbase_init_1(typespectagbind_(t), var, off1, e);
        }
    }
    return e;
}

/* On entry, 'var' is a side-effect-free expression (variable or content(e) */
/* with 'e' side-effect free) of class 'cl'. For each virtual base of       */
/* 'cl' in turn, vbase_init() calls class vbase_init_1() to make a compound */
/* assignment expression initialising all pointers to that virtual base.    */
/* If there is more than one virtual base, these compound assignments are   */
/* collected via comma expressions to yield a single initialising Expr.     */

Expr *vbase_init(TagBinder *cl, Expr *var)
{   Expr *e = NULL;
    ClassMember *m = tagbindmems_(cl);
    if (m != NULL && (attributes_(m) & CB_CORE))
    {   /* deal with vbase construction for each vbase pointer in turn */
        for (m = memcdr_(m); m != NULL; m = memcdr_(m))
        {   if (!(attributes_(m) & CB_VBASE))
                syserr("vbase_init($b, $r)", cl, memsv_(m));
            e = commacons(e,
                  vbase_init_1(cl, var, 0,
                    mk_expr1(s_addrof, ptrtotype_(memtype_(m)),
                        mk_exprwdot(s_dot, memtype_(m), var, memwoff_(m)))));
        }
    }
    return e;
}

#ifdef NEVER

static Expr *virt_init_1(TagBinder *cl, Expr *var, int32 off)
{   /* Now scan for any non-base members (including non-base members    */
    /* of base members) which need initialising:                        */
    Expr *e = 0;
    ClassMember *m;
    for (m = tagbindmems_(cl);  m != NULL;  m = memcdr_(m))
    {   TypeExpr *t = princtype(memtype_(m));
        if (!is_datamember_(m)) continue;
        if (isclasstype_(t))
        {   TagBinder *cl2 = typespectagbind_(t);
            int32 off1 = off == OFFSET_UNSET || memwoff_(m) == OFFSET_UNSET ?
                            OFFSET_UNSET : off + memwoff_(m);
            if (!(attributes_(m) & (CB_CORE|CB_VBASE|CB_BASE)))
            {   Expr *v2 = mk_exprwdot(s_dot, t, var, off1);
                e = commacons(e,
                      commacons(vbase_init(cl2, v2), vtab_init(cl2, v2)));
            }
            e = commacons(e, virt_init_1(cl2, var, off1));
        }
    }
    return e;
}

static Expr *virt_init(TagBinder *cl, Expr *var)
{   return commacons(commacons(vbase_init(cl, var), vtab_init(cl, var)),
                     virt_init_1(cl, var, 0));
}

#endif

extern bool typehasctor(TypeExpr *t)
{   t = princtype(t);
    if (isclasstype_(t) &&
        (tagbindbits_(typespectagbind_(t)) & TB_NEEDSCTOR ||
         (tagbindbits_(typespectagbind_(t)) & TB_TEMPLATE &&
          findbinding(ctorsym, typespectagbind_(t), INCLASSONLY) != NULL)))
            return 1;
    return 0;
}

extern bool isarraytype(TypeExpr *t, TypeExpr ** elmtype)
{   bool isarray = NO;
    for (; h0_((t = princtype(t))) == t_subscript; t = typearg_(t))
        isarray = YES;

    if (isarray && elmtype != NULL) *elmtype = t;
    return isarray;
}

/* returns the number of elements in a possibly multi-dimensional array */
/* as well as the element type.  '[]' is taken as '[1]' */
extern int32 arraysize(TypeExpr *t, TypeExpr ** elmtype) /* @@@ should return size_t */
{   size_t nelts = 1;
    for (; h0_((t = princtype(t))) == t_subscript; t = typearg_(t))
        if (typesubsize_(t) != 0 && h0_(typesubsize_(t)) != s_binder)
            nelts *= evaluate(typesubsize_(t));

    if (elmtype != NULL) *elmtype = t;
    return nelts;
}

Expr *array_of_class_map_expr(Expr *p, Expr *nelts, int32 stride, Expr *mapfn)
{   ExprList *l;
    if (mapfn == 0) return 0;

    l = mkExprList1(mapfn);
    l = mkExprList(l, mkintconst(te_int, stride, 0)); /* /* should be size_t? */
    l = mkExprList(l, nelts);
    l = mkExprList(l, p);
    return mkfnap(cppsim.xmapvec1, l);
}

Expr *array_of_class_map(Expr *e, int32 nelts, int32 stride, bool up,
                         Expr *mapfn, bool twoargmapfn)
{   if (mapfn == 0) return 0;

  { TypeExpr *fnargt =
        ptrtotype_(te_fntype(te_void, te_voidptr, twoargmapfn ? te_int : 0, 0, 0, 0));
    Expr *limit;
    if (up)
    {   limit = /* '(char*)e + nelts * stride' */
            mkbinary(s_plus,
                 mkcast(s_cast|s_qualified, e, te_charptr),
                 mkintconst(te_size_t, nelts * stride, 0));
    }
    else
    {   /* We cast to unsigned long instead of the more obvious */
        /* char* to avoid a subscript out-of-range warning      */
        /* /* Technically limit is a undefined pointer.         */
        limit = /* '(void*)((unsigned long)e - stride' */
            mkcast(s_cast|s_qualified,
                   mkbinary(s_minus,
                            mkcast(s_cast|s_qualified, e, te_ulint),
                            mkintconst(te_size_t, stride, 0)),
                   te_voidptr);
        e = /* '(char*)e + (nelts - 1) * stride' */
            mkbinary(s_plus,
                 mkcast(s_cast|s_qualified, e, te_charptr),
                 mkintconst(te_size_t, (nelts - 1) * stride, 0));
        stride = -stride;
    }
    return mkfnap(twoargmapfn ? cppsim.xmapvec1ci : cppsim.xmapvec1c,
               mkExprList4(e,
                           limit,
                           mkintconst(te_int, stride, 0),
                           mkcast(s_cast|s_qualified, mapfn, fnargt)));
  }
}

Expr *array_of_class_copy(Expr *to, Expr *fm, Expr *frmlimit, int32 stride,
        Binder *mapfn)
{   if (mapfn == 0) return 0;

  { ExprList *l;
    TypeExpr *fnargt = ptrtotype_(te_fntype(te_void, te_voidptr, te_voidptr, 0, 0, 0));

    l = mkExprList1(mk_expr1(s_addrof, fnargt, (Expr *)mapfn));
    l = mkExprList(l, mkintconst(te_size_t, stride, 0));
    l = mkExprList(l, frmlimit);
    l = mkExprList(l, mkcast(s_cast, mkunary(s_addrof, fm), te_voidptr));
    l = mkExprList(l, mkcast(s_cast, mkunary(s_addrof, to), te_voidptr));

    return mkfnap(cppsim.xmapvec2, l);
  }
}

static Expr *mkctor_v_1(Expr *e, ExprList *init, bool init_without_ctor)
{   /* e is a side-effect-free lvalue, typically var or *var.           */
    TypeExpr *t = typeofexpr(e);
    Expr *r = 0;
    ExprList *l;

    /* don't even try if earlier serious error in argument construction */
    for (l = init;  l != 0;  l = cdr_(l))
        if (h0_(exprcar_(l)) == s_error) return errornode;

    if (recursing)
    {   cc_err(sem_err_ctor_confused, t);
        --recursing;
        return errornode;
    }
    else
        ++recursing;

    t = princtype(t);
    if (isclasstype_(t))
    {   TagBinder *cla = typespectagbind_(t);
        r = mkopap(s_init, cla, e, init);
        if (r == 0 && (tagbindbits_(cla) & TB_NEEDSCTOR))
        {   cc_err(sem_err_no_ctor_at_type, cla);
            r = errornode;
        }
    }
    else if (h0_(t) == t_subscript)
    {   TypeExpr *elmtype;
        size_t nelts = arraysize(t, &elmtype);
        if (isclasstype_(elmtype))
        {   TagBinder *tb = typespectagbind_(elmtype);
            Binder *ctorb = findbinding(ctorsym, tb, INCLASSONLY);
            /* @@@ Bjarne says we have to allow things like: */
            /*   struct T { T(int=99); }; */
            /*   void f() { T a[3]; T* p = new T[5]; } */
            /* We don't yet */
            if (ctorb != NULL)
            {   Expr *ctorfn = ovld_picknullary(ctorb);
                if (ctorfn == NULL)
                {   cc_err(syn_err_no_nullary_ctor, ctorb);
                    return errornode;
                }
                /* lose const/volatile for dtor for e.g. const class A x[];   */
                e = mkcast(s_cast|s_qualified, e, ptrtotype_(tagbindtype_(tb)));
                /* code gen will give error message for 'T a[];' */
                r = array_of_class_map(e, nelts, sizeoftype(elmtype), YES,
                                       ctorfn, NO);
            }
        }
    }
    if (r == 0 && init_without_ctor && init != 0)
    {   /* no constructor and init-val(s) */
        if (cdr_(init) != 0)
            cc_rerr(sem_rerr_too_many_args, t);
        r = mkbinary(s_init, e,
                     mkcast(s_new,     /* not s_cast (no int("abc")). */
                            exprcar_(init), t));
    }

    --recursing;
    return r;
}

Expr *mkctor_v(Expr *e, ExprList *init)
{   return mkctor_v_1(e, init, YES);
}

static Expr *mkctor_p(Expr *nw, ExprList *init)
{   TypeExpr *pt = typeofexpr(nw);
    Binder *b = gentempbinder(pt);
    Expr *ctor = mkctor_v(mkunary(s_content, (Expr *)b), init);
/* Generate: "let (t *b) in (b = nw(), b?ctor():0, b)".                 */
/* Note that making ctors return their arg could optimise reg use?      */
    return ctor==0 ? nw : mklet(b, pt,         /* mkinvisible? */
        commacons(mkbinary(s_assign, (Expr *)b, nw),
                  commacons(mkcond((Expr *)b,
                                   mkcast(s_new, ctor, te_void),
                                   mkintconst(te_void, 0, 0)),
                            (Expr *)b)));
}

static Expr *mkctor_temp(TypeExpr *t, ExprList *l, int takeaddress)
{  Binder *b = genexprtemp(t);
   TypeExpr *pt = princtype(t);
/* Maybe we should prefer a "to-end-of-expr" temp here insteam of       */
/* the required "to-end-of-scope" temp for reference temps.             */
    Expr *e, *init;
/* beware the following line -- two deficiencies: 1. too much at        */
/* run-time and doesn't alwyas require init.                            */
    attributes_(b) |= A_DYNINIT;
    if (isclasstype_(pt))
    {   bindtype_(b) = primtype2_(
            typespecmap_(pt) & ~bitoftype_(s_const), typespectagbind_(pt));
        if (attributes_(b) & A_GLOBALSTORE)
            bindtype_(b) = globalize_typeexpr(bindtype_(b));
    }
    init = mkctor_v((Expr *)b, l);
    if (h0_(init) == s_error) return errornode;
    e = takeaddress ? mkunary(s_addrof, (Expr *)b) : (Expr *)b;
    e = commacons(init, e);
    t = type_(e);
    return mkinvisible(t, mk_expr1(s_ctor, t, e), e);
}

Expr *mkctor_t(TypeExpr *t, ExprList *l)
{   return mkctor_temp(t, l, NO);
}

#if 0
static Expr *mkctor_r(TypeExpr *t, Expr *e)
{   return mkctor_temp(t, mkExprList1(e), YES);
}
#endif

static Expr *mkdtor_v_1(Expr *e, Expr* do_op_dl)
{   /* e is a side-effect-free lvalue, typically var or *var.           */
    TypeExpr *t = princtype(typeofexpr(e));
    if (isclasstype_(t))
    {   TagBinder *tb = typespectagbind_(t);
        ClassMember *dtormem = findbinding(dtorsym, tb, INCLASSONLY);
        if (dtormem != NULL)
        {   /* lose const/volatile for dtor for e.g. const class A x;   */
            e = mkunary(s_content,
                    mkcast(s_cast|s_qualified, mkunary(s_addrof, e),
                           ptrtotype_(tagbindtype_(tb))));
            return mkfnap(mkfieldselector(s_dot, e, dtormem),
                          mkExprList1(do_op_dl));
        }
    }
    else if (h0_(t) == t_subscript)
    {   TypeExpr* elmtype;
        size_t nelts = arraysize(t, &elmtype);
        if (isclasstype_(elmtype))
        {   Binder *dtorb = findbinding(dtorsym, typespectagbind_(elmtype),
                                        INCLASSONLY);
            if (dtorb != NULL)
            {   Expr* dtorfn = ovld_picknullary(dtorb);
                if (dtorfn == NULL)
                    return errornode;   /* /* syserr ? */
                return array_of_class_map(e, nelts, sizeoftype(elmtype), NO,
                                          dtorfn, YES);
            }
        }
    }

    return 0;
}

Expr *mkdtor_v(Expr *e)
{   return mkdtor_v_1(e, lit_zero);
}

static Expr *mkdtor_p(Expr *e, Binder* delgeneric, bool forceglobal)
{ TypeExpr *te = princtype(typeofexpr(e));
  /* Presumably 'everyone knows' arg is a t_content or a typedef to it. */
  /* Check anyway.                                                      */
  if (h0_(te) != t_content) syserr("mkdtor_p %ld", (long)h0_(te));
  {
    TypeExpr *ncte = (typeptrmap_(te)) & bitoftype_(s_const) ?
        ptrtotype_(typearg_(te)) :
        te;
    Binder *b = gentempbinder(ncte);
    Expr *dtor = mkdtor_v_1(mkunary(s_content, (Expr *)b),
                            forceglobal ? lit_zero : lit_one);
    if (dtor != 0)
    {   Expr *dl = mkcast(s_delete, dtor, te_void);
        if (forceglobal)
            dl = commacons(dl,
                    mkfnap((Expr*)delgeneric, mkExprList1((Expr*)b)));
        else
        {   /* check access of operator delete() */
            ExprList *delargs = 0;
            if (is_two_arg_delete(delgeneric))
                delargs = mkExprList1(mkintconst(te_size_t, 0, 0));
            delargs = mkExprList(delargs, (Expr*)b);
            (void)ovld_resolve(delgeneric, typeovldlist_(bindtype_(delgeneric)),
                               delargs, delargs, NO);
        }
/* Have to guard dtor calls and user operator deletes                   */
/* Generate: "let (t *b) in (b = e, b?b->dtor(), dl(b):0)".             */
/* or: "let (t *b) in (b = e, b?b->dtor(), dl(b, size):0)".             */
/* Note that making dtors return their arg could optimise reg use?      */
        e = mklet(b, te_void,         /* mkinvisible? */
                commacons(mkbinary(s_init, (Expr *)b, e),
                          mkcond((Expr *)b, dl, mkintconst(te_void, 0, 0))));
    }
    else
        /* Don't have to guard ::operator delete calls                  */
        e = mkfnap((Expr*)delgeneric, mkExprList1((Expr*)e));
    return e;
  }
}

Expr *mkdtor_v_list(SynBindList *bl)
{   Expr *edtor = 0;
    for (; bl != NULL; bl = bl->bindlistcdr)
    {   Binder *b = bl->bindlistcar;
        if (!b) syserr("Bad syn scope member");
        if (bindstg_(b) & (bitofstg_(s_auto)|bitofstg_(s_register)))
            /* what about b_globregvar? */
            edtor = commacons(edtor, mkdtor_v((Expr *)b));
    }
    return edtor;
}

/* calls __ex_pop(), to pop the top exception from the exception stack */
Cmd *mkexpop(FileLine fl)
{   Expr* e = mkfnap((Expr *)cppsim.x__ex_pop, 0);
    /*e = mk_expr1(s_throw, te_void, e);*/
    return mk_cmd_e (s_semicolon, fl, e);
}

/* calls __ex_top(), to return the top entry on the exception stack */
Cmd *mkextop(FileLine fl)
{   Expr* e = mkfnap((Expr *)cppsim.x__ex_top, 0);
    /*e = mk_expr1(s_throw, te_charptr, e);*/
    return mk_cmd_e (s_semicolon, fl, e);
}

/* calls __ex_push(), to create space for a new exception on the excep. stack*/
Expr *mkexpush(FileLine fl, Expr* typeid, Expr* size)
{   Expr* e =  (mkfnap((Expr *)cppsim.x__ex_push, mkExprList2(typeid, size)));
        fl=fl; /*don't need this, huh?*/

    /*need to cast this to void.*/
    e = mkcast(s_cast, e, te_void);
    return e; /* mk_cmd_e (s_semicolon, fl, e);*/
}

/* calls __ex_push, unless e==NULL;  always calls __throw()  */
Cmd *mkthrow(FileLine fl, Expr *e)
{
  Expr* exprtree;
    if (!(e && h0_(e) != s_error))
      {
        exprtree = mkfnap((Expr *)cppsim.x__throw, 0);
      }
    else
    {
      Expr *e2 = coerceunary_2(e, COERCE_COMMA);
      TypeExpr *t = typeofexpr(e2);
      TypeExpr *tstar = ptrtotype_(t);
      /*TypeExpr *ct = mkqualifiedtype(t, bitoftype_(s_const));*/
      /*TypeExpr *reft = mk_typeexpr1(t_ref, ct, 0);*/
      String *s = exception_name(t);
      /* We should use a 'placed' allocation instead of a mkcast auto temp.  */
      /* We should also pass multiple catch-names, e.g. int* => int*,void* to*/
      /* cope with the rules on [ES,p359].  Note that COMMON data areas      */
      /* holding strings and linker unique remove much strcmp...             */

      /*Expr *oldarg2 = mkunary(s_addrof, mkcast(s_throw, e2, reft));*/
      Expr *arg1 = (Expr *)s;

      int sizeofexception = 8; /*ignore base types for now.*/
      Expr* arg2 = mkintconst (te_int, sizeofexception, 0);

      Binder *gen = gentempbinder(tstar);
      Expr* temp_tstar =
        cpp_mkbinaryorop(s_init, (Expr *)gen,
                         mkcast(s_cast,
                                mkfnap((Expr *)cppsim.x__ex_push,/*te_charptr*/
                                       mkExprList2
                                       (mkcast(s_cast, arg1, te_int), arg2)),
                                tstar));

      Expr* temp_t = mkunary(s_content, (Expr*) gen);
      Expr* assign = cpp_mkbinaryorop(s_assign, temp_t, mkcast(s_cast, e2, t));

      Expr* bind_temp =
        mk_exprlet(s_let, tstar, mkSynBindList(0, gen),
                   cpp_mkbinaryorop(s_comma, temp_tstar, assign));

      Expr *throwcall = mkfnap((Expr *)cppsim.x__throw, 0);
      exprtree = cpp_mkbinaryorop(s_comma, bind_temp, throwcall);
      exprtree = optimise0 (exprtree);
    }
    exprtree = mk_expr1(s_throw, te_void, exprtree);
    return mk_cmd_e (s_semicolon, fl, exprtree);
}

/* /* #ifdef CPLUSPLUS -- to be merged with ensurelvalue...             */
/* this works for refs before and after coerceunary to pointers.        */
TypeExpr *lvalue_type(Expr *x)   /* isaddressablelvalue??        */
{   TypeExpr *tx, *t;
    if (h0_(x) == s_error) return 0;
    tx = typeofexpr(x);
    t = princtype(tx);
    if (isbitfield_type(t)) return 0;
    if (isclasstype_(t)) return t;      /* N.B. hack -- see caller.     */
    if (h0_(t) == t_ref) return typearg_(t);

    for (;;) switch (h0_(x))
    {   case s_binder:
        {   Binder *b = exb_(x);
            if (isenumconst_(b)) return 0;     /* can't happen */
            return tx;
        }
/* constructors are an odd case: given   class C { C(int); } we want    */
/* C(3) not to be an l-value (i.e. &C(3) illegal -- check), but we      */
/* need it to make a reference without a further temporary so that      */
/* C x = C(3) works by first using C(int) then copy ctor C(const C&).   */
/* @@@ argument now subsumed by all class fn results should be lvalues  */
/* from the point of view of ref-taking (at least in copyctors!).       */
        case s_ctor:
/* strings are probably OK: e.g. char (&v)[4] = "abc";                  */
        case_s_any_string
        case s_subscript:
        case s_arrow:
        case s_content:   return tx;
        case s_dot:       x = arg1_(x); break;
        case s_invisible: x = orig_(x); break;
        default:          return 0;
    }
}

static Expr *mknewarray(TypeExpr* t, Expr* nelts, ExprList *placement, Binder *newgeneric)
{   int32 stride = sizeoftype(t);
    Expr *nw;
    Expr *eltsize = mkintconst(te_size_t, stride, 0);
    Binder *ctorb = findbinding(ctorsym, typespectagbind_(t),
                                INCLASSONLY);
    /* @@@ Bjarne says we have to allow things like: */
    /*   struct T { T(int=99); }; */
    /*   void f() { T a[3]; T* p = new T[5]; } */
    /* We don't yet */
    Expr* ctorfn = 0;
    if (ctorb != NULL)
    {   ctorfn = ovld_picknullary(ctorb);
        if (ctorfn != NULL)
            ctorfn = mkcast(s_cast, ctorfn,
                     ptrtotype_(te_fntype(te_void, te_voidptr, 0, 0, 0, 0)));
        else
        {   cc_err(syn_err_no_nullary_ctor, ctorb);
            return errornode;
        }
    }
    else
        ctorfn = lit_zero;
/* @@@ need to handle T::operator new[] and ::operator new[] here */
    if (placement == 0 &&
        (tagbindbits_(typespectagbind_(princtype(t))) & TB_HASDTOR))
        nw = mkfnap(cppsim.xnewvec,
                    mkExprList4(lit_zero, /* /* useless arg */
                                nelts, eltsize, ctorfn));
    else
    {   if (ctorb != 0)
        {   Binder *telts = gentempbinder(typeofexpr(nelts));
            Binder *nwp = gentempbinder(te_voidptr);
            nw = mkletmany(te_voidptr, /* mkinvisible? */
                  mkcommalist(
                    mkbinary(s_init, (Expr *)telts, nelts),
                    mkbinary(s_init, (Expr *)nwp,
                       mkfnap((Expr*)newgeneric,
                              mkExprList(placement, mkbinary(s_times, (Expr*)telts, eltsize)))),
                    mkcond((Expr *)nwp,
                           array_of_class_map_expr((Expr*)nwp, (Expr*)telts, stride, ctorfn),
                           mkintconst(te_void, 0, 0)),
                   (Expr *)nwp,
                    0),
                  nwp, telts, 0);
        }
        else
            nw = mkfnap((Expr*)newgeneric,
                        mkExprList(placement, mkbinary(s_times, nelts, eltsize)));
    }

    return nw;
}


Expr *mknew(TypeExpr *newt, TypeExpr *t, Binder *newgeneric, Expr* nelts,
            ExprList* placement, ExprList* init, bool forceglobal)
{   Expr *nw = 0;
/* Note that 'new' prefers class to global scope whereas, mkopap()      */
/* may choose from either.                                              */
    if (t == 0)             /* non-class, possibly array                */
    {   nw = mkfnap((Expr*)newgeneric, mkExprList(placement, nelts));
        nw = mkcast(s_cast, nw,
               ptrtotype_((h0_(newt) == t_subscript) ? typearg_(newt) : newt));
        if (init && h0_(nw) != s_error)
            nw = mkctor_p(nw, init);
    }
    else if (nelts == 0)    /* single class allocation                  */
    {   if (placement != 0 || forceglobal)
        {   Expr *eltsize = mkintconst(te_size_t, sizeoftype(t), 0);
            nw = mkfnap((Expr*)newgeneric,
                        mkExprList(placement, eltsize));
            nw = mkctor_p(mkcast(s_cast, nw, ptrtotype_(newt)), init);
        }
        else
        {   /* do allocation in ctor */
            nw = mkctor_v_1(mk_expr1(s_content, t, lit_zero), init, NO);
            if (nw == 0)
            {   /* no constructor & none needed */
                nw = mkfnap((Expr*)newgeneric,
                            mkExprList1(mkintconst(te_size_t, sizeoftype(t), 0)));
                nw = mkctor_p(mkcast(s_cast, nw, ptrtotype_(newt)), init);
            }
            else
            {   /* check access and overloading of operator new().      */
                /* Using '(size_t)0' instead of actual size avoids      */
                /* spuriously needing size (for opaque type).           */
                ExprList *sizearg = mkExprList1(mkintconst(te_size_t, 0, 0));
                (void)ovld_resolve(newgeneric,
                                   typeovldlist_(princtype(bindtype_(newgeneric))),
                                   sizearg, sizearg, NO);
            }
        }
    }
    else /* array of class */
        nw = mkcast(s_cast,
                    mknewarray(t, nelts, placement, newgeneric),
                    ptrtotype_(typearg_(newt)));
    return (h0_(nw) == s_error) ? errornode : nw;
}


Expr *mkdelete(Expr *e, TypeExpr *t, bool isarray, Binder *delgeneric, bool forceglobal)
{
/* Note that 'delete' prefers class to global scope whereas, mkopap()   */
/* may choose from either.                                              */
    if (t != 0 && isarray) /* delete [] ptr-to-class;                   */
    {   Expr *eltsize = mkintconst(te_size_t, sizeoftype(t), 0);
        Binder *dtorb = findbinding(dtorsym, typespectagbind_(t),
                                    INCLASSONLY);
/* @@@ need to handle T::operator delete[] and ::operator delete[] here */
        if (dtorb != 0)
        {   Binder *b = gentempbinder(typeofexpr(e));
            /* there only one dtor but this checks access */
            ExprList *zeroarg = mkExprList1(lit_zero);
            ExprList *args = mkExprList(zeroarg, (Expr*)b);
            Binder *dtorspecific = ovld_resolve(dtorb,
                          typeovldlist_(princtype(bindtype_(dtorb))),
                          zeroarg, args, NO);
            Expr *dtorfn =
                mkcast(s_cast, mkaddr((Expr*)realbinder_(dtorspecific)),
                    /* Beware: this may later produce a                 */
                    /* pointer-to-memfn -> pointer-to-fn cast warning.  */
                    ptrtotype_(te_fntype(te_void, te_voidptr, te_int, 0, 0, 0)));
            return /* mkinvisible? */
                mklet(b, te_void,
                  commacons(mkbinary(s_init, (Expr *)b, e),
                            mkfnap(cppsim.xdelvec,
                                   mkExprList3(b, eltsize, dtorfn))));
        }
        else
            return mkfnap((Expr*)delgeneric, mkExprList1(e));
    }
    else
    {   if (t == te_void)
            return mkfnap((Expr*)delgeneric, mkExprList1(e));
        else
            return mkdtor_p(e, delgeneric, forceglobal);
    }
/* Errors: 1. mkdtor_p() catches 'e' non-pointer.  2. __dl(void *)      */
/* ensures that we cannot delete (const T *) pointers.                  */
}

static bool call_dependency_type(TypeExpr *t, ScopeSaver tactuals)
{
#ifdef IMPLEMENTED_PARTIAL_BINDING
    TypeExpr *t2 = NULL;
    t = princtype(t);
    switch (h0_(t)) {
    case s_typespec:
        if (isprimtypein_(t, CLASSBITS) &&
            tagactuals_(typespectagbind_(t)) != NULL)
        {   ScopeSaver ss = tagactuals_(typespectagbind_(t));
            ScopeSaver tt = tactuals;
            if (env_size(ss) != env_size(tt)) return NO;
            for (; ss; ss = bindcdr_(ss))
                for (; tt; tt = bindcdr_(tt))
                    if (bindsym_(tt) == bindsym_(ss) &&
                        equivtype(bindtype_(tt), bindtype_(ss)))
                        return YES;
        }
        else
            t2 = t;
        break;
    case t_coloncolon:
        if (call_dependency_type(bindtype_(typespecbind_(t)), tactuals) ||
            call_dependency_type(typearg_(t), tactuals))
            return YES;
        break;
    case t_unknown:
        t2 = t;
        break;
    case t_content:
    case t_ref:
    case t_subscript:
        return call_dependency_type(typearg_(t), tactuals);
    case t_fnap:
        {   FormTypeList *ft = typefnargs_(t);
            for (; ft; ft = ft->ftcdr)
                if (call_dependency_type(ft->fttype, tactuals))
                    return YES;
            /* DWP Oct95 did not say anything about return type */
            return NO;
        }
    default:
        syserr("call_dependency: unknown type %ld\n", (long)h0_(t));
    }

    if (t2)
        for (; tactuals; tactuals = bindcdr_(tactuals))
        {   if (h0_(bindtype_(tactuals)) != s_typespec) continue;
            if (equivtype(t2, bindtype_(tactuals))) return YES;
        }
    return NO;
#else
    IGNORE(t);
    IGNORE(tactuals);
    return YES;
#endif
}

static bool call_dependency_val(Expr *e, ScopeSaver tactuals)
{
#ifdef IMPLEMENTED_PARTIAL_BINDING
    for (; tactuals; tactuals = bindcdr_(tactuals))
        if (h0_(bindtype_(tactuals)) == s_typespec)
        {   TypeExpr *t = princtype(typeofexpr(e));
            TagBinder *cl = (isclasstype_(t)) ? typespectagbind_(t) : NULL;
            if (cl && class_has_conversion(cl, bindtype_(tactuals), YES))
                return YES;
        }
        else
            if ((h0_(e) == s_binder) &&
                (bindsym_(exb_(e)) == bindsym_(tactuals)))
                return YES;
    return NO;
#else
    IGNORE(e);
    IGNORE(tactuals);
    return YES;
#endif
}

static void fix_typevar_in(TypeExpr *f)
{   SET_BITMAP m;
    Binder *b;
    FormTypeList *ft;
    switch h0_(f) {
case s_typespec:
        m = typespecmap_(f);
        switch (m & -m)    /* LSB - unsigned/long etc. are higher */
        {
    case bitoftype_(s_typedefname):
        /* The following allows fixup_template_arg_type() to be called on
           the same type repeatedly with the desired effect.
           It is an implicit assumption that the local scope is a
           Scope_TemplateArg. Effectively, it binds a typedef whose name
           can be found in scope.
         */
        if ((b = findbinding(bindsym_(typespecbind_(f)), 0, FB_LOCALS|FB_THISSCOPE))
            != NULL)
            typespecbind_(f) = b;
    default:
            return;
        }
default:
        syserr("fix_typevar_in(%ld,%#lx)", (long)h0_(f), (long)typespecmap_(f));
case t_fnap:
        fix_typevar_in(typearg_(f));
        for (ft = typefnargs_(f); ft; ft = ft->ftcdr)
        {   fix_typevar_in(ft->fttype);
            if (!istypevar(ft->fttype))
                ft->fttype = prunetype(ft->fttype);
        }
        return;
case t_coloncolon:
case t_subscript:
case t_content:
case t_ref:
        fix_typevar_in(typearg_(f));
        if (!istypevar(typearg_(f)))
            typearg_(f) = prunetype(typearg_(f));
        return;
    }
}

void fixup_template_arg_type(TypeExpr *f, ScopeSaver actuals)
{   int scope_level = push_var_scope(actuals, Scope_Ord);
    fix_typevar_in(f);
    pop_scope_no_check(scope_level);
}

/* Assume caller is for full explicit instantiation */
ScopeSaver globalize_template_arg_binders(ScopeSaver f, ExprList *a)
{   Binder *tp = NULL, *tq = NULL;
    for (; f; f = bindcdr_(f))
    {   Expr *e = (a && exprcar_(a)) ? exprcar_(a) : bindconst_(f);
        Binder *temp;
        TypeExpr *t = (e && h0_(e) == s_typespec) ? type_(e) : clone_typeexpr(bindtype_(f));

        if (e && e == bindconst_(f) && h0_(e) == s_typespec &&
            istypevar(type_(e)))
        {   t = clone_typeexpr(type_(e));
            fixup_template_arg_type(t, tp);
        }
        temp = global_mk_binder(0, bindsym_(f), bindstg_(f), globalize_typeexpr(t));
#if 0
        /* rationale: template <class T, class U = T> */
        if (istypevar(bindtype_(temp)) &&
            isprimtype_(bindtype_(temp), s_typedefname) && tp)
            fixup_template_arg_type(bindtype_(temp), tp);
#endif

        if (!tp)
            tp = tq = temp;
        else
        {   bindcdr_(tq) = temp;
            tq = temp;
        }
        if (e && h0_(e) != s_typespec)
        {   bindconst_(temp) = (h0_(e) == s_binder) ? e : globalize_expr(e);
            /* Rationale for the following line, considers,
               template <class T, T *p> struct X {};
               And sharing destroyed by clone_typeexpr() above.
             */
            fixup_template_arg_type(bindtype_(temp), tp);
        }
        if (a) a = cdr_(a);
    }
    return tp;
}

/* almost like a globalize_template_arg_binders(), more forgiving. */
ScopeSaver dup_env_actuals(ScopeSaver tformals, ExprList *a)
{   ScopeSaver temp = NULL;
    if (prefer_tmptfn(a)) a = NULL;
    for (; tformals; tformals = bindcdr_(tformals))
    {
        Binder *b = mk_binder(bindsym_(tformals), bindstg_(tformals),  bindtype_(tformals));
        bindcdr_(b) = temp;
        if (a)
        {   if (h0_(exprcar_(a)) == s_typespec)
            {   bindtype_(b) = globalize_typeexpr(type_(exprcar_(a)));
                if (debugging(DEBUG_TEMPLATE))
                    cc_msg("assigned: $b -> $t\n", b, bindtype_(b));
            }
            else
                bindconst_(b) = globalize_expr(exprcar_(a));
            a = cdr_(a);
        }
        else if (bindconst_(tformals))
        {   if (h0_(bindconst_(tformals)) == s_typespec)
                bindtype_(b) = type_(bindconst_(tformals));
            else
                bindconst_(b) = bindconst_(tformals);
        }
        temp = b;
    }
    return dreverse_binder(temp);
}

static TagBindList *typevars_tag_list;
static bool is_in_typevars_tag_list(TagBinder *tb)
{   if (!typevars_tag_list)
        typevars_tag_list = (TagBindList *)mkBindList(NULL, tb);
    else
    {   TagBindList *tbl = typevars_tag_list;
        for (; tbl; tbl = (TagBindList *)tbl->bindlistcdr)
            if ((TagBinder *)tbl->bindlistcar == tb)
                return YES;
        typevars_tag_list = (TagBindList *)mkBindList(typevars_tag_list, tb);
    }
    return NO;
}

static bool contains_typevars_0(TypeExpr *t, bool dependent)
{
    if (istypevar(t))
    {   Binder *b;
        if (h0_(t) == t_unknown) return (dependent) ? NO : YES;

        /* It may not have been bounded! */
        if (!isprimtype_(t, s_typedefname))
            syserr("what sort of unknown type is this?");
        b = findbinding(bindsym_(typespecbind_(t)), 0, ALLSCOPES);
        return (b && istypevar(bindtype_(b)));
    }
    t = princtype(t);
    switch (h0_(t)) {
    case s_typespec:
        {   SET_BITMAP m = typespecmap_(t);
            switch (m & -m) {
            default:
                break;
            case bitoftype_(s_struct):
            case bitoftype_(s_class):
            case bitoftype_(s_union):
                {   TagBinder *tb = typespectagbind_(t);
                    if (tagbindbits_(tb) & TB_TEMPLATE)
                    {   if (dependent)
                        {    ScopeSaver formals = tagformals_(tb);
                             for (; formals != NULL; formals = bindcdr_(formals))
                                 if (is_template_arg_binder((Expr *)formals))
                                     return YES;
                        }
                        else if (!is_in_typevars_tag_list(tb))
                        {   ClassMember *m = tagbindmems_(tb);
                            for (; m; m = memcdr_(m))
                                if (contains_typevars_0(memtype_(m), NO))
                                    return YES;
                        }
                    }
                    else if (tagactuals_(tb) != NULL)
                    {   ScopeSaver actuals = tagactuals_(tb);
                        for (; actuals; actuals = bindcdr_(actuals))
                            if (contains_typevars_0(bindtype_(actuals), dependent))
                                return YES;
                    }
                }
            }
        }
        break;
    case t_ref:
    case t_content:
        return contains_typevars_0(typearg_(t), dependent);
    case t_subscript:
    case t_coloncolon:
        if (contains_typevars_0(typearg_(t), dependent))
            return YES;
        if (h0_(t) == t_coloncolon)
            return contains_typevars_0(tagbindtype_(typespectagbind_(t)), dependent);
        break;
    case t_fnap:
        if (contains_typevars_0(typearg_(t), dependent))
            return YES;
        {   FormTypeList *ft = typefnargs_(t);
            for (; ft; ft = ft->ftcdr)
                if (contains_typevars_0(ft->fttype, dependent))
                    return YES;
        }
        break;
    }
    return NO;
}

#define TYPE_DEDUCE_MASK (QUALIFIER_MASK|bitoftype_(s_unsigned)|bitoftype_(s_signed))
static void check_type_equivalence(TypeExpr *t1, TypeExpr *t2, bool silent, bool *failed)
{
    *failed = !equivtype_4(t1, t2, TYPE_DEDUCE_MASK, TYPE_DEDUCE_MASK, NO);
    if (*failed && !silent)
        cc_err(sem_err_typededuce_disagree, t1, t2);
}

static void fix_target_type_1(Binder *tpltarg, TypeExpr *target, bool silent,
                              bool *failed, bool convallowed, bool preserve)
{
    if (!istypevar(bindtype_(tpltarg)))
    {   TypeExpr *temp = princtype(bindtype_(tpltarg));
        if (convallowed)
        {   Binder *b = gentempbinder(target);
            if (isclasstype_(temp))
            {   if (!equivtype_4(temp, target, TYPE_DEDUCE_MASK, TYPE_DEDUCE_MASK, NO))
                    *failed = (class_has_ctor_1(typespectagbind_(temp), target, (Expr *)b,
                                                NO, YES) == NULL);
            } else
            {   if (!(attributes_(tpltarg) & DEDUCED) &&
                    isarithtype_(temp) && isarithtype_(target))
                    ;
                else
                    check_type_equivalence(temp, modify_formaltype(target), silent, failed);
            }
        } else
            check_type_equivalence(temp, target, silent, failed);
    }
    else
    {   if (attributes_(tpltarg) & NON_CONFORMING)
        {   /* strict equality here. */
            if (bindtype_(tpltarg) != target)
            {   *failed = YES;
                if (!silent)
                    cc_err(sem_err_typededuce_disagree, bindtype_(tpltarg), target);
            }
        }
        else
        {   attributes_(tpltarg) |= (istypevar(target)) ? NON_CONFORMING : DEDUCED;
            if (!preserve) {
                target = clone_typeexpr(princtype(target));
                switch (h0_(target)) {
                case s_typespec:
                    typespecmap_(target) &= ~CVBITS;
                    break;
                case t_fnap:
                case t_ref:
                case t_content:
                    typeptrmap_(target) &= ~CVBITS;
                    break;
                }
            }
            bindtype_(tpltarg) = modify_formaltype(target);
            if (debugging(DEBUG_TEMPLATE))
                cc_msg("deduced: $b -> $t\n", tpltarg, target);
        }
    }
}

static void fix_target_type(TypeExpr *t, TypeExpr *target, bool silent, bool *failed,
                            bool convallowed, bool preserve)
{   Binder *b = NULL;
    if (!isprimtype_(t, s_typedefname) || !istypevar(t))
        syserr("expecting typevar");
    if (bindparent_(typespecbind_(t)) != NULL)
    {   Binder *bb = typespecbind_(t);
        TagBinder *parent = bindparent_(bb), *curScope = NULL;
        TagBindList *scopes = NULL;
        for (; parent; parent = tagbindparent_(parent))
            scopes = (TagBindList *)binder_cons2(scopes, parent);
        parent = (TagBinder *)scopes->bindlistcar;
        scopes = (TagBindList *)scopes->bindlistcdr;
        b = findbinding(bindsym_(parent), 0, FB_LOCALS|FB_THISSCOPE);
        if (b && isclasstype_(princtype(bindtype_(b))))
        {   curScope = typespectagbind_(princtype(bindtype_(b)));
            for (; curScope && scopes; scopes = (TagBindList *)scopes->bindlistcdr)
                curScope = findtagbinding(bindsym_((TagBinder *)scopes->bindlistcar),
                                          curScope, INCLASSONLY);
        }
        if (curScope &&
            (bb = findbinding(bindsym_(bb), curScope, FB_LOCALS|FB_THISSCOPE)) != NULL)
            typespecbind_(t) = bb;
        else
        {   if (!silent) cc_err(sem_err_typename_not_found, typespecbind_(t));
            *failed = YES;
        }
    }
    else
    {   b = findbinding(bindsym_(typespecbind_(t)), 0, FB_LOCALS|FB_THISSCOPE);
        if (!b) syserr("Odd template type arg $b", typespecbind_(t));
        fix_target_type_1(b, target, silent, failed, convallowed, preserve);
        typespecbind_(t) = b;
    }
}

static void fixup_type_1(TypeExpr *t)
{
    if (!isprimtype_(t, s_typedefname)) syserr("typevar expected, $t given", t);
    {   Binder *b = findbinding(bindsym_(typespecbind_(t)), 0, FB_LOCALS|FB_THISSCOPE);
        if (!b)
            syserr("Odd template type arg $r", bindsym_(typespecbind_(t)));
        typespecbind_(t) = b;
    }
}

static TypeExpr *fixup_type(TypeExpr *t)
{
    switch (h0_(t)) {
    case s_typespec:
        {   SET_BITMAP m = typespecmap_(princtype(t));
            TagBinder *tb;
            if (istypevar(t)) m = 0; /* T may have been qualified
                                        e.g. s_struct, ignored */
            switch (m & -m) {
            default:
                if (istypevar(t)) fixup_type_1(t);
                break;
            case bitoftype_(s_struct):
            case bitoftype_(s_class):
            case bitoftype_(s_union):
                tb = typespectagbind_(princtype(t));
                if (tagbindbits_(tb) & TB_TEMPLATE || !(tagbindbits_(tb) & TB_DEFD))
                {   tb = syn_implicit_instantiate_2(tb);
                    t = tagbindtype_(tb);
                }
            }
            break;
        }
    /* Only t_content now? */
    case t_subscript:
        typearg_(t) = fixup_type(typearg_(t));
        break;
    case t_coloncolon:
        typearg_(t) = fixup_type(typearg_(t));
        typespecbind_(t) = typespecbind_(fixup_type(tagbindtype_(typespectagbind_(t))));
        break;
    case t_fnap:
        {   FormTypeList *ft = typefnargs_(t);
            typearg_(t) = fixup_type(typearg_(t));
            for (; ft; ft = ft->ftcdr)
                ft->fttype = fixup_type(ft->fttype);
            break;
        }
    default:
        syserr("type deduction failed: un-recognized type $t", t);

    }
    return t;
}

/* upto 32 params */
#define TYPEMEMOSIZE 32

static struct te_memo { TypeExpr *orig, *to; }
    local_prunetype_memo[TYPEMEMOSIZE];

#define EQtype_(t1,t2)   ((t1)->h0==(t2)->h0 && typearg_(t1)==typearg_(t2) \
                          && typespecbind_(t1)==typespecbind_(t2))

static TypeExpr *prunetype_memo(TypeExpr *t)
{   struct te_memo *p;
    for (p = local_prunetype_memo; p->orig != NULL; p++)
        if (EQtype_(t, p->orig)) break;
    if (p->orig == NULL)
    {   p->orig = t;
        p->to = prunetype(t);
    }
    return p->to;
}

/* This is a 3-result function. A result is that of a binding env that's
   free from typevars and all const binders are initialized in non-template
   scope. It also returns the deduced fntype as well as an indication if
   type deduction has failed.
*/
static TypeExpr *type_deduction_0(TypeExpr *fntype, ExprList *args, ExprList *actuals,
              ScopeSaver *tformals, bool silent, bool *failed, bool strict, bool preserve)
{   TypeExpr *temp = clone_typeexpr(fntype);
    FormTypeList *ft = typefnargs_(temp);
    int varlevel, nargs = length((List *)args);

    if (nargs > length((List *)ft) || minargs_(temp) > nargs)
    {   *failed = YES;
        return temp;
    }

    *tformals = dup_env_actuals(*tformals, actuals);
    varlevel = push_var_scope(*tformals, Scope_TemplateArgs);
    memset(local_prunetype_memo, 0, sizeof local_prunetype_memo);
    for (; ft && args && !*failed; ft = ft->ftcdr, args = cdr_(args))
    {   TypeExpr *t = ft->fttype, *t2;
        SET_BITMAP qt2;
        Expr *e = exprcar_(args);

        /* First check that non-type arg has the same value as the default.
           Applicable to reduction purpose really.
         */
        if (ft->ftdefault != NULL && h0_(ft->ftdefault) != s_binder &&
            h0_(ft->ftdefault) != s_typespec &&
            h0_(e) == s_binder && isgensym(bindsym_(exb_(e))) &&
            bindconst_(exb_(e)) != NULL && ft->ftdefault != bindconst_(exb_(e)))
        {   *failed = YES;
            break;
        }

        t2 = typeofexpr(e);
        qt2 = qualifiersoftype(t2);
        if (h0_(t) == t_content || h0_(t) == t_ref)
        {   TypeExpr *tmp = princtype(t2);
            if (h0_(t) == t_content &&
                h0_(tmp = princtype(typeofexpr(e = coerceunary_2(e, COERCE_ARG)))) == h0_(t))
            {   t2 = typearg_(tmp);
                preserve = YES;
            }
            else if (h0_(t) == t_ref && (h0_(tmp) == t_ref || lvalue_type(e) ||
                                         qualifiersoftype(typearg_(t)) & bitoftype_(s_const)))
            {   if (h0_(tmp) == t_ref) t2 = typearg_(tmp);
                preserve = YES;
            }
            else if (!istypevar(tmp))
            {   *failed = YES;
                if (!silent)
                    cc_err(sem_err_typededuce_disagree, t, t2);
                continue;
            }
            t = typearg_(t);
        }
        t2 = prunetype_memo(t2);

        /* No princtype() on t yet because the name of an unknown type is needed. */
        switch (h0_(t)) {
        case s_typespec:
            {   SET_BITMAP m = typespecmap_(princtype(t));
                TagBinder *tb, *tb2;
                if (istypevar(t)) m = 0;        /* T may have been qualified by a
                                                   eg. s_struct, ignored.
                                                 */
                switch (m & -m) {
                default:
                    if (istypevar(t))
                    {   if (is_template_arg_binder((Expr *)typespecbind_(t)))
                            fix_target_type(t, t2, silent, failed, YES, preserve);
                        /* /* do we need to do anything about typenames? */
                    }
                    else
                        if (strict) check_type_equivalence(t, t2, silent, failed);
                    break;
                case bitoftype_(s_struct):
                case bitoftype_(s_class):
                case bitoftype_(s_union):
                    t = princtype(t);
                    tb = typespectagbind_(t);
                    tb2 = (isclasstype_(t2)) ? typespectagbind_(t2) : NULL;
                    /* There maybe a derivation relationship. */
                    if (tb2 != NULL)
                    {   ClassMember *m = tagbindmems_(tb2);
                        for (; m != NULL; m = memcdr_(m))
                        {   TagBinder *tmp = NULL;
                            if (!(attributes_(m) & (CB_BASE|CB_VBASE))) continue;
                            tmp = typespectagbind_(princtype(bindtype_(m)));
                            if (tagprimary_(tmp) == tb
                                || (tagprimary_(tmp) != NULL &&
                                    tagprimary_(tmp) == tagprimary_(tb)))
                            {   tb2 = tmp;
                                t2 = tagbindtype_(tb2);
                                break;
                            }
                        }
                    }
                    if (tagformals_(tb) != NULL &&
                        tb2 != NULL && ((tagprimary_(tb2) != NULL &&
                                        tagprimary_(tb) == tagprimary_(tb2)) ||
                                        tagprimary_(tb2) == tb))
                    {   ScopeSaver actuals, formals;
                        Symstr *sv;
                        actuals = tagactuals_(tb2);
                        formals = (tagprimary_(tb2)==tb) ? tagformals_(tb) : tagactuals_(tb);
                        if (env_size(actuals) != env_size(formals))
                            syserr("Odd specializations %c & %c", tb, tb2);
                        if (qt2 > qualifiersoftype(t))
                            *failed = YES;
                        else {
                            for (; actuals && formals;
                                 actuals = bindcdr_(actuals), formals = bindcdr_(formals))
                            {   Binder *b = NULL;
                                bool istype = NO;
                                if ((istype = istypevar(bindtype_(formals))) == YES)
                                    sv = (h0_(bindtype_(formals)) == t_unknown) ?
                                        bindsym_(formals) :
                                    bindsym_(typespecbind_(bindtype_(formals)));
                                else if (bindconst_(formals) != NULL
                                         && h0_(bindconst_(formals)) == s_binder)
                                    sv = bindsym_(exb_(bindconst_(formals)));
                                else
                                    sv = bindsym_(formals);
                                b = findbinding(sv, 0, FB_LOCALS|FB_THISSCOPE);
                                if (!b)
                                    syserr("Odd template type/no-type arg $r", sv);
                                if (istype)
                                    fix_target_type_1(b, bindtype_(actuals), silent,
                                                      failed, NO, preserve);
                                else
                                    bindconst_(b) = globalize_expr(bindconst_(actuals));
                            }
                            if (h0_(ft->fttype) == t_ref || h0_(ft->fttype) == t_content)
                            {   TypeExpr *clone = clone_typeexpr(ft->fttype);
                                typearg_(clone) =
                                    mkqualifiedtype(t2, qualifiersoftype(typearg_(ft->fttype)));
                                ft->fttype = clone;
                            }
                            else
                                ft->fttype = t2;
                        }
                    }
                    else
                    {
                        if (tb != NULL && tb2 == NULL && !istypevar(t2) &&
                            !contains_typevars(tagbindtype_(tb)) &&
                            class_has_ctor_1(tb, t2, e, NO, YES) != NULL)
                            ;
                        else
                            if (strict) check_type_equivalence(t, t2, silent, failed);
                    }
                }
            }
            break;
        case t_subscript:
            if (h0_(t2) == t_subscript)
            {   if (istypevar(typearg_(t)))
                    fix_target_type(typearg_(t), typearg_(t2), silent, failed, NO, preserve);
                if (h0_(typesubsize_(t)) == s_binder)
                {   Binder *b = exb_(typesubsize_(t));
                    b = findbinding(bindsym_(b), 0, FB_LOCALS|FB_THISSCOPE);
                    if (!b) syserr("Odd template non-type arg $r", bindsym_(b));
                    if (bindconst_(b) != NULL &&
                        evaluate(bindconst_(b)) != evaluate(typesubsize_(t2)))
                    {   if (!silent) cc_warn(sem_warn_typededuce_arraysize);
                        /*
                            *failed = YES;
                        */
                    }
                    typesubsize_(t) = bindconst_(b) = globalize_expr(typesubsize_(t2));
                }
            }
            else
                if (strict) check_type_equivalence(t, t2, silent, failed);
            break;
        case t_coloncolon:
            if (h0_(t2) == t_coloncolon)
            {   TypeExpr *dest = NULL, *target = NULL;
                bool needsupdate = NO;

                if (istypevar(tagbindtype_(typespectagbind_(t))) &&
                    equivtype(typearg_(t), typearg_(t2)))
                {   dest = tagbindtype_(typespectagbind_(t));
                    target = tagbindtype_(typespectagbind_(t2));
                    needsupdate = YES;
                }
                else if (istypevar(typearg_(t)) &&
                         equivtype(tagbindtype_(typespectagbind_(t)),
                                   tagbindtype_(typespectagbind_(t2))))
                {   dest = typearg_(t);
                    target = typearg_(t2);
                }


                if (dest != NULL)
                {   Binder *b;

                    if (!isprimtype_(dest, s_typedefname))
                        syserr("bare t_unknown");
                    b = findbinding(bindsym_(typespecbind_(dest)), 0,
                                    FB_LOCALS|FB_THISSCOPE);
                    if (!b) syserr("Odd template type arg $r",
                                   bindsym_(typespecbind_(dest)) );
                    fix_target_type_1(b, target, silent, failed, NO, preserve);
                    if (!*failed && !silent && needsupdate)
                        typespectagbind_(t) = typespectagbind_(target);
                }

            }
            else
                if (strict) check_type_equivalence(t, t2, silent, failed);
            break;
        case t_fnap:
            if ((h0_(t2) == t_ovld && typeovldlist_(t2) != NULL) ||
                h0_(t2) == t_fnap)
            {   BindList *bl;
                int candidates = 0;
                TypeExpr *best = NULL;
                ScopeSaver best_env = NULL;
                int len = length((List *)typefnargs_(t));
                bl = (h0_(t2) == t_fnap) ?
                    binder_cons2(NULL, (h0_(skip_invisible(e)) == s_addrof) ?
                                 arg1_(e) : e) :
                    typeovldlist_(t2);
                for (; bl; bl = bl->bindlistcdr)
                {   Binder *b = bl->bindlistcar;
                    FormTypeList *ft2;
                    ExprList *args2 = NULL;
                    bool local_failed = NO;

                    ft2 = (h0_(t2) == t_fnap) ? typefnargs_(t2) : typefnargs_(bindtype_(b));
                    if (len != length((List *)ft2)) continue;
                    for (; ft2; ft2 = ft2->ftcdr)
                        args2 = mkExprList(args2, gentempbinder(ft2->fttype));
                    best_env = *tformals;
                    best = type_deduction(t, dreverse(args2), NULL,
                                          &best_env, YES, &local_failed);
                    if (!local_failed)
                    {   if (istypevar(typearg_(best)))
                            fix_target_type(typearg_(best), typearg_(bindtype_(b)),
                                            silent, &local_failed, NO, preserve);
                        else
                            if (strict)
                                check_type_equivalence(typearg_(best), typearg_(bindtype_(b)),
                                                       silent, &local_failed);
                        if (!local_failed) candidates++;
                    }
                }
                if (candidates != 1 || !best)
                {   *failed = YES;
                    if (!silent)
                        cc_err(sem_err_typededuce_ambiguous, candidates);
                    /* recovered by picking up the latest best, if exists */
                    if (!best) best = te_int;
                }
                typearg_(ft->fttype) = best;
                for (; best_env; best_env = bindcdr_(best_env))
                {   Binder *b = findbinding(bindsym_(best_env), 0,
                                            FB_LOCALS|FB_THISSCOPE);
                    if (!b) syserr("Odd template type arg $r", bindsym_(best_env));
                    if (!istypevar(bindtype_(best_env)))
                        fix_target_type_1(b, bindtype_(best_env), silent, failed, NO, preserve);
                }
            }
            else
                if (strict) check_type_equivalence(t, t2, silent, failed);
            break;
        default:
            {   if (!silent) cc_err(sem_err_typededuce_recognize, ft->fttype);
                *failed = YES;
            }
        }
    }

    if (*failed)
    {   pop_scope_no_check(varlevel);
        return temp;
    }

    for (; ft; ft = ft->ftcdr)
        if (istypevar(ft->fttype)) fixup_type(ft->fttype);

    /* Fix up the result type */
    {   TypeExpr *t = typearg_(temp);
        /* Update in-situ, temp was a copy anyway. */
        if (h0_(t) == t_ref || h0_(t) == t_content)
            typearg_(t) = fixup_type(typearg_(t));
        else
            typearg_(temp) = fixup_type(t);
    }

    pop_scope_no_check(varlevel);
    if (!has_template_arg_scope())
    {   Binder *b = *tformals;
        for (; b && !*failed; b = bindcdr_(b))
            if (bindstg_(b) & bitofstg_(s_typedef))
            {   if (istypevar(bindtype_(b)))
                {   bindtype_(b) = te_void;
                    if (!silent) cc_err(sem_err_typededuce_type, bindsym_(b));
                    *failed = YES;
                }
            }
            else if (bindconst_(b) == NULL)
            {   if (!silent) cc_err(sem_err_typededuce_const, bindsym_(b));
                *failed = YES;
            }
    }
    return temp;
}

TypeExpr *type_deduction(TypeExpr *fntype, ExprList *args, ExprList *actuals,
                         ScopeSaver *tformals, bool silent, bool *failed)
{
    return type_deduction_0(fntype, args, actuals, tformals, silent, failed, NO, NO);
}

static BindList *temp_candidates(BindList *temps, ExprList *l, ExprList *tactuals, bool silent)
{   BindList *res = NULL;
    for (; temps; temps = temps->bindlistcdr)
    {   bool failed = NO;
        Binder *b = temps->bindlistcar;
        ScopeSaver env = bindenv_(b);
        (void) type_deduction_0(bindtype_(b), l, tactuals, &env, silent, &failed,
                                YES, NO);
        if (!failed)
            res = binder_cons2(res, b);
    }
    return res;
}

static bool po_equivtype_0(TypeExpr *t1, TypeExpr *t2)
{
    if (istypevar(t1) && istypevar(t2))
        return qualifiersoftype(t1) == qualifiersoftype(t2);
    else
        switch (h0_(t1)) {
        case t_subscript:
        case t_ref:
        case t_content:
            return qualifiersoftype(t1) == qualifiersoftype(t2) &&
                po_equivtype_0(typearg_(t1), typearg_(t2));
        default:
            return (equivtype(t1, t2) == 2);
        }
}

static bool po_equivtype(TypeExpr *t1, TypeExpr *t2)
{   FormTypeList *ft1, *ft2;
    bool res = YES;
    if (h0_(t1) != s_fnap || h0_(t2) != s_fnap)
        syserr("po_equivtype: fntype expected");
    ft1 = typefnargs_(t1), ft2 = typefnargs_(t2);
    for (; ft1 && ft2 && res; ft1 = ft1->ftcdr, ft2 = ft2->ftcdr)
    {   t1 = ft1->fttype, t2 = ft2->fttype;
        switch (equivtype(t1, t2)) {
        case 2:
            res = YES; break;
        case 1:
            res = po_equivtype_0(t1, t2); break;
        default:
            res = NO;
        }
    }
    return (ft1 == ft2) && res;
}


BindList *temp_reduce(BindList *temps, ExprList *l, ExprList *tactuals, Binder *bgeneric)
{   Binder *cur_best_temp;
    int varlevel;
    bool silent;
    if (temps == NULL && bgeneric != NULL)
    {   int len = length((List *) (tactuals = bindactuals_(bgeneric)));
        BindList *tmpts = bindftlist_(bgeneric), *tmpts2 = NULL;
        /* filtered through the candidates */
        for (; tmpts != NULL; tmpts = tmpts->bindlistcdr)
            if (env_size(bindformals_(tmpts->bindlistcar)) >= len)
                tmpts2 = (BindList *)
                    binder_cons2(tmpts2, tmpts->bindlistcar);
        temps = tmpts2;
    }
    silent = (length((List *)temps) > 1 || bgeneric == NULL ||
              typeovldlist_(bindtype_(bgeneric)) ||
              is_operator_name(bindsym_(bgeneric)));

    temps = temp_candidates(temps, l, tactuals, silent);
    if (temps == NULL) return NULL;
    if (length((List *)temps) == 1)
    {   if (debugging(DEBUG_TEMPLATE))
            cc_msg("best template $r\n", bindsym_(temps->bindlistcar));
        return temps;
    }
    cur_best_temp = temps->bindlistcar;
    temps = temps->bindlistcdr;
    /* suppress type deduction moaning about t_unknown. */
    varlevel = push_var_scope(NULL, Scope_TemplateArgs);
    for (; temps; temps = temps->bindlistcdr)
    {   FormTypeList *ft;
        ExprList *args = NULL;
        bool local_failed = NO;
        TypeExpr *deduced;
        Binder *b = temps->bindlistcar;
        ScopeSaver env = bindenv_(b);
        bool best, cur;

        for (ft = typefnargs_(bindtype_(cur_best_temp)); ft; ft = ft->ftcdr)
        {   Binder *tmp = gentempbinder(ft->fttype);
            bindconst_(tmp) = ft->ftdefault;
            args = mkExprList(args, tmp);
        }
        deduced = type_deduction_0(bindtype_(b), dreverse(args), tactuals,
                                 &env, YES, &local_failed, NO, YES);
        best = (!local_failed && po_equivtype(bindtype_(cur_best_temp),
                                (fixup_template_arg_type(deduced, env), deduced)));

        for (args = NULL, ft = typefnargs_(bindtype_(b)); ft; ft = ft->ftcdr)
        {   Binder *tmp = gentempbinder(ft->fttype);
            bindconst_(tmp) = ft->ftdefault;
            args = mkExprList(args, tmp);
        }
        env = bindenv_(cur_best_temp);
        local_failed = NO;
        deduced = type_deduction_0(bindtype_(cur_best_temp), dreverse(args), tactuals,
                                 &env, YES, &local_failed, NO, YES);
        cur = (!local_failed && po_equivtype(bindtype_(b),
                                (fixup_template_arg_type(deduced, env), deduced)));
        if (best && !cur)
            /* best still the best */;
        else if (!best && cur)
        {   if (debugging(DEBUG_TEMPLATE))
                cc_msg("dropped template $r\n", bindsym_(cur_best_temp));
            cur_best_temp = b;
        }
        else
        {   ExprList *args2 = args;
            BindList *bl = binder_cons2(binder_cons2(NULL, cur_best_temp), b);
            Binder *b1;

            if (bindparent_(b) != NULL)
            {   TypeExpr *pt = tagbindtype_(bindparent_(b));
                Binder *tempb = gentempbinder(pt);
                Expr *thisptr = mk_expr1(s_addrof, ptrtotype_(pt), (Expr *)tempb);
                bindstg_(tempb) |= b_addrof|u_referenced;
                args2 = mkExprList(args2, thisptr);
            }
            if (bgeneric != NULL &&
                (b1 = ovld_resolve(bgeneric, bl, args, args2, YES)) != NULL)
                if (h0_(b1) != s_error)
                {   cur_best_temp = b1;
                    continue;
                }

            if (tag_global_(bindsym_(cur_best_temp)) &&
                tag_global_(bindsym_(b)) &&
                tagprimary_(tag_global_(bindsym_(b))) != NULL &&
                        /* make sure its comparing non-null */
                tagprimary_(tag_global_(bindsym_(b))) ==
                tagprimary_(tag_global_(bindsym_(cur_best_temp))))
                /* if we can't separate them and they're from the same parent, it's
                   not an error. They are from the same generic type.
                   Conspiring with class_template_reduce() to pick the primary.
                   @@@ watch out for namespace scope though.
                 */
                ;
            else
            {   if (debugging(DEBUG_TEMPLATE))
                    cc_msg("templates $r & $r are possible candidates\n",
                           bindsym_(cur_best_temp), bindsym_(b));
                cc_err(sem_err_template_ambiguous);
                cur_best_temp = NULL;
            }
            break;
        }
    }
    if (debugging(DEBUG_TEMPLATE) && cur_best_temp)
        cc_msg("best template $r\n", bindsym_(cur_best_temp));
    pop_scope_no_check(varlevel);
    return (cur_best_temp != NULL) ? mkBindList(NULL, cur_best_temp) : NULL;
}

TagBinder *class_template_reduce(TagBinder *primary, TagBindList *instances,
                                 ScopeSaver tactuals)
{   int nargs;
    BindList *temps = NULL;
    TagBindList *ins;
    ExprList *args;
    ScopeSaver actuals;

    if (primary == NULL) syserr("no primary to reduce");
    if (instances == NULL) return primary;
    for (args = NULL, actuals = tactuals; actuals; actuals = bindcdr_(actuals))
    {   Binder *tmp = gentempbinder(bindtype_(actuals));
        bindconst_(tmp) = bindconst_(actuals);
        args = mkExprList(args, tmp);
    }
    args = (ExprList *)dreverse(args);
    nargs = env_size(tagformals_(primary));
    for (ins = instances; ins; ins = (TagBindList *)ins->bindlistcdr)
    {   Binder *b;
        TagBinder *tb = (TagBinder *)ins->bindlistcar;
        TypeExprFnAux s;
        TypeExpr *fntype;
        FormTypeList *fttype = NULL;
        ScopeSaver env = tagactuals_(tb);

        if (!(tagbindbits_(tb) & TB_DEFD) || tagbindsym_(primary) == tagbindsym_(tb))
            continue;
        if (env_size(env) != nargs) syserr("wrong no. of actuals to $c", tb);
        for (; env; env = bindcdr_(env))
            fttype = mkFormTypeList(fttype, NULL, bindtype_(env), bindconst_(env));
        fntype = mkTypeExprfn(t_fnap, te_void, 0, (FormTypeList *)dreverse((List *)fttype),
                          packTypeExprFnAux(s, nargs, nargs, 0, 0, 0));
        b = mk_binder(tagbindsym_(tb), 0, fntype);
        bindenv_(b) = tagformals_(tb);
        temps = binder_cons2(temps, b);
    }
    temps = temp_reduce(temps, args, NULL, NULL);
    if (temps != NULL)
    {   Binder *res = temps->bindlistcar;
        TagBinder *best = NULL;
        for (; instances; instances = (TagBindList *)instances->bindlistcdr)
            if (bindsym_(instances->bindlistcar) == bindsym_(res)) break;
        if (instances == NULL) syserr("unexpected null instance");
        best = (TagBinder *)instances->bindlistcar;
        /* Make sure if it is a cloned, specialized instance, return the
           primary instead.
         */
        return (tagtext_(best) < 0) ? primary : best;
    }
    else
        return primary;
}

void check_temp_arg_linkage(Expr *e)
{   AE_op op = h0_(e);
    switch (op) {
    case s_invisible:
        check_temp_arg_linkage(compl_(e));
        break;
    case s_cast:
        check_temp_arg_linkage(arg1_(e));
        break;
    case s_binder:
        {   Binder *b = exb_(e);
            if (bindstg_(b) & (bitofstg_(s_static)|bitofstg_(s_auto)))
                cc_err(sem_err_non_type_arg_linkage, b);
        }
        break;
    case s_evalerror:
    case s_integer:
    case s_floatcon:
        break;
    default:
        if (ismonad_(op))
            check_temp_arg_linkage(arg1_(e));
        else if (isdiad_(op))
        {   check_temp_arg_linkage(arg1_(e));
            check_temp_arg_linkage(arg2_(e));
        } else if (op == s_cond)
        {   check_temp_arg_linkage(arg1_(e));
            check_temp_arg_linkage(arg2_(e));
            check_temp_arg_linkage(arg3_(e));
        } else
            cc_err(sem_err_non_type_arg_value, e);
    }
}

void check_temp_type_arg_linkage(TypeExpr *t)
{   if (t == NULL) return;
    switch (h0_(t)) {
    case t_subscript:
    case t_ref:
    case t_content:
    case t_coloncolon:
        check_temp_type_arg_linkage(typearg_(t));
        break;
    default:
        /* the linkage attributes are in the tagbinder; access bits
           are in the typedef binder.
         */
        if (isprimtype_(t, s_typedefname))
        {   SET_BITMAP attr = 0;

            if (isclassorenumtype_(bindtype_(typespecbind_(t))))
                attr = attributes_(typespectagbind_(princtype(t)));
            else if (bindparent_(typespecbind_(t)))
                attr = attributes_(bindparent_(typespecbind_(t)));
            if (attr & (A_INTERN+A_NOLINKAGE))
                cc_err(sem_err_template_arg_linkage, princtype(t));
        }
    }
}

/* Attempt to generate a defn from a template for a specific which is not
   a specialization.
*/
static void sem_attempt_template_function(Binder *generic, Binder *specific)
{   BindList *bl;
    if ((bl = bindftlist_(generic)) == NULL) return;
    {   FormTypeList *ft = typefnargs_(bindtype_(specific));
        int len = length((List *)ft);
        ExprList *l = NULL;
        BindList *tmpts = NULL;
        for (; ft; ft = ft->ftcdr)
            l = mkExprList(l, (Expr *)gentempbinder(ft->fttype));
        l = (ExprList *)dreverse(l);
        for (; bl; bl = bl->bindlistcdr)
        {   Binder *ftemp = bl->bindlistcar;
            int len2 = length((List *)typefnargs_(bindtype_(ftemp)));
            if (bindstg_(ftemp) & b_undef || len != len2) continue;
            tmpts = binder_cons2(tmpts, ftemp);
        }
        if ((tmpts = temp_reduce(tmpts, l, NULL, generic)) != NULL)
        {   Binder *ftemp = tmpts->bindlistcar;
            ScopeSaver env = bindenv_(ftemp);
            bool has_failed = NO;
            TypeExpr *t;
            BindList *bl = bindinstances_(ftemp);

            for (; bl; bl = bl->bindlistcdr)
                if (bl->bindlistcar == specific) return;
            if (currentfunction.symstr == bindsym_(ftemp)) return;
            t = type_deduction(bindtype_(ftemp), l, NULL, &env, YES, &has_failed);
            if (has_failed) syserr("type deduction failed, shouldn't happen.");
            /* Make sure its the type we want. */
            if (!equivtype(t, bindtype_(specific))) return;
            for (bl = typeovldlist_(bindtype_(generic)); bl; bl = bl->bindlistcdr)
                if (equivtype(bindtype_(bl->bindlistcar), t))
                    return;
            t = globalize_typeexpr(t);
            env = globalize_env(env);
            fixup_template_arg_type(t, env);
            add_pendingfn(bindsym_(generic),
                          ovld_tmptfn_instance_name(bindsym_(ftemp), env), t,
                          (bindstg_(bindstg_(specific) & b_impl ?
                                    realbinder_(specific) : specific)&~b_undef),
                          NULL, NULL, bindtext_(ftemp), env, YES);
        }
    }
}

bool is_comparable_specialization(TypeExpr *t1, TypeExpr *t2)
{
    if (isclasstype_(t1) && isclasstype_(t2))
    {   TagBinder *tb1 = typespectagbind_(t1), *tb2 = typespectagbind_(t2);
        if (tagprimary_(tb1) != NULL && tagprimary_(tb1) == tagprimary_(tb2))
        {   ScopeSaver f1 = tagactuals_(tb1), f2 = tagactuals_(tb2);
            for (; f1 && f2; f1 = bindcdr_(f1), f2 = bindcdr_(f2))
                if (!istypevar(bindtype_(f1)) && !istypevar(bindtype_(f2)))
                    return NO;          /* the equivalence case is tested elsewhere */
            return YES;
        }
        /* Consider template <T> struct Y { struct X {}; };
           and Y<whatever>::X, Y<T>::X == Y<whatever>::X.
         */
        if (tagbindparent_(tb1) != NULL && tagbindparent_(tb2) != NULL &&
            (tagprimary_(tagbindparent_(tb2)) == tagbindparent_(tb1) ||
             tagprimary_(tagbindparent_(tb1)) == tagbindparent_(tb2)))
        {   return YES;
        }
    }
    return NO;
}

bool is_an_instance(BindList *ins, Binder *b)
{
    for (; ins; ins = ins->bindlistcdr)
        if (ins->bindlistcar == b) return YES;
    return NO;
}

bool has_template_parameter(ScopeSaver tformals)
{   for (; tformals; tformals = bindcdr_(tformals))
        if (contains_typevars(bindtype_(tformals))
            || (bindstg_(tformals) == 0 && !bindconst_(tformals)))
            return YES;
    return NO;
}

void add_instance(Binder *b, BindList **bl, bool bindstore)
{   BindList *l = *bl;
    Symstr *sv = bindsym_(b);
    for (; l != NULL; l = l->bindlistcdr)
        if (sv == bindsym_(l->bindlistcar)) return;
    *bl = global_cons2((bindstore)? SU_Bind : SU_Type, *bl, b);
}

bool contains_typevars(TypeExpr *t)
{   typevars_tag_list = NULL;
    return contains_typevars_0(t, NO);
}

bool is_dependent_type(TypeExpr *t)
{   return contains_typevars_0(t, YES);
}

bool comparable_templates(TagBinder *tb1, TagBinder *tb2)
{   ScopeSaver f1 = tagformals_(tb1), f2 = tagformals_(tb2);
    if (env_size(f1) != env_size(f2)) return NO;
    for (; f1 && f2; f1 = bindcdr_(f1), f2 = bindcdr_(f2))
        if (!equivtype(bindtype_(f1), bindtype_(f2))) return NO;
    return (f1 == f2) ? YES : NO;
}

void merge_default_template_args(ScopeSaver new, TagBinder *tempclass, Binder *tempfn)
{   ScopeSaver old = (tempclass) ? tagformals_(tempclass) : bindformals_(tempfn);
    bool musthavedefault = NO;
    int argno = 1;
    if (env_size(new) != env_size(old))
    {   if (tempclass)
            cc_rerr(sem_rerr_template_formal_length_class, tempclass);
        else
            cc_rerr(sem_rerr_template_formal_length_function, tempfn);
    }
    else
        for(; new && old; new = bindcdr_(new), old = bindcdr_(old), argno++)
        {   if (old != new && !equivtype(bindtype_(old), bindtype_(new)))
                cc_rerr(sem_rerr_template_formal_type, bindtype_(old), bindtype_(new));
            if (bindconst_(old) != NULL || bindconst_(new) != NULL)
            {   if (bindconst_(old) != NULL)
                    bindconst_(new) = bindconst_(old);
                /* @@@ check if both exist and consistent */
                musthavedefault = YES;
            }
            else
                if (musthavedefault)
                    cc_rerr(sem_err_missing_default_value, argno, bindsym_(old));
        }

}

/* End of xsem.c */
