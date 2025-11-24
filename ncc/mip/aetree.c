/*
 * C compiler file aetree.c, version 42
 * Copyright (C) Codemist Ltd., 1987.
 * Copyright (C) Acorn Computers Ltd., 1988
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#ifdef __STDC__
#  include <stdarg.h>
#else
#  include <varargs.h>
#endif
#include <stddef.h>
#include <ctype.h>
#include <string.h>

#include "globals.h"
#include "aetree.h"
#include "defs.h"
#include "store.h"
#include "aeops.h"
#include "bind.h"
#include "builtin.h"
/*/* The following inclusion of sem.h for isbitfield() and moan_nonconst() */
/*   shows a structural weakness. Mid-end code should not depend on the    */
/*   front-end in this sort of way.                                        */
#include "sem.h"
#include "errors.h"
#include "syn.h"        /* for copy_env() */

AEop tagbindsort(TagBinder *b)
{   return tagbindbits_(b) & bitoftype_(s_enum) ? s_enum :
           tagbindbits_(b) & bitoftype_(s_struct) ? s_struct :
           tagbindbits_(b) & bitoftype_(s_class) ? s_class :
           tagbindbits_(b) & bitoftype_(s_union) ? s_union : s_nothing;
}

/* Expr parse tree constructors */
Expr *mk_expr1(AEop op, TypeExpr *t, Expr *a1)
{
    return (Expr *) syn_list4(op, t, (FileLine *)0, a1);
}

Expr *mk_expr2(AEop op, TypeExpr *t, Expr *a1, Expr *a2)
{
    return (Expr *) syn_list5(op, t, (FileLine *)0, a1, a2);
}

Expr *mk_exprlet(AEop op, TypeExpr *t, SynBindList *a1, Expr *a2)
{
    return (Expr *) syn_list5(op, t, (FileLine *)0, a1, a2);
}

Expr *mk_expr3(AEop op, TypeExpr *t, Expr *a1, Expr *a2, Expr *a3)
{
    return (Expr *) syn_list6(op, t, (FileLine *)0, a1, a2, a3);
}

#ifdef EXTENSION_VALOF
Expr *mk_expr_valof(AEop op, TypeExpr *t, Cmd *c)
{
    return (Expr *) syn_list4(op, t, (FileLine *)0, c);
}
#endif

Expr *mk_exprwdot(AEop op, TypeExpr *t, Expr *a1, IPtr a2)
{
    return (Expr *) syn_list5(op, t, (FileLine *)0, a1, a2);
}

Expr *mk_exprbdot(AEop op, TypeExpr *t, Expr *a1, int32 a2, int32 a3,
                  int32 a4)
{
    return (Expr *)syn_list7(op, t, (FileLine *)0, a1, a2, a3, a4);
}

#ifdef TARGET_HAS_INLINE_ASSEMBLER

AsmInstr *mk_asminstr(void)
{
    AsmInstr *a = (AsmInstr *)SynAlloc(sizeof(AsmInstr));
    a->opcode = 0, a->cdr = 0; a->opnd1 = a->opnd2 = a->opnd3 = a->opnd4 = 0;
    return a;
}

#endif

DeclRhsList *mkDeclRhsList(Symstr *sv, TypeExpr *t, SET_BITMAP s)
{   /* slowly becoming local to syn.c */
    DeclRhsList *p = (DeclRhsList *) SynAlloc(sizeof(DeclRhsList));
    p->declcdr  = NULL;  p->declname = sv;  p->declrealname = NULL;
    p->decltype = t;
    declinit_(p) = NULL; /* p->decbits = 0; */
    p->declstg  = s;  p->declbind = NULL;
    p->fileline.f = NULL; p->fileline.l = 0;
    p->tentative = NULL;
#ifdef PASCAL /*ECN*/
    p->synflags = 0;
#endif
    return(p);
}

/* Hmm.  The last arg to this varies wildly in type */
TypeExpr *mk_typeexpr1(AEop op, TypeExpr *t, Expr *a1)
{
    return (TypeExpr *)syn_list4(op, t, a1, 0);
}

TopDecl *mkTopDeclFnDef(AEop a, Binder *b, SynBindList *c, Cmd *d, bool e)
{
    return (TopDecl *)syn_list5(a, b, c, d, e);
}

TypeExpr *mkTypeExprfn(AEop a, TypeExpr *b, SET_BITMAP s, FormTypeList *c,
                       const TypeExprFnAux *d)
{
/*
 * The fnaux field in a TypeExpr contains a RealRegSet, the size of which
 * depends on the number of registers that our target has. For this reason,
 * we allocate the TypeExpr in Binder store rather than syntax store, so that
 * regalloc can locate and use the RealRegSet value.
 */
    TypeExpr *t = (TypeExpr *)BindAlloc(sizeof(TypeExpr));
    h0_(t) = a;
    typearg_(t) = b;
    typeptrmap_(t) = s;
    typefnargs_(t) = c;
    typedbginfo_(t) = 0;
    typefnaux_(t) = *d;  /* At least 2 words, more if > 32 real registers exist */
#ifdef PASCAL /*ECN*/
    t->pun.type = syn_list3(t_fnap, 0, 0);
#endif
    return t;
}

TypeExpr *g_mkTypeExprfn(AEop a, TypeExpr *b, SET_BITMAP s, FormTypeList *c,
                         const TypeExprFnAux *d)
{
    TypeExpr *t = (TypeExpr *)GlobAlloc(SU_Type, sizeof(TypeExpr));
    h0_(t) = a;
    typearg_(t) = b;
    typeptrmap_(t) = s;
    typefnargs_(t) = c;
    typedbginfo_(t) = 0;
    typefnaux_(t) = *d;
#ifdef PASCAL /*ECN*/
    t->pun.type = global_list3(SU_Type, t_fnap, 0, 0);
#endif
    return t;
}

FormTypeList *mkFormTypeList(FormTypeList *ftcdr, Symstr *ftname,
                             TypeExpr *fttype, Expr *ftdefault)
{   return (FormTypeList *)syn_list4(ftcdr, ftname, fttype, ftdefault);
}

FormTypeList *g_mkFormTypeList(FormTypeList *ftcdr, Symstr *ftname,
                                      TypeExpr *fttype, Expr *ftdefault)
{   return (FormTypeList *)global_list4(SU_Other, ftcdr, ftname, fttype,
                                        ftdefault);
}

/* comments re globalisation:
   Binders are globalized or not on creation, the only need for
   globalize routines is for the type expressions (see globalize_typeexpr()
   below) which hang from them.
*/

Expr *globalize_int(int32 n)
{   /* could insert special code here to use globalize_bool()...        */
    /* possibly via lit_true or lit_false.                              */
    return (Expr*)global_list5(SU_Const, s_integer,te_int,(FileLine *)0,n,0);
}

static FormTypeList *globalize_formals_1(FormTypeList *d, bool defaultvals)
{   FormTypeList *d1;
    if (d == NULL) return NULL;
    d1 = g_mkFormTypeList(0, d->ftname,
                             globalize_typeexpr(d->fttype),
                             defaultvals && d->ftdefault ?
                             globalize_expr(d->ftdefault) : 0);
    d1->ftcdr = globalize_formals_1(d->ftcdr, defaultvals);
    return d1;
}

#define TYPEMEMOHASHSIZE 128
#define typehash_(t) (h0_(t) + (IPtr)typearg_(t) + ((IPtr)typespecbind_(t))>>2)

static struct te_memo { struct te_memo *cdr; TypeExpr te; }
    *glob_typeexpr_memo[TYPEMEMOHASHSIZE];

#define EQtype_(t1,t2)   ((t1)->h0==(t2)->h0 && typearg_(t1)==typearg_(t2) \
                          && typespecbind_(t1)==typespecbind_(t2))

static TypeExpr *globalize_memo(TypeExpr *t)
{   struct te_memo *p;
    int hash = ((int)typehash_(t)) & (TYPEMEMOHASHSIZE - 1);
    for (p = glob_typeexpr_memo[hash]; p != 0; p = p->cdr)
        if (EQtype_(t, &p->te)) break;
    if (p == 0)
        p = glob_typeexpr_memo[hash] =
            (struct te_memo*) global_list5(SU_Type, glob_typeexpr_memo[hash],
                         h0_(t), typespecmap_(t), typespecbind_(t), 0);
    return &p->te;
}

#if 0
static void globaltypehashstats(void)
{   struct te_memo **p = glob_typeexpr_memo;
    struct te_memo **limit =
        p + (sizeof glob_typeexpr_memo / sizeof *glob_typeexpr_memo);
    int used = 0, maxlen = 0;
    for (; p < limit; ++p)
    {   int len = 0;
        struct te_memo *p2 = *p;
        for (; p2 != 0; p2 = p2->cdr) ++len;
        if (maxlen < len) maxlen = len;
        if (0 < len) ++used;
        cc_msg("bucket %d, chain length = %d\n", p - glob_typeexpr_memo, len);
    }
    cc_msg("glob_typeexpr_memo:  %d of %d buckets used; max chain length = %d\n",
           used, TYPEMEMOHASHSIZE, maxlen);
}
#endif

/*
 * a temporary home before its demise...
 */
int32 evaluate(Expr *a)
{
  /* evaluate the compile-time expression a to yield an integer result     */
    for (;;) switch (h0_(a))
    {
    case s_evalerror:
        if (has_template_arg_scope() && arg3_(a) == NULL)
            /* silent mode */ ;
        else
            cc_rerr((msg_t)arg3_(a), h0_(arg2_(a)));
        a = arg1_(a);
        break;
    case s_integer:
        return(intval_(a));
    case s_int64con:
        {   int32 n;
            if ((int64map_(a) & bitoftype_(s_unsigned))
                || I64_SToI(&n, &int64val_(a).i) != i64_ok) {
                if (I64_UToI((uint32 *)&n, &int64val_(a).u) != i64_ok)
                    cc_rerr(sem_rerr_implicit_cast_overflow(te_uint, 0, 0));
            }
            return n;
        }

    default:
        /* Beware: this is not a catch-all. Some callers don't have the right
           scope for it. Requires fix at the call site.
           */
        if (!is_template_arg_binder(a))
            moan_nonconst(a, bind_msg_const_nonconst, bind_msg_const_nonconst1,
                          bind_msg_const_nonconst2);
        return 1;
    }
}

/* globalize_typeexpr caches only basic types (including structs/typedefs) */
/* and pointers/refs to things already cached.  Tough ched arrays/fns.     */
/* N.B. we should never cache empty arrays as size may get updated.        */

static TypeExpr *globalize_typeexpr_1(TypeExpr *t, bool defaultvals)
{   static bool glob_incache;
    TypeExpr *ans;
#ifdef PASCAL /*ECN*/
    assert(0);
#else
    switch (h0_(t))
    {
case t_content:
case t_ref:
        {   TypeExpr *gt = globalize_typeexpr(typearg_(t));
            if (glob_incache)
            {   TypeExpr temp;
                h0_(&temp) = h0_(t), typearg_(&temp) = gt,
                typeptrmap_(&temp) = typeptrmap_(t);
                /* dbglanginfo field?  Doesn't matter for C! */
                return globalize_memo(&temp);
            }
            return (TypeExpr *)global_list4(SU_Type,
                                            h0_(t), gt, typeptrmap_(t), 0);
            /* note that glob_incache is set correctly */
        }
case t_subscript:
        {   Expr *subsz = typesubsize_(t);
            ans = (TypeExpr*) global_list4(SU_Type, t_subscript,
                                globalize_typeexpr(typearg_(t)),
               subsz == 0 ? (Expr *)0 : (h0_(subsz) == s_binder ||
               (h0_(subsz) == s_cast) && h0_(arg1_(subsz)) == s_binder) ?
                                           globalize_expr(subsz) :
                                    globalize_int(evaluate(subsz)),
                                0);
            glob_incache = 0;
            return ans;
        }
case t_fnap:
            /* the DeclRhsList of formals could well become a ClassMember */
            ans = g_mkTypeExprfn(t_fnap,
                               globalize_typeexpr(typearg_(t)),
                               typeptrmap_(t),
                               globalize_formals_1(typefnargs_(t), defaultvals),
                               &typefnaux_(t));
            glob_incache = 0;
            return ans;
case t_ovld: /* all t_ovld types a global */
            glob_incache = 0;
            return t;
case t_coloncolon:
            ans = (TypeExpr *)global_list4(SU_Type, t_coloncolon,
                                           globalize_typeexpr(typearg_(t)),
                                           typespectagbind_(t),
                                           0);
            glob_incache = 0;
            return ans;
case s_typespec:
            /* N.B. any binder in typespecbind_(t) is assumed globalised */
            if (typespecmap_(t) & (bitoftype_(s_typedefname)|ENUMORCLASSBITS)
                 && (!(typespecmap_(t) & ENUMORCLASSBITS ?
                         attributes_(typespectagbind_(t)) :
                         attributes_(typespecbind_(t))) & A_GLOBALSTORE))
                syserr("globalization failure: $b", typespecbind_(t));
            glob_incache = 1;
            return typespecmap_(t) == typespecmap_(te_void) ? te_void :
                   typespecmap_(t) == typespecmap_(te_int) ? te_int :
                   typespecmap_(t) == typespecmap_(te_lint) ? te_lint :
                   typespecmap_(t) == typespecmap_(te_uint) ? te_uint :
                   typespecmap_(t) == typespecmap_(te_ulint) ? te_ulint :
                   typespecmap_(t) == typespecmap_(te_float) ? te_float :
                   typespecmap_(t) == typespecmap_(te_double) ? te_double :
                   typespecmap_(t) == typespecmap_(te_ldble) ? te_ldble :
                   globalize_memo(t);
case t_unknown:
            return t;
default:
            syserr(syserr_globalize1, (VoidStar)t, (long)h0_(t));
            return t;
    }
#endif
}

FormTypeList *globalize_formals(FormTypeList *d)
{
    return globalize_formals_1(d, YES);
}

TypeExpr *globalize_typeexpr(TypeExpr *t)
{
    return globalize_typeexpr_1(t, YES);
}

static FormTypeList *clone_formals(FormTypeList *ft);
static FormTypeList *clone_formals(FormTypeList *ft)
{   if (!ft) return NULL;
    return (FormTypeList *)syn_list4(clone_formals(ft->ftcdr), ft->ftname,
            clone_typeexpr(ft->fttype), ft->ftdefault);
}

ScopeSaver globalize_env(ScopeSaver env)
{   ScopeSaver temp = NULL;
    for (; env; env = bindcdr_(env))
    {   temp = global_mk_binder(temp, bindsym_(env), bindstg_(env),
                                globalize_typeexpr(bindtype_(env)));
        bindconst_(temp) = bindconst_(env);
    }
    return dreverse_binder(temp);
}

TypeExpr *clone_typeexpr(TypeExpr *t)
{
    switch (h0_(t)) {
    case t_content:
    case t_ref:
        return mk_typeexpr1(h0_(t),
                  clone_typeexpr(typearg_(t)), (Expr*)typeptrmap_(t));
    case t_subscript:
        return mk_typeexpr1(t_subscript,
                  clone_typeexpr(typearg_(t)), (Expr*)typesubsize_(t));
    case t_ovld:
        if (length((List *)typeovldlist_(t)) == 1)
            t = bindtype_(typeovldlist_(t)->bindlistcar);
        else
        {   syserr("clone_typeexpr: lack of target type, overload found");
            return t;
        }
    case t_fnap:
        return mkTypeExprfn(t_fnap,
                  clone_typeexpr(typearg_(t)), typeptrmap_(t),
                      clone_formals(typefnargs_(t)), &typefnaux_(t));
    case t_coloncolon:
        return mk_typeexpr1(t_coloncolon,
                  clone_typeexpr(typearg_(t)), (Expr*)typespectagbind_(t));
    case s_typespec:
    {   Binder *b = typespecbind_(t);
        TypeExpr *t1 = princtype(t);
        /* break structure sharing, name is the link */
        if (isprimtype_(t, s_typedefname) && (h0_(t1) == t_unknown
            || (isclasstype_(t1) && (tagbindbits_(typespectagbind_(t1)) & TB_TEMPLATE))))
        {   TagBinder *parent;
            if (b == NULL) syserr("Odd typevar");
            parent = bindparent_(b);
            b = (attributes_(b) & A_GLOBALSTORE) ?
                global_mk_binder(0, bindsym_(b), bindstg_(b), bindtype_(b)) :
                mk_binder(bindsym_(b), bindstg_(b), bindtype_(b));
            bindparent_(b) = parent;
            if (isclasstype_(t1))
            {   TagBinder *tb = typespectagbind_(t1);
                Symstr *sv = specialized_name_of(tb);
                BindList *bl = taginstances_(tb);
                TagBinder *clone = NULL;

                for (; bl != NULL; bl = bl->bindlistcdr)
                    if (tagbindsym_(bl->bindlistcar) == sv)
                    {   clone = (TagBinder *)bl->bindlistcar;
                        break;
                    }
                if (clone == NULL)
                {   Binder *b1;
                    ExprList *types = NULL;
                    AEop sort = tagbindsort(tb);

                    /* pretends this is a specialization */
                    clone = (attributes_(tb) & A_GLOBALSTORE) ?
                        global_mk_tagbinder(0, sv, sort) : mk_tagbinder(sv, sort);
                    /* Exactly the same as the primary, except for the those
                       used in type deduction.
                       Beware instance list shared and the clone is on it!
                     */
                    *clone = *tb;
                    tagformals_(clone) =
                        globalize_env(copy_env(tagformals_(tb), env_size(tagformals_(tb))));
                    tagprimary_(clone) = tb;
                    for (b1 = tagformals_(tb); b1 != NULL; b1 = bindcdr_(b))
                        types = syn_cons2(types,
                                          mk_typeexpr1(s_typespec, bindtype_(b1), 0));
                    types = dreverse((List *)types);
                    tagactuals_(clone) =
                        globalize_template_arg_binders(tagformals_(tb), types);
#if 0
                    tagbindtype_(clone) = mk_typeexpr1(s_typespec,
                                               (TypeExpr*)bitoftype_(sort), (Expr*)clone);
#endif
                    add_instance((Binder *)clone, &taginstances_(tb), YES);
                }
                bindtype_(b) = tagbindtype_(clone);
            }
        }
        return mk_typeexpr1(s_typespec, typearg_(t), (Expr*)b);
    }
    case t_unknown:
        return t;
    default:
        syserr("un-clonable type");
        return t;
    }

}

TypeExpr *globalize_typeexpr_no_default_arg_vals(TypeExpr *t)
{
    return globalize_typeexpr_1(t, NO);
}

static FileLine *globalize_fileline(Expr *e)
{   if (hasfileline_(h0_(e)) && exprfileline_(e) != NULL)
    {   FileLine *fl = (FileLine *)GlobAlloc(SU_Other, (int32)sizeof(FileLine));
        *fl = *exprfileline_(e);
        return fl;
    }
    return NULL;
}

static Expr *globalize_integer(Expr *e)
{   Binder *b = exb_(arg2_(e));
/* Don't bother with "globalize_expr(arg2_(e))" for intorig_() field    */
/* unless the intorig_field is already a global binder... Relied on by  */
/* C++'s end-of-class default argument binding code. FRIGORAMA!         */
    if (b != 0 && !(attributes_(b) & A_GLOBALSTORE)) b = 0;
    return (Expr *)global_list5(SU_Other, s_integer,
                                globalize_typeexpr(type_(e)),
                                globalize_fileline(e),
                                arg1_(e),
/* preseve global binder => */  b);
}

StringSegList *globalize_strseg(StringSegList *s)
{   if (s == NULL) return NULL;
    return (StringSegList *)global_list3(SU_Other,
        globalize_strseg(s->strsegcdr),
        memcpy(GlobAlloc(SU_Other, s->strseglen),
               s->strsegbase, (size_t)s->strseglen),
        s->strseglen);
}

static Expr *globalize_string(AEop op, String *s)
{
    return (Expr *)global_cons2(SU_Other,
        op,
        globalize_strseg(s->strseg));
}

static ExprList *globalize_exprlist(ExprList *l)
{   if (l == NULL) return NULL;
    return (ExprList *)global_cons2(SU_Other,
        globalize_exprlist(l->cdr),
        globalize_expr(exprcar_(l)));
}

static Binder *globalize_binder(Binder *b)
{   Binder *p;
    Symstr *sv;

/* Non-temp binders are global iff they need to be global. Temp ones */
/* may need to be globalized (cf s_let in globalize_expr() below).   */

    if (attributes_(b) & A_GLOBALSTORE) return b;

    sv = bindsym_(b);
    if (!isgensym(sv))
    {   syserr("globalize_binder");
        return b;
    }
    else if (bind_global_(sv) != 0)
        return bind_global_(sv);

    sv = sym_insert_id(sv->symname);
    p = global_mk_binder(0, sv, bindstg_(b), globalize_typeexpr(bindtype_(b)));
    bind_global_(bindsym_(b)) = p;
    attributes_(p) = (attributes_(b) & ~A_LOCALSTORE) | A_GLOBALSTORE;
    bindaddr_(p) = bindaddr_(b);
    bindconst_(p) = bindconst_(b) ? globalize_expr(bindconst_(b)) : 0;
    return p;
}

static SynBindList *globalize_bindlist(SynBindList *l)
{   if (l == NULL) return NULL;
    return (SynBindList *)global_cons2(SU_Other,
        globalize_bindlist(l->bindlistcdr),
        globalize_binder(l->bindlistcar));
}

Expr *globalize_expr(Expr *e)
{   AEop op;
    /* This is now sometimes needed even in a C-only compiler (though   */
    /* the more complicated cases can't arise) now that constant values */
    /* get propagated in C from the bindconst_ field of a const binder  */

    switch (op = e ? h0_(e) : s_error)
    {
case s_typespec:
                return global_list3(SU_Type, s_typespec,
                                    globalize_typeexpr(type_(e)), arg1_(e));
case s_evalerror:
                if (has_template_arg_scope()) return globalize_expr(arg1_(e));
                /* else same as s_error, drop thru */
case s_error:
case s_invisible:         /* shouldn't occur in optimise0() results.    */
                break;
case s_binder:
                return (Expr *)globalize_binder(exb_(e));
case s_floatcon:          /* uses global store @@@ DANGEROUS assumption */
case s_int64con:          /* uses global store @@@ DANGEROUS assumption */
                return e;
case s_integer:
                return globalize_integer(e);
#ifdef EXTENSION_UNSIGNED_STRINGS
case s_ustring:
#endif
case s_wstring:
case s_string:
                return globalize_string(h0_(e), (String *)e);
case s_fnapstruct:
case s_fnap:
                return (Expr *) global_list5(SU_Other,
                    op,
                    globalize_typeexpr(type_(e)),
                    globalize_fileline(e),
                    globalize_expr(arg1_(e)),
                    globalize_exprlist(exprfnargs_(e)));
case s_qualified|s_let:
case s_let:
                return (Expr *) global_list5(SU_Other,
                    op,
                    globalize_typeexpr(type_(e)),
                    globalize_fileline(e),
                    globalize_bindlist(exprletbind_(e)),
                    globalize_expr(arg2_(e)));

#ifdef RANGECHECK_SUPPORTED
case s_rangecheck:
#endif
case s_cond:
                return (Expr *) global_list6(SU_Other,
                    op,
                    globalize_typeexpr(type_(e)),
                    globalize_fileline(e),
                    globalize_expr(arg1_(e)),
                    globalize_expr(arg2_(e)),
                    globalize_expr(arg3_(e)));
case s_dot:
        {       bool is_bitfield = isbitfield_type(type_(e));
                Expr *r = (Expr *)GlobAlloc(SU_Other,
                    is_bitfield ? 7L*sizeof(int32) : 5L*sizeof(int32));
                h0_(r) = op;
                type_(r) = globalize_typeexpr(type_(e));
                exprfileline_(r) = globalize_fileline(e);
                arg1_(r) = globalize_expr(arg1_(e));
                exprdotoff_(r) = exprdotoff_(e);
                if (is_bitfield)
                {   exprbsize_(r) = exprbsize_(e);
                    exprmsboff_(r) = exprmsboff_(e);
                }
                return r;
        }
default:
        if (ismonad_(op) || op == s_return || op == s_cast)
        {
                return (Expr *) global_list4(SU_Other,
                    op,
                    globalize_typeexpr(type_(e)),
                    globalize_fileline(e),
                    globalize_expr(arg1_(e)));
        }
        else if (isdiad_(op) || op == s_init
#ifdef RANGECHECK_SUPPORTED
                 || op == s_checknot
#endif
                )
        {
                return (Expr *) global_list5(SU_Other,
                    op,
                    globalize_typeexpr(type_(e)),
                    globalize_fileline(e),
                    globalize_expr(arg1_(e)),
                    globalize_expr(arg2_(e)));
        }
    }
    syserr("globalize_expr(%p:%.lu)", e, op);
    return NULL;
}

void aetree_init(void)
{   struct te_memo **p = glob_typeexpr_memo;
    struct te_memo **limit =
        p + (sizeof glob_typeexpr_memo / sizeof *glob_typeexpr_memo);
    for (; p < limit; ++p)
      *p = 0;
}

/* command nodes... */
Cmd *mk_cmd_0(AEop op, FileLine x)   /* op = s_break,s_endcase,s_continue */
{
    Cmd *p = (Cmd *) SynAlloc(offsetof(Cmd,cmd1));
    p->fileline = x;
    h0_(p) = op;
    return p;
}

Cmd *mk_cmd_e(AEop op, FileLine x, Expr *e)   /* op = s_return,s_semicolon */
{
    Cmd *p = (Cmd *) SynAlloc(offsetof(Cmd,cmd2));
    p->fileline = x;
    h0_(p) = op, cmd1e_(p) = e;
    return p;
}

Cmd *mk_cmd_default(FileLine x, Cmd *c)
{
    Cmd *p = (Cmd *) SynAlloc(offsetof(Cmd,cmd2));
    p->fileline = x;
    h0_(p) = s_default, cmd1c_(p) = c;
    return p;
}

Cmd *mk_cmd_lab(AEop op, FileLine x, LabBind *b, Cmd *c)
{   /* op = s_colon,s_goto */
    Cmd *p = (Cmd *) SynAlloc(offsetof(Cmd,cmd3));
    p->fileline = x;
    h0_(p) = op, cmd1c_(p) = (Cmd *)b, cmd2c_(p) = c;
    return p;
}

Cmd *mk_cmd_block(FileLine x, SynBindList *bl, CmdList *cl)
{
    Cmd *p = (Cmd *) SynAlloc(offsetof(Cmd,cmd3));
    p->fileline = x;

    if ( (LanguageIsCPlusPlus) && bl && (bl -> bindlistcdr != NULL))
      /* For ease of generating destructor information after each
         declaration of an auto variable for which there is a destructor,
         allow only one declaration per block SW09Sep97*/
      {
        SynBindList* blc = bl -> bindlistcdr;
        bl -> bindlistcdr = NULL;
        cmd2c_(p) = (Cmd *) mkCmdList (0, mk_cmd_block(x, blc, cl));
      }
    else
      cmd2c_(p) = (Cmd *)cl;
    h0_(p) = s_block, cmd1c_(p) = (Cmd *)bl;
    return p;
}

Cmd *mk_cmd_do(FileLine x, Cmd *c, Expr *e)
{
    Cmd *p = (Cmd *) SynAlloc(offsetof(Cmd,cmd3));
    p->fileline = x;
    h0_(p) = s_do, cmd1c_(p) = c, cmd2e_(p) = e;
    return p;
}

Cmd *mk_cmd_if(FileLine x, Expr *e, Cmd *c1, Cmd *c2)
{
    Cmd *p = (Cmd *) SynAlloc(offsetof(Cmd,cmd4));
    p->fileline = x;
    h0_(p) = s_if, cmd1e_(p) = e, cmd2c_(p) = c1, cmd3c_(p) = c2;
    return p;
}

Cmd *mk_cmd_switch(FileLine x, Expr *e, Cmd *c1, Cmd *c2, Cmd *c3)
{
    Cmd *p = (Cmd *) SynAlloc(sizeof(Cmd));
    p->fileline = x;
    h0_(p) = s_switch, cmd1e_(p) = e, cmd2c_(p) = c1,
                       cmd3c_(p) = c2, cmd4c_(p) = c3;
    return p;
}

Cmd *mk_cmd_for(FileLine x, Expr *e1, Expr *e2, Expr *e3, Cmd *c)
{
    Cmd *p = (Cmd *) SynAlloc(sizeof(Cmd));
    p->fileline = x;
    h0_(p) = s_for, cmd1e_(p) = e1, cmd2e_(p) = e2,
                    cmd3e_(p) = e3, cmd4c_(p) = c;
    return p;
}

/* for 'case' labels of a switch */
Cmd *mk_cmd_case(FileLine x, Expr *e, Cmd *c1, Cmd *c2)
{
    Cmd *p = (Cmd *) SynAlloc(sizeof(Cmd));
    p->fileline = x;
    h0_(p) = s_case, cmd1e_(p) = e, cmd2c_(p) = c1,
                     cmd3c_(p) = c2, cmd4c_(p) = 0; /* cmd4c_ = LabelNumber */
    return p;
}

Cmd *mk_cmd_try(FileLine x, Cmd *body, Handler *handler_list, Cmd *exit)
{
    Cmd *p = (Cmd *) SynAlloc(offsetof(Cmd,cmd4));
    p->fileline = x;
    h0_(p) = s_try, cmd1c_(p) = body,
      cmd2c_(p) = (Cmd *) handler_list, cmd3c_(p) = exit;
    return p;
}


static bool is_fpval(Expr const *e, FPConst const *fc)
{
    while (h0_(e) == s_invisible) e = arg2_(e);
    if (h0_(e) == s_floatcon)
    {   FloatCon const *f = (FloatCon const *)e;
        if (is_float_(f->floatlen))
            return (f->floatbin.fb.val == fc->s->floatbin.fb.val);
        else if (is_anydouble_(f->floatlen))
            return (f->floatbin.db.msd == fc->d->floatbin.db.msd &&
                    f->floatbin.db.lsd == fc->d->floatbin.db.lsd);
    }
    return NO;
}

bool is_fpzero(Expr const *e)
{
    return is_fpval(e, &fc_zero);
}

bool is_fpone(Expr const *e)
{
    return is_fpval(e, &fc_one);
}

bool is_fpminusone(Expr const *e)
{
    return is_fpval(e, &fc_minusone);
}

int32 result2;

bool integer_constant(Expr const *x)
{
/* Test if x is an integer constant, and if it is leave its value in result2 */
    if (h0_(x)==s_integer)
    {   result2 = intval_(x);
        return YES;
    }
    return NO;
}

bool is_intzero(Expr const *x)
{
    return (integer_constant(x) && result2==0);
}

bool is_intone(Expr const *x)
{
    return (integer_constant(x) && result2==1);
}

bool is_intminusone(Expr const *x)
{
    return (integer_constant(x) && result2==-1);
}

bool resultinflags_fn(Expr *e)
{
    if (h0_(e) == s_fnap)
    {
        TypeExpr *t = princtype(typeofexpr(arg1_(e)));
        while (h0_(t) == t_content || h0_(t) == t_coloncolon || h0_(t) == t_ref)
            t = princtype(typearg_(t));
        if (h0_(t) != t_fnap) syserr("function type expected");
        return typefnauxflags_(t) & f_resultinflags;
    }
    return NO;
}

#ifdef ENABLE_AETREE
#define ANY_ENABLED ENABLE_AETREE
#else
#ifdef ENABLE_BIND
#define ANY_ENABLED ENABLE_BIND
#else
#ifdef ENABLE_CG
#define ANY_ENABLED ENABLE_CG
#else
#ifdef ENABLE_REGS
#define ANY_ENABLED ENABLE_REGS
#else
#ifdef ENABLE_TYPE
#define ANY_ENABLED ENABLE_TYPE
#endif
#endif
#endif
#endif
#endif


int32 aetree_debugcount;

#define DebugShowBinderTypes (aetree_debugcount > 1)
#define DebugShowTypedefTypes (aetree_debugcount > 1)
#define DebugShowRealBinders (aetree_debugcount > 1)
#define DebugShowPointers (aetree_debugcount > 2)

static void pr_typeexpr_e(TypeExpr *x, Symstr *s, bool nolinebreak);

#define PR_CMD          1
#define PR_HAND         2
#define PR_BIND         3
#define PR_FORMTYPE     4
#define PR_VTAB         5

#define symbol_name_(s) ((sym_name_table[s]))

static int32 position = 0;

void eprintf(char const *s, ...)
{   char b[512];
    va_list ap;
    va_start(ap,s);
    vsprintf(b, s, ap);
    {   size_t len = strlen(b);
        if (0 < len && b[len - 1] == '\n')
            position = 0;
        else
            position += len;
    }
    cc_msg("%s", b);
    va_end(ap);
}

void pr_stringsegs(StringSegList *z)
/* only used here and in jopprint.c                                     */
{   eprintf("\"");
    for (; z!=NULL; z = z->strsegcdr)
    {   char *s = z->strsegbase;
        int32 len = z->strseglen, i;
        for (i=0; i<len; i++)
        {   int ch = ((unsigned char *)s)[i];   /* for isprint */
            if (isprint(ch)) eprintf("%c", ch);
            else if (ch=='\n') eprintf("\\n");
            else eprintf("\\%lo", (long)ch);
        }
    }
    eprintf("\"");
}

#ifdef ANY_ENABLED
static void enewline(void)
{   cc_msg("\n");
    position = 0;
}

static void elinebreak(void)
{
    if (position>64)
        enewline();
}

static void elinebreakorspace(void)
{
    if (position>64)
        enewline();
    else
    {   cc_msg(" ");
        ++position;
    }
}

static void pr_id(Symstr *sv)
{
    if (sv == 0) eprintf("<NULL-ID>");
    else if (h0_(sv) != s_identifier) eprintf("<odd id %p/%lx>", sv, (long)h0_(sv));
    else eprintf("[id:%s]",symname_(sv));
    elinebreak();
}

static void pr_memb(ClassMember *m)
{
    Symstr *sv = memsv_(m);
    eprintf("[mem:%s]", sv ? symname_(sv) : "*NULL*");
}

static void pr_label(LabBind *x)
{   pr_id(x->labsym);
}

static void pr_bind0(Binder *b)
{   Symstr *sv = bindsym_(b);
    if (sv != 0)
        eprintf("%s", symname_(sv));
    else
    {   eprintf("nullbinder<");
        pr_typeexpr(bindtype_(b), 0);
        eprintf(">");
    }
}


static void pr_stg(SET_BITMAP *m)
{   AEop op = s_auto;
    for (; bitofstg_(op) & STGBITS; ++op)
        if (*m & bitofstg_(op))
        {   eprintf("%s ", symbol_name_(op));
            *m &= ~bitofstg_(op);
        }
}


static void pr_bind1(Binder *b)
{   Symstr *sv = bindsym_(b);
    SET_BITMAP orig_s = bindstg_(b);
    SET_BITMAP s = orig_s;
    eprintf(DebugShowPointers ? "[Bind%p:" : "[Bind:", (VoidStar)b);
    if (sv) eprintf(" %s ", symname_(sv)); else eprintf(" <no name>");
    pr_stg(&s);
    if (s != 0) eprintf("s=%lx", (long)s);
    if (DebugShowBinderTypes)
    {   eprintf(" t=");
        pr_typeexpr_e(bindtype_(b), 0, YES);
        elinebreakorspace();
    }
    if (orig_s & (b_impl|b_pseudonym))
    {   if (DebugShowRealBinders)
            eprintf("real="), pr_bind1(realbinder_(b));
    }
    else if ((orig_s & bitofstg_(s_auto)) && (bindaddr_(b) & BINDADDR_MASK) == BINDADDR_ARG)
        eprintf(" formal(%ld)", (long)(bindaddr_(b) & ~BINDADDR_MASK));
    else if ((orig_s & bitofstg_(s_auto)) && (bindaddr_(b) & BINDADDR_MASK) == BINDADDR_LOC)
        eprintf(" local(%ld)", (long)(bindaddr_(b) & ~BINDADDR_MASK));
    else if (bindaddr_(b) != 0 && bindaddr_(b) != BINDADDR_UNSET)
        eprintf(" addr=%ld", (long)bindaddr_(b));
    eprintf("]");
    elinebreak();
}

static void pr_tagbindname(TagBinder *b)
{   if (DebugShowPointers)
        eprintf("[TagBind%p: %s %s]",
                (VoidStar)b, symbol_name_(tagbindsort(b)), symname_(bindsym_(b)));
    else
        eprintf("%s", symname_(bindsym_(b)));
    /* do not print member list in case circular type! */
    elinebreak();
}

/* pr_tagbind is not actually used anywhere in the compiler, but is */
/* intended to be called from a debugger                            */
static void pr_tagbind(TagBinder *tb)
{   eprintf("%s ", symbol_name_(tagbindsort(tb)));
    pr_tagbindname(tb);
    eprintf(" {\n");
    if (isclasstagbinder_(tb))
    {   ClassMember *m = tagbindmems_(tb);
        for (;  m != NULL;  m = memcdr_(m))
        {   eprintf("  %s:  ", symname_(memsv_(m)));
            pr_typeexpr_e(memtype_(m), 0, YES);
        }
    }
    else if (isenumtagbinder_(tb))
    {   BindList *bl = tagbindenums_(tb);
        for (;  bl != NULL;  bl = bl->bindlistcdr)
            eprintf("  %s = %d,\n",
                    symname_(bindsym_(bl->bindlistcar)),
                    bindenumval_(bl->bindlistcar));
    } else
        eprintf("<unknown tag bind kind>");
    eprintf("};\n");
    enewline();
}

static void pr_optexpr(Expr *x, char *s)
{
        if (x!=0) pr_expr(x);
        eprintf("%s", s);
        elinebreak();
}

static void pr_condition(Expr *x)
{
    eprintf("(");
    pr_expr(x);
    eprintf(")");
    elinebreak();
}

static void pr_handler(Handler *x);

static void pr_list(int32 frep, VoidStar x)
{
    if (x != NULL)
        for (;;)
        {       switch (frep)
                {
        default:        eprintf("?");
                        break;
        case PR_CMD:    pr_cmd(cmdcar_((CmdList *)x));
                        break;
        case PR_FORMTYPE:
                        pr_typeexpr(((FormTypeList *)x)->fttype, ((FormTypeList *)x)->ftname);
                        break;
        case PR_BIND:   pr_bind1(((BindList *)x)->bindlistcar);
                        break;
        case PR_HAND:   pr_handler((Handler *)x);
                        break;
        case PR_VTAB:   {   VfnList *v = (VfnList *)x;
                            pr_bind0(v->vfmem);
                            eprintf("[delta=%ld]", v->vfdelta);
                        }
                        break;
                }
                x = (VoidStar) cdr_((List *)x);
                if (x == NULL)
                    break;
                eprintf(" ");
                elinebreak();
        }
}

static void pr_cv(SET_BITMAP *m)
{   AEop op = s_const;
    for (; op <= s_unaligned; ++op)
        if (*m & bitoftype_(op))
        {   eprintf("%s ", symbol_name_(op));
            *m &= ~bitoftype_(op);
        }
}

static void pr_typespec(TypeExpr *x)
{
    SET_BITMAP orig_m = typespecmap_(x);
    SET_BITMAP m = orig_m;
    AEop op = s_unsigned;
    if (DebugShowPointers)
        eprintf("<Type%p: ", (VoidStar)x);
    if (h0_(x)!=s_typespec)
        eprintf("<bad typespec %ld>", (long)h0_(x));
    else
    {   pr_cv(&m);
        if (int_islonglong_(m)) {
            m ^= (bitoftype_(s_short)|bitoftype_(s_long)|bitoftype_(s_longlong));
            if (HasFeature(Feature_Fussy))
            /* in which case, the printname of s_longlong is __int64, */
            /* rather than  long long                                 */
                m ^= bitoftype_(s_int);
        }
        for (; s_bool <= op; --op)
            if (m & bitoftype_(op))
            {   m &= ~bitoftype_(op);
                eprintf("%s%s", symbol_name_(op), m == 0 ? "" : " ");
            }
        if (m != 0) eprintf(" __typespecmap(%lx)", (long)m);
        if (orig_m & ENUMORCLASSBITS)
        {   elinebreakorspace();
            pr_tagbindname(typespectagbind_(x));
        } else if (orig_m & bitoftype_(s_typedefname))
        {   elinebreakorspace();
            pr_bind1(typespecbind_(x));
        } else if (typespecbind_(x) != 0)
        {   elinebreakorspace();
            eprintf("Odd type binder %p", (VoidStar)typespecbind_(x));
        }
    }
    if (DebugShowPointers)
        eprintf(">");
}

static void pr_ptr(TypeExpr *x, Symstr *s)
{   AEop op = h0_(x);
    SET_BITMAP m = typeptrmap_(x);
    eprintf(op == t_content ? "*" :
            op == t_ref ? "&" :
            "Unexpected op %ld (%s)", (long)op, symbol_name_(op));
    pr_cv(&m);
    if (m != 0) eprintf("%lx ", (long)m);
    pr_typeexpr_e(typearg_(x),s,YES);
}

/* this SHOULD print out the typeexpr backwards as a declarator with
   string s (possibly 0) as the declaree innermost.  Some fine day... */
static void pr_typeexpr_e(TypeExpr *x, Symstr *s, bool nolinebreak)
{
        switch (h0_(x))
        {
case s_typespec:pr_typespec(x);
                if (s != NULL)
                {   eprintf(" ");
                    pr_id(s);
                }
                break;
case t_coloncolon: eprintf("<"); pr_tagbindname(typespectagbind_(x));
                eprintf("::"); pr_typeexpr_e(typearg_(x),s,YES);
                eprintf(">");
                break;
case t_content:
case t_ref:     pr_ptr(x, s);
                break;
case t_subscript:
                pr_typeexpr(typearg_(x),s);
                eprintf("[");
                pr_optexpr(typesubsize_(x),"");
                eprintf("]");
                break;
case t_fnap:    pr_typeexpr(typearg_(x),s);
                eprintf(" (");
                pr_list(PR_FORMTYPE, typefnargs_(x));
                eprintf(" fnauxflags %x", typefnauxflags_(typearg_(princtype(x))));
                eprintf(")");
                break;
case t_ovld:    eprintf("<ovld:");
                if (s != NULL)
                {   eprintf(" ");
                    pr_id(s);
                }
                pr_list(PR_BIND, typeovldlist_(x));
                eprintf(">");
                break;
case t_unknown:
                {   SET_BITMAP m = typespecmap_(x);
                    pr_cv(&m);
                    eprintf("typevar");
                    if (m & (bitoftype_(s_struct)|bitoftype_(s_class)))
                        eprintf(" %s",
                                symbol_name_(m & bitoftype_(s_struct) ? s_struct : s_class));
                }
                break;
default:        eprintf("[unrecognized typeexpr %p:%ld]",
                        (void *)x, (long)h0_(x));
                if (s != NULL)
                {   eprintf(" ");
                    pr_id(s);
                }
                break;
        }
        if (!nolinebreak) elinebreak();
}

void pr_typeexpr(TypeExpr *x, Symstr *s)
{   pr_typeexpr_e(x, s, NO);
}

void pr_int64(int64 const *x)
{    eprintf("<int64 0x%lx_%.8lx>", (long)x->hi, (long)x->lo);
}

void pr_expr(Expr *x)
{
    AEop op;
    if (x == 0) eprintf("<missing expr>");
    else if (x == (Expr *)DUFF_ADDR) eprintf("<DUFF_ADDR>");
    else switch (op = h0_(x))
    {
case s_error:   eprintf("previous_error");
                return;
case s_identifier:
                pr_id((Symstr *)x);
                return;
case s_member:
                pr_memb((ClassMember *)x);
                return;
case s_binder:
#ifdef DETAILED
                pr_bind1(exb_(x));
#else
                pr_bind0(exb_(x));
#endif
                return;
case s_integer: {   TypeExpr *t = princtype(type_(x));
                    if (isprimtype_(t, s_bool))
                    {   if (intval_(x)==1)
                        {   eprintf("true");
                            return;
                        }
                        if (intval_(x)==0)
                        {   eprintf("false");
                            return;
                        }
                    }
                }
                eprintf("%ld", (long)intval_(x));
                return;
case s_floatcon:eprintf("<float %s>", exf_(x)->floatstr);
                return;
case s_int64con:pr_int64(&int64val_(x).i);
                return;
case s_string:  elinebreak();
                eprintf(" ");
                pr_stringsegs(exs_(x) -> strseg);
                eprintf(" ");
                elinebreak();
                return;
case s_fnapstructvoid:
case s_fnapstruct:
case s_fnap:    pr_expr(arg1_(x));
                eprintf("(");
                {   ExprList *y = exprfnargs_(x);
                    while (y != NULL)
                    {   pr_expr(exprcar_(y));
                        y = cdr_(y);
                        if (y != NULL) { eprintf(", "); elinebreak(); }
                    }
                }
                eprintf(")");
                return;
case s_cond:    eprintf("(");
                pr_expr(arg1_(x));
                eprintf(" ? ");
                elinebreak();
                pr_expr(arg2_(x));
                eprintf(" : ");
                elinebreak();
                pr_expr(arg3_(x));
                eprintf(")");
                elinebreak();
                return;
#ifdef RANGECHECK_SUPPORTED
case s_checknot: eprintf("(");
                pr_expr(arg1_(x));
                eprintf(" ne ");
                elinebreak();
                pr_expr(arg2_(x));
                eprintf(")");
                elinebreak();
                return;
case s_rangecheck: eprintf("(");
                pr_expr(arg1_(x));
                eprintf(" in ");
                elinebreak();
                eprintf("[");
                pr_expr(arg2_(x));
                eprintf(" : ");
                elinebreak();
                pr_expr(arg3_(x));
                eprintf("])");
                elinebreak();
                return;
#endif
case s_dot:
case s_qualdot: eprintf("(");
                pr_expr(arg1_(x));
                eprintf(op == s_dot ? " . " : " ::. ");
                if (h0_(type_(x)) == t_ovld || h0_(type_(x)) == t_fnap)
                    pr_expr(arg2_(x));
                else
                    eprintf("%ld", (long)exprdotoff_(x));
                eprintf(")");
                return;
case s_cast:    eprintf("(CAST(");
                pr_typeexpr(type_(x),0);
                eprintf(") ");
                elinebreak();
                pr_expr(arg1_(x));
                eprintf(")");
                return;
case s_invisible: eprintf("INVISIBLE(");
                pr_expr(arg1_(x));
                eprintf(" ==> ");
                elinebreak();
                pr_expr(arg2_(x));
                eprintf(")");
                return;
case s_let:     eprintf("(LET ");
                elinebreak();
                pr_list(PR_BIND, arg1_(x));
                eprintf(" IN ");
                elinebreak();
                pr_expr(arg2_(x));
                eprintf(")");
                return;
#ifdef EXTENSION_VALOF
case s_valof:   eprintf("VALOF ");
                pr_cmd(expr1c_(x));
                return;
#endif
case s_content4:op = s_content;  /* and fall through */
default:
        if (ismonad_(op) || op == s_return || op == s_throw)
        {       eprintf("(%s ", symbol_name_(op));
                elinebreak();
                pr_expr(arg1_(x));
                eprintf(")");
        }
        else if (isdiad_(op))
        {   eprintf("(");
            pr_expr(arg1_(x));
            eprintf(" %s ", symbol_name_(op));
            elinebreak();
            pr_expr(arg2_(x));
            eprintf(")");
        }
        else
        {   eprintf("Unprintable op %ld (%s)\n", (long)op, symbol_name_(op));
            position = 0;
        }
        return;
    }
}

static void pr_handler(Handler *x)
{   eprintf("catch(");
    pr_list(PR_BIND, x->handbl);
    eprintf(")");
    pr_cmd(x->handbody);
    elinebreak();
}

void pr_cmd(Cmd *x)
{
        AEop op;
        for (;;)
        {
                if (x!=0) switch (op = h0_(x))
                {
        default:        eprintf("<odd cmd %ld = %s>",(long)op, symbol_name_(op));
                        elinebreak();
                        return;
        case s_break:
        case s_endcase:
        case s_continue:eprintf("%s", symbol_name_(op));
                        break;
        case s_return:  eprintf("return ");
                        pr_optexpr(cmd1e_(x),";");
                        elinebreak();
                        return;
#ifdef EXTENSION_VALOF
        case s_resultis:
                        eprintf("resultis ");
                        pr_optexpr(cmd1e_(x),";");
                        elinebreak();
                        return;
#endif
        case s_case:    eprintf("case");
                        pr_condition(cmd1e_(x));
                        eprintf(":");
                        elinebreak();
                        x = cmd2c_(x);
                        continue;
        case s_default: eprintf("default:");
                        elinebreak();
                        x = cmd1c_(x);
                        continue;
        case s_do:      eprintf("do ");
                        pr_cmd(cmd1c_(x));
                        eprintf("while");
                        elinebreak();
                        pr_condition(cmd2e_(x));
                        break;
        case s_for:     eprintf("for(");
                        pr_optexpr(cmd1e_(x),";");
                        elinebreak();
                        pr_optexpr(cmd2e_(x),";");
                        elinebreak();
                        pr_optexpr(cmd3e_(x),")");
                        elinebreak();
                        x = cmd4c_(x);
                        continue;
        case s_goto:    eprintf("goto");
                        pr_label(cmd1lab_(x));
                        break;
        case s_if:      eprintf("if");
                        pr_condition(cmd1e_(x));
                        elinebreak();
                        pr_cmd(cmd2c_(x));
                        elinebreak();
                        if ((x = cmd3c_(x)) != 0) continue;
                        else return;
        case s_switch:  eprintf("switch ");
                        pr_condition(cmd1e_(x));
                        elinebreak();
                        x = cmd2c_(x);
                        continue;
        case s_colon:   pr_label(cmd1lab_(x));
                        eprintf(":");
                        elinebreak();
                        x = cmd2c_(x);
                        continue;
        case s_thunkentry:
                        eprintf("thunktable{");
                        pr_list(PR_VTAB, cmd1c_(x));
                        eprintf("}");
                        elinebreak();
                        break;
        case s_semicolon:
                        pr_expr(cmd1e_(x));
                        break;
        case s_block:   eprintf("{");
                        pr_list(PR_BIND, cmdblk_bl_(x));
                        eprintf(" ");
                        elinebreak();
                        pr_list(PR_CMD, cmdblk_cl_(x));
                        eprintf("}");
                        break;
        case s_catch:   eprintf("(Error: catch block, should be try block: ");
                        continue;
        case s_try:     eprintf("try");
                        pr_cmd(cmd1c_(x));
                        elinebreak();
                        pr_list(PR_HAND, cmdhand_(x));
                        break;
                }
                eprintf(";");
                elinebreak();
                return;
        }
}

void pr_topdecl(TopDecl *x)
{
        position = 0;
        if (x==NULL)
        {   eprintf("<missing topdecl>\n");
            position = 0;
            return;
        }
        switch (h0_(x))
        {
case s_fndef:   eprintf("FNDEF ");
                pr_bind1(x->v_f.fn.name);
                eprintf("\n");
                pr_list(PR_BIND, x->v_f.fn.formals);
                if (x->v_f.fn.ellipsis) eprintf(" (...)");
                eprintf("\n");
                pr_cmd(x->v_f.fn.body);
                eprintf("\n");
case s_eof:
case s_decl:    break;
default:        eprintf("<unknown top level %ld>", (long)h0_(x));
                position = 0;
                break;
         }
}

void pr_exproftype(char const *s, Expr *e)
{   position = 0;
    eprintf(s); pr_expr(e);
    eprintf(" of type "); pr_typeexpr_e(typeofexpr(e), 0, YES);
    eprintf("\n");
}

void pr_typeexpr_nl(TypeExpr *x, Symstr *s)
{   pr_typeexpr(x, s);
    eprintf("\n");
}

void pr_expr_nl(Expr *x)
{   pr_expr(x);
    eprintf("\n");
}

#else

/* non-debugging version: */
void pr_topdecl(TopDecl *x) { IGNORE(x); }
void pr_expr(Expr *x) { IGNORE(x); }
void pr_cmd(Cmd *x) { IGNORE(x); }
void pr_typeexpr(TypeExpr *x, Symstr *s) { IGNORE(x); IGNORE(s); }
void pr_exproftype(char const *s, Expr *e) { IGNORE(s); IGNORE(e); }

void pr_typeexpr_nl(TypeExpr *x, Symstr *s) { IGNORE(x); IGNORE(s); }
void pr_expr_nl(Expr *x) { IGNORE(x); }
#endif

/* End of section aetree.c */
