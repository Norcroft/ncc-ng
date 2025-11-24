/*
 * xsyn.c: syntax analysis phase of C++ compiler.
 * Copyright (C) Codemist Ltd., 1988-1993
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Advanced RISC Machines Limited, 1992, 1994
 * SPDX-Licence-Identifier: Apache-2.0
 * All rights reserved.
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#include <string.h>    /* for memset */
#include "globals.h"
#include "syn.h"
#include "pp.h"        /* for pp_inhashif */
#include "lex.h"
#include "simplify.h"
#include "bind.h"
#include "sem.h"
#include "aetree.h"
#include "builtin.h"
#include "vargen.h"
#include "mcdep.h"     /* for dbg_xxx */
#include "store.h"
#include "errors.h"
#include "aeops.h"
#include "codebuf.h"
#include "compiler.h"  /* UpdateProgress */
#include "cg.h"  /* for cg_topdecl - @@@ BREAKS the dependency structure */

#ifdef CALLABLE_COMPILER
#include "dbg_hdr.h"
#include "dbg_hl.h"     /* for dbg_mk_formatpack() */
#endif

#define _SYN_H
/* It seems better to forbid "int a{2};" etc in C++.    c                */
#define archaic_init(s) 0

static Expr *cpp_mkunaryorop(AEop, Expr *);
static Expr *cpp_mkfnaporop(Expr *, ExprList *);
static void gen_reftemps(void);
static Cmd *cmd_rescope(SynScope *to, SynScope *from, Cmd *c);
static void syn_setlab(LabBind *, SynScope *);
static Cmd *syn_reflab(LabBind *lab, SynScope *s, Cmd *c);

/* Peter Armistead - Make it compile by losing the static */
#ifdef CALLABLE_COMPILER
SynBindList *reverse_SynBindList(SynBindList *x);
#else
static SynBindList *reverse_SynBindList(SynBindList *x);
#endif
static void rd_cpp_name(TagBinder *leftScope);
static void rd_template_postfix(ScopeSaver tformals, bool name_only);
static void rd_exception_spec(void);
static void rd_dtor(TagBinder *scope);
static Expr *rd_cpp_prefixextra(AEop op);
static void memfn_typefix(DeclRhsList *, TagBinder *);
static DeclRhsList *DeclRhs_of_FormType(FormTypeList *x);
static DeclRhsList *reinvent_fn_DeclRhsList(Symstr *name, Symstr *realname,
                                            TypeExpr *t,SET_BITMAP s);
static void cpp_end_strdecl(TagBinder *cl);
static void syn_pop_linkage(void);
static ExprList *rd_template_actuals(bool check);
static ScopeSaver rd_template_formals(void);
static Cmd *rd_meminit(TagBinder *ctorcl, Binder *ctor, SynBindList *args,
                       Cmd **pre, Cmd **post);
static Expr *syn_memdtor(TagBinder *dtorclass, Binder *dtor, SynBindList *formals,
                         Cmd **pre);
static bool ispurefnconst(Expr *e);
static void instate_anonu_members(int declflag, Binder *b);
static void use_classname_typedef(TypeExpr *t);
static Binder *ovld_match_def(Binder *b, TypeExpr *t, BindList *l,
                              bool prefer_tmpt, SET_BITMAP declflag);
static TypeExpr *fixup_special_member(Symstr *,
    TypeExpr *, TypeExpr *, TagBinder *, SET_BITMAP stg);
static Binder *instate_classname_typedef(TagBinder *tb, int declflag);
static Handler *rd_handler(void);
static Cmd *rd_compound_statement(AEop op);
static Expr *rd_declrhs_exec_cpp(DeclRhsList *d, int* initflag);
static Cmd *syn_embed_if(CmdList *cl);
static Expr *rd_cppcast(void);
static void rd_classdecl(TagBinder *tb);
static void rd_access_adjuster(TagBinder *b, AEop access);
static Cmd *conditionalised_delete(Binder *thisb, Binder *isdelb, TagBinder *parent);
static int is_declaration(int n);
static int is_type_id(void);
static void xsyn_init(void);
static void add_memfn_template(TagBinder *p, Symstr *name, Symstr *realname, TypeExpr *t,
                               SET_BITMAP stg, TagBinder *scope, ScopeSaver formaltags,
                               int tokhandle, ScopeSaver templateformals);

static ScopeSaver applicable_template_formals(void);
static ScopeSaver cur_tformals(void);
static void syn_implicit_instantiate(TagBinder *primary, TagBinder *instance);
static Binder *find_typename(Symstr *sv, TagBinder *scope);
TagBindList *rootOfPath;

/* Peter Armistead - Make it compile */
#ifdef CALLABLE_COMPILER
#define CheckSWIValue(n) n
#endif

/* This next function should be handled by some form of attribute flag. */
/* Oh woe, even (d->declname == ctorsym) etc fails (name-munging).      */

static bool cpp_special_member(DeclRhsList *d)
{   const char *s = symname_(d->declname);
    return LanguageIsCPlusPlus &&  /* these names aren't special in C mode */
        (strncmp(s, "__ct", 4) == 0 ||
         strncmp(s, "__dt", 4) == 0 ||
         strncmp(s, "__op", 4) == 0);
}

static TagBinder DNAME = {s_tagbind};
static TagBinder TAS = {s_tagbind};             /* Template Actual Scope */
static SynScope *temps = 0;
static int32 temps_scopeid = 0;

#include "syn.c"
#include "doe.c"

int recursing;

static void save_pendingfns(PendingFnList **saved_pendingfns)
{   *saved_pendingfns = syn_pendingfns;
    syn_pendingfns = NULL;
}

static void restore_pendingfns(PendingFnList *saved_pendingfns)
{   syn_pendingfns = saved_pendingfns;
}

static void save_curfn_misc(FuncMisc *tmp)
{   tmp->switchcmd = cur_switchcmd;
    tmp->loopscope = cur_loopscope;
    tmp->switchscope = cur_switchscope;
    tmp->kaerb = cur_break;
    tmp->resttype = cur_restype;
    tmp->switchtype = cur_switchtype;
    tmp->is_ctor = cur_fn_is_ctor;
    tmp->is_dtor = cur_fn_is_dtor;
    tmp->structresult = cur_structresult;
    tmp->curfndetails = currentfunction;
    tmp->recurse = recursing, recursing = 0;
    save_labels(&tmp->labels, tmp->labsyms);
}

static void restore_curfn_misc(FuncMisc *tmp)
{   cur_switchcmd = tmp->switchcmd;
    cur_loopscope = tmp->loopscope;
    cur_switchscope = tmp->switchscope;
    cur_break = tmp->kaerb;
    cur_restype = tmp->resttype;
    cur_switchtype = tmp->switchtype;
    cur_structresult = tmp->structresult;
    cur_fn_is_ctor = tmp->is_ctor;
    cur_fn_is_dtor = tmp->is_dtor;
    currentfunction = tmp->curfndetails;
    recursing = tmp->recurse;
    restore_labels(tmp->labels, tmp->labsyms);
}

/* AM, Sept 91: memo: too much effort is spent mapping between          */
/* DeclRhsList and FormTypeLists, and Binders.  @@@ Think.              */
/* FormTypeList is now an initial sub-struct of DeclRhsList.            */

static DeclRhsList *DeclRhs_of_FormType(FormTypeList *x)
{   DeclRhsList *p = 0, *q = 0, *t;
/* This routine loses any s_register on args of member fn definitions   */
/* which are specified in a class definition.  Tough.                   */
    for (; x; x = x->ftcdr)
    {   TypeExpr *tt = x->fttype;
        t = mkDeclRhsList(x->ftname, tt, bitofstg_(s_auto));
        declinit_(t) = x->ftdefault;
        if (p == 0) p = q = t; else q->declcdr = t, q = t;
    }
    return p;
}

static DeclRhsList *reinvent_fn_DeclRhsList(Symstr *name, Symstr *realname,
                                            TypeExpr *t, SET_BITMAP s)
{   DeclRhsList *p;
    TypeExpr *newt;
    if (h0_(t) != t_fnap)
        syserr("not a function type");
    /* make a global shallow copy of 't' since we're going to reuse the */
    /* typefnargs of it                                                 */
    newt = g_mkTypeExprfn(t_fnap,
                          typearg_(t),
                          (SET_BITMAP)typespecbind_(t),
                          (FormTypeList*)DeclRhs_of_FormType(typefnargs_(t)),
                          &typefnaux_(t));
    typedbginfo_(newt) = typedbginfo_(t);
    p = mkDeclRhsList(name, newt, s);
    p->declrealname = realname;
    fault_incomplete_formals(typefnargs1_(p->decltype), 1);
    return p;
}

static void rd_operator_name(void)
{   AEop op = curlex.sym;
    /*/* need to parse 'operator new[]' and 'operator delete[]' here */
    if (op == s_lbracket || op == s_lpar)
    {    AEop ket;
         if (op == s_lbracket)
             op = s_subscript, ket = s_rbracket;
         else
             op = s_fnap, ket = s_rpar;
         nextsym();
         checkfor_ket(ket);
         ungetsym();
    }
    curlex.a1.sv = operator_name(op);
    curlex.sym = s_pseudoid;
}

static void rd_operator_or_conversion_name(void)
{   if (curlex.sym == s_identifier) rd_cpp_name(0);
    if (isdeclstarter2_(curlex))        /* rd_declspec(stgclass) moans  */
    {   TypeExpr *t = rd_typename(CONVERSIONTYPE);
        ungetsym();
        curlex_optype = t;
        curlex.a1.sv = conversion_name(t);
        curlex.sym = s_pseudoid;
    }
    else
        rd_operator_name();
}


/* Temporary routine to read and ignore C++ exception specifications.  An
 * error should be raised if an exception specification is used in a typedef
 * (DWP 15.4.1) and there are restrictions on the allowed types. None of this
 * is yet checked for.
 */

static void rd_exception_spec(void)
{
  if (curlex.sym != s_throw) return;
  nextsym();
  checkfor_ket(s_lpar);
  if (curlex.sym != s_rpar)
    for(;;) {
      (void)rd_typename(TYPENAME);
      if (curlex.sym != s_comma) break;
      nextsym();
    }
  checkfor_ket(s_rpar);
}


/* rd_dtor is now called only from rd_declarator() to read the decl of  */
/* a dtor. The syntactic form is, therefore, very simple. More complex  */
/* forms of ctors and dtors are now all handled by rd_cpp_name.         */

static void rd_dtor(TagBinder *scope)
{   if (scope)
    {   nextsym();
        if (curlex.sym == s_identifier) rd_template_postfix(NULL, YES);
        if (curlex.sym != s_identifier
            || (curlex.a1.sv != bindsym_(scope)
                && (tagprimary_(scope) == NULL
                    || bindsym_(tagprimary_(scope)) != curlex.a1.sv)))
        {   cc_err(syn_err_illdtor);
            if (curlex.sym != s_identifier) ungetsym();
        }
        else
            curlex.sym = s_pseudoid;
        curlex_optype = 0;
        curlex.a1.sv = dtorsym;
        return;
    }
    syserr("rd_dtor(0)");   /* should never happen now */
}

void diagnose_access(Symstr *sv, TagBinder *scope)
{   accessOK |= 4;      /* prevent multiple diagnoses of the same token */
    if (suppress & D_ACCESS)
        cc_warn(sem_rerr_nonpublic, scope, sv);
    else
        cc_rerr(sem_rerr_nonpublic, scope, sv);
}

static ClassMember *last_type_seen;

static void check_last_type_seen(void)
{   if (last_type_seen)
    {   check_access_1(last_type_seen, curlex_scope);
        last_type_seen = 0;
    }
}

static void check_last_access(TagBinder *leftScope)
{   TagBinder *scope;
    if (accessOK)       /* allowable or more serious error */
        return;
    if (no_access_context())
    {   last_type_seen = (curlex_typename && bindparent_(curlex_typename) &&
                !(attributes_(curlex_typename) & bitofaccess_(s_public))) ?
                (ClassMember *)curlex_typename : 0;
        return;
    }
    scope = (curlex.sym & s_qualified) ? curlex_scope :
            (leftScope != 0) ? leftScope :
            (curlex_member != 0) ? bindparent_(curlex_member) : 0;
    if (scope == 0) return;
    diagnose_access(curlex.a1.sv, scope);
}

static TagBinder *findscope(Symstr *sv, TagBinder *scope, int flags,
        bool is_dname)
{   /* I'd like to use 'findtagbinder' but it won't do FB_INHERIT */
    Binder *b = findbinding(sv, scope, flags|FB_CLASSNAME);
    if (b != NULL)
    {   if (scope != 0 && accessOK == 0 && !is_dname)
            diagnose_access(curlex.a1.sv, scope);
        /* Check to see if it is a typedef to a tagbinder */
        if (bindstg_(b) & bitofstg_(s_typedef))
        {   TypeExpr *tbt = princtype(bindtype_(b));
            if (isclasstype_(tbt))
                return typespectagbind_(tbt);
        }
    }
    return (b != NULL && h0_(b) == s_tagbind) ? (TagBinder *)b : NULL;
}

static TagBinder *globalize_tagbinder(TagBinder *tb)
{   TagBinder *res = NULL;
    if (attributes_(tb) & A_GLOBALSTORE) return tb;
    if (tb != NULL)
    {   res = global_mk_tagbinder(NULL, bindsym_(tb), tagbindsort(tb));
        tagbindparent_(res) = globalize_tagbinder(tagbindparent_(tb));
    }
    return res;
}

/* Reading a name in C++.                                               */
/* When we have a s_identifier in C++, we sometimes (but e.g. not after */
/* symbols like 'goto') read a qualified name. Other tokens - :: ~ and  */
/* operator - also introduce entities handled as names. Here, all are   */
/* read by a single mechanism. A serious wart on the implementation is  */
/* caused by the recursion rd_cpp_name -> rd_operator_or_type_name() -> */
/* rd_typename() -> rd_cpp_name(). We handle this explicitly in rd_cpp_ */
/* name() rather than add yet another argument to every invocation of a */
/* function from this cycle.                                            */
/* NOTE: we don't transform A to __ct_1A in class A MEMBER declaration  */
/* context to avoid look-ahead (e.g. A(*B)() vs A(B) problems). We only */
/* do the transformation if it is completely certain, eg A::A, A::~A.   */
/* NOTE: we should be careful about the (non-)effect of ungetsym() on   */
/* the following statics as they aren't part of curlex. All is OK but   */
/* rd_cpp_name()'s post-conditions must be maintained carefully.        */

/* Lexical pre-conditions:                                              */
/* curlex.sym is in {s_coloncolon,s_identifier,s_bitnot,s_operator}     */
/* otherwise rd_cpp_name() is a no-op.                                  */
/* Example constructs parsed:                                           */
/* ::new, ::delete, ::name, S::*, S::operator op, S::identifier, S::~S  */
/* S::operator X::T (which causes recursion), S::new, S::delete.        */
/* Ambiguity detection following X. and X->:                            */
/* After X. and X-> (leftScope != 0), if there is an initial-type-name, */
/* it must be sought twice: once in leftScope and once in the scope     */
/* enclosing X. In, for example, X.A::B::m, A::B must denote the same   */
/* type in both contexts. NOTE: it is quite possible for this to hold   */
/* even though A:: denotes <different> types in each context. See the   */
/* DRAFT standard 5.2.4 <Class member access>.                          */

#define  MSG_SILENT   0
#define  MSG_DIAGNOSE 1
#define  MSG_NOMORE   2

static void rd_cpp_name(TagBinder *leftScope)
{   int scopeFlags = ALLSCOPES, msg;
    static bool reading_conversion_typename = NO;
    bool is_dname = NO, expect_dtor = NO, expect_typename = NO,
        is_template_instance = NO, allowable_template_name = NO;
    Binder *tvb = NULL;

    switch (curlex.sym)
    {
case s_bitnot:
        /* except after . -> and ::, ~ means bitnot, by A.R.M. fiat.    */
        if (leftScope == 0) return;
case s_identifier:
        /* curlex.a2.flag on s_identifier protects against infinite     */
        /* recursion via rd_operator_or_type_name() if input is broken. */
        if (curlex.a2.flag != 0) return;
case s_typename:
case s_operator:
case s_coloncolon:
        /* These cases will consume tokens and/or alter curlex state.   */
        break;
default:
        /* let the caller handle things we don't understand...          */
        return;
    }

    if (!reading_conversion_typename)
    {   /* first entry - initialise return values */
        curlex_scope = 0;
        curlex_binder = curlex_typename = 0;
        curlex_path = 0;
        curlex_member = 0;
        curlex_optype = 0;
    }

    if (leftScope == &DNAME)
    /* reading a name in declaration context - syntactically a dname... */
    {   leftScope = 0;
        is_dname = YES;
        msg = MSG_SILENT;
    }
    else if (leftScope == &TAS)
    {   leftScope = 0;
        allowable_template_name = YES;
        msg = MSG_DIAGNOSE;
    }
    else msg = MSG_DIAGNOSE;

    switch (curlex.sym)
    {
case s_typename:
        nextsym();
        expect_typename = YES;
        break;
case s_bitnot:
        nextsym();
        if (curlex.sym != s_identifier)
        {   ungetsym();
            /* let the caller handle the diagnosis... */
            return;
        }
        expect_dtor = YES;
        break;
case s_operator:
        if (reading_conversion_typename)
            /* parsing botch - let the caller diagnose it */
                return;
        nextsym();
        curlex_scope = leftScope;            /* in case a.operator B::T */
        reading_conversion_typename = YES;
        rd_operator_or_conversion_name();
        reading_conversion_typename = NO;
        if ((bind_scope & TOPLEVEL) && (curlex_scope == 0) &&
            curlex.a1.sv == operator_name(s_assign))
            cc_warn(syn_warn_special_ops);
        /* curlex.sym == s_pseudoid or error */
        /* Are there operator templates?                                */
        break;
case s_coloncolon:
        /* leftScope != 0 is a parsing botch - let the caller handle.   */
        if (pp_inhashif || leftScope != 0) return;
        nextsym();
        switch (curlex.sym)
        {
    default:            cc_err(syn_err_cannot_follow_unary_dcolon);  return;
    case s_new:
    case s_delete:      curlex.sym |= s_qualified;  return;
    case s_operator:    nextsym(); rd_operator_name(); break;
    case s_identifier:  break;
        }
        /* curlex.sym in {s_identifier,s_pseudoid} otherwise error.     */
        scopeFlags = FB_GLOBAL;
        break;
case s_identifier:
        break;
    }

/* Assert: curlex.sym in {s_pseudoid, s_identifier} otherwise error.    */
    if (curlex.sym == s_identifier)
    {   Symstr *sv = curlex.a1.sv;
        TagBinder *lscope = leftScope;

        /* May have the start of a nested-name-specifier: check for ::  */
        for (;;)
        {   TagBinder *primary = NULL, *instance = NULL;
            if (peepsym() == s_less &&
                (primary = findtagbinding(sv, curlex_scope, ALLSCOPES)) != NULL)
            {   if (peepsym() == s_less) is_template_instance = YES;
                rd_template_postfix(applicable_template_formals(), is_dname);
                if (curlex.a1.sv != sv
                    && (instance = tag_global_(curlex.a1.sv)) != NULL
                    && peepsym() != s_times)
                {   syn_implicit_instantiate(primary, instance);
                    sv = bindsym_(instance);
                }
            }
            nextsym();
            if (curlex.sym != s_coloncolon) {ungetsym();  break;}

            if (primary == NULL &&
                (tvb = findbinding(sv, NULL, ALLSCOPES)) != NULL &&
                istypevar(bindtype_(tvb)))
            {   typespecmap_(princtype(bindtype_(tvb))) |=
                    bitoftype_(s_struct)|bitoftype_(s_class);
                binduses_(tvb) |= u_referenced;
                /* /* globalized just in case its parameter type */
                curlex_scope = global_mk_tagbinder(NULL, sv, s_struct);
                tagbindparent_(curlex_scope) = NULL;
                tagbindtype_(curlex_scope) =
                    globalize_typeexpr(mk_typeexpr1(s_typespec,
                                                    (TypeExpr *)bitoftype_(s_typedefname),
                                                    (Expr *)tvb));
            }
            else
            {   if (lscope != 0)
                    lscope = findscope(sv, lscope, INDERIVATION, is_dname);
                if (curlex_scope != NULL && istypevar(tagbindtype_(curlex_scope)))
                {   TagBinder *curScope = global_mk_tagbinder(NULL, sv, s_struct);
                    tagbindparent_(curScope) = curlex_scope;
                    curlex_scope = curScope;
                    tagbindtype_(curlex_scope) = mk_typevar();
                }
                else
                    curlex_scope = findscope(sv, curlex_scope, scopeFlags, is_dname);
                if (curlex_scope == 0 && lscope == 0 && msg != MSG_NOMORE)
                   msg = MSG_NOMORE, cc_err(syn_err_classname_not_found, sv);
            }
            /* once we have a curlex_scope, lookup is constrained to it */
            scopeFlags = INDERIVATION;
            nextsym();
            /* class-name coloncolon tilde ... is a destructor or error */
            if (curlex.sym != s_identifier) break;
            sv = curlex.a1.sv;
        }
        /* Assert curlex.sym != s_identifier OR nxtsym != s_coloncolcon */

        if (scopeFlags == INDERIVATION && lscope != 0)
        {   if (curlex_scope != 0)
            {
                if (curlex_scope != lscope)
                {
/* message re ambiguity... DRAFT standard 5.2.4 <Class member access>.  */
                    cc_rerr(syn_rerr_ambiguous_qualification, curlex.a1.sv);
                    msg = MSG_NOMORE;
                }
            }
            else
                curlex_scope = lscope;
        }

        switch (curlex.sym)
        {
default:            cc_err(syn_err_cannot_follow_binary_dcolon); return;
case s_times:       if (curlex_scope != 0) curlex.sym |= s_qualified; return;
case s_bitnot:      nextsym();
                    if (curlex.sym != s_identifier)
                    {   cc_err(syn_err_expected_dtor_name);
                        ungetsym();  /* hope this is a good way to recover */
                        return;
                    }
                    expect_dtor = YES;
                    break;
case s_operator:    if (reading_conversion_typename) return;
                        /* parsing botch - let the caller diagnose it   */
                    nextsym();
                    {   TagBinder *curScope = curlex_scope;
                        int scopelevel = push_multi_scope(curScope);
                        curlex_scope = 0;
                        reading_conversion_typename = YES;
                        rd_operator_or_conversion_name();
                        reading_conversion_typename = NO;
                        pop_scope(scopelevel);
                        curlex_scope = curScope;
                    }
                    /* curlex.sym == s_pseudoid or error */
                    /* Are there operator templates?                    */
                    break;
case s_template:    nextsym(); break;
case s_identifier:  break;
        }
    }

    if (msg == MSG_NOMORE || curlex.sym != s_identifier &&
        curlex.sym != s_pseudoid)
        return;

    if (scopeFlags != ALLSCOPES) curlex.sym |= s_qualified;

    /* rootOfPath is exported to xbind to support access control checks */
    rootOfPath = (leftScope || curlex_scope) ?
        binder_cons2(binder_cons2(NULL, leftScope), curlex_scope) : NULL;

    /* Assert: scopeFlags is one of ALLSCOPES, INDERIVATION, FB_GLOBAL. */
    if (leftScope != 0)
        curlex_path = findpath(curlex.a1.sv,leftScope,scopeFlags,curlex_scope);
    else
        curlex_path =
            findpath(curlex.a1.sv, curlex_scope,
                (is_dname ? ((scopeFlags&~FB_INHERIT)|FB_THISSCOPE) : scopeFlags), 0);
    curlex.a2.flag = 1;
            /* prevent reentry without an intervening call to nextsym() */
    if (is_dname) rootOfPath = NULL;
    if (curlex_path == 0 &&
        HasFeature(Feature_CFront) &&
            /* This is illegal by the standard... last desperate effort */
            /* to make sense of X::[~]X() where typedef T X...          */
        (curlex_scope != 0 || leftScope != 0))
    {   TagBinder *tb = findscope(curlex.a1.sv, 0, ALLSCOPES, is_dname);
        if (tb != 0 && (tb == curlex_scope || tb == leftScope))
            curlex.a1.sv = tagbindsym_(tb);
    }

try_again_for_ctor_or_dtor:
    if (curlex_path == 0)
    {   Symstr *sv = curlex.a1.sv;
        if (scopeFlags == FB_GLOBAL)
        {   /* unbound :: entity */
            cc_err(syn_err_missing_tlevel_decl, sv);
            curlex_path = errornode;
            return;
        }
        rd_template_postfix(NULL, is_dname);
        if (curlex_scope != 0 && (tagbindsym_(curlex_scope) == sv ||
                                  (tagprimary_(curlex_scope) != NULL &&
                                   tagbindsym_(tagprimary_(curlex_scope)) == sv))
            || leftScope != 0 && tagbindsym_(leftScope) == sv)
        {   sv = expect_dtor ? dtorsym : ctorsym;
            if (curlex_scope == 0) curlex_scope = leftScope;
            curlex.a1.sv = sv;
            curlex.sym = (scopeFlags == ALLSCOPES) ? s_pseudoid : s_pseudoid|s_qualified;
            curlex_path = findpath(sv, curlex_scope, INCLASSONLY,0);
        }
        else if (leftScope == 0 && curlex_scope == 0 ||
                 curlex_scope != NULL && istypevar(tagbindtype_(curlex_scope)) ||
        /* a la Microsoft Visual C++ - can declare class S {int S::x;}. */
                 curlex_scope == syn_class_scope)
        {   /* allowably not found */
            TagBinder *cl = current_member_scope();
            if (is_dname)
                check_last_type_seen();
            else
                if ((curlex_scope && istypevar(tagbindtype_(curlex_scope)))
                    || (cl && (tagbindbits_(cl) & TB_TEMPLATE)))
                {   if (expect_typename)
                    {   curlex_binder = find_typename(sv, curlex_scope);
                        if (curlex_binder == NULL)
                        {   curlex_binder = global_mk_binder(NULL, sv, bitofstg_(s_typedef),
                                                             mk_typevar());
                            bindparent_(curlex_binder) = curlex_scope;
                        }
                        curlex_typename = curlex_binder;
                    }
                    else
                        curlex_binder = global_mk_binder(NULL, sv, bitofstg_(s_auto),
                                                         mk_typevar());
                }
            return;
        }
        if (curlex_path == 0)
        {
#ifdef SURE_ABOUT_STATIC_MEM_SEMANTICS
            Expr *e;
            if (tagprimary_(curlex_scope) &&
                (e = findpath(sv, tagprimary_(curlex_scope), scopeFlags, 0)) != NULL &&
                h0_(e) == s_binder)
            {   Binder *b = e;
                DeclRhsList decl;
                TypeExpr *t = clone_typeexpr(bindtype_(b));
                fixup_template_arg_type(t, tagactuals_(curlex_scope));
                decl.declname = ovld_add_memclass(sv, curlex_scope, NO);
                decl.declstg = bindstg_(b)|b_undef;
                decl.decltype = globalize_typeexpr(t);
                if (bindconst_(b) != NULL)
                    declinit_(&decl) = mkcast(s_init, bindconst_(b), t);
                curlex_binder = instate_declaration(&decl, TOPLEVEL);
                return;
            }
#endif
            cc_err(syn_err_not_found_named_member, sv,
                   (leftScope != NULL) ? leftScope : curlex_scope);
            curlex_path = errornode;
            return;
        }
    }
    if (h0_(curlex_path) == s_binder)
    {   TagBinder *thisscope = (curlex_scope) ? curlex_scope : current_member_scope();
        curlex_binder = exb_(curlex_path);
        curlex_path = 0;
        /* first use, implicit instantiation from primary, any explicit
           specialization afterwards is a fault: specialization after use.
           14.7.3 cl 5.
         */
        if (!is_dname && bindstg_(curlex_binder) & b_undef &&
            curlex_member != NULL &&
            bindstg_(curlex_member) & b_pseudonym &&
            !isfntype(bindtype_(curlex_binder)) &&
            thisscope != NULL &&
            tagprimary_(thisscope) != NULL)
        {   Binder *b1 = findbinding(curlex.a1.sv, tagprimary_(thisscope),
                                     FB_LOCALS|FB_THISSCOPE);
            if (!b1 || !realbinder_(b1))
                syserr("Lost static member $l in $c", thisscope);
            if (bindconst_(realbinder_(b1)) != NULL)
            {   DeclRhsList *d;
                Expr *einit = bindconst_(realbinder_(b1));
                push_exprtemp_scope();
                einit = mkcast(s_init, einit, bindtype_(curlex_binder));
                if (h0_(einit) != s_error)
                {   einit = cpp_mkbinaryorop(s_init, (Expr *)curlex_binder, einit);
                    bindstg_(curlex_binder) &= ~b_undef;
                    d = mkDeclRhsList(bindsym_(curlex_binder), bindtype_(curlex_binder),
                                      bindstg_(curlex_binder));
                    d->declbind = curlex_binder;
                    (void) genstaticparts(d, YES, typehasctor(bindtype_(curlex_binder)), einit);
                }
                if (killexprtemp() != NULL) syserr("extra temps leaked");;
            }
        }
    }
    else if (h0_(curlex_path) == s_dot)
    {   TypeExpr *t = type_(curlex_path);
        if (h0_(t) == t_ovld || h0_(t) == t_fnap)
        {   /* exprdotmemfn case... */
            if (h0_(arg2_(curlex_path)) != s_binder)
                syserr("rd_cpp_name(bad exprdomemfn)");
            curlex_binder = exb_(arg2_(curlex_path));
            if (curlex_binder != NULL && peepsym() == s_less &&
                h0_(princtype(bindtype_(curlex_binder))) == t_ovld)
                (void) rd_template_postfix(cur_tformals(), is_dname);
            if (curlex.sym & s_qualified)
/* s_qualdot demands direct call/inhibits the virtual call mechanism.   */
/* NB: modifying h0_() in place is OK: nothing points to the node yet.  */
                h0_(curlex_path) = s_qualdot;
            if (msg == MSG_DIAGNOSE)
                check_last_access(leftScope);
            if (is_dname)
                check_last_type_seen();
            return;
        }
    }
/* don't recognise typedefs in #if even if extension "keywords in #if"! */
    if (pp_inhashif || (curlex.sym & ~s_qualified) == s_pseudoid) return;

    if (curlex_binder != 0 && (bindstg_(curlex_binder) & bitofstg_(s_typedef)))
    {   TagBinder *thisscope = current_member_scope();
        if (attributes_(curlex_binder) & A_PRIMARY &&
            (thisscope == NULL || bindsym_(curlex_binder) != bindsym_(thisscope)))
        {   if (thisscope != NULL
                && tagprimary_(thisscope) == typespectagbind_(bindtype_(curlex_binder)))
            {   Binder *b;
                curlex.a1.sv = bindsym_(thisscope);
                curlex_binder = ((b = bind_global_(bindsym_(thisscope))) != NULL) ? b :
                    findbinding(bindsym_(thisscope), NULL, FB_THISSCOPE|FB_CLASSNAME);
            }
            else if (!is_template_instance && !allowable_template_name)
            {   cc_err(syn_err_unspecialized_template, curlex_binder);
                return;
            }
        }

        curlex_typename = curlex_binder;
        {   TypeExpr *t = princtype(bindtype_(curlex_typename));
            TagBinder *scope = leftScope != 0 ? leftScope : curlex_scope;
            int ctor_or_dtor = isclasstype_(t) && typespectagbind_(t) == scope;
            if (ctor_or_dtor || expect_dtor)
            {   if (!ctor_or_dtor)
                    cc_rerr(syn_rerr_expect_dtor, scope, curlex.a1.sv);
                curlex.a1.sv = tagbindsym_(scope);
                curlex_typename = 0;
                scopeFlags = INDERIVATION;
                goto try_again_for_ctor_or_dtor;
            }
        }
    }

    if (curlex_binder != NULL && h0_(princtype(bindtype_(curlex_binder))) == t_ovld)
        (void)rd_template_postfix(cur_tformals(), is_dname);

    if (msg == MSG_DIAGNOSE) check_last_access(leftScope);
    if (is_dname) check_last_type_seen();
}

ScopeSaver copy_env(ScopeSaver env, int n)
{   Binder *p = NULL, *q = NULL;
    for (; env && n; env = bindcdr_(env), n--)
    {   Binder *tmp = mk_binder(bindsym_(env), bindstg_(env), bindtype_(env));
        if (!p) p = q = tmp;
        else
        {   bindcdr_(q) = tmp;
            q = tmp;
        }
    }
    return p;
}

static void rd_template_postfix(ScopeSaver tformals, bool name_only)
{   /* assert: curlex.sym == s_identifer */
    Symstr *sv = curlex.a1.sv, *sv2 = sv;
    TagBinder *tb;
    bool done = NO;
    int qualified = (curlex.sym & s_qualified);

/* Question: if global S is a template class but local S is an int,     */
/* then "S<..." is extremely dubious.  Maybe 'findtagbinding' is wrong  */
/* in the next line for this reason.                                    */
    if (peepsym() != s_less) return;

    if ((tb = findtagbinding(sv, NULL, ALLSCOPES)) != NULL &&
        tagbindbits_(tb) & TB_TEMPLATE)
    {   ExprList *actuals;
        int scope_level;
        bool newtag;  /* @@@ need to move the unaliged-check code in rd_declspec */
        TagBinder *tb2;
        ScopeSaver env = tagformals_(tb);
        int size = env_size(env);
        nextsym();              /* skip the identifier.                 */
        nextsym();              /* skip the '<' seen by peepsym().      */
        if ((tformals != NULL) && (size == env_size(tformals)) && name_only)
            /* Make sure names don't matter for ovld_template_app() purpose. */
            env = copy_env(tformals, size);
        /* Push tformals the typenames introduced in a partial specialisation */
        scope_level = push_var_scope(tformals, Scope_TemplateArgs);
        actuals = rd_template_actuals(YES);
        /* sv not necessarily the same as tagbindsym_() because of defaults */
        sv = tagbindsym_(tb);
        sv2 = ovld_template_app(sv, env, actuals);
        if (sv2 != sv)
        {   AEop s = tagbindsort(tb);
            tb2 = instate_tagbinding(sv2, s, TD_Decl, TOPLEVEL|TEMPLATE, &newtag);
            if (newtag)
            {   Binder *b;
                tagprimary_(tb2) = tb;
                tagparent_(tb2) = NULL;         /* always at top-level until namespace */
                tagscope_(tb2) = /*dup_template_scope()*/ tagscope_(tb);
                add_instance((Binder *)tb2, &taginstances_(tb), YES);
                tagactuals_(tb2) =
                    globalize_template_arg_binders(tagformals_(tb), actuals);
                b = instate_classname_typedef(tb2, TOPLEVEL);
                if (is_dependent_type(tagbindtype_(tb2)))
                    tagformals_(tb2) = tformals /*tagformals_(tb)*/;
                else
                    attributes_(b) |= A_TEMPLATE;
            }
        }
        (void)pop_scope(scope_level);
        done = YES;
    }
    /* Try function template */
    else if (curlex_binder != NULL && bindftlist_(curlex_binder) != NULL)
    {   Binder *b = curlex_binder;
        nextsym();
        nextsym();
        sv2 = bindsym_(b);
        /* A temp store for the actuals before specialization takes place. */
        bindactuals_(b) = rd_template_actuals(YES);
        done = YES;
    }

    if (done)
    {   /* @@@ the next 3 lines are unspeakably nasty (rationalise!).       */
        ungetsym();
        curlex.sym = s_identifier|qualified;
        curlex.a1.sv = lex_replaceable_template_sym(sv2);
    }
}

static Binder *genstatictemp(TypeExpr *t)
{   Binder *b = mk_binder(gensymval(0), bitofstg_(s_static), t);
    SetDataArea(DS_ReadWrite);
    syn_initdepth = -1; syn_initpeek = 0;       /* institutionalise!    */
    initstaticvar(b, 0);
    return b;
}

static void gen_reftemps()
{   for (; syn_reftemps; syn_reftemps = syn_reftemps->bindlistcdr)
    {
        SetDataArea(DS_ReadWrite);
        syn_initdepth = -1; syn_initpeek = 0;   /* institutionalise!    */
        initstaticvar(syn_reftemps->bindlistcar, 0);
    }
}

static Cmd *syn_embed_if(CmdList *cl)
{   /* assert(cl != NULL); */
    FileLine fl; fl = cmdcar_(cl)->fileline;  /* fl for *first* dyn-static  */
    {
    Binder *b = genstatictemp(te_int);
    Expr *btest = optimise0(mkbinary(s_equalequal, (Expr *)b, lit_zero));
    Expr *bset = optimise0(mkbinary(s_assign, (Expr *)b, lit_one));
    CmdList *act = mkCmdList(cl, mk_cmd_e(s_semicolon, fl, bset));
    return mk_cmd_if(fl, btest, mk_cmd_block(fl, 0, act), 0);
    }
}

static Cmd *rd_compound_statement(AEop op)
{   Cmd *c;
    if (curlex.sym == s_lbrace) c = rd_block(blk_INNER, YES);
    else
    {   cc_rerr(syn_rerr_insert_braces, op);
        c = rd_command(1);
    }
    if (curlex.sym == s_nothing) nextsym();
    return c;
}

static void syn_pop_linkage(void)
{   Linkage *p = syn_linkage;
    if (p == 0) syserr("pop_linkage(0)");
    syn_linkage = p->linkcdr;
    p->linkcdr = syn_linkage_free;
    syn_linkage_free = p;
}

static int cmpANSIstring(String *s, char *t)
{   /* @@@ beware: treats concatenation as mismatch currently!          */
    StringSegList *z = s->strseg;
    return (h0_(s) == s_string && z->strsegcdr == 0
                               && z->strseglen == (IPtr)strlen(t))
             ? memcmp(t, z->strsegbase, (size_t)z->strseglen) : 99;
}

static enum LinkSort linkage_of_string(String *s)
{   static struct { char lang[4]; enum LinkSort code; } valid[] =
      { "C++", LINK_CPP, "C", LINK_C };
    unsigned i = 0;
    for (; i < sizeof valid/sizeof valid[0]; i++)
        if (cmpANSIstring((String *)s, valid[i].lang) == 0)
            return valid[i].code;
    cc_rerr(syn_rerr_unknown_linkage, s);
    return LINK_CPP;
}

static Binder *ovld_match_def(Binder *b, TypeExpr *t, BindList *l,
                              bool prefer_tmpt, SET_BITMAP declflag)
{   /* declflag is examined for SPECIALIZE or INSTANTIATE purpose. */
    if (!prefer_tmpt)
        for (; l != 0; l=l->bindlistcdr)
        {   Binder *bb = l->bindlistcar;
            if (bindenv_(bb)) continue;         /* ignore specialized */
            if (equivtype(bindtype_(bb), t)) return bb;
        }

    /* try again for template memfn */
    for (l = bindftlist_(b); l; l = l->bindlistcdr)
    {   Binder *bb = l->bindlistcar;
        if (equivtype(bindtype_(bb), t)) return bb;
    }

    if (bindftlist_(b) != NULL &&
        bindparent_(bindftlist_(b)->bindlistcar) !=NULL)
    {   BindList *tmpts;
        ExprList *l = NULL;
        FormTypeList *ft = typefnargs_(t);
        for (; ft; ft = ft->ftcdr)
            l = mkExprList(l, (Expr *)gentempbinder(ft->fttype));
        l = (ExprList *)dreverse((List *)l);
        if ((tmpts = temp_reduce(NULL, l, NULL, b)) != NULL)
        {   Binder *ftemp = tmpts->bindlistcar, *fbind = NULL;
            ScopeSaver env = bindformals_(ftemp);
            bool has_failed = NO;
            TypeExpr *t = type_deduction(bindtype_(ftemp), l, bindactuals_(b), &env,
                                         YES, &has_failed);
            Binder *btop;
            DeclRhsList decl;
            SET_BITMAP stg;

            if (has_failed) syserr("type deduction failed: shouldn't happen");
            t = globalize_typeexpr(t);
            env = globalize_env(env);
            fixup_template_arg_type(t, env);
            fbind = global_mk_binder(NULL,
                         ovld_instance_name(ovld_tmptfn_instance_name(bindsym_(ftemp), env), t),
                                     bindstg_(ftemp), t);
            attributes_(fbind) |= attributes_(ftemp);
            bindstg_(fbind) |= b_undef;
            bindparent_(fbind) = bindparent_(ftemp);
            bindenv_(fbind) = env;
            /*typeovldlist_(bindtype_(b)) = (BindList *)
                global_cons2(SU_Type, typeovldlist_(bindtype_(b)), fbind);*/
            add_instance(fbind, &typeovldlist_(bindtype_(b)), NO);
            add_instance(fbind, &bindinstances_(ftemp), YES);
            decl.declname = ovld_add_memclass(bindsym_(fbind), bindparent_(fbind),
                                              (bindstg_(fbind) & b_memfns) != 0);
            stg = killstgacc_(bindstg_(fbind));
            if (stg & bitofstg_(s_static))
                stg = (stg & ~bitofstg_(s_static))|bitofstg_(s_extern);
            decl.declstg = stg;
            decl.decltype = (stg & b_memfna) ? memfn_realtype(t, bindparent_(fbind)) : t;
            btop = instate_declaration(&decl, TOPLEVEL);
            bindenv_(btop) = bindenv_(fbind);
            realbinder_(fbind) = btop;
            bindactuals_(b) = NULL;
            if (declflag & INSTANTIATE && !(bindstg_(ftemp) & b_undef))
            {   ScopeSaver temp, q;
                temp = q = tagactuals_(bindparent_(fbind));
                for (; q != NULL && bindcdr_(q) != NULL; q = bindcdr_(q));
                if (q != NULL) bindcdr_(q) = env; else temp = env;
                add_pendingfn(bindsym_(btop),
                              ovld_tmptfn_instance_name(bindsym_(ftemp), bindenv_(btop)),
                              t, bindstg_(btop), bindparent_(fbind),
                              temp, bindtext_(ftemp), bindenv_(btop), YES);
                if (q != NULL) bindcdr_(q) = NULL;
                bindstg_(fbind) &= ~b_undef;
            }
            return fbind;
        }
    }
    cc_err(syn_err_no_decl_at_type, b);
    return 0;
}

static void use_classname_typedef(TypeExpr *t)
{   /* Assert: isclasstype_(t)... */
    TagBinder *tb = typespectagbind_(t);
    /* If tb->tagparent != 0, the associated type name will be found in */
    /* scope tb->tagparent, unless tb is anonymous (gensym'd name).     */
    /* If tagparent is 0 and tb is not anonymous, then seek the nearest */
    /* binding, which <should> be found in the scope containing tb...   */
    /* Note that we <must> find a typename if there is one...           */
    Binder *b = isgensym(tagbindsym_(tb)) ? 0 :
        findbinding(tagbindsym_(tb), tb->tagparent, ALLSCOPES|FB_CLASSNAME);
    if (b) binduses_(b) |= u_referenced;
    if (!LanguageIsCPlusPlus) syserr("use_classname_typedef()");
}

static bool ispurefnconst(Expr *e)
{   /* Share the next tests with isnullptrconst()/move to sem.c?        */
    /* The present code allows "int f() = 0" but not "int f() = 0L" nor */
    /* "int f() = 1-1" as [ES] suggest.                                 */
    TypeExpr *t;
    return (h0_(e) == s_integer &&
            intval_(e) == 0 &&
            intorig_(e) == 0 &&
            h0_(t = princtype(type_(e))) == s_typespec &&
            typespecmap_(t) == bitoftype_(s_int));
}

/* Peter Armistead - Make it compile by losing the static */
#ifdef CALLABLE_COMPILER
SynBindList *reverse_SynBindList(SynBindList *x)
#else
static SynBindList *reverse_SynBindList(SynBindList *x)
#endif
{   SynBindList *p = 0;
    for (; x; x = x->bindlistcdr)
        p = mkSynBindList(p, x->bindlistcar);
    return p;
}

/* syn_copyscope() is expensive, but only called for labels/gotos.      */
/* We *are* removing it by removing some of the dreverses and nconcs.   */
static SynBindList *copy_SynBindList(SynBindList *x)
{   SynBindList *p = 0, *q = 0;
    if (debugging(DEBUG_SYN)) cc_msg("(");
    for (; x; x = x->bindlistcdr)
    {   SynBindList *t = mkSynBindList(0, x->bindlistcar);
        if (p == 0) p = q = t; else q->bindlistcdr = t, q = t;
        if (debugging(DEBUG_SYN)) cc_msg("$b", x->bindlistcar);
    }
    if (debugging(DEBUG_SYN)) cc_msg(")");
    return p;
}

static SynScope *syn_copyscope(SynScope *x)
{   SynScope *p = 0, *q = 0;
    if (debugging(DEBUG_SYN)) cc_msg("copy_scope[");
    for (; x; x = x->cdr)
    {   SynBindList *bl = copy_SynBindList(x->car);
        SynScope *t = mkSynScope(0, bl, x->scopeid);
        if (p == 0) p = q = t; else cdr_(q) = t, q = t;
    }
    if (debugging(DEBUG_SYN)) cc_msg("]\n");
    return p;
}

static Expr *unbind_dtor(SynScope *to, SynScope *from)
{   Expr *edtor = 0, *ector = 0;
    SynScope *s, *fromx = from, *tox = to;
    /* Find a common, but possibly copied, substring of from and to:    */
    /* Relies on scopeid(children) > scopeid(parent).                   */
    if (!LanguageIsCPlusPlus) return edtor;
    for (;;)
    {   if (fromx == 0) { tox = 0; break; }
        if (tox == 0) { fromx = 0; break; }
        if (fromx->scopeid == tox->scopeid) break;
        if (fromx->scopeid > tox->scopeid)
            fromx = fromx->cdr;
        else
            tox = tox->cdr;
    }
    for (s = to; s != tox; s = s->cdr)
    {   SynBindList *l;
        for (l = s->car; l; l = l->bindlistcdr)
        {   Binder *b = l->bindlistcar;
            if (attributes_(b) & A_DYNINIT /* && ector == 0 */ )
            {   /* one day do ctors for such, hence ector.              */
/* @@@ in particular setting b to undefined would improve liveness      */
/* calculations for branches into blocks!                               */
                ector = (Expr *)b;
/* next line is error to agree with Cfront 3.1                          */
                if (HasFeature(Feature_CFront) &&
                    !typehasctor(bindtype_(b)) &&
                    h0_(princtype(bindtype_(b))) != t_ref)
                    cc_warn(syn_rerr_jump_past_init, b);
                else
                    cc_rerr(syn_rerr_jump_past_init, b);
            }
        }
    }
    for (s = from; s != fromx; s = s->cdr)
    {   Expr *e = mkdtor_v_list(s->car);         /* @@@ backwards?      */
        /* next line is 'commacons'.                                    */
        edtor = edtor==0 ? e : e==0 ? edtor : mkbinary(s_comma, edtor, e);
    }
    return edtor;
}

static Cmd *cmd_rescope(SynScope *to, SynScope *from, Cmd *c)
{   Expr *edtor = unbind_dtor(to, from);
    if (edtor && h0_(edtor = optimise0(edtor)) != s_error)
    {   if (h0_(c) == s_return && cmd1e_(c) != 0)
        {   if (cur_structresult != 0)
                cmd1e_(c) = mkbinary(s_comma, cmd1e_(c),
                        mkcast(s_return, edtor, te_void));
            else
            {   Expr *e = cmd1e_(c);
                Expr *ee = (h0_(e) == s_return) ? arg1_(e) : e;
                TypeExpr *t = typeofexpr(ee);
                Binder *gen = gentempbinder(t);
                ee = mkbinary(s_init, (Expr *)gen, ee);
                ee = mkbinary(s_comma, ee, edtor);
                ee = mkbinary(s_comma, ee, (Expr *)gen);
                ee = mk_exprlet(s_let, t, mkSynBindList(0, gen), ee);
                /* may change type (in a harmless way)                  */
                ee = optimise0(ee);
                if (h0_(e) == s_return)
                    arg1_(e) = ee;
                else
                    cmd1e_(c) = ee;
            }
        }
        else
        {   FileLine fl; fl = c ? c->fileline : syn_invented_fl;
            c = mk_cmd_block(fl, 0,
                    mkCmdList(mkCmdList(0, c),
                        mk_cmd_e(s_semicolon, fl, edtor)));
        }
    }
    return c;
}

static void syn_setlab(LabBind *lab, SynScope *defscope)
{   /* Modifies code in forward-reference gotos to include dtors.       */
    SynGoto *ref = lab->labu.ref;
    lab->labu.def = syn_copyscope(defscope);
    for (; ref; ref = ref->cdr)
    {   Expr *edtor = unbind_dtor(defscope, ref->gotoscope);
        if (edtor)
        {   Cmd *c = ref->gotocmd;
            CmdList *cl = cmdblk_cl_(c);
            cmdcar_(cl) = mk_cmd_e(s_semicolon, c->fileline, optimise0(edtor));
        }
    }
}

static Cmd *syn_reflab(LabBind *lab, SynScope *s, Cmd *c)
{   if (lab->labuses & l_defined)
        c = cmd_rescope(lab->labu.def, s, c);
    else
    {   /* for goto-destructors -- updated by syn_setlab().             */
        c = mk_cmd_block(c->fileline, 0, mkCmdList(mkCmdList(0, c), 0));
/* The top-level copy of synscope is essential (avoids dtors of yet-to- */
/* -be-bound reftemps).  The rest is needed because of dreverses (q.v.) */
        lab->labu.ref = mkSynGoto(lab->labu.ref, c, syn_copyscope(s));
    }
    return c;
}

void push_exprtemp_scope(void)
{   if (temps == 0)
        temps = mkSynScope(0, 0, ++temps_scopeid);
    else
        temps = mkSynScope(temps, 0, ++temps_scopeid);
}

void pop_exprtemp_scope(void)
{   SynScope *prev = temps->cdr;
    if (temps == NULL)
        syserr("pop_exprtemp_scope: no exprtemp scope");
    discardSynScope(temps);
    temps = prev;
    --temps_scopeid;
}

Binder *genexprtemp(TypeExpr *t)
{   Binder *b = (bind_scope & TOPLEVEL) ?
        genglobinder(globalize_typeexpr(t)) : gentempbinder(t);
#ifdef CALLABLE_COMPILER
    dbgdata_(b, VoidStar) = (VoidStar)dbg_mk_formatpack(NULL, NULL);
#endif
    if (temps == NULL)
    {   /*/* surely this should be a syserr */
#if 0
        syserr("genexprtemp: no temp scope");
#else
        if (var_cc_private_flags & 65536)
            cc_msg("genexprtemp: called without a temp scope\n");
#endif
    }
    else
        temps->car = mkSynBindList(temps->car, b);
    return b;
}

static SynScope *saved_temps;

void push_saved_temps(int32 scopeid)
{   if (LanguageIsCPlusPlus)
        saved_temps = mkSynScope(saved_temps, 0, scopeid);
}

/* prepends the binders of the saved temps to bl */
SynBindList *pop_saved_temps(SynBindList *bl)
{   if (LanguageIsCPlusPlus)
    {   SynBindList *st = saved_temps->car;
        SynScope *prev = saved_temps->cdr;
        while (st)
        {   Binder *b = st->bindlistcar;
            bl = mkSynBindList(bl, b);
            st = st->bindlistcdr;
        }
        discardSynScope(saved_temps);
        saved_temps = prev;
        return bl;
    }
    else if (saved_temps != NULL)
        syserr("unexpected saved temps");
    return bl;
}

void add_expr_dtors(Expr *edtor)
{   if (edtor != NULL) expr_dtors = commacons(expr_dtors, edtor);
}

void add_to_saved_temps(SynBindList *tmps)
{   if (!saved_temps) syserr("no saved temps scope");
    for(; tmps != NULL; tmps = tmps->bindlistcdr)
        saved_temps->car = mkSynBindList(saved_temps->car, tmps->bindlistcar);
}

Expr *killexprtemp()
{   Expr *edtor = 0;
    SynBindList *t;

    if (temps == 0)
    {   /*/* surely this should be a syserr */
#if 0
        syserr("genexprtemp: no temp scope");
#else
        if (var_cc_private_flags & 65536)
            cc_msg("killexprtemp: no temps scope\n");
#endif
    }
    else
    {   t = temps->car;
        while (t != 0 && saved_temps)
        {   Binder *b = t->bindlistcar;
            edtor = commacons(edtor, mkdtor_v((Expr *)b));
            saved_temps->car = mkSynBindList(saved_temps->car, b);
            t = t->bindlistcdr;
        }
        pop_exprtemp_scope();
    }
    return (edtor == 0) ? 0 : optimise0(edtor);
}

/* Note that these following routine is declared in bind.h (!!).        */
Binder *genreftemp(TypeExpr *t)
{   /* the test below may be made more generous so we can deal more     */
    /* effectively with f() { extern foo(); ... } etc.                  */
    Binder *b = (bind_scope & TOPLEVEL) ?
        genglobinder(globalize_typeexpr(t)) : gentempbinder(t);
#ifdef CALLABLE_COMPILER
    dbgdata_(b, VoidStar) = (VoidStar) dbg_mk_formatpack(NULL, NULL);
#endif
    /* in flux: */
    if (synscope)
        synscope->car = mkSynBindList(synscope->car, b);
    else
        syn_reftemps = mkSynBindList(syn_reftemps, b);
    return b;
}

int killnexprtemp(Binder *b)
{   if (temps)
    {   SynBindList *bl, **blp = &temps->car;
        for (bl = *blp;  bl != 0;  bl = *(blp = &bl->bindlistcdr))
            if (bl->bindlistcar == b)
            {   *blp = bl->bindlistcdr;
                return 1;
            }
    }
    return 0;
}

int killreftemp(Binder *b)
{   SynBindList *bl, **blp = synscope ? &synscope->car : &syn_reftemps;
    for (bl = *blp;  bl != 0;  bl = *(blp = &bl->bindlistcdr))
        if (bl->bindlistcar == b)
        {    *blp = bl->bindlistcdr;
             return 1;
        }
    return 0;
}

static Expr *rd_cppcast(void)
{   /* C++ casts of the form  type(e1,...,en)                           */
    /* return 0 to indicate absence of '( after the type.               */
    TypeSpec *t;
    AE_op s = (AE_op)(curlex.sym & ~s_qualified);

/*/* @@@ Need to add wchar_t to this list...                            */
    if ((s == s_char || s == s_short || s == s_signed || s == s_int ||
         s == s_long || s == s_float || s == s_double || s == s_unsigned ||
         s == s_bool || s == s_float || s == s_identifier) &&
         peepsym() == s_lpar)
    {   ExprList *l;
        t = rd_typename(SIMPLETYPE);
        nextsym();
        l = rd_exprlist_opt();
/* There is an ambiguity in the semantics of the 'type(e1,...,en)'      */
/* construct which means that this code does not share with mkcast().   */
/* Consider:    class A { A(B&); }; class B { operator A(); };          */
/*              ...; A a; B b; ...; a = b;                              */
/* This is ambiguous as to whether a = A::A(b) or a = b.operator A()    */
/* is meant.  This is presumably also true for a = (A)b;                */
/* However, it seems plausible that a = A(b) can ONLY have the former   */
/* meaning (conversion by constructor).                                 */
/* Hence we take all such calls to mean conversion by constructor.      */
/* (the alternative would be to pass all 1-argument calls to mkcast     */
/* by swapping the following two tests.                                 */
        if (typehasctor(t)) return mkctor_t(t, l);
        if (l && !cdr_(l)) return mkcast(s_cast, exprcar_(l), t);
        if (l == 0)
        {   TypeExpr *pt = princtype(t);
            if (h0_(pt) == t_ref || h0_(pt) == t_content)
                return mkintconst(t, 0, 0);
            if (issimpletype_(pt))
                return mkcast(s_init, lit_zero, t);
            t = pt;
        }
        if (!istypevar(t)) cc_err(syn_err_lacks_arg_ctor, t, (long)length(l));
        return errornode;
    }
    return 0;
}

/* The following mirrors rd_declrhslist()...                            */
/* But should it be in bind.c?                                          */
/* Yes, but only if we get rid of the FileLine's.                       */
static Binder *instate_classname_typedef(TagBinder *tb, int declflag)
{   DeclRhsList *d = mkDeclRhsList(bindsym_(tb), tagbindtype_(tb),
            bitofstg_(s_typedef)|u_implicitdef);
    Binder *b;
    FileLine fl;  fl = curlex.fl;
    fl.p = dbg_notefileline(fl);
    d->fileline = fl;
    if ((declflag & MEMBER) && (tb->tagparent != 0))
    {   d->declstg |= stgaccof_(access);
        b = instate_member(d, bind_scope);
    }
    else
    {   b = instate_classname(d, tb);
        if (b != NULL &&  usrdbg(DBG_PROC))
            dbg_type(bindsym_(b), bindtype_(b), d->fileline);
    }
    /* propagate linkage attributes from type to typename... */
    /* @@@ Danger of collision with attribofstgacc_() */
    if (b != NULL)
        attributes_(b) |= attributes_(tb) & (A_NOLINKAGE+A_INTERN+A_EXTERN);
    return b;
}

static void instate_anonu_members(int declflag, Binder *b)
{   ClassMember *l = tagbindmems_(typespectagbind_(bindtype_(b)));
    for (; l != NULL; l = memcdr_(l))
    {   Symstr *sv = memsv_(l);
        if (h0_(l) == s_tagbind) continue;
        if (h0_(l) != s_member || sv == 0)
            cc_rerr(syn_rerr_illegal_anon_union_mem, sv);
        else
        {   TypeExpr *t = memtype_(l);
            DeclRhsList *d = mkDeclRhsList(sv, t, 0);
            Binder *db;
            if ((attributes_(l) & ACCESSBITS) != bitofaccess_(s_public))
                cc_rerr(syn_rerr_illegal_nonpub_anon_union_mem, sv);
            if (declflag & MEMBER)
            {   d->declstg = (attributes_(b) & ACCESSBITS) <<
                    28-shiftoftype_(s_union+1);  /* @@@ stgaccof_(...) */
                db = instate_member(d, bind_scope);
                membits_(db) = membits_(l);
            }
            else
                db = instate_declaration(d, declflag);
            attributes_(db) |= CB_ANON;
            realbinder_(db) = b;
        }
    }
}

/* rationalise next code with caller.                               */
/* there are also similarities with mkopap().                       */
static Binder *syn_binderofname(Symstr *sv, TagBinder *optclass)
{       Binder *b;
        if (sv == 0) syserr("syn_binderofname");
/* @@@ if s_qualified then curlex_binder should already hold!           */
/* Hmm, the above comment taken from rd_idexpr().  It applies to        */
/* the call from cfe/syn.c but not from new/delete below.               */
        b = optclass == NULL ? NULL : findbinding(sv, optclass, INDERIVATION);
        if (b == NULL && (b = findbinding(sv, NULL, FB_GLOBAL)) == NULL)
            syserr("syn_binderofname '%s'", symname_(sv));
        else if (h0_(b) != s_binder)
            syserr("non fn operator member '%s'", symname_(sv));
        else if (bindstg_(b) & bitofstg_(s_typedef))
            syserr("operator typedef '%s'", symname_(sv));
        return b;
}

static Cmd *conditionalised_delete(Binder* thisb, Binder* isdelb, TagBinder *parent)
{   Binder *delgeneric = syn_binderofname(cppsim.xdel, parent);
    Expr *magic_test = optimise0(mkbinary(s_notequal,
#ifdef CFRONT_COMPATIBLE_DESTRUCTORS
        /* testing '(is_delete & 1) != 0' instead of 'is_delete != 0'   */
        /* creates destructors that Cfront-built code can call (if      */
        /* there is no muliple inheiritance).  The code is the same     */
        /* size on the ARM.                                             */
                                          mkbinary(s_and, (Expr *)isdelb,
                                                   lit_one),
#else
                                          (Expr *)isdelb,
#endif
                                          lit_zero));
    ExprList *delargs = 0;
    Expr *e;
    binduses_(isdelb) |= u_referenced;
    if (is_two_arg_delete(delgeneric))
        delargs = mkExprList1(mkintconst(te_size_t,
                     sizeoftype(typearg_(typeofexpr((Expr *)thisb))), 0));
    delargs = mkExprList(delargs, (Expr*)thisb);
    e = mkfnap((Expr *)delgeneric, delargs);
    return mk_cmd_if(curlex.fl, magic_test,
                     mk_cmd_e(s_semicolon, curlex.fl, optimise0(e)), 0);
}

/* Move to aeops.h (can be done via bit twiddle)...                     */
#define ispostop_(op) ((op) == s_postinc || (op) == s_postdec)

/* We treat operator->() as a monadic op -- see [ES, p337].             */
static Expr *cpp_mkunaryorop(AEop op, Expr *x)
{   TypeExpr *tx = typeofexpr(x);
    TagBinder *bx;
    if (is_dependent_type(tx)) return errornode;
    bx = isclassenumorref_type(tx);
    if (bx)
    {   /* [ES, p338] say that postfix ++/-- gets an 2nd param of 0.    */
        Expr *r = mkopap(op, bx, x,
                         ispostop_(op) ? mkExprList1(lit_zero) : NULL);
        if (r)
        {   if(h0_(r) != s_operator)
            {   if (op != s_arrow) return r;
                if (bx == isclassenumorref_type(typeofexpr(r)))
                {   cc_err(syn_err_recursive_app_operator_arrow, bx);
                    return errornode;
                }
                else return cpp_mkunaryorop(op,r);
            }
            x = user_conversion(x, bx, (TypeExpr *)((List3 *)r)->car);
            discard3(r);
        }
    }
    return op == s_arrow ? x : mkunary(op, x);
}

Expr *cpp_mkbinaryorop(AEop op, Expr *x, Expr *y)
{   TypeExpr *tx = typeofexpr(x);
    TypeExpr *ty = typeofexpr(y);
    TagBinder *bx, *by;

    if (is_dependent_type(tx) || is_dependent_type(ty))
        return errornode;
    bx = isclassenumorref_type(tx);
    by = isclassenumorref_type(ty);
    if (op != s_dotstar && (bx || by))
    {   Expr *r = mkopap(op, bx, x, mkExprList1(y));
        if (r)
        {   if (h0_(r) != s_operator) return r;
            x = user_conversion(x, bx, (TypeExpr *)((List3 *)r)->car);
            y = user_conversion(y, by, (TypeExpr *)((List3 *)r)->csr);
            discard3(r);
        }
        else if (op == s_assign && bx && (tagbindbits_(bx) & TB_HASCMEM))
        /* should really complained about const member, new error msg? */
            cc_rerr(syn_err_not_found_named_member, assignsym, bx);
    }
    return mkbinary(op, x, y);
}

static Expr *cpp_mkfnaporop(Expr *e, ExprList *l)
{   TypeExpr *te = typeofexpr(e);
    TagBinder *be;
    if (is_dependent_type(te)) return errornode;
    be = isclassenumorref_type(te);
    if (te)
    {   /* [ES, p355] require operator() to be a member fn.  We don't.  */
        Expr *r = mkopap(s_fnap, be, e, l);
        if (r)
        {   if (h0_(r) != s_operator) return r;
        }
    }
    return mkfnap(e, l);
}

/* Calculate from inside so that any variable will be at the top.       */
static TypeExpr *new_basetype(TypeExpr *t, Expr **nelts)
{   t = princtype(t);
    if (h0_(t) == t_subscript)
    {   Expr *size = typesubsize_(t);
        t = new_basetype(typearg_(t), nelts);
/* The next error message is borrowed from sem.c(sizeoftype).           */
        if (size == 0) cc_rerr(sem_rerr_sizeof_array);
        else if (*nelts == 0) *nelts = size;
        else *nelts = mkbinary(s_times, *nelts, size);
        return t;
    }
    if (!isclasstype_(t))
    {   *nelts = mkintconst(te_size_t, sizeoftype(t), 0);
        return 0;
    }
    else
    {   *nelts = 0;
        return t;
    }
}

static Expr *rd_new(AEop op)
{   TypeExpr *t, *newt;
    Binder *newgeneric;
    ExprList *placement = 0, *init = 0;
    Expr *nelts;
    bool forceglobal = NO;
    nextsym();
retry:  if (curlex.sym == s_lpar)
    {   nextsym();
        rd_cpp_name(0);     /* don't know if type or expr yet */
        if (placement != 0 ||
            (isdeclstarter2_(curlex) &&
                (peepsym() != s_lpar || is_type_id())))
        {   t = rd_typename(FLEX_TYPENAME);
            checkfor_ket(s_rpar);
        }
        else
        {   placement = rd_exprlist_opt();
            /* fault '()' above as Type, so opt() doesn't happen.   */
            goto retry;
        }
    }
    else t = rd_typename(NEW_TYPENAME);
    newt = prunetype(t);
    t = new_basetype(t, &nelts);
    if (curlex.sym == s_lpar)
    {   nextsym();
/* @@@ we need to allow '{}' form inits in the following soon.          */
        init = rd_exprlist_opt();
        if (init && h0_(newt) == t_subscript)
            cc_err(syn_err_ignored_new_array_ctor), init = 0;
    }
    if (t == 0)
        newgeneric = syn_binderofname(cppsim.xnew, 0);
    else
    {   newgeneric = syn_binderofname(cppsim.xnew, typespectagbind_(t));
/* /* should we really check 'op new' access for '::new T' and '::new T[n]'?    */
        forceglobal = (op & s_qualified) && bindparent_(newgeneric) != 0;
        if ((op & s_qualified) || nelts)
            newgeneric = syn_binderofname(cppsim.xnew, 0);
    }
    return mknew(newt, t, newgeneric, nelts, placement, init, forceglobal);
}

static Expr *rd_delete(AEop op)
{   Expr *e;
    TypeExpr *t;
    bool isarray = NO;
    nextsym();
/* call __dl(p) for delete p/delete [] p; where p is not ptr-to-class.  */
/* call __dl_v(p,eltsize,dtor) for delete[]p; where p is ptr-to-class.  */
    if (curlex.sym == s_lbracket)
    {   isarray = YES;
        nextsym();
        if (curlex.sym != s_rbracket)
        {   if (HasFeature(Feature_CFront))
                cc_warn(syn_rerr_delete_expr_anachronism);
            else
                cc_rerr(syn_rerr_delete_expr_anachronism);
            (void)rd_expr(PASTCOMMA);
        }
        checkfor_ket(s_rbracket);
    }
    e = rd_prefixexp(NOLABEL);
    /* disallow int a[5]; delete a; */
    if (h0_(princtype(typeofexpr(e))) == t_subscript)
    {   cc_err(syn_err_requires_pntr_arg, s_delete);
        return errornode;
    }
    if (h0_(e = coerceunary(e)) == s_error) return e;
    t = princtype(typeofexpr(e));
    if (h0_(t) != t_content)
    {   cc_err(syn_err_requires_pntr_arg, s_delete);
        return errornode;
    }
    t = princtype(typearg_(t));
    if (isclasstype_(t) &&
        !(tagbindbits_(typespectagbind_(t)) & TB_DEFD))
        cc_warn(xsyn_warn_delete_undef, typespectagbind_(t));
    {   Expr *temp;
        bool forceglobal = NO;
        Binder *delgeneric;
        t = isprimtype_(t, s_void) ? te_void : new_basetype(t, &temp);
        if (t == 0)
            delgeneric = syn_binderofname(cppsim.xdel, 0);
        else
        {   delgeneric = syn_binderofname(cppsim.xdel, typespectagbind_(t));
/* /* should we really check 'op delete' access for '::delete T' and '::delete T[n]'?   */
            forceglobal = (op & s_qualified) && bindparent_(delgeneric) != 0;
            if ((op & s_qualified) || isarray)
                delgeneric = syn_binderofname(cppsim.xdel, 0);
        }
        return mkdelete(e, t, isarray, delgeneric, forceglobal);
    }
}

static Expr *rd_cpp_prefixextra(AEop op)
{
    switch (op)
    {
case s_new:    case s_qualified+s_new:
        /* maybe s_qualified (by top-level only).                       */
        return rd_new(op);
case s_delete: case s_qualified+s_delete:
        /* maybe s_qualified (by top-level only).                       */
        return rd_delete(op);
case s_throw:
        {   Expr *a;
            nextsym();
            /* use same binding as sizeof xxx for throw xxx.            */
            a = isexprstarter(curlex.sym) ? rd_prefixexp(NOLABEL) : 0;
            return a; /*will be something like mkthrow(syn_invented_fl, a);*/
        }
default:
        syserr("rd_cpp_prefixextra()");
    }
    return errornode;
}

#if 0
/* C++ for's (i.e. of the form  "for (decl; exp; exp) cmd") are nasty   */
/* and presumably subject to change -- Ellis and Stroustrup require     */
/* the scope of decl to be the rest of the block: simulate this.        */
/* Draft std of 28-April-1995 said scope of decl extends to end of the  */
/* for-statement.                                                       */
static Cmd *rd_cplusplus_for(FileLine fl)
{ synscope = mkSynScope(synscope, 0, ++synscopeid);
  { DeclRhsList *d = rd_decl2(BLOCKHEAD, 0), *dp;  /* is BLOCKHEAD right?  */
    SynBindList *dd;
    Expr *e1 = 0, *edtor;
    CmdList *cp, *cq;
/* The following code to perform initialisation is turned into a        */
/* s_comma Expr (this allows exploitation of for-init code in cg.c      */
/* for constant propagation) but similar code in rd_block() uses Cmd!!  */
    for (dp = d; dp != 0; dp = dp->declcdr)     /* add dynamic inits    */
    {   Expr *einit = declinit_(dp);            /* see genstaticparts() */
        if (einit)
        {   if (debugging(DEBUG_SYN)) cc_msg("[Init]");
            e1 = e1 ? mkbinary(s_comma, e1, einit) : einit;
        }
    }
    e1 = e1 ? optimise0(mkcast(s_for, e1, te_void)) : 0;
    if (curlex.sym == s_nothing) nextsym();     /* tidy after rd_decl2. */
    cp = cq = mkCmdList(0, rd_for_2(e1,fl));
#if NEVER
    synscope->car = mkSynBindList_from_Decl(d, synscope->car);
#endif
    if (curlex.sym == s_nothing) nextsym();
    while (curlex.sym != s_rbrace &&               /* not end of scope */
           curlex.sym != s_eof)                    /* not botched eof */
    {   CmdList *ct = mkCmdList(0, rd_command(1));
        if (curlex.sym == s_nothing) nextsym();
        cdr_(cq) = ct, cq = ct;
    }
    dd = synscope->car; synscope = synscope->cdr;
    pop_scope(scope_level);
    edtor = mkdtor_v_list(dd);
    if (edtor)
    {   /* just what is the right FileLine for a dtor?                  */
        CmdList *ct = mkCmdList(0, mk_cmd_e(s_semicolon, fl,
                                            optimise0(edtor)));
        if (cp == 0) cp = cq = ct; else cdr_(cq) = ct, cq = ct;
    }
    return mk_cmd_block(fl, reverse_SynBindList(dd), cp);
  }
}
#endif

static Expr *rd_declrhs_exec_cpp(DeclRhsList *d, int* initflag)
{   TypeExpr *dtype = d->decltype, *elmtype;
    Expr* init = 0;
    if (typehasctor(dtype))
    {   if (curlex.sym == s_assign)
        {   nextsym();
            if (curlex.sym == s_lbrace)
            {   cc_err(syn_err_constructor_init, d->declname);
                syn_initdepth = 0, syn_initpeek = 0, (void)syn_rdinit(0,0,4);
            }
            else
            {   Expr *einit = rd_expr(UPTOCOMMA);
                /* this cast keeps 12p3p1b.c from breaking */
                einit = mkcast(s_init, einit, d->decltype);
                if (h0_(einit) != s_error)
                    init = cpp_mkbinaryorop(s_init,
                        (Expr *)d->declbind, einit);
            }
            *initflag = 3;
        }
        else
        {   init = mkctor_v((Expr *)d->declbind, 0);
            *initflag = 3;
        }
    }
    else
    /* initialising an array of class */
    if (isarraytype(dtype, &elmtype) && typehasctor(elmtype))
    {   if (curlex.sym == s_assign)
        {   int32 i, upb, note;
            TypeExpr *t = ptrtotype_(elmtype);
            nextsym();
            /* @@@ botch to error recovery? */
            syn_initdepth = 0;
            note = syn_begin_agg();
 #define OPEN_ARRAY_SIZE 0xffffff
            upb = (typesubsize_(dtype) && h0_(typesubsize_(dtype)) != s_binder) ?
                        evaluate(typesubsize_(dtype)) : OPEN_ARRAY_SIZE;
            for (i = 0; i < upb; ++i)
            {   Expr *thisp, *init = NULL;

                if (syn_canrdinit())
                    init = rd_expr(UPTOCOMMA);
                else
                {   if (upb == OPEN_ARRAY_SIZE)
                    {   if (i)
                            typesubsize_(bindtype_(d->declbind)) =
                                        globalize_int(i);
                        break;
                    }
                }
                thisp = mk_expr2(s_plus, t,
                            mk_expr1(s_addrof, t, (Expr *)datasegment),
                                mkintconst(te_int, get_datadesc_size(), 0));
                /* initializing value may not have the right type */
                if (init != NULL) init = mkcast(s_init, init, elmtype);
                if (init == NULL || h0_(init) != s_error)
                {   TagBinder *cla = typespectagbind_(elmtype);
                    Expr *einit = init == NULL ?
            mkfnap(mkfieldselector(s_arrow, thisp,
                        findbinding(ctorsym, cla, INCLASSONLY)), 0) :
            cpp_mkbinaryorop(s_init, mkunary(s_content, thisp), init);
                    init = init == 0 ? einit :
                            mkbinary(s_comma, init, einit);
                }
                gendc0(sizeoftype(elmtype));
                if (curlex.sym == s_comma) nextsym();
            }
            *initflag = 3;
            syn_end_agg(note);
        }
        else
        {   init = mkctor_v((Expr *)d->declbind, 0);
            if (init) binduses_(d->declbind) |= u_referenced;
            *initflag = 3;
        }
    }
    else if (!(d->declstg & bitofstg_(s_auto)) &&
             curlex.sym == s_assign && (issimpletype_(princtype(dtype)) ||
                                        istypevar(dtype)))
    {   nextsym();
        init = syn_rdinit(dtype, d->declbind, 0);
        *initflag = 1;
    }
    return init;
}

static TypeExpr *fixup_special_member(Symstr *name, TypeExpr *giventype,
                      TypeExpr *fnrtype, TagBinder *scope, SET_BITMAP stg)
{   /* cc_msg("fixup_special_member $r\n", name); */
/* Note that special members (ctors/dtors &c) cannot have result types  */
/* and hence we don't have to check for s_typedef with prunetype().     */
/* But we do it to catch 'typedef void F(); struct T { F T; };' */
    TypeExpr *pt = princtype(giventype);
    if (h0_(pt) == t_fnap && !(stg & bitofstg_(s_typedef)))
    {   bool msg = 0;
        TypeExpr *pta;
        FormTypeList *f = 0;
        SET_BITMAP quals = typeptrmap_(pt);
        if (name == ctorsym)
        {   f = typefnargs_(pt);
            if (f && minargs_(pt) <= 1 && 1 <= maxargs_(pt))
            {   TypeExpr *t = princtype(f->fttype);
                if (isclasstype_(t) && typespectagbind_(t) == scope)
                {   cc_rerr(syn_rerr_self_copying_ctor, scope);
                    msg = 1;
                    f = mkFormTypeList(f->ftcdr, f->ftname,
                                       mk_typeexpr1(t_ref, f->fttype, 0),
                                       f->ftdefault);
                }
            }
        }
        else if (typefnargs_(pt) != NULL)
            cc_rerr(xsyn_rerr_zero_params, scope, name);
        else if (name != dtorsym)
        {   /* conversion operator */
            if (scope == 0 || (stg & bitofstg_(s_static)))
                cc_rerr(xsyn_rerr_non_memfn_operator, scope, name);
            else if (equivtype(fnrtype, te_void))
                cc_rerr(xsyn_rerr_bad_conv, scope, name);
        }
        if (!msg
            && !((typefnaux_(pt).flags & f_norettype) &&
                 h0_(pta = typearg_(pt)) == s_typespec &&
                 typespecmap_(pta) == bitoftype_(s_int)))
            cc_rerr(xsyn_rerr_no_return_type_allowed, scope, name);
    /* Make ctor's return their 'this' arg. */
        /* @@@ This syserr happens for broken input like
           'struct X { int f(); }; X::X() { }' needs fixing */
        if (name == ctorsym)
        {   if (scope == 0) syserr("fix up ctor:  scope == 0");
            fnrtype = ptrtotype_(tagbindtype_(scope));
        }
        return mkTypeExprfn(t_fnap, fnrtype, quals, f, &typefnaux_(pt));
    }
    else
        cc_rerr(xsyn_rerr_must_be_function, scope, name);
    return giventype;
}

static void memfn_typefix(DeclRhsList *d, TagBinder *scope)
{   TypeExpr *fntype = prunetype(d->decltype);
    if (h0_(fntype) != t_fnap || scope == 0)
        syserr("memfn_typefix");
    if (strncmp(symname_(d->declname), "__dt", 4) == 0)
        fntype = add_delete_arg(fntype, NO);
    d->decltype = memfn_realtype(fntype, scope);
}

static ClassMember *nconc_member(ClassMember *list, ClassMember *member)
{   ClassMember *q = list;
    if (q == NULL) return member;
    for (;;)
    {   if (equivtype(memtype_(q), memtype_(member)))
        {   TypeExpr *t = memtype_(q);
            TagBinder *b;
            if (h0_(t) == t_content) t = typearg_(t);
            b = typespectagbind_(t);
            if (tagbindbits_(b) & TB_CORE) b = b->tagparent;
            cc_rerr(syn_rerr_duplicated_base, b);
            return list;
        }
        if (memcdr_(q) == NULL) break;
        q = memcdr_(q);
    }
    memcdr_(q) = member;
    return list;
}

static ClassMember *clone_member(ClassMember *p, SET_BITMAP attributes)
{   ClassMember *q = (ClassMember *)
        memcpy(GlobAlloc(SU_Other,(int32)SIZEOF_CLASSMEMBER),
               p, (size_t)SIZEOF_CLASSMEMBER);
    memcdr_(q) = NULL;
    attributes_(q) = attributes & ~A_LOCALSTORE | A_GLOBALSTORE;
    return q;
}

#define DONT_COPY ((SET_BITMAP)-1)

static ClassMember *append_no_dups(ClassMember *mem, SET_BITMAP attributes,
        ClassMember *list)
{   ClassMember *q, *prev = NULL;
    for (q = list;  q != NULL;  prev = q, q = memcdr_(q))
        if (equivtype(memtype_(q), memtype_(mem)) == 2) return list;
    if (attributes == DONT_COPY)
        q = mem;
    else
        q = clone_member(mem, attributes);
    if (list == NULL) list = q; else memcdr_(prev) = q;
    return list;
}

static ClassMember *append_vbases_of(TagBinder *base_tag,
        SET_BITMAP attributes, ClassMember *list)
{   ClassMember *p = tagbindmems_(base_tag);

    if (p != NULL && (attributes_(p) & CB_CORE))
        for (p = memcdr_(p); p && (attributes_(p) & CB_VBASE); p = memcdr_(p))
            list = append_no_dups(p, attributes, list);
    return list;
}

#ifdef DEBUG_CLASS
static void print_classdecl(ClassMember *list, int indent)
{   ClassMember *p;
    for (p = list;  p != NULL;  p = memcdr_(p))
    {   printf("  %*s%s\n", indent, "", memsv_(p)->symname);
        if (isclasstype_(memtype_(p)))
        {   printf("    %*s{%s}\n", indent, "",
                typespectagbind_(bindsym_(memtype_(p)))->symname);
            print_classdecl(
                typespectagbind_(memtype_(p))->tagbindmems, indent+4);
        }
    }
}
#endif  /* DEBUG_CLASS */

#define is_purevirtual(l)       (bindstg_(l) & b_purevirtual)
static bool chk_abstractness(TagBinder *cl, List *derivation)
{   ClassMember *l;
    TagBinder *tb;

    for (l = tagbindmems_(cl); l != NULL; l = memcdr_(l))
    {   SET_BITMAP bm = attributes_(l);
        if (h0_(l) == s_tagbind) continue;
        tb = typespectagbind_(memtype_(l));
        if (bm & CB_CORE)
        {   if (chk_abstractness(tb, (List *)syn_cons2(derivation, tb))) return YES;
        }
        else if (bm & CB_BASE)
        {   if (tagbindbits_(tb) & TB_ABSTRACT)
            if (chk_abstractness(tb, (List *)syn_cons2(derivation, tb))) return YES;
        }
        else
        {   if (is_purevirtual(l))
            {    List *d;
                 for (d = derivation; d != 0; d = d->cdr)
                 { Binder *b = findbinding(bindsym_(l), (TagBinder *)d->car, INCLASSONLY);
                   if ((b != 0) && (b != l)) break;
                 }
                 if (d == 0) return YES;
             }
        }
    }
    return NO;
}

static void rd_classdecl(TagBinder *b)
{   ClassMember *vbase_members = NULL, *base_members = NULL;
    SET_BITMAP bitsinherit = 0;
    if (curlex.sym == s_colon)
    {   nextsym();
        if (typespecmap_(tagbindtype_(b)) & bitoftype_(s_union))
            cc_rerr(syn_rerr_union_w_base);
        for (;;)
        {   SET_BITMAP access = 0;
            bool is_virtual = 0;
            TypeExpr *pt = NULL;
            TagBinder *base_tag = 0;
            for (;;)
            {  if (curlex.sym == s_virtual && !is_virtual)
               {   is_virtual = 1;
                   bitsinherit |= TB_HASVBASE;
               }
               else if (isaccessspec_(curlex.sym) && access == 0)
/* [ES] has 'protected' allowed syntactically, but offers no meaning!   */
                   access = bitofaccess_(curlex.sym);
               else break;
               nextsym();
            }

            rd_cpp_name(0);
            if (curlex.sym != s_identifier)
            {   cc_err(syn_err_missing_basetag);
                while (curlex.sym != s_lbrace &&
                       curlex.sym != s_comma) nextsym();
            }
            else if (curlex_typename == 0 ||
                     (typespecmap_(pt=princtype(bindtype_(curlex_typename))) &
                      (bitoftype_(s_struct)|bitoftype_(s_class))) == 0 ||
                     !(tagbindbits_(base_tag = typespectagbind_(pt)) &
                       TB_DEFD))
            {   if (pt != NULL && h0_(pt) == t_unknown)
                {   typespecmap_(pt) |= bitoftype_(s_class)|bitoftype_(s_struct);
                    if (curlex_typename == NULL) syserr("base type $t", pt);
                    binduses_(curlex_typename) |= u_referenced;
                }
                else if (base_tag && tagprimary_(base_tag) &&
                         (tagbindbits_(tagprimary_(base_tag)) & TB_DEFD) &&
                         !(tagbindbits_(base_tag) & TB_DEFD))
                {   syn_implicit_instantiate(tagprimary_(base_tag), base_tag);
                    goto base_tag_member;
                }
                else
                {   if (!base_tag) base_tag = mk_tagbinder(curlex.a1.sv, s_struct);
                    cc_err(syn_err_undef_basetag, base_tag);
                }
                nextsym();
            }
            else if (!(tagbindbits_(base_tag) & (TB_DEFD|TB_UNDEFMSG)))
            {   cc_err(syn_err_undef_basetag, base_tag);
                tagbindbits_(base_tag) |= TB_UNDEFMSG;
                nextsym();
            }
            else
base_tag_member:
            {   TypeExpr *t = core_type(base_tag);
                ClassMember *m;
                if (access == 0)
                {  if (tagbindbits_(b) & bitoftype_(s_class))
                    {   cc_warn(xsyn_warn_implicit_private_base, base_tag);
                        access = bitofaccess_(s_private);
                    }
                    else
                        access = bitofaccess_(s_public);
                }
                m = mk_member(base_tag, t, access |
                              (is_virtual ? CB_VBASE : CB_BASE), b);
                vbase_members = append_vbases_of(base_tag, access|CB_VBASE,
                                                 vbase_members);
                if (is_virtual)
                {   vbase_members = append_no_dups(m, DONT_COPY, vbase_members);
                    m = mk_member(base_tag, ptrtotype_(t), access|CB_VBPTR, b);
                }
                bitsinherit |= tagbindbits_(base_tag);
                base_members = nconc_member(base_members, m);
                nextsym();
            }
            if (curlex.sym != s_comma) break;
            nextsym();
        }
    }
/* We presume an abstractly-based class is abstract until this is       */
/* disproved.   Is this right/moral?                                    */
/* !!!! Not any more !!!! (29.6.94) FW                                  */
/* Logic: inherit abstractness in class C:A { ... } but don't fault     */
/* member/friend fns in '...' with C as arg/result until reach '}'.     */
/* Also flag need vtable if vfn members (later) or any base needs one.  */
    tagbindbits_(b) |= bitsinherit & TB_HASVTABLE;
    checkfor_ket(s_lbrace);
/* The organisation of a class is:                                         */
/*      base-member base-member... base-member member member ... member    */
/* or   core-member virtual-base virtual-base ... virtual-base             */
/* where core-member contains:                                             */
/*      base-member base-member... base-member member member ... member.   */
/* Note that the 2nd arg below has direct bases.  It also has direct and   */
/* INDIRECT virtual bases.  Beware use for 'access-spec' in rd_strdecl.    */
    rd_strdecl(b, mk_core_part(b, base_members, vbase_members));
    if (!(tagbindbits_(b) & TB_ABSTRACT) &&
         chk_abstractness(b, (List *)syn_cons2(0, b)))
      tagbindbits_(b) |= TB_ABSTRACT;
/* @@@ probably we wish to add a static vfntable here, but sadly the    */
/* scope has been closed by rd_strdecl().  Think.                       */
/* @@@@@@@@@@@ not any more!                                            */
#ifdef DEBUG_CLASS
    print_classdecl(base_members, 0);
#endif
}


static void rd_access_adjuster(TagBinder *b, AEop access)
{
/* Assert: (curlex.sym == s_qualified+s_identifier ||                   */
/*          curlex.sym == s_qualified+s_pseudoid)                       */
/*      && (curlex_typename != 0 || curlex_path != 0)                   */
/*      && (peepsym() in {s_semicolon, s_comma, s_rbrace})              */

    ClassMember *basemem;


/* Access declarations must refer to a base class... */
/* @@@ but is it a direct or indirect base?          */

    if (curlex_scope == NULL ||
        (basemem = derived_from(curlex_scope, b)) == NULL)
        cc_rerr(syn_rerr_not_base(curlex_scope, b));
/* Access declarations may only occur in a public or protected part... */
    else if (access == s_private)
        cc_rerr(syn_rerr_badly_placed_access);
/* Finally, an access declaration may not vary base access rights...   */
    else if (accessOK == 1)
    {   if (attributes_(basemem) & bitofaccess_(s_public))
        {   /* publicly derived */
/* Warn of vacuously useless declarations and fault all others...      */
            if (attributes_(curlex_member) & bitofaccess_(access))
                cc_warn(syn_warn_modify_access);
            else
                cc_rerr(syn_rerr_modify_access);
        }
        else
        {   /* privately derived... */
/* Fault attempts to grant access greater or less than base access...  */
            if ((attributes_(curlex_member) & bitofaccess_(access)) == 0 &&
                (access == s_protected ||
                ((attributes_(curlex_member) & bitofaccess_(s_public)) == 0)))
                cc_rerr(syn_rerr_modify_access);
            else
            {   Symstr *sv = memsv_(curlex_member);
                Binder *bm = findbinding(sv, b, INCLASSONLY);
                if (bm != NULL)
                    cc_rerr(syn_rerr_duplicate_member(bm));
                else
                {   Binder *bm = findbinding(sv, b, INDERIVATION);
                    TypeExpr *bmt = bindtype_(bm);
                    BindList *l;
                    DeclRhsList *d;
                    if ((l = typeovldlist_(bmt)) != NULL)
                    {   bool done_once = NO;
                        for (; l != NULL; l = l->bindlistcdr)
                        {   Binder *tmp = l->bindlistcar;
                            if (attributes_(tmp) & bitofaccess_(s_public) ||
                                attributes_(tmp) & bitofaccess_(s_protected))
                            {   if (!done_once)
                                {   d = mkDeclRhsList(sv, ACCESSADJ,
                                        stgaccof_(access)|bindstg_(tmp));
                                    (void) instate_member(d, bind_scope);
                                    done_once = YES;
                                }
                            } else
                                cc_rerr(syn_rerr_private_bmember_ignored);
                        }
                    } else
                    {   d = mkDeclRhsList(sv, curlex_typename ?
                                            memtype_(curlex_typename) : type_(curlex_path),
                                          stgaccof_(access));
                        (void) instate_member(d, bind_scope);
                    }
                }
            }
        }
    }
    nextsym();
    checkfor_ket(s_semicolon);
}

static TagBinder *firstbaseclass(TagBinder *cl)
{   ClassMember *p;
    ClassMemo memo;
/* Beware: the following code doesn't always give the FIRST base class  */
/* in that it prefers non-virtual bases.  Since it only exists to patch */
/* up an anachronism (where only ONE base was allowed) I don't care.    */
    forClassMember(p, tagbindmems_(cl), &memo)
        if (attributes_(p) & (CB_BASE|CB_VBASE))
        {   TypeExpr *t = memtype_(p);
            if (isclasstype_(t)) return typespectagbind_(t);
            syserr("firstbaseclass $t", t);
        }
    return 0;
}

#define NOARGS ((SET_BITMAP)1)
static Expr *nonconst_thislv(Expr *thislv, TypeExpr *lvt);

/* find a default cctor, dtor, copy constructor or operator=()          */
static Binder *default_structor(Symstr *sv, TagBinder *cl, SET_BITMAP flags)
{   Binder *bgeneric = findbinding(sv, cl, INCLASSONLY);
    Binder *bimpl = 0;
    if (bgeneric)
    {   TypeExpr *tt = bindtype_(bgeneric);                   /* t_ovld */
        Binder *b;
        Expr *thisptr;
        ExprList *l, *ll;

        /* if cl is a core class TagBinder then use the real class...   */
        if (tagbindbits_(cl) & TB_CORE) cl = cl->tagparent;
        b = gentempbinder(tagbindtype_(cl));
        thisptr = mk_expr1(s_addrof, ptrtotype_(tagbindtype_(cl)), (Expr *)b);
        if (flags == NOARGS)
        {   l = NULL;
            ll = mkExprList(l, thisptr);
        } else
        {   Expr *nextarg = nonconst_thislv((Expr *)b, tagbindtype_(cl));
            l = mkExprList1(nextarg);
            ll = mkExprList(l, thisptr);
        }
        if ((bimpl = ovld_resolve(bgeneric, typeovldlist_(tt), l, ll, YES)) != NULL)
        {   Binder *bspecific = bimpl;
            bimpl = (h0_(bimpl) == s_error) ? NULL : realbinder_(bimpl);
            if ((bimpl != NULL) && (bindstg_(bimpl) & b_undef) &&
                !contains_typevars(bindtype_(bimpl)))
                syn_attempt_template_memfn(bgeneric, bspecific);
        }
    }
    return bimpl;
}

typedef struct MemInitList {
  struct MemInitList *micdr;
  ClassMember *mimem;
  ExprList *miargs;
} MemInitList;
#define mkMemInit(x,y,z) ((MemInitList *)syn_list3(x,y,z))

/* MemInitLists are built in declaration order, for convenient use later */

static MemInitList *addmeminit(MemInitList *mi, Symstr *sv, ExprList *init,
                               TagBinder *cl)
{   TagBinder *core;
    ClassMember *p;
    MemInitList *mip = mi, *miq = 0;
/* What should we do with "class B:A { int A; };"?  Fault earlier by    */
/* making A's clash?  Currently first look for virtual base A, then     */
/* member A, then base A.                                               */
    p = tagbindmems_(cl);
    if (p != 0 && (attributes_(p) & CB_CORE))
    {   core = typespectagbind_(memtype_(p));
        for (p = memcdr_(p);  p != 0;  p = memcdr_(p))
        {   TypeExpr *t = memtype_(p);
            if (!isclasstype_(t)) syserr("addmeminit");
            if (sv == bindsym_(typespectagbind_(t))) goto found;
            if (mip && p == mip->mimem) mip = (miq = mip)->micdr;
        }
    }
    else
        core = cl;
    for (p = tagbindmems_(core);  p != 0;  p = memcdr_(p))
    {   if (h0_(p) != s_member) continue;
        if (sv == memsv_(p)) goto found;
        if (attributes_(p) & CB_BASE)
        {   TypeExpr *t = memtype_(p);
            TagBinder *cla;
            if (!isclasstype_(t)) syserr("addmeminit");
            cla = typespectagbind_(t);
            if (sv == bindsym_(cla) ||
                (tagbindbits_(cla) & TB_CORE) &&
                sv == bindsym_(cla->tagparent)) goto found;
        }
        if (mip && p == mip->mimem) mip = (miq = mip)->micdr;
    }
    cc_err(syn_err_no_named_member, cl, sv);
    return mi;
found:
    if (debugging(DEBUG_SYN))
        cc_msg("addmeminit($r)\n", sv);
    if (mip && p == mip->mimem)
        cc_err(syn_err_duplicated_mem_init, memsv_(p));
    else
    {   /* Insert the new initialiser in declaration order.             */
/* @@@ Beware the thisify syserr()s for static members &c &c            */
        mip = mkMemInit(mip, p, init);
        if (miq == 0) mi = mip; else miq->micdr = mip;
    }
    return mi;
}

static Expr *nonconst_thislv(Expr *thislv, TypeExpr *lvt)
{   return mkunary(s_content,
                   mkcast(s_cast, mkunary(s_addrof, thislv), ptrtotype_(lvt)));
}

static Expr *mkspecialfnap(Binder *b, Expr *thislv, ExprList *args, bool corefn)
{   if (b == 0)
        return 0;
    else if (corefn && realbinder_(b) != 0)
    {   /* call core_function(args)...  */
        Expr *thisp = (h0_(thislv) == s_dot) ?
               arg1_(thislv) : mkunary(s_addrof, thislv);
        return mkfnap((Expr *)realbinder_(b), mkExprList(args, thisp));
    }
    else /* exprdotmemfn(args)... */
        return mkfnap(
                mk_exprwdot(s_qualdot, bindtype_(b), thislv, (IPtr)b),
                    args);
}

static const char* structor_string(const Symstr *structorsv)
{   return structorsv == ctorsym ?
               msg_lookup(xsyn_constructor_string) :
           structorsv == dtorsym ?
               msg_lookup(xsyn_destructor_string) :
           structorsv == assignsym ?
               msg_lookup(xsyn_copy_assign_string) :
           symname_(structorsv);
}

/* called for (default?) ctors and dtors ('structors) only... */
static Expr *structor_expr(Symstr *structorsv, Binder *thisb, ClassMember *p)
{   TypeExpr *t = memtype_(p);
    TypeExpr *pt = princtype(t);
    Expr *e = 0;
    int32 nelts = 0;
    ExprList *args = 0;

    if (h0_(pt) == t_subscript)
        nelts = arraysize(pt, &pt);

    if (isclasstype_(pt))
    {   TagBinder *cla = typespectagbind_(pt);
        bool is_dtor = structorsv == dtorsym;
        if (structorsv == ctorsym && (tagbindbits_(cla) & TB_NEEDSCTOR) ||
            is_dtor && (tagbindbits_(cla) & TB_HASDTOR))
        {   /* call the default ctor/dtor if the member is of a class  */
            /* type which isn't Plain Ol' Data. Call the core function */
            /* if the member is a base or a vbase.                     */
            Expr *thislv = mkfieldselector(s_arrow, (Expr *)thisb, p);
            binduses_(thisb) |= u_referenced;
            if (nelts == 0)
            {   if (is_dtor)
                    args = mkExprList1(lit_zero);
                e = mkspecialfnap(default_structor(structorsv, cla, NOARGS),
                                  nonconst_thislv(thislv, tagbindtype_(cla)),
                                  args,
                                  (attributes_(p) & (CB_BASE|CB_VBASE)) != 0);
            }
            else
            {   int32 size = sizeoftype(pt);
                thislv = nonconst_thislv(thislv, tagbindtype_(cla));
                thislv = mkcast(s_cast, mkunary(s_addrof, thislv), te_voidptr);
                e = array_of_class_map(
                        thislv,
                        nelts, size, structorsv != dtorsym,
                        mkunary(s_addrof,
                                (Expr *)default_structor(structorsv, cla, NOARGS)),
                        structorsv == dtorsym);
            }
            if (e == 0)
                cc_warn(syn_warn_no_default_structor, p, cla,
                        structor_string(structorsv));
        }
    }
    else if (structorsv == ctorsym)
        {   if (h0_(pt) == t_ref)
                cc_rerr(syn_rerr_ref_not_initialised, p);
            else if (qualifiersoftype(t) & bitoftype_(s_const))
                cc_rerr(syn_rerr_const_not_initialised, p);
        }
    return e;
}

static Expr *meminit_expr(TagBinder *ctorcl, Binder *thisb, MemInitList **mip)
{   Expr *e = 0;
    ClassMember *p;
    MemInitList *mi = (mip == 0) ? 0 : *mip;

/* Pass in 'thisb' rather than thisify() in deference to compiler-  */
/* generated fns which don't set up a local scope containing 'this' */
/* Other ctors <always> have a ___this, so it's safe and convenient.*/
/* 'srcb' is used only by copy ctors...                             */

    for (p = tagbindmems_(ctorcl);  p != 0;  p = memcdr_(p))
    {   if (h0_(p) != s_member || (attributes_(p) & CB_CORE)) continue;
        /* i.e. not for memfns, static members or typedefs.         */
        /* NB. mi is built in declaration order so use is simple... */
        if (mi != 0 && mi->mimem == p)
        {   Expr *thislv = mkfieldselector(s_arrow, (Expr *)thisb, p);
            TypeExpr *pt = princtype(type_(thislv));
            TagBinder *cla = isclasstype_(pt) ? typespectagbind_(pt) : 0;
            Expr *ee = 0;
            binduses_(thisb) |= u_referenced;
            if (cla != 0)
                ee = mkopap(s_init, cla, thislv, mi->miargs);
            if (ee == 0)
            {   if (mi->miargs != 0)
                    ee = mkbinary(s_init, thislv, exprcar_(mi->miargs));
                if (mi->miargs == 0 || mi->miargs->cdr != 0)
                    cc_rerr(syn_rerr_meminit_wrong_args, p);
            }
            *mip = (mi = mi->micdr);
            e = commacons(e, ee);
        }
        else
            e = commacons(e, structor_expr(ctorsym, thisb, p));
    }
    return e;
}


static Cmd *alloc_cmd(TagBinder *cl, Binder *thisb)
{   Binder *newb = syn_binderofname(cppsim.xnew, cl);
    TypeExpr *bt;
    if (newb == 0)
    {   syserr("alloc_cmd 1, $b", newb);
        return 0;
    }
    if (h0_(bt = bindtype_(newb)) != t_ovld) syserr("alloc_cmd 1, $b", newb);
    if (bindparent_(newb) != 0)
    {   BindList *bl;
        Binder *newspecific = 0;
        /* find T::operator new(size_t) if there is one */
        for (bl = typeovldlist_(bt); bl != 0; bl = bl->bindlistcdr)
        {   FormTypeList *f;
            bt = princtype(bindtype_(bl->bindlistcar));
            if (h0_(bt) != t_fnap) syserr("alloc_cmd 2 $b?", bl->bindlistcar);
            f = typefnargs_(bt);
            if (f != NULL && f->ftcdr == NULL &&
                equivtype(f->fttype, te_size_t))
            {   newspecific = bl->bindlistcar;
                break;
            }
        }
        if (newspecific == 0)
            return 0;
        else
            newb = newspecific;
    }
/* 'if (this == 0) { this = operator new(sizeof(T)); if (this == 0) return this; }' */
/* Note that 'new' prefers class to global scope whereas, mkopap()      */
/* may choose from either.                                              */
/* We use s_init to allow initting this which is a const T* */
/* /* intzero (and intone) are used enough to move them to builtin */
  {
    Expr *testthis = optimise0(mkbinary(s_equalequal, (Expr*)thisb, lit_zero));
    TypeExpr *t = tagbindtype_(cl);
    Expr *e = mkcast(s_cast,
                     mkfnap((Expr*)newb, mkExprList1(mkintconst(te_size_t, sizeoftype(t), 0))),
                     ptrtotype_(t));
    Cmd *init = mk_cmd_e(s_semicolon, syn_invented_fl,
                         optimise0(mkbinary(s_init, (Expr*)thisb, e)));
    return
      mk_cmd_block(syn_invented_fl, 0,
          mkCmdList(0,
            mk_cmd_if(syn_invented_fl, testthis,
              mk_cmd_block(syn_invented_fl, 0,
                mkCmdList(
                  mkCmdList(0,

                    mk_cmd_if(syn_invented_fl, testthis,
                              mk_cmd_e(s_return, syn_invented_fl, (Expr*)thisb),
                              0)),
                  init)), 0)));
  }
}

#define CTOR_DEFAULT   1
#define DTOR_DEFAULT   2
#define CTOR_COPY      4
#define OP_ASSIGN      8
#define HAS_CORE      16
#define IN_CORE       32

static void generate_fn_body(TagBinder *cl, int sort, Binder *fnbinder,
        SynBindList *argbinders, MemInitList **mip);

static Cmd *meminit_cmd(TagBinder *ctorclass, Binder *ctor,
        SynBindList *argbinders, MemInitList *mi, Cmd **alloc)
{   Binder *thisb = argbinders->bindlistcar;
    TagBinder *coreclass = core_class(ctorclass);
    Expr *e = 0;
    if (coreclass != ctorclass)
/* Split the function into a top-level part and a core part. We need to */
/* clone the argbinders, re-writing their types appropriately.          */
    {   SynBindList *a;
        SynBindList *blp = 0, *blq = 0;

        for (a = argbinders;  a != 0;  a = a->bindlistcdr)
        {   Binder *b = a->bindlistcar;
            TypeExpr *t = bindtype_(b);
            SynBindList *bla;

            if (isclasstype_(princtype(t)))
            {   Binder *ob = b;
                bindtype_(ob) = mk_typeexpr1(t_ref, t, 0);
                b = mk_binder(bindsym_(b), bitofstg_(s_auto), t);
            }
            bla = (SynBindList *) syn_list3(0, b, 0);
            if (blp == 0)
                blq = (blp = bla);
            else
                blq = (blq->bindlistcdr = bla);
        }
        /* binders in argbinders have been re-typed - class T -> T&.    */
        generate_fn_body(ctorclass, CTOR_DEFAULT|HAS_CORE, ctor, blp, &mi);
    }
    else
        *alloc = alloc_cmd(ctorclass, thisb);
    e = commacons(e, meminit_expr(coreclass, thisb, &mi));
    if (mi != 0) syserr("meminit_cmd");

    if (coreclass == ctorclass && tagbindbits_(ctorclass) & TB_HASVTABLE)
    {   Expr *thislv =
                mk_expr1(s_content, typearg_(bindtype_(thisb)), (Expr *)thisb);
        e = commacons(e, vtab_init(ctorclass, thislv));
    }
    {   FileLine fl;
        SynBindList *bl;
        fl = curlex.fl;
        fl.p = dbg_notefileline(fl);
        add_expr_dtors(killexprtemp());
        bl = pop_saved_temps(NULL);
        if (expr_dtors != NULL)
        {   e = commacons(e, expr_dtors);
            e = mk_exprlet(s_let, te_void, bl, e);
            expr_dtors = NULL;
            extra_flags = NULL;
        }
        return e == 0 ? 0 : mk_cmd_e(s_semicolon, fl,
               optimise0(mkcast(s_semicolon, e, te_void)));
    }
}

static Cmd *rd_meminit(TagBinder *ctorclass, Binder *ctor,
                       SynBindList *argbinders, Cmd **pre, Cmd **post)
{   MemInitList *mi = 0;
    *pre = *post = 0;
    if (strncmp(symname_(bindsym_(ctor)), "__ct", 4) != 0) ctorclass = 0;

    if (ctorclass == 0)
    {   if (curlex.sym == s_colon)
            cc_err(syn_err_init_not_in_ctor);
        else
            return 0;
    }
    push_saved_temps(synscopeid);  /* popped in meminit_cmd */
    push_exprtemp_scope();
/* Here we read the meminit list even if not a ctor, for error recovery */
    if (curlex.sym == s_colon)
    {   for (;;)
        {   Symstr *sv = 0;
            ExprList *init;
            nextsym();
            rd_cpp_name(0);
            switch (curlex.sym)
            {
    case s_lpar:
                if (ctorclass)
                {   TagBinder *b = firstbaseclass(ctorclass);
                    if (b != 0)
                        sv = bindsym_(b),
                        cc_warn(syn_warn_insert_sym_anachronism, sv);
                    else
                        cc_err(syn_err_lacks_bclass_anachronism,
                               ctorclass);
                }
                break;
    case s_identifier:      /* s_qualified? */
                sv = 0;
                if (ctorclass != 0)
                {   TypeExpr *pt;
                    if (curlex_typename != 0 &&
                        (typespecmap_(pt=princtype(bindtype_(curlex_typename))) &
                         (bitoftype_(s_struct)|bitoftype_(s_class))) != 0)
                        /* basename case... */
                    {   if (istypevar(pt))
                        {
                            pop_exprtemp_scope();
                            (void)pop_saved_temps(NULL);
                            return 0;
                        }
                        sv = tagbindsym_(typespectagbind_(pt));
                    } else
                        /* data-member-name case ... */
                        sv = curlex.a1.sv;
                }
                nextsym();
                break;
    default:    cc_err(syn_err_expected_id_in_mem_init);
                while (!(curlex.sym == s_lbrace ||
                         curlex.sym == s_eof)) nextsym();
                pop_exprtemp_scope();
                (void)pop_saved_temps(NULL);
                return 0;
            }
            checkfor_ket(s_lpar);
            init = rd_exprlist_opt();
            if (sv) mi = addmeminit(mi, sv, init, ctorclass);
            if (curlex.sym == s_nothing) nextsym();
            if (curlex.sym != s_comma) break;
        }
    }
    if (ctorclass == 0)     /* not a constructor meminit list */
    {   pop_exprtemp_scope();
        (void)pop_saved_temps(NULL);
        return 0;
    }
    *post = mk_cmd_e(s_return, syn_invented_fl,
                     (Expr*) argbinders->bindlistcar /* thisb */);
    return meminit_cmd(ctorclass, ctor, argbinders, mi, pre);
}

static Expr *memdtor_expr(TagBinder *dtorclass, Binder *thisb)
{   Expr *e = 0;
    ClassMember *p;
    for (p = tagbindmems_(dtorclass);  p != 0;  p = memcdr_(p))
        if (h0_(p) == s_member && !(attributes_(p) & CB_CORE))
/* NB: cons in REVERSE order - last constructed is first destroyed...   */
            e = commacons(structor_expr(dtorsym, thisb, p), e);
    return e;
}

static Expr *syn_memdtor(TagBinder *dtorclass, Binder *dtor, SynBindList *formals,
                         Cmd **pre)
{   Binder *thisb = formals->bindlistcar;
    TagBinder *coreclass = core_class(dtorclass);
    if (tagbindbits_(dtorclass) & TB_HASVTABLE)
    {   Expr *thislv = mk_expr1(s_content,
                typearg_(bindtype_(thisb)), (Expr *)thisb);
        /* this is only really needed if the body has any function calls in it */
        *pre = mk_cmd_e(s_semicolon, syn_invented_fl,
                        optimise0(vtab_init(dtorclass, thislv)));
    }
    else
        *pre = 0;
/* NB: cons in REVERSE order - last constructed is first destroyed...   */
    if (coreclass != dtorclass)
        generate_fn_body(dtorclass, DTOR_DEFAULT|HAS_CORE, dtor,
            (SynBindList *) syn_list3(
                 syn_list3(0, formals->bindlistcdr->bindlistcar, 0), thisb, 0),
                         0);
    return memdtor_expr(coreclass, thisb);
}

/* Given the type of a vbase, this fn locates a pointer to it. NB there */
/* is exactly one vbase of a given type in a derivation, so any pointer */
/* to it suffices.                                                      */

static Expr *vbaserv_1(TagBinder *core, Binder *srcb, TagBinder *vbase)
{   ClassMember *p;
    Expr *e;

    for (p = tagbindmems_(core);  p != 0;  p = memcdr_(p))
    {   if (h0_(p) != s_member) continue;
        if ((attributes_(p) & CB_VBPTR) &&
            typespectagbind_(typearg_(memtype_(p))) == vbase)
            return mkunary(s_content,
                mkfieldselector(s_dot, (Expr *)srcb, p));
        else if ((attributes_(p) & CB_BASE) &&
                 (e=vbaserv_1(typespectagbind_(memtype_(p)), srcb, vbase)) !=0)
            return e;
    }
    return 0;
}

static Expr *vbaserv(TagBinder *core, Binder *srcb, TagBinder *vbase)
{   Expr *e = vbaserv_1(core, srcb,vbase);
    if (e) return e;
    syserr("copy_expr/vbaserv");
    return errornode;
}

static Expr *pod_copy(Expr *to, Expr *fm, int32 len, TypeExpr *t)
{   if (len == 0) return 0;
    to = mk_expr1(s_addrof, ptrtotype_(t), to);
    fm = mk_expr1(s_addrof, ptrtotype_(t), fm);
    if (t == te_int && len == sizeof_int)
        return mkbinary(s_assign,
                mkunary(s_content, to),
                    mkunary(s_content, fm));
    return mk_expr2(s_fnap, t, sim.realmemcpyfn,
            (Expr *)mkExprList(
                        mkExprList(mkExprList1(mkintconst(te_int, len, 0)),
                                   fm),
                               to));
}

/* sv == assignsym (for operator=()) or sv == ctorsym (for copy ctors) */
static Expr *copy_expr(TagBinder *cl, Symstr *sv, Binder *thisb, Binder *srcb)
{   Expr *e = 0;
    ClassMember *p;
    TagBinder *core = core_class(cl);
    Expr *fromlv = 0, *fromrv = 0;
    int32 pod_len = 0;
    TypeExpr *pod_type = 0;
    bool is_assign = sv == assignsym;
    SET_BITMAP needstest = is_assign ? TB_NEEDSOPEQ : TB_NEEDSCCTOR;

    for (p = tagbindmems_(cl);  p != 0;  p = memcdr_(p))
    {   if (h0_(p) == s_member &&
           !(attributes_(p) & (CB_CORE|CB_VBPTR|CB_VTAB)))
        {   Expr *thislv = mkfieldselector(s_arrow, (Expr *)thisb, p);
            TypeExpr *pt = princtype(memtype_(p));
            TagBinder *cla = typespectagbind_(pt);
            Expr *thisrv, *ee;

            if (attributes_(p) & CB_VBASE)
/* If copying to a vbase, the source expression must indirect via an    */
/* appropriate vbptr, as the source object need not be 'most derived'.  */
            {   e = commacons(e, pod_copy(fromlv, fromrv, pod_len, pod_type));
                pod_len = 0;
                thisrv = vbaserv(core, srcb, cla);
            }
            else
                thisrv = mkfieldselector(s_dot, (Expr *)srcb, p);

            if (pod_len == 0)
            {   fromlv = thislv;
                fromrv = thisrv;
                if ((arg2i_(fromlv) % alignof_int) == 0)
                    pod_type = te_int;
                else
                    pod_type = te_char;
            }

            if (is_assign &&
                (qualifiersoftype(memtype_(p)) & bitoftype_(s_const)))
                cc_rerr(sem_rerr_assign_const, p);

            if (isclasstype_(pt) && tagbindbits_(cla) & needstest)
            {   ee = mkspecialfnap(
                        default_structor(sv, cla,
                    qualifiersoftype(memtype_(p)) & bitoftype_(s_const)),
                            nonconst_thislv(thislv, tagbindtype_(cla)),
                                mkExprList1(thisrv),
                                    (attributes_(p) & (CB_BASE|CB_VBASE)) != 0);
                if (ee == 0)
                    cc_warn(syn_warn_no_default_structor, p, cla,
                            structor_string(sv));
                        /* 'recover' by treating as POD... for now...   */
                else
                {   e = commacons(e,
                        pod_copy(fromlv, fromrv, pod_len, pod_type));
                    pod_len = 0;
                    e = commacons(e, ee);
                    continue;
                }
            }
            else if (h0_(pt) == t_subscript)
            {   /* array of foo... */
                TypeExpr *et = pt;
                int32 nelts = arraysize(pt, &et);
                if (isclasstype_(et) &&
                    (cla = typespectagbind_(et), tagbindbits_(cla) & needstest))
                {   SET_BITMAP constness =
                        qualifiersoftype(memtype_(p)) & bitoftype_(s_const);
                    Expr* limit = /* '(char*)(&thisrv) + nelts * sizeoftype(et)' */
                        mkbinary(s_plus,
                             mkcast(s_cast, mkunary(s_addrof, thisrv), te_charptr),
                             mkintconst(te_size_t, nelts * sizeoftype(et), 0));
                    ee = array_of_class_copy(thislv, thisrv, limit,
                                         sizeoftype(et),
                                         default_structor(sv, cla, constness));
                    if (ee == 0)
                        cc_warn(syn_warn_no_default_structor, p, cla,
                                structor_string(sv));
                            /* 'recover' by treating as POD... for now. */
                    else
                    {   e = commacons(e,
                            pod_copy(fromlv, fromrv, pod_len, pod_type));
                        pod_len = 0;
                        e = commacons(e, ee);
                    }
                    continue;
                }
            }

            pod_len = arg2i_(thislv) - arg2i_(fromlv);
            if (isbitfield_type(pt))
                pt = unbitfield_type(pt);
            if (!(attributes_(p) & CB_BASE &&
                  isclasstype_(pt) &&
                  tagbindmems_(typespectagbind_(pt)) == 0))
                /* NOT empty base class... */
                pod_len += sizeoftype(pt);
        }
    }
    e = commacons(e, pod_copy(fromlv, fromrv, pod_len, pod_type));
    return e;
}

/* cpp_end_strdecl() is called at the end of adding members to (the     */
/* core of) a class (bind.c::insertionpoint() knows to add members to   */
/* the core of a class if it has a CB_CORE member). cpp_end_strdecl()   */
/* accumulates information about the class, initialises its vtable if   */
/* it has one and adds decls of a default ctor, dtor, copy ctor and     */
/* operator= if any of these are needed. The info accumulated is:       */
/*  -  TB_NOTPOD - an attribute_() of the class TagBinder (meaning not  */
/*     Plain Ol' Data) set if:                                          */
/*      -  any base or member is NOTPOD;                                */
/*      -  there is any ctor or dtor declared;                          */
/*      -  there are any virtual bases or virtual function tables.      */
/*     Jan-1995 TB_NOTPOD is no longer an attribute bit, see defs.h     */
/*  -  CB_CGEN - an attribute_() of realbinders for ctors, dtors and    */
/*     operator= memers - which indicates that part of the function     */
/*     definition is compiler-generated.                                */
/*  -  TB_HASVTABLE - a TagBinder attribute_() if the class has a       */
/*     vtable member.                                                   */
/* -   TB_HASDTOR - a TagBinder attribute_() set if any base has a dtor */
/*     or a dtor is declared in this class.                             */

static void inherit_tagbindbits(TagBinder *b)
{   ClassMember *m;
    ClassMemo memo;

    forClassMember(m, tagbindmems_(b), &memo)
    {   TagBinder *mb = 0;
        if (h0_(m) != s_member) continue;
        if (qualifiersoftype(memtype_(m)) & bitoftype_(s_const))
            tagbindbits_(b) |= TB_HASCMEM;
        if (attributes_(m) & (CB_BASE|CB_VBASE))
        {   mb = typespectagbind_(memtype_(m));
            if (attributes_(m) & CB_VBASE) tagbindbits_(b) |= TB_HASVBASE;
        }
        else if (attributes_(m) & CB_VTAB)
        {   int32 sz = base_vtable_sz(b);
            memtype_(m) = globalize_typeexpr(
                ptrtotype_(mk_typeexpr1(t_subscript, te_ulint,
                                        mkintconst(te_int, sz, 0))));
            tagbindbits_(b) |= TB_HASVTABLE;
        }
        else
        {   TypeExpr *pt = princtype(memtype_(m));
            (void)isarraytype(pt, &pt);
            if (isclasstype_(pt)) mb = typespectagbind_(pt);
        }

        if (mb != 0)
        {   tagbindbits_(b) |= (tagbindbits_(mb) & TB_HASDTOR);
            tagbindbits_(b) &= (tagbindbits_(mb) |
                   ~(TB_HASCONSTCCTOR|TB_HASCONSTOPEQ));
            tagbindbits_(b) |= (tagbindbits_(mb) &
                (TB_NEEDSCCTOR|TB_NEEDSOPEQ|TB_NEEDSCTOR|TB_HASCMEM));
        }
    }
}

void syn_note_generated_fn(TopDecl *d)
{  syn_generatedfns = (GenFnList *) syn_list3(syn_generatedfns, d, 0);
/* The following protects the function definition until later unmark()'d */
/* by syn.c::rd_topdecl(). This avoids spurious globalization and deals  */
/* naturally with compiler-generated fns in nested classes.              */
   syn_generatedfns->mark = alloc_mark();
}

static void generate_fn_body(TagBinder *cl, int sort, Binder *fnbinder,
        SynBindList *argbinders, MemInitList **mip)
{   CmdList *cmds = 0;
    Expr *e = 0, *vtabinit = 0;
/* Assert: argbinders is non-empty and has >=2 elements for OP_ASSIGN */
    Binder *thisb = argbinders->bindlistcar;
    Binder *srcb = (argbinders->bindlistcdr == 0) ? 0 :
                    argbinders->bindlistcdr->bindlistcar;

if (var_cc_private_flags & 0x200000)
    cc_msg("generating $b in $c\n", fnbinder, cl);

    if (sort & (CTOR_DEFAULT|CTOR_COPY))
    {   if (!(sort & IN_CORE))
        {   Expr *thislv = 0;
            Cmd *alloc = alloc_cmd(cl, thisb);
            if (alloc)
                cmds = mkCmdList(cmds, alloc);
            if ((sort & HAS_CORE) || (tagbindbits_(cl) & TB_HASVTABLE))
            {   thislv =  mk_expr1(s_content,
                        typearg_(bindtype_(thisb)), (Expr *)thisb);
            }
            if (tagbindbits_(cl) & TB_HASVTABLE)
                vtabinit = vtab_init(cl, thislv);   /* save up for later */
            if (sort & HAS_CORE)
                e = vbase_init(cl, thislv);       /* init vbase pointers */
        }
        if (sort & CTOR_DEFAULT)
            e = commacons(e, meminit_expr(cl, thisb, mip));
        else    /* CTOR_COPY */
            e = commacons(e, copy_expr(cl, ctorsym, thisb, srcb));
    }
    else if (sort & OP_ASSIGN)
        e = copy_expr(cl, assignsym, thisb, srcb);

    if ((sort & HAS_CORE) && !(sort & IN_CORE))
    /* call the core function of this sort... */
    {   TypeExpr *fntype = bindtype_(fnbinder);
        FormTypeList *ft;
        SynBindList *a = argbinders;
        ExprList *l = 0;
        for (ft = typefnargs_(fntype);  ft != 0 && a != 0;  ft = ft->ftcdr)
        {   TypeExpr *t = princtype(ft->fttype);
            Expr *e = (Expr *)(a->bindlistcar);
            if (h0_(t) == t_ref) e = mk_expr1(s_content, typearg_(t), e);
            l = mkExprList(l, e);
            /* /* core dtors really only need one argument */
            if (sort & DTOR_DEFAULT)
            {   l = mkExprList(l, lit_zero);
                break;
            }
            a = a->bindlistcdr;
        }
        /* /* for op= and ctors it would be nice if this were a tail call */
        /* when possible (always?) */
        e = commacons(e, mkfnap((Expr *)realbinder_(fnbinder), dreverse(l)));
    }

/* vtabinit != 0 iff: (sort & (CTOR_DEFAULT|CTOR_COPY)) &&               */
/*                    !(sort & IN_CORE) &&                               */
/*                    (tagbindbits_(cl) & TB_HASVTABLE))                 */
    e = commacons(e, vtabinit);

    if (sort & DTOR_DEFAULT)
        e = commacons(e, memdtor_expr(cl, thisb));

    if (e)
    {   cmds = mkCmdList(cmds,
            mk_cmd_e(s_semicolon, curlex.fl,
                optimise0(mkcast(s_semicolon, e, te_void))));
    }
    if (sort & OP_ASSIGN)
    {   TypeExpr *restype = typearg_(bindtype_(fnbinder));
        e = optimise0(mkcast(s_cast,
                mkunary(s_content, (Expr *)thisb), restype));
        cmds = mkCmdList(cmds, mk_cmd_e(s_return, curlex.fl, e));
    }
    else if (sort & (CTOR_DEFAULT|CTOR_COPY))
        cmds = mkCmdList(cmds, mk_cmd_e(s_return, curlex.fl, (Expr*)thisb));
    else if ((sort & DTOR_DEFAULT) && !(sort & IN_CORE))
        cmds = mkCmdList(cmds, conditionalised_delete(thisb, srcb, cl));

    syn_note_generated_fn(mkTopDeclFnDef(s_fndef, fnbinder, argbinders,
                mk_cmd_block(curlex.fl, 0, (CmdList *)dreverse((List *)cmds)),
                    0));
}

static void mk_generated_fn(TagBinder *cl, int sort, Binder *fnbinder)
{   TypeExpr *fnrtype = bindtype_(fnbinder);
    FormTypeList *ft = typefnargs_(fnrtype);
    SynBindList *argbinders = 0;
    Binder *thisb = mk_binder(ft->ftname, bitofstg_(s_auto), ft->fttype);

    binduses_(thisb) |= u_referenced;
    if ((ft = ft->ftcdr) != 0)
    {   Symstr *argsym = (sort & DTOR_DEFAULT) ? deletesym :
                                                 sym_insert_id("__src");
        Binder *srcb = mk_binder(argsym, bitofstg_(s_auto), ft->fttype);
        argbinders = (SynBindList *) syn_list3(0, srcb, 0);
    }
    argbinders = (SynBindList *) syn_list3(argbinders, thisb, 0);

    generate_fn_body(cl, sort, fnbinder, argbinders, 0);
}

#define declsort_(d) ((d)->u.stgval)

static DeclRhsList *generate_fndecl(DeclRhsList *dl, TagBinder *cl, int sort)
{   TypeExprFnAux s, *fnaux;
    TypeExpr *fnrtype = te_void, *argt = 0;
    DeclRhsList *d;
    Binder *bspecific;
    FormTypeList *fnargs = 0;
    Symstr *sv;

    switch (sort)
    {
case CTOR_DEFAULT:
        fnaux = packTypeExprFnAux(s, 0, 0, 0, 0, 0);
        fnrtype = ptrtotype_(tagbindtype_(cl));
        sv = ctorsym;
        break;
case DTOR_DEFAULT:
        fnaux = packTypeExprFnAux(s, 0, 0, 0, 0, 0);
        sv = dtorsym;
        break;
case CTOR_COPY:
        argt = mk_typeexpr1(t_ref,
            mkqualifiedtype(tagbindtype_(cl),
                tagbindbits_(cl) & TB_HASCONSTCCTOR ? bitoftype_(s_const) : 0),
                     0);
        fnaux = packTypeExprFnAux(s, 1, 1, 0, 0, 0);
        fnrtype = ptrtotype_(tagbindtype_(cl));
        sv = ctorsym;
        break;
case OP_ASSIGN:
        argt = mk_typeexpr1(t_ref,
            mkqualifiedtype(tagbindtype_(cl),
                tagbindbits_(cl) & TB_HASCONSTOPEQ ? bitoftype_(s_const) : 0),
                    0);
        fnrtype = mk_typeexpr1(t_ref, tagbindtype_(cl), 0);
        fnaux = packTypeExprFnAux(s, 1, 1, 0, 0, 0);
        sv = assignsym;
        break;
default:
        syserr("generate_fndecl(%d)", sort);
        return dl;
    }
    if (argt != 0)
        fnargs = mkFormTypeList(0, 0, argt, 0);
    d = mkDeclRhsList(sv, mkTypeExprfn(t_fnap, fnrtype, 0, fnargs, fnaux),
        b_generated | stgaccof_(s_public) | bitofstg_(s_inline) | b_fnconst);

    bspecific = instate_member(d, bind_scope);

    attributes_(bspecific) |= CB_CGEN;
    binduses_(bspecific) |= u_referenced;
    bspecific = realbinder_(bspecific);
    bindstg_(bspecific) &= ~b_undef;
    attributes_(bspecific) |= CB_CGEN;

    d->declbind = bspecific;
    d->declcdr = dl;
    declsort_(d) = sort;

    return d;
}

static void generate_fndef(DeclRhsList *d, TagBinder *cl)
{   int sort = (int)declsort_(d);
    Binder *bspecific = d->declbind;
    TagBinder *core = core_class(cl);
    if (tagbindbits_(cl) & TB_TEMPLATE) return;
    if (core != cl)
        sort |= HAS_CORE;
    mk_generated_fn(cl, sort, bspecific);
    if (sort & HAS_CORE)
        mk_generated_fn(core, sort|IN_CORE, realbinder_(bspecific));
}

static void bind_function_default_arguments(Binder *bimpl)
{   TypeExpr *t2 = princtype(bindtype_(bimpl));
    FormTypeList *f;
    Expr *init;
    for (f = typefnargs_(t2);  f != 0;  f = f->ftcdr)
    {   SynBindList *bl = NULL;
        TypeExpr *t;
        if (f->ftdefault == 0 ||
            exb_(arg2_(f->ftdefault)) != &deferred_default_arg_expr)
                continue;
        lex_openbody(evaluate(f->ftdefault), NO, NO, NULL, NULL);
/* AM is now of the opinion that the following code (and similar code   */
/* in mkfnap()) to widen_formaltype() is somewhat wrong-minded.         */
/* It means that "void f(char); void g() { f(257); }" is treated        */
/* differently from the similar "char x = 257".  Maybe we should defer  */
/* some of this code to cg.c.                                           */
        push_saved_temps(synscopeid);
        push_exprtemp_scope();
        init = optimise0(mkcast(s_fnap, rd_expr(UPTOCOMMA),
                                (t = widen_formaltype(f->fttype))));
        add_expr_dtors(killexprtemp());
        bl = pop_saved_temps(bl);
        if (init && bl)
        {   init = (!expr_dtors) ? mk_exprlet(s_let, t, bl, init) :
                    mk_exprlet(s_qualified|s_let, t, bl, commacons(init, expr_dtors));
            expr_dtors = NULL;
            extra_flags = NULL;
        }
/* Note that optimise0() on the next line means (1) the top-type may    */
/* be incompatibly changed (so don't check it again) and moreover that  */
/* (2) optimise0() will get called on it again.  Hmm @@@.               */
/* Add a special 'optimise0'd flag node?                                */
/* optimise0() maps errornode => NULL; moved above                      */
/* LDS: 12-Jul-94 - need to globalize here or disaster can ensue...     */
        f->ftdefault = (init) ? globalize_expr(init) : NULL;
        lex_closebody();
    }
}

static void bind_default_arguments(TagBinder *cl)
{   ClassMember *m = tagbindmems_(cl);
    Friend *fr;
    if (m && attributes_(m) & CB_CORE)
        m = tagbindmems_(typespectagbind_(memtype_(m)));
    for (; m != 0;  m = memcdr_(m))
    {   if (h0_(m) == s_binder)
        {   TypeExpr *t = memtype_(m);
            BindList *bl;
            if (h0_(t) != t_ovld) continue;
/* found a class member function */
            for (bl = typeovldlist_(t);  bl != 0;  bl = bl->bindlistcdr)
                bind_function_default_arguments(realbinder_(bl->bindlistcar));
        }
    }
    for (fr = cl->friends;  fr != 0;  fr = fr->friendcdr)
        if (h0_(fr->u.friendfn) == s_binder)
            bind_function_default_arguments(fr->u.friendfn);
}

/* /* should fault if any ref mems or const mems and no user ctor */
static void cpp_end_strdecl(TagBinder *cl)
{   Binder *mb;
    int has_user_copy_ctor = NO;                /* until shown otherwise */
    int has_user_const_copy_ctor = NO;          /* until shown otherwise */
    int has_user_ctor = NO;
    DeclRhsList *fndecl = 0;

    bind_default_arguments(cl);

    tagbindbits_(cl) |= TB_HASCONSTCCTOR|TB_HASCONSTOPEQ;
                                            /* until proven otherwise... */
    inherit_tagbindbits(cl);

    if ((mb = findbinding(ctorsym, cl, INCLASSONLY)) != 0)
/* There are constructors, so mark CB_CGEN and check for a copy ctor.    */
    {   TypeExpr *t1 = memtype_(mb), *thistype = tagbindtype_(cl);
        BindList *bl;
        bool semantics_differ = YES;
        Binder* armb = NULL;
        if (h0_(t1) != t_ovld) syserr("odd ctor type in $c", cl);
        for (bl = bindftlist_(mb) ? bindftlist_(mb) : typeovldlist_(t1);
             bl != NULL; bl = bl->bindlistcdr)
        {   Binder *bspecific = bl->bindlistcar;
            TypeExpr *t2 = princtype(bindtype_(bspecific));
            FormTypeList *f = typefnargs_(t2);
            if (h0_(t2) != t_fnap) continue; /* @@@ what else could it be? */
/* A user-defined constructor nontheless has compiler-generated parts... */
            attributes_(realbinder_(bspecific)) |= CB_CGEN;
            if (!has_user_ctor && (f == 0 ||
                                   qualfree_equivtype(princtype(f->fttype), thistype) != 2))
                has_user_ctor = YES;
            if ((!has_user_const_copy_ctor || semantics_differ) &&
                f != NULL && minargs_(t2) <= 1)
            {   /* at least one formal and any args from 2 up optional.  */
                TypeExpr *t3 = princtype(f->fttype);
                TypeExpr *t4 = h0_(t3) == t_ref ? typearg_(t3) : t3;
                const bool equiv = qualfree_equivtype(t4, thistype);
                const bool derived = type_derived_from(t4, thistype) != NULL;
/* Here we check A.R.M. semantics as well as DRAFT semantics.  In Cfront */
/* mode we implement A.R.M. semantics, otherwise we implement DRAFT     */
/* semantics.  We warn in either mode if the semantics differ.          */
/* For "A.R.M." semantics we allow a copy constructor to take as formal */
/* argument an object of a class which is a base class of the class     */
/* which the operator belongs.  The A.R.M. is even more generous and    */
/* allows any conversion.  This is also done below for operator=.       */
                if (equiv || (HasFeature(Feature_CFront) && derived))
                {   if (h0_(t3) != t_ref) syserr("self-copying $c constructor", cl);
                    has_user_copy_ctor = YES;
                    if (equiv)
                        semantics_differ = NO;
                    else
                        armb = bspecific;
                    if (qualifiersoftype(t4) & bitoftype_(s_const))
                        has_user_const_copy_ctor = YES;
                }
                else if (derived)
                    armb = bspecific;
            }
        }
        if (semantics_differ && armb)
            cc_warn(HasFeature(Feature_CFront) ?
                       xsyn_warn_ARM_cctor_suppress : xsyn_warn_ISO_cctor_no_suppress,
                    armb);
        if (has_user_copy_ctor)
        {   if (has_user_const_copy_ctor)
                tagbindbits_(cl) |= TB_HASCONSTCCTOR;
            else
                tagbindbits_(cl) &= ~TB_HASCONSTCCTOR;
        }
    }

    if (tagbindbits_(cl) & (TB_HASVTABLE|TB_HASVBASE))
        tagbindbits_(cl) |= TB_NEEDSCTOR|TB_NEEDSCCTOR;
    else
    {   if (has_user_ctor)
            tagbindbits_(cl) |= TB_NEEDSCTOR;
        if (has_user_copy_ctor)
            tagbindbits_(cl) |= TB_NEEDSCCTOR;
    }

    /* declare the default ctor if there is no suitable ctor and    */
    /* declare the default copy ctor if there isn't a copy ctor...  */
    if (mb == 0 && (tagbindbits_(cl) & TB_NEEDSCTOR))
        fndecl = generate_fndecl(fndecl, cl, CTOR_DEFAULT);

    /* declare the default cctor if there isn't one in class        */
    if (!has_user_copy_ctor && (tagbindbits_(cl) & (TB_NEEDSCTOR|TB_NEEDSCCTOR)))
        fndecl = generate_fndecl(fndecl, cl, CTOR_COPY);

  { /* may need to declare a generated operator=()...                */
    BindList *bl;

    int has_user_op_assign = NO;         /* until shown otherwise... */
    int has_user_const_op_assign = NO;   /* until shown otherwise... */
    if ((mb = findbinding(assignsym, cl, INCLASSONLY)) != 0)
    {   /* There are some assignment operators...                    */
        TypeExpr *t1 = memtype_(mb);
        bool semantics_differ = YES;
        Binder* armb = NULL;
        if (h0_(t1) != t_ovld) syserr("odd operator=() type in $c", cl);
        for (bl = bindftlist_(mb) ? bindftlist_(mb) : typeovldlist_(t1);
             bl != NULL; bl = bl->bindlistcdr)
        {   Binder *bspecific = bl->bindlistcar;
            TypeExpr *t2 = princtype(bindtype_(bspecific));
            FormTypeList *f = typefnargs_(t2);
/* NB. user-defined operator=() contain no compiler-generated parts so  */
/*     don't give the binder the CB_CGEN attribute: ctors/dtors only.   */
            if (h0_(t2) == t_fnap && f != NULL && minargs_(t2) <= 1)
            {   /* > 0 formals and any arg from 2 up optional...        */
                TypeExpr *t3 = princtype(f->fttype);
                TypeExpr *t4 = h0_(t3) == t_ref ? typearg_(t3) : t3;
                const bool equiv = qualfree_equivtype(t4, tagbindtype_(cl));
                const bool derived = type_derived_from(t4, tagbindtype_(cl)) != NULL;
                if (equiv || (HasFeature(Feature_CFront) && derived))
                {   has_user_op_assign = YES;
                    if (equiv)
                        semantics_differ = NO;
                    else
                        armb = bspecific;
                    if (h0_(t3) != t_ref || (qualifiersoftype(t4) &
                                             bitoftype_(s_const)))
                    {   has_user_const_op_assign = YES;
                        /* break if there's no point in scanning the rest */
                        if (!semantics_differ)
                            break;
                    }
                }
                else if (derived)
                    armb = bspecific;
            }
        }
        if (semantics_differ && armb)
            cc_warn(HasFeature(Feature_CFront) ?
                       xsyn_warn_ARM_opeq_suppress : xsyn_warn_ISO_opeq_no_suppress,
                    armb);
        if (has_user_op_assign)
        {   if (has_user_const_op_assign)
                tagbindbits_(cl) |= TB_HASCONSTOPEQ;
            else
                tagbindbits_(cl) &= ~TB_HASCONSTOPEQ;
        }
    }

    /* TB_HASVTABLE is needed to force skipping of the vtable pointers */
    if (tagbindbits_(cl) & (TB_HASVTABLE|TB_HASVBASE))
        tagbindbits_(cl) |= TB_NEEDSOPEQ;
    else if (has_user_op_assign)
        tagbindbits_(cl) |= TB_NEEDSOPEQ;

    /* declare the default operator=() if there isn't one in class or
       one of its base class has one                                 */
    /* but make sure there is no const mem around ... */
    if (!has_user_op_assign && (tagbindbits_(cl) & TB_NEEDSOPEQ) &&
        !(tagbindbits_(cl) & TB_HASCMEM))
        fndecl = generate_fndecl(fndecl, cl, OP_ASSIGN);
  }

    if ((mb = findbinding(dtorsym, cl, INCLASSONLY)) != 0)
    {   TypeExpr *t1 = memtype_(mb);
        BindList *bl;
        if (h0_(t1) == t_ovld
            && (bl = (bindftlist_(mb) ? bindftlist_(mb) : typeovldlist_(t1)))->bindlistcdr == 0)
/* This predicate can only fail as a result of previous diagnosed errors */
        {   attributes_(realbinder_(bl->bindlistcar)) |= CB_CGEN;
            tagbindbits_(cl) |= TB_HASDTOR;
        }
    }
    else if (tagbindbits_(cl) & TB_HASDTOR)
        fndecl = generate_fndecl(fndecl, cl, DTOR_DEFAULT);

    {   TagBinder *core = core_class(cl);
        if (core != cl)
            tagbindbits_(core) |= tagbindbits_(cl) &
                (TB_HASDTOR   | TB_HASCONSTCCTOR | TB_HASCONSTOPEQ |
                 TB_NEEDSCTOR | TB_NEEDSCCTOR    | TB_NEEDSOPEQ);
    }

    {   TagBinder *core = core_class(cl);
        tagbindbits_(core) = (tagbindbits_(core) & ~TB_BEINGDEFD) | TB_DEFD;
        tagbindbits_(cl) = (tagbindbits_(cl) & ~TB_BEINGDEFD) | TB_DEFD;
        /* (perhaps redundantly. Another redundant setting of TB_DEFD is */
        /* coming up in pop_scope, but is needed for C.                  */
    }

    for (; fndecl != 0; fndecl = fndecl->declcdr)
        generate_fndef(fndecl, cl);
}

static ScopeSaver template_formals_filter(ScopeSaver popplings)
{   /* Lose the tagbinders, but they still hang around in global store */
    ScopeSaver h, p =
        (popplings && h0_(popplings) != s_binder) ? bindcdr_(popplings) : popplings;
    h = p;
    for (; p != NULL; p = bindcdr_(p))
    {   ScopeSaver q = bindcdr_(p);
        if (q != NULL &&
            h0_(q) != s_binder) bindcdr_(p) = bindcdr_(q);
    }
    return dreverse_binder(h);
}

/* Keep reasonably in step with scope actions with rd_formals().        */
static ScopeSaver rd_template_formals()
{   ScopeSaver popplings = NULL;
    if (curlex.sym == s_greater)
        /* no formal */;
    else {
      int scope_level = push_scope(0, Scope_TemplateArgs);
      for (;;)
      {   DeclRhsList *temp = rd_decl2(TFORMAL, 0);
          if (curlex.sym == s_nothing) nextsym();
          for (; temp != 0; temp = temp->declcdr)
          { if (debugging(DEBUG_TEMPLATE))
              cc_msg("template-formal: $r\n", temp->declname);
            if (temp->declname == 0)
              temp->declname = gensymval(1);  /* fixup to continue    */
          }
          if (curlex.sym == s_semicolon)   /* error recovery */
            cc_rerr(syn_rerr_semicolon_in_arglist);
          else if (curlex.sym != s_comma) break;
          nextsym();
      }
      popplings = template_formals_filter(pop_scope_no_check(scope_level));
    }
    checkfor_2ket(s_greater, s_comma);
    return popplings;
}

static Binder *find_typename(Symstr *sv, TagBinder *scope)
{   ExprList *p = (cur_template_actuals) ? *cur_template_actuals : NULL;
    Binder *b = NULL;
    for (; p != NULL; p = p->cdr)
    {   Expr *e = exprcar_(p);
        if (e && isprimtype_(type_(e), s_typedefname) &&
            bindsym_(typespecbind_(type_(e))) == sv &&
            tagbindsym_(bindparent_(typespecbind_(type_(e)))) == tagbindsym_(scope))
            return typespecbind_(type_(e));
    }
    if (!scope || (b = findbinding(sv, scope, INCLASSONLY)) == NULL)
        b = findbinding(sv, NULL, ALLSCOPES);
    if (b)
    {   if (!isprimtype_(bindtype_(b), s_typedefname) || !istypevar(bindtype_(b)))
            b = NULL;
    }
    return b;
}

static ExprList *rd_template_actuals(bool check)
{   ExprList *p = 0, *q = 0, *temp;
    TagBinder *old_curlex_scope = curlex_scope;
    Binder *old_curlex_binder = curlex_binder,
        *old_curlex_typename = curlex_typename;
    Expr *old_curlex_path = curlex_path;

    cur_template_actuals = &p;
    if (curlex.sym != s_greater) for (;;)
    {   Expr *e;
        rd_cpp_name(&TAS);
/* here we need to read a 't' or a 'e': generalise this routine.        */
        if (isdeclstarter2_(curlex))
        {   TypeExpr *t = rd_typename(TYPENAME);
            check_temp_type_arg_linkage(t);
            if (t != NULL)
                e = mk_expr1(s_typespec, t, 0);
            else
                e = errornode;
        }
        else
        {   e = rd_expr(UPTORELOP);
            check_temp_arg_linkage(e);
        }
/* The above line represents an ambiguity in [ES]. Page 345 gives a     */
/* good example.  Consider template-name<2*1>x...  We can't determine   */
/* from the read above whether '>' is greater-than or close-paren.      */
/* Resolve by reading a 'shift-expression' not a general expression.    */
        if (h0_(e) != s_error)
        {   temp = (ExprList *)syn_cons2(0, e);
            if (p == 0) p = q = temp; else cdr_(q) = temp, q = temp;
        }
        if (!check || curlex.sym != s_comma) break;
        nextsym();
    } else if (curlex.sym == s_greater)
        p = (ExprList *)syn_cons2(0, 0); /* empty actuals */
    if (check) checkfor_2ket(s_greater, s_comma);
    curlex_binder = old_curlex_binder;
    curlex_scope = old_curlex_scope;
    curlex_path = old_curlex_path;
    curlex_typename = old_curlex_typename;
    cur_template_actuals = NULL;
    return p;
}

static Handler *rd_handler()
{   Handler *p = 0, *q = 0, *temp;
    int ellipsis_yet = 0;
    if (curlex.sym == s_catch) while (curlex.sym == s_catch)
    {   int scope_level = push_scope(0, Scope_Ord);
        SynBindList *b = 0;
        Cmd *c;
        TypeExpr* caught_type = 0;
        bool handler_arg = false;
        nextsym();
        checkfor_ket(s_lpar);
        if (ellipsis_yet != 0)
          cc_err(sem_err_dotdotdot_handler_not_last);
        if (curlex.sym == s_ellipsis)
          {ellipsis_yet=1; nextsym();}
        else
        {   DeclRhsList *d = rd_decl2(CATCHER, 0);
            /* should we default declname to a gensym?                  */
            if (d && d->declname)
              { handler_arg = true;
                b = mkSynBindList(0, instate_declaration(d, CATCHER));
                caught_type = b -> bindlistcar -> bindtype;
              }
            else
              caught_type = d -> decltype; /* there's no handler arg */
            {
              Handler* pp = p;
              while (pp != 0)
                {
                    if (0 == type_derived_from(caught_type, pp->caught_type))
                      cc_warn(xsem_warn_unreachable_handler), pp=0;
                    else
                      pp = pp -> handcdr;
                  }
              }
        }
        checkfor_ket(s_rpar);
        c = rd_compound_statement(s_catch);
/* do we wish to read with blk_BODY (c.f. fn args and local body scope? */
        pop_scope(scope_level);
        temp = mkHandler(0, b, c, caught_type);
        if (p==0) p = q = temp; else q->handcdr = temp, q = temp;
    }
    else
        cc_err(syn_err_missing_catch_after_try);
    if (ellipsis_yet == 0)
      {     /* if there is no ... case, add  catch(...){throw;} */
        Cmd* c = mkthrow(syn_invented_fl, 0);
        temp = mkHandler(0, (SynBindList*) 0, c, 0);
        if (p==0) p = q = temp; else q->handcdr = temp, q = temp;
      }
    return p;
}

static void add_pendingfn_0(PendingFnList **pp, Symstr *name, Symstr *realname, TypeExpr *t,
                            SET_BITMAP stg, TagBinder *scope, ScopeSaver formaltags,
                            int tokhandle, ScopeSaver templateformals, bool tfn)
{   PendingFnList *x, *p;
    while ((p = *pp) != NULL) pp = &p->pfcdr;
    x = (PendingFnList *)GlobAlloc(SU_Other, sizeof(*x));
    x->pfcdr = NULL;
    x->pfname = name;
    x->pfrealname = realname;
    x->pftype = t;
    x->pfstg = stg;
    x->pfscope = scope;
    x->pf_formaltags = formaltags;
    x->pf_toklist_handle = tokhandle;
    x->pf_templateformals = templateformals;
    x->pf_tfn = tfn;
    *pp = x;
}

static void add_memfn_template(TagBinder *p, Symstr *name, Symstr *realname, TypeExpr *t,
                               SET_BITMAP stg, TagBinder *scope, ScopeSaver formaltags,
                               int tokhandle, ScopeSaver templateformals)
{
    add_pendingfn_0((PendingFnList **)&tagmemfns_(p), name, realname, t, stg, scope,
                    formaltags, tokhandle, templateformals, YES);
}

void add_pendingfn(Symstr *name, Symstr *realname, TypeExpr *t, SET_BITMAP stg,
                   TagBinder *scope, ScopeSaver formaltags, int tokhandle,
                   ScopeSaver templateformals, bool tfn)
{
    bool parse_only = (scope && ((tagbindbits_(scope) & TB_TEMPLATE)) ||
                       has_template_parameter(templateformals));
    if (tfn && !parse_only)
    {   TopDecl *fd;
        DeclRhsList *d;
        int sl;
        int save_bind_scope = bind_scope; /* will be changed by rd_fndef */
        TagBinder *old_access_context = set_access_context(NULL, NULL);
        SynBindList *old_syn_reftemps = syn_reftemps;
        FuncMisc tmp;
        Mark* mark;
        syn_reftemps = NULL;
        save_curfn_misc(&tmp);
        if (scope && tagactuals_(scope))
        {
            /*if (!tagscope_(scope)) syserr("weird template $c", scope);*/
            sl = push_var_scope(tagscope_(scope), Scope_TemplateDef);
            (void) push_var_scope(tagactuals_(scope), Scope_TemplateArgs);
            (void) push_var_scope(templateformals, Scope_TemplateArgs);
        }
        else
            sl = push_var_scope(templateformals, Scope_TemplateArgs);
        mark = alloc_mark();
        cg_reinit();
        /* If I'm cg'ing on the fly, I can be a bit more adventurous.
           A bitofstg_(s_inline) may help performance. But the function
           becomes static. Dump the function in a common code area?
         */
        d = reinvent_fn_DeclRhsList(name, realname, t, stg);
        if (stg & b_memfna) memfn_typefix(d, scope);
        (void) set_access_context(scope, NULL);
        if (debugging(DEBUG_TEMPLATE))
            cc_msg("template fn $r ...\n", realname != NULL ? realname : d->declname);
        push_nested_context(xsyn_info_instantiate_fn, (IPtr)scope,
                            (IPtr)(realname != NULL ? realname : d->declname));
        lex_openbody(tokhandle, tfn, NO, NULL, NULL);
        fd = rd_fndef(d, TOPLEVEL, scope, formaltags, templateformals);
        bind_scope = save_bind_scope;
        pop_scope_no_check(sl);
        lex_closebody();
        (void)set_access_context(old_access_context, NULL);
        cg_topdecl(fd, curlex.fl);
        drop_local_store();
        pop_nested_context();
        alloc_unmark(mark);
        syn_reftemps = old_syn_reftemps;
        restore_curfn_misc(&tmp);
    }
    else
        add_pendingfn_0(&syn_pendingfns, name, realname, t, stg, scope, formaltags,
                        tokhandle, templateformals, tfn);
}

static void rebind_typename_typedef(BindList *cc, ScopeSaver env)
{
    for (; cc; cc = cc->bindlistcdr)
        /* misnomer here, the intention is to fix up class specific
           typedef's which were originally hidden away by typename.
         */
        fixup_template_arg_type(bindtype_(cc->bindlistcar), env);
}

void syn_attempt_template_memfn(Binder *generic, Binder *specific)
{   PendingFnList *x, **prev;
    TagBinder *primary;
    if (realbinder_(specific) == NULL)
        syserr("weird member $b\n", specific);
    {   BindList *bl;
        if ((bl = bindftlist_(generic)) != NULL)
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
            {   BindList *ins = bindinstances_(tmpts->bindlistcar);

                for (; ins; ins = ins->bindlistcdr)
                    if (ins->bindlistcar == specific) return;
            }
        }
    }

    prev = (PendingFnList **)&tagmemfns_(bindparent_(specific));
    x = *prev;
    for (; x != NULL; prev = &x->pfcdr, x = x->pfcdr)
        if (x->pfname == bindsym_(realbinder_(specific)))
        {   add_pendingfn(x->pfname, x->pfrealname, x->pftype, x->pfstg, x->pfscope,
                          x->pf_formaltags, x->pf_toklist_handle, x->pf_templateformals,
                          x->pf_tfn);
            bindstg_(specific) &= ~b_undef;
            *prev = x->pfcdr;
            return;
        }

    /* try again for out-of-class definition for the specific of the
       primary, but not if it an explicitly specialized instance */
    if (!(tagbindbits_(bindparent_(specific)) & TB_SPECIALIZED) &&
        (primary = tagprimary_(bindparent_(specific))) != NULL)
    {   Binder *b;
        Symstr *sv = bindsym_(generic);

        if (generic == specific)
        {   char *tmp = symname_(sv);
            bool a = (strncmp(tmp, symname_(ctorsym), strlen(symname_(ctorsym))) == 0),
                 b = (strncmp(tmp, symname_(dtorsym), strlen(symname_(dtorsym))) == 0);
            if (!a && !b)
                syserr("syn_attempt_template_memfn: what kind of generic is this $b?",
                       generic);
            sv = a ? ctorsym : dtorsym;
        }
        b = findbinding(sv, primary, INCLASSONLY);

        if (b != NULL && h0_(bindtype_(b)) == t_ovld)
        {   BindList *tmpts;
            ExprList *args = NULL;
            FormTypeList *ft = typefnargs_(bindtype_(specific));
            int temp_scope;
            BindList *candidates = clone_bindlist(typeovldlist_(bindtype_(b)), NO);
            for (; ft; ft = ft->ftcdr)
                args = mkExprList(args, (Expr *)gentempbinder(ft->fttype));
            args = (ExprList *)dreverse((List *)args);
            rebind_typename_typedef(candidates, tagbindmems_(bindparent_(specific)));
            temp_scope = push_var_scope(tagactuals_(bindparent_(specific)),
                                        Scope_TemplateArgs);
            tmpts = temp_reduce(candidates, args, NULL, generic);
            if (tmpts == NULL)
            {   /* try again for template memfn */
                candidates = clone_bindlist(bindftlist_(b), NO);
                rebind_typename_typedef(candidates, tagbindmems_(bindparent_(specific)));
                tmpts = temp_reduce(bindftlist_(b), args, NULL, generic);
            }
            pop_scope_no_check(temp_scope);
            if (tmpts != NULL &&
                !(bindstg_(realbinder_(b = tmpts->bindlistcar)) & b_undef))
            {   FormTypeList *ft = typefnargs_(bindtype_(specific)),
                    *ft2 = typefnargs_(bindtype_(realbinder_(b)));
                ScopeSaver env = dup_env_actuals(bindformals_(realbinder_(b)), NULL);
                for (ft2 = ft2->ftcdr; ft && ft2; ft = ft->ftcdr, ft2 = ft2->ftcdr)
                    if (ft->ftname == NULL) ft->ftname = ft2->ftname;
                if (env)
                {   ScopeSaver tmp = env;
#if 0
                    for (; tmp; tmp = bindcdr_(tmp))
                    {   ScopeSaver actuals_env = tagactuals_(bindparent_(specific));
                        for (; actuals_env; actuals_env = bindcdr_(actuals_env))
                            if (bindsym_(actuals_env) == bindsym_(tmp))
                                bindtype_(tmp) = bindtype_(actuals_env);
                    }
#else
                    ScopeSaver actuals_env = tagactuals_(bindparent_(specific));
                    for (; tmp && actuals_env; tmp = bindcdr_(tmp),
                             actuals_env = bindcdr_(actuals_env))
                        bindtype_(tmp) = bindtype_(actuals_env);
                    if (tmp || actuals_env) syserr("incompatible type env");
#endif
                }
                add_pendingfn(bindsym_(realbinder_(specific)),
                              ovld_tmptfn_instance_name(bindsym_(realbinder_(b)), env),
                              globalize_typeexpr_no_default_arg_vals(bindtype_(specific)),
                              bindstg_(realbinder_(b)), bindparent_(specific),
                              tagactuals_(bindparent_(specific)),
                              bindtext_(realbinder_(b)), env, YES);
                bindstg_(specific) &= ~b_undef;
            }
        } else if (b != NULL && h0_(bindtype_(b)) == s_fnap)
        {   Binder *realb = realbinder_(b);
            if (realb != NULL && bindtext_(realb) >= 0)
            {   add_pendingfn(bindsym_(realbinder_(specific)),
                              ovld_tmptfn_instance_name(bindsym_(realb), bindenv_(realb)),
                              globalize_typeexpr_no_default_arg_vals(bindtype_(specific)),
                              bindstg_(realb), bindparent_(specific),
                              tagactuals_(bindparent_(specific)),
                              bindtext_(realb), bindformals_(realb), YES);
                bindstg_(specific) &= ~b_undef;
            }
        }
    }
}

static ScopeSaver applicable_template_formals(void)
{   ScopeSaver t = NULL;
    if (cur_template_formals)
    {   t = cur_template_formals->bindlistcar;
        cur_template_formals = (BindList *) discard2((VoidStar)cur_template_formals);
    }
    return t;
}

ScopeSaver cur_tformals(void)
{
    return (cur_template_formals) ? cur_template_formals->bindlistcar : NULL;
}

static void syn_implicit_instantiate(TagBinder *primary, TagBinder *instance)
{   TagBinder *instantiatetemplate;

    if ((tagbindbits_(instance) & TB_DEFD) || (tagbindbits_(instance) & TB_BEINGDEFD))
        return;
    instantiatetemplate = class_template_reduce(primary, taginstances_(primary),
                                                tagactuals_(instance));

    if (tagbindbits_(instantiatetemplate) & TB_DEFD)
    {   int h = tagtext_(instantiatetemplate);
        BindList *old_cur_template_formals = cur_template_formals;
        if (debugging(DEBUG_TEMPLATE))
            cc_msg("instantiate $c buffer[%d]\n", instantiatetemplate, h);
        if (h < 0)
            syserr("template symbol buffer lost");
        else
        {   int instantiatescope = push_var_scope(tagscope_(instance), Scope_TemplateDef);
            (void) push_var_scope(tagactuals_(instance), Scope_TemplateArgs);
            push_nested_context(xsyn_info_instantiate_class, (IPtr)instance, 0);
            lex_openbody(h, YES, NO, bindsym_(instantiatetemplate), bindsym_(instance));
            tagbindbits_(instance) |= TB_BEINGDEFD;
            rd_classdecl_(instance);
            /* more to do c.f. rd_declspec */
            tagbindbits_(instance) = (tagbindbits_(instance) & ~TB_BEINGDEFD)|TB_DEFD;
            tagprimary_(instance) = instantiatetemplate;
            lex_closebody();
            pop_scope_no_check(instantiatescope);
            if (syn_generatedfns || syn_pendingfns)
            {   TagBinder *old_access_context = set_access_context(NULL, NULL);
                PendingFnList *old_pendingfns;
                FuncMisc tmp;
                Mark* mark;
                save_pendingfns(&old_pendingfns), save_curfn_misc(&tmp);
                mark = alloc_mark();
                chk_for_auto = YES;
                while (syn_generatedfns || syn_pendingfns)
                {   TopDecl *d;
                    cg_reinit();  /* BEFORE rd_topdecl() */
                    /* there is a alloc_unmark() in case of
                       syn_generatedfns */
                    d = rd_topdecl(NO);
                    /* careful about function template */
                    if (h0_(d) != s_fndef) continue;
                    cg_topdecl(d, curlex.fl);
                }
                chk_for_auto = NO;
                alloc_unmark(mark);
                restore_curfn_misc(&tmp), restore_pendingfns(old_pendingfns);
                (void)set_access_context(old_access_context, NULL);
            }
            pop_nested_context();
        }
        cur_template_formals = old_cur_template_formals;
    }
}

/* Almost rd_template_postfix() but without the tokens available */
TagBinder *syn_implicit_instantiate_2(TagBinder *tb)
{   Symstr *sv;
    TagBinder *tb2;
    ScopeSaver env = tagformals_(tb);
    ExprList *actuals = NULL;
    bool newtag = NO;
    for (; env; env = bindcdr_(env))
    {   Binder *b = findbinding(bindsym_(env), 0, FB_LOCALS|FB_THISSCOPE);
        Expr *e;
        if (!b) syserr("Odd template type arg $r", bindsym_(env));
        e = (Expr *)syn_list4(s_typespec,
                              primtype2_(bitoftype_(s_typedefname), b), 0, 0);
        actuals = (ExprList *)syn_cons2(actuals, e);
    }
    actuals = (ExprList *)dreverse((List *)actuals);
    env = tagformals_(tb);
    sv = ovld_template_app(bindsym_(tb), env, actuals);
    tb2 = instate_tagbinding(sv, tagbindsort(tb), TD_Decl, TOPLEVEL|TEMPLATE, &newtag);
    if (newtag)
    {   Binder *b = instate_classname_typedef(tb2, TOPLEVEL);
        tagprimary_(tb2) = tb;
        tb2->tagparent = NULL;
        tagscope_(tb2) = tagscope_(tb);
        attributes_(b) |= A_TEMPLATE;
        tagactuals_(tb2) = globalize_template_arg_binders(env, actuals);
    }
    syn_implicit_instantiate(tb, tb2);
    return tb2;
}

void parameter_names_transfer(FormTypeList *from, FormTypeList *to)
{   if (length((List*)from) != length((List *)to))
        syserr("incompatible parameter type lists");
    for (; to && from; to = to->ftcdr, from = from->ftcdr)
        to->ftname = from->ftname;
}

void xsyn_reinit()
{   rootOfPath = NULL;
    recursing = 0;
}

static void xsyn_init(void)
{   saved_temps = NULL;
    recursing = 0;
}

/* End of cppfe/xsyn.c */
