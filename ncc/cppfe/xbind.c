/*
 * xbind.c: various binding and lexing routines for C++ compiler
 * Copyright (C) Codemist Ltd., 1987-1992.
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Advanced RISC Machines Limited, 1991-1992, 1994
 * SPDX-Licence-Identifier: Apache-2.0
 * All rights reserved
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#include <stddef.h>         /* for offsetof() */
#include <string.h>
#include <ctype.h>
#include "globals.h"
#include "defs.h"
#include "aetree.h"
#include "util.h"           /* for padstrlen()... */
#include "codebuf.h"        /* for padstatic()... */
#include "cgdefs.h"         /* @@@ just for GAP */
#include "bind.h"
#include "builtin.h"
#include "lex.h"            /* for curlex... */
#include "sem.h"            /* for prunetype, equivtype... */
#include "syn.h"            /* for add_pendingfn */
#include "store.h"
#include "vargen.h"         /* for initstaticvar()... */
#include "xrefs.h"          /* for LIT_LABEL */
#include "errors.h"
#include "aeops.h"
#define _BIND_H

static void set_linkage(Binder *b, SET_BITMAP linkage, Binder *m);
static Expr *path_to_member_2(ClassMember *mem, TagBinder *b, int flags,
        ClassMember *vbases, TagBinder *privately_deriving_class);
static Expr *path_to_base_member(ClassMember *mem, TagBinder *b, int flags,
        ClassMember *vbases, TagBinder *privately_deriving_class);
static ClassMember *instate_member_cpp(DeclRhsList *d, int bindflg);
static Binder *instate_member_binder(DeclRhsList *d /*, int bindflg*/);
static Binder *instate_declaration_cpp(DeclRhsList *d, int declflag);
static Binder *implicit_decl_cpp(Symstr*);


static int merge_default_arguments(TypeExpr *bt, TypeExpr *dt)
{   FormTypeList *bft, *dft;
    int msg = 0, musthavedefault = 0, minargs = 0, argno = 1;
    bt = princtype(bt);
    dt = princtype(dt);
    if (h0_(bt) != t_fnap || h0_(dt) != t_fnap)
        syserr("merge_default_arguments(%ld, %ld)", h0_(bt), h0_(dt));
    bft = typefnargs_(bt);
    dft = typefnargs_(dt);

/* Called with bt == dt to check that default arguments on a first decl */
/* of this function are at the end of the argument list.                */

    while (bft != 0 && dft != 0)
    {   if (dft->ftdefault != 0)
        {   /* the new declaration has a default argument value... */
            if (dft != bft && bft->ftdefault != 0)
            {   cc_err(sem_err_dupl_default_value,
                    argno, bft->ftname != 0 ? bft->ftname : dft->ftname);
                msg = 1;
            }
            else
            {   bft->ftdefault = dft->ftdefault;
                musthavedefault = 1;
            }
        }
        else if (bft->ftdefault == 0)
        {   if (musthavedefault)
            {   cc_err(sem_err_missing_default_value,
                   argno, bft->ftname != 0 ? bft->ftname : dft->ftname);
                msg = 1;
            }
            else
                ++minargs;
        }
        /* template fns need the following line */
        bft->ftname = dft->ftname;
        if (bft->ftname != thissym) ++argno;
        bft = bft->ftcdr;  dft = dft->ftcdr;
    }
    minargs_(bt) = minargs_(dt) = minargs;
    if (msg) return 0;
    if (bt == dt) return 2;
    return equivtype(bt, dt);
}

static Expr *nullbinder(TagBinder *cl)
{
    return (Expr *)mk_binder(0, u_referenced, tagbindtype_(cl));
}

static Symstr *hiddenmembername(char pfx, Symstr *sv)
{   char name[128];
    sprintf(name, "__%c_%s", pfx, symname_(sv));
    return sym_insert_id(name);
}

#include "bind.c"
#include "mcdep.h"

ClassMember *mk_member(TagBinder *basename, TypeExpr *t,
                       SET_BITMAP attributes, TagBinder *parent)
{   ClassMember *mem =
        (ClassMember *)GlobAlloc(SU_Other, (int32)SIZEOF_CLASSMEMBER);
    h0_(mem) = s_member;
    memcdr_(mem) = NULL;
    memsv_(mem) = hiddenmembername(attributes & CB_VBASE ? 'V' :
                                     attributes & CB_BASE ? 'B' :
                                     attributes & CB_CORE ? 'C' : 'P',
                                   bindsym_(basename));
/* AM: I have chosen to globalise 't' here -- this parallels            */
/* instate_member &c.  It also allows the possibility of an             */
/* 'attributes' flag to alter this dynamically.                         */
/* Caching in globalize() will mean that this does not cost store.      */
    memtype_(mem) = globalize_typeexpr(t);
    bindparent_(mem) = parent;
    attributes_(mem) = attributes & ~A_LOCALSTORE | A_GLOBALSTORE;
    bindstg_(mem) = 0;  /* b_member? */ /* @@@ share this forgery code! */
    return RecordGlobalBinder(mem);
}

/* mk_core_part has to forge a struct definition and hence to           */
/* globalise types in its members.                                      */
/* Can this code be shared with instate_tagbinding &c?                  */
ClassMember *mk_core_part(TagBinder *cl, ClassMember *bases,
                          ClassMember *vbases)
{   ClassMember *m = bases;
    if (vbases)
    {   Symstr *corename = hiddenmembername('K', bindsym_(cl));
        TagBinder *b = clone_tagbinder(corename, cl);
        tagbindbits_(b) |= TB_CORE|TB_BEINGDEFD;
        tagbindmems_(b) = bases;
        b->tagparent = cl;
        m = mk_member(cl, tagbindtype_(b), bitofaccess_(s_public)|CB_CORE, cl);
        memcdr_(m) = vbases;
    }
    return m;
}

/* used for C++ 'core' members.                                         */
TagBinder *clone_tagbinder(Symstr *newname, TagBinder *b)
{   SET_BITMAP bits = tagbindbits_(b) & ENUMORCLASSBITS;
    TagBinder *p = global_mk_tagbinder(NULL, newname, s_struct);
    tagbindbits_(p) = bits | TB_CORE;
    tagbindtype_(p) =
        globalize_typeexpr(primtype2_(bits, p)); /* or tagbindtype_(b)? */
    tagbindparent_(p) = tagbindparent_(b);
    return p;
}

#define CHECK_INHERITED_VIRTUAL  FB_CIV

/* memfn_realtype performs the mapping (e.g.)                           */
/*      'int cl::f() volatile' => 'int f(volatile cl *const)'           */
/* fntype is presumed already prunetype()d.                             */
extern TypeExpr *memfn_realtype(TypeExpr *fntype, TagBinder *cl)
{   /* now in local store -- users (or instate_declaration) globalize.  */
    /* @@@ soon add extra arg for __ct if TagBinder has a virt. base.   */
    TypeExprFnAux s;
    TypeExpr *thistype = mk_typeexpr1(t_content,
                    mkqualifiedtype(tagbindtype_(cl), typeptrmap_(fntype)),
                    (Expr *)bitoftype_(s_const));
/* Next line allocates a DeclRhsList for use by memfn_fixtype (q.v.)    */
/* when, for this code, a FormTypeList would suffice.                   */
    DeclRhsList *d = mkDeclRhsList(thissym, thistype, bitofstg_(s_auto));
    d->declcdr = typefnargs1_(fntype);
    return mkTypeExprfn(t_fnap, typearg_(fntype), 0, (FormTypeList *)d,
        packTypeExprFnAux(s, minargs_(fntype) + 1,
                             maxargs_(fntype) + (maxargs_(fntype)<999 ? 1:0),
                             0,     /* special_variad  */
                             0,     /* syn_oldeformals */
                             0));   /* flags - e.g. no side effects */
}

extern TypeExpr *add_delete_arg(TypeExpr *fntype, bool is_declaration)
{   TypeExprFnAux s;
    DeclRhsList *d = mkDeclRhsList(deletesym, te_int, bitofstg_(s_auto));
    d->declcdr = typefnargs1_(fntype);
    if (is_declaration)
        declinit_(d) = lit_zero;
    return mkTypeExprfn(t_fnap, typearg_(fntype), 0, (FormTypeList *)d,
        packTypeExprFnAux(s, minargs_(fntype) + 1,
                             maxargs_(fntype) + (maxargs_(fntype)<999 ? 1:0),
                             0,     /* special_variad  */
                             0,     /* syn_oldeformals */
                             0));   /* flags - e.g. no side effects */
}

static void set_linkage(Binder *b, SET_BITMAP linkage, Binder *m)
/* b may also be a TagBinder *... */
{   SET_BITMAP a = attributes_(b) & (A_NOLINKAGE+A_INTERN+A_EXTERN);

    if (a == 0)
        attributes_(b) |= linkage;
    else if (a != linkage)
    {   if (a & A_NOLINKAGE)
            cc_rerr(bind_rerr_linkage_disagreement_2, b, m);
        else
            cc_rerr(bind_rerr_linkage_disagreement_3, b, m);
   }
}

int32 base_vtable_sz(TagBinder *b)
{   ClassMember *m;
    int32 sz = 0;
    for (m = tagbindmems_(b);  m != NULL;  m = memcdr_(m))
    {   if (attributes_(m) & (CB_CORE|CB_BASE|CB_VBASE))
            sz += base_vtable_sz(typespectagbind_(princtype(memtype_(m))));
        else if (attributes_(m) & CB_VTAB)
            sz += memvtablesize_(m);
    }
    return sz;
}

static ClassMember *lmost_vtable0(TagBinder *b)
{   ClassMember *m = tagbindmems_(b), *vtab;

    if ((m != NULL) && (attributes_(m) & (CB_CORE|CB_BASE)))
    {   vtab = lmost_vtable0(typespectagbind_(princtype(memtype_(m))));
        if (vtab) return vtab;
    }
    for (; m != NULL; m = memcdr_(m))
        if (is_datamember_(m) && (attributes_(m) & CB_VTAB))
            return m;

    return NULL;
}

static ClassMember *lmost_vtable(TagBinder *b)
{   ClassMember *m = tagbindmems_(b);
    if ((m != NULL) && (attributes_(m) & (CB_CORE|CB_BASE)))
        return lmost_vtable0(typespectagbind_(princtype(memtype_(m))));
    return NULL;
}

static int32 lmost_vtable_sz0(TagBinder *b)
{   ClassMember *m;
    int32 sz = 0;
    bool seen_lmost = NO;
    for (m = tagbindmems_(b); m != NULL; m = memcdr_(m))
    {   if (attributes_(m) & (CB_VBASE|CB_BASE))
        {   if (!seen_lmost)
            {   sz = lmost_vtable_sz0(typespectagbind_(princtype(memtype_(m))));
                seen_lmost = YES;
            } else
                sz += base_vtable_sz(typespectagbind_(princtype(memtype_(m))));
        }
        if (attributes_(m) & CB_VTAB)
            sz += memvtablesize_(m);
    }
    return sz;
}

static int32 lmost_vtable_sz(TagBinder *b)
{   ClassMember *m = tagbindmems_(core_class(b));
    if ((m != NULL) && (attributes_(m) & CB_BASE))
        return lmost_vtable_sz0(typespectagbind_(princtype(memtype_(m))));
    return 0;
}

static ClassMember *add_vtable_pointer(void)
{   ClassMember *m;
    ClassMember *vtab, *p, **pp = &tagbindmems_(local_scope->class_tag);

    if ((vtab = lmost_vtable(local_scope->class_tag)) != NULL)
    {   /* we'll share the __VTABLE slot with our left-most base class  */
        /* but we add a typedef __VTABLE member to remember the number  */
        /* of virtual functions in this class that are not also in the  */
        /* left-most base class.  Being a typedef it will take no       */
        /* storage.                                                     */
        /* type for vtab points to the parent class to look for the     */
        /* actual vtab.                                                 */
        DeclRhsList *d = mkDeclRhsList(vtabsym,
                ptrtotype_(tagbindtype_(bindparent_(vtab))), bitofstg_(s_typedef));
        m = instate_member_binder(d /*, LOCALSCOPE*/);
        attributes_(m) = bitofaccess_(s_public) | CB_VTAB;
        return m;
    }
    m  = (ClassMember *)GlobAlloc(SU_Bind, SIZEOF_CLASSMEMBER);
    h0_(m) = s_member;
    memsv_(m) = vtabsym;
    memtype_(m) = globalize_typeexpr(ptrtotype_(te_ulint));
    memwoff_(m) = OFFSET_UNSET; memboff_(m) = 0; membits_(m) = 0;
    memvtablesize_(m) = 0;
    attributes_(m) = bitofaccess_(s_public) | CB_VTAB;
    bindstg_(m) = 0;
    bindparent_(m) = local_scope->class_tag;
again:
    for (p = *pp;  p != 0;  pp = &memcdr_(p), p = *pp)
    {   if (attributes_(p) & CB_CORE)
        {   pp = &tagbindmems_(typespectagbind_(memtype_(p)));
            goto again;
        }
        if (!(attributes_(p) & (CB_BASE|CB_VBPTR))) break;
    }
    *pp = m;
    memcdr_(m) = p;

    return RecordGlobalBinder(m);
}

static bool is_leftmost_derivation(TagBinder *tb, TagBinder *parent)
{   ClassMember *m = tagbindmems_(parent);

    if (attributes_(m) & (CB_CORE|CB_BASE))
    {   TypeExpr *t = princtype(memtype_(m));
        TagBinder *base;
        if ((base = typespectagbind_(t)) == tb) return YES;
        return is_leftmost_derivation(tb, base);
    }
    return NO;
}

/* This function creates the skeleton of a 'core' function for generated */
/* ctors, dtors, operator=() and for user-defined ctors and dtors, for   */
/* classes which have virtual bases. The core function contains the body */
/* of the user-written code and deals with non-virtual bases. The top    */
/* level function handles virtual bases, vtable pointers and calls the   */
/* core function. The core function is not a class member. The type of   */
/* the core function is similar to that of the top-level function, save  */
/* that class-valued arguments are replaced by ref-to-class arguments.   */

static Binder *add_core_binder_to(Binder *b)
{   char corename[128];
    Symstr *sv;
    TypeExpr *fntype = bindtype_(b);
    FormTypeList *ft, *ftp = 0, *ftq = 0;
/* inherit inline/static/extern from the top-level binder...             */
    SET_BITMAP stg = (bindstg_(b) &
        (bitofstg_(s_inline)|bitofstg_(s_static)|bitofstg_(s_extern))) |
                      b_generated | b_fnconst;

/* The name of the core function is foo__C...                            */
    strcpy(corename, bindsym_(b)->symname);
    strcat(corename, "__C");
    sv = sym_insert_id(corename);

/* Clone the function's type - class-type args become ref-type args...   */
    for (ft = typefnargs_(fntype);  ft != 0;  ft = ft->ftcdr)
    {   TypeExpr *t = princtype(ft->fttype);
        FormTypeList *f = mkFormTypeList(0, ft->ftname,
              isclasstype_(t) ? mk_typeexpr1(t_ref, t, 0) : ft->fttype, 0);
        if (ftp == 0)
            ftp = (ftq = f);
        else
            ftq = (ftq->ftcdr = f);
    }
    fntype = mkTypeExprfn(t_fnap, typearg_(fntype),
                typeptrmap_(fntype), ftp, &typefnaux_(fntype));

    attributes_(b) |= CB_HASCOREFN;             /* used by mkfnap_cpp() */
    return realbinder_(b) =
        global_mk_binder(0, sv, stg, globalize_typeexpr(fntype));
}

static Binder *instate_member_binder(DeclRhsList *d /*, int bindflg*/)
{   Binder *b, *btop;
/* bindflg is set so that all structs are globalized except within fns. */
/* This includes structs declared in formal parameter lists whose scope */
/* is only the function.                                                */
    TypeExpr *t = d->decltype;
    SET_BITMAP stg = killstgacc_(d->declstg);
    SET_BITMAP access = attribofstgacc_(d->declstg);
    TagBinder *parent = local_scope->class_tag;
    Binder *inheritb = NULL;

    if (parent == NULL)
    {   /* this happens when member is a function template, and local_scope is
           the formal template type scope.
         */
        parent = local_scope->prev->class_tag;
    }
    t = globalize_typeexpr(t);
    if (isfntype(t) && !(stg & bitofstg_(s_typedef)))
    {   inheritb = findbinding(d->declname, parent,
                               INDERIVATION+CHECK_INHERITED_VIRTUAL);
/* @@@ See [ES, p209], but there is a nasty ambiguity in the following: */
/*    class A { virtual int f(); }; class B { int f(); };               */
/*    class C:A,B { int f(); }.  Is C::f virtual or not?                */
        if (inheritb && bindstg_(inheritb) & bitofstg_(s_virtual))
        {   if (!equivtype(t, bindtype_(inheritb)))
                cc_rerr(xbind_rerr_inherited_type_differs, inheritb);
            if (!(stg & (bitofstg_(s_virtual)|b_generated))
                && !SuppressDB_Has(Suppress_ImplicitVirtual))
                cc_warn(xbind_warn_implicit_virtual, parent, d->declname);
            stg |= bitofstg_(s_virtual);
/* Conspire with syn.c(MEMFNBITS) to suppress 'unused this' warnings:   */
            d->declstg |= bitofstg_(s_virtual);
        }
        else
            inheritb = 0;
    }
    /* always globalise member fns for C++ (local structs!).            */
    b = global_mk_binder(NULL, d->declname, stg, t);
    bindparent_(b) = parent;
/* @@@ Fix the next line?  (E.g.) generate a top-level extern struct    */
/* with bit field entry.  Also such padding (sv=0) bit fields.          */
    if (declbits_(d)) syserr("static member bit field");
    attributes_(b) |= access;
    if (strncmp(symname_(bindsym_(b)), "__op", 4) == 0)
        attributes_(b) |= CB_TCONV;

    {   Scope *saved_scope = local_scope;
        while (local_scope->kind == Scope_Args ||
               local_scope->kind == Scope_TemplateArgs)
            local_scope = local_scope->prev;
        add_local_binder(b);
        local_scope = saved_scope;
    }

    t = princtype(t);
    if (h0_(t) == t_fnap && !(stg & bitofstg_(s_typedef)) ||
            (stg & bitofstg_(s_static)))
    {   DeclRhsList decl;               /* @@@ forgery! */
        ClassMember *vtable = NULL;
        if (h0_(t) == t_fnap)
        {   stg |= b_fnconst;
            if (stg & bitofstg_(s_virtual))
            {   vtable = findbinding(vtabsym, parent, INCLASSONLY);
                if (vtable == NULL) vtable = add_vtable_pointer();
                tagbindbits_(parent) |= TB_HASVTABLE;
            }
            if (!(stg & bitofstg_(s_inline)))
            {   /* and not inline => maybe inline... */
/*/* The DRAFT in section 7.1.2 agrees with the A.R.M. but contradicts  */
/* the DRAFT section 3.4, which implies member fns have EXTERN linkage  */
/* or NO LINKAGE, following the linkage of the containing class. They   */
/* cannot have INTERNAL linkage, which is what b_maybeinline manages.   */
/*              stg |= b_maybeinline;   <<<<<<<<<<<<<<<<<<<<<<<<<<<<<   */

                /* a member function not explicitly inline gives this   */
                /* class external linkage. (DRAFT std section 3.4).     */
                set_linkage((Binder *)parent, A_EXTERN, b);
            }
            if (stg & bitofstg_(s_static))
                stg |= b_memfns;
            else
            {   /* a MEMBER function, not static or friend... */
                if (strncmp(symname_(d->declname), "__dt", 4) == 0)
                    t = add_delete_arg(t, YES);
                t = memfn_realtype(t, parent);
                stg |= b_memfna;
            }
        }
        else
        {   /* a static data member gives this class external linkage   */
            /* (DRAFT std section 3.4).                                 */
            set_linkage((Binder *)parent, A_EXTERN, b);
        }
        decl.declname = ovld_add_memclass(d->declname, parent,
                                          (stg & b_memfns) != 0);
        /* We are declaring a member function or static member. Linkage */
        /* is in fact external unless we have an in-line function in a  */
        /* NOLINKAGE (local) class.                                     */
        if ((stg & bitofstg_(s_inline)) && (attributes_(parent) & A_NOLINKAGE))
            stg = (stg & ~bitofstg_(s_extern)) | bitofstg_(s_static);
        else
            stg = (stg & ~bitofstg_(s_static)) | bitofstg_(s_extern);
#if WANTS_BAD_TYPE_DISAGREEMENT_BUG
        decl.decltype = t;
#else
        /* princtype() removes qualifiers from the typedef type. This
           is BAD news for "typedef int Int; struct X { static const Int x; };"
         */
        decl.decltype = (h0_(t) == t_fnap) ? t : d->decltype;
#endif
        decl.declstg = stg | b_undef;   /* no stgaccof_() bits!         */
        d->declstg = stg;
            /* In case of inline fn defn..., because rd_decl() saves it */
            /* when the fn body is read... later used by instate_decl() */
        btop = instate_declaration_cpp(&decl, TOPLEVEL);
        realbinder_(b) = btop;
#if 0
        /* See if there is a defn in the primary template */
        if (bindstg_(btop) & bitofstg_(s_extern)
            && !(qualifiersoftype(t) & bitoftype_(s_const))
            && h0_(t) != t_fnap
            && tagprimary_(local_scope->class_tag) != NULL)
        {   TagBinder *tb = local_scope->class_tag;
            Binder *b1 = findbinding(bindsym_(b), tagprimary_(tb),
                                     FB_LOCALS|FB_THISSCOPE);
            if (!b1 || !realbinder_(b1))
                syserr("Lost static member $b in $c", b, tb);
            if (bindconst_(realbinder_(b1)) != NULL)
            {   DeclRhsList *d;
                Expr *einit = bindconst_(realbinder_(b1));
                push_exprtemp_scope();
                einit = mkcast(s_init, einit, bindtype_(btop));
                if (h0_(einit) != s_error)
                {   einit = cpp_mkbinaryorop(s_init, (Expr *)btop, einit);
                    bindstg_(btop) &= ~b_undef;
                    d = mkDeclRhsList(bindsym_(btop), bindtype_(btop), bindstg_(btop));
                    d->declbind = btop;
                    (void) genstaticparts(d, YES, typehasctor(bindtype_(btop)), einit);
                }
                if (killexprtemp() != NULL) syserr("extra temps leaked");;
            }
        }
#endif
/* @@@ AM wants to revisit the b_pseudonym code.  Maybe more should     */
/* be done by simplify or cg?                                           */
        bindstg_(b) = stg;
        bindstg_(b) |= stg & (b_memfna|b_memfns) ? b_impl : b_pseudonym;
        if (vtable != NULL)
        {   if (inheritb && var_cc_private_flags & 4194304)
                cc_msg("Override $b @%2d\n", realbinder_(inheritb),
                        bindxx_(realbinder_(inheritb)));
            if (inheritb != NULL)
            {   TagBinder *tb = core_class(bindparent_(inheritb));
                if (is_leftmost_derivation(tb, parent) == NO)
                    inheritb = 0;
            }
            if (inheritb && h0_(inheritb) != s_error)
                bindxx_(btop) = bindxx_(realbinder_(inheritb));
            else
            {   bindxx_(btop) = lmost_vtable_sz(parent) + memvtablesize_(vtable);
                ++memvtablesize_(vtable);
            }
            if (!inheritb && var_cc_private_flags & 4194304)
                cc_msg("Final override $b @%2d\n", btop, bindxx_(btop));
        }
        if (h0_(t) == t_fnap && symname_(bindsym_(b))[0] == '_')
        { /* tagbindbits_(parent) & TB_HASVBASE is not setup until end_strdecl */
          ClassMember *firstmem = tagbindmems_(parent);
          if (firstmem != 0 && (attributes_(firstmem) & CB_CORE))
          {   /* /* probably we should have attributes bits CB_CTOR, etc. */
              const char* name = symname_(bindsym_(b));
              if (strncmp(name, "__ct", 4) ||
                  strncmp(name, "__dt", 4) ||
                  strncmp(name, "__as", 4))
                  add_core_binder_to(btop);
          }
        }
    }
    else if (stg & bitofstg_(s_typedef))
    {   /* class-local typedef... */
        TypeExpr *pt = princtype(d->decltype);
        if (usrdbg(DBG_PROC))
            /* /* Err... what's the real intention here? */
            dbg_type(ovld_add_memclass(bindsym_(b), parent, 0),
                     bindtype_(b), d->fileline);
        /* a member type with EXTERNAL linkage gives this class extern  */
        /* linkage (DRAFT std section 3.4).                             */
        if (isclasstype_(pt) && (attributes_(typespectagbind_(pt)) & A_EXTERN))
            set_linkage((Binder *)parent, A_EXTERN, b);
    }
    return b;
}

/* overloading parts: unify with instate_declaration.                   */
static ClassMember *instate_member_cpp(DeclRhsList *d, int bindflg)
{   Symstr *sv = d->declname;
    TypeExpr *dt = d->decltype;

    d->declbind = 0;
    if (sv == NULL || !isfntype(dt) || (d->declstg & bitofstg_(s_typedef)))
    {   /* bitfield padding, not a function, or a typedef  */
        /*/* class-scope ENUMs not properly handled yet... */
        if (sv != 0 && (d->declstg & STGBITS))
            /* non-function static member or typedef */
            return instate_member_binder(d /*, bindflg*/);
        else
            return instate_member_1(d, bindflg);
    }
    else if (d->declstg & bitofstg_(s_friend))
    {   TagBinder *parent = local_scope->class_tag;
        Binder *btop;
        SET_BITMAP stg = killstgacc_(d->declstg);
        int flags = /*(tagbindbits_(parent) & TB_TEMPLATE || tagprimary_(parent)) ?
            LOCALSCOPE|GLOBALSTG :*/ TOPLEVEL;

        /* CD #2 11.4 disallows storage classes in friend decls         */
        /* 'extern' is already disallowed for all member decls          */
        /* catch 'static', 'mutable', etc, here                         */
        if (stg & (PRINCSTGBITS /* | bitofstg_(s_mutable) */))
            cc_rerr("storage class not allowed for friends -- ignored");
        stg = (stg & ~(PRINCSTGBITS /* | bitofstg_(s_mutable)*/)) |
            bitofstg_(s_extern);        /* 'extern' if no previus decl  */
        /* We need to set undef in case never defined... and unset it   */
        /* if defined inline. Side effects back in rd_declrhslist().    */
        d->declstg = stg | b_undef;
        if (is_dependent_type(d->decltype) || bindflg & TEMPLATE)
            flags |= TEMPLATE;
        if (tagprimary_(parent) != NULL &&
            (tagbindbits_(tagprimary_(parent)) & TB_TEMPLATE))
            flags |= SPECIALIZE;
        btop = instate_declaration_cpp(d, flags);
        mk_friend_fn(btop, parent);
        if (bindparent_(btop)) syserr("odd friend parent $b", btop);
        return btop;
    }
    else
    {   Binder *bgeneric = findbinding(sv, local_scope->class_tag, INCLASSONLY);
        if (bgeneric == NULL)
        {   /* always global for now (not for ever!).                   */
            bgeneric = global_mk_binder(NULL, d->declname, b_fnconst,
                    (TypeExpr *)global_list4(SU_Type, t_ovld,
                                             (TypeExpr*)DUFF_ADDR, 0, 0));
/* The t_ovld pseudo is marked to have the most access of any instance. */
/* @@@ However, instances then need checking (and aren't currently).    */
/* @@@ global_mk_binder etc need an attributes arg too!                 */
            attributes_(bgeneric) |= bitofaccess_(s_private);
            bindparent_(bgeneric) = local_scope->class_tag;
            add_local_binder(bgeneric);
        }
        /* If not the expected t_ovld, then show error and gen up a name */
        if (h0_(bgeneric) != s_binder ||
            h0_(bindtype_(bgeneric)) != t_ovld)
        {   cc_rerr(xbind_rerr_ovld_non_fn, bgeneric);
            d->declname = sv = gensymval(1);
            bgeneric = global_mk_binder(NULL, d->declname, b_fnconst,
                    (TypeExpr *)global_list4(SU_Type, t_ovld,
                                             (TypeExpr*)DUFF_ADDR, 0, 0));
/* The t_ovld pseudo is marked to have the most access of any instance. */
/* @@@ However, instances then need checking (and aren't currently).    */
/* @@@ global_mk_binder etc need an attributes arg too!                 */
            attributes_(bgeneric) |= bitofaccess_(s_private);
            bindparent_(bgeneric) = local_scope->class_tag;
            add_local_binder(bgeneric);
        }

        {   Binder *bspecific;
            TypeExpr *bt = bindtype_(bgeneric);
            BindList *bl = typeovldlist_(bt);
            /* 'operator new()' and 'operator delete()' are always static (12.5) */
            /* @@@ this needs to be extended to 'operator new[]()' and 'operator delete[]()' */
            bool is_operator_new = strcmp(sv->symname, "__nw") == 0;
            bool is_operator_delete = strcmp(sv->symname, "__dl") == 0;
            if (is_operator_new || is_operator_delete)
                d->declstg |= bitofstg_(s_static);
            d->declname = sv = (bindflg & TEMPLATE) ? ovld_function_template_name(sv, dt) :
                ovld_instance_name(sv, dt);
            if (is_operator_delete)
            {   if (bl != NULL)
                    cc_rerr(xbind_rerr_dl_cant_be_overloaded);
                else
                {   FormTypeList *f = typefnargs_(dt);
                    if (!isvoidtype(typearg_(dt)) ||
                        f == NULL || !isptrtovoidtype(f->fttype) ||
                        f->ftcdr != NULL && !equivtype(f->ftcdr->fttype, te_size_t))
                        cc_rerr(xbind_rerr_bad_dl_type, bgeneric);
                }
            }
            else
            {   if (is_operator_new)
                {   FormTypeList *f = typefnargs_(dt);
                    if (!isptrtovoidtype(typearg_(dt)) ||
                        f == NULL || !equivtype(f->fttype, te_size_t))
                        cc_rerr(xbind_rerr_bad_nw_type, bgeneric);
                }
                /* check for duplicates */
                for (; bl != NULL; bl = bl->bindlistcdr)
                {   if (bindsym_(bl->bindlistcar) == sv)
                    {   cc_rerr(syn_rerr_duplicate_member2(local_scope->class_tag, sv));
                        break;
                    }
                }
            }
           if (debugging(DEBUG_BIND)) cc_msg("overload member $r\n", sv);
/* Assert: sv != NULL && isfntype(dt) &&                                */
/*         !(d->declstg & (bitofstg_(s_typedef)|bitofstg_(s_friend)))   */
/* Now set minargs_(d->decltype) and check that default args trail...   */
            merge_default_arguments(dt, dt);
            bspecific = instate_member_binder(d /*, bindflg*/);
            if (h0_(bspecific) != s_binder) syserr("instate_member_overload");
            if (bindflg & TEMPLATE)
            {   /*bindstg_(bspecific) &= ~bitofstg_(s_inline);*/
                bindftlist_(bgeneric) = (BindList *)
                    global_cons2(SU_Bind, bindftlist_(bgeneric), bspecific);
            }
            else
                typeovldlist_(bt) =
                    (BindList *)global_cons2(SU_Type, typeovldlist_(bt), bspecific);
            if ((attributes_(bspecific) & ACCESSBITS) >
                (attributes_(bgeneric) & ACCESSBITS))
                attributes_(bgeneric) = (attributes_(bgeneric) & ~ACCESSBITS) |
                    (attributes_(bspecific) & ACCESSBITS);
            return bspecific;
        }
    }
}

static Scope *enclosing_non_class_scope(void)
{   Scope *scope = local_scope;
    while (scope && (scope->class_tag != NULL ||
                     scope->kind == Scope_TemplateDef ||
                     scope->kind == Scope_TemplateArgs))
        scope = scope->prev;
    return scope;
}

/* should declflag here be in d->declstg?                               */
static Binder *instate_declaration_cpp(DeclRhsList *d, int declflag)
{   Symstr *sv = d->declname;
    SET_BITMAP stg = d->declstg;
    if (debugging(DEBUG_BIND))
        cc_msg("instate_declaration_cpp(%x,%lx): $r\n", declflag,(long)stg,sv);
    if (!(declflag & INSTANCE) &&
        (h0_(princtype(d->decltype)) == t_fnap) &&
        sv != mainsym &&        /* static overloaded main forbidden!    */
        /* not top-level impl. of memfn or typedef  */
        !(stg & b_memfna+b_memfns+bitofstg_(s_typedef)))
    {   Scope* save_scope = local_scope;
        Binder *bgeneric, *bspecific;
        TagBinder *parent = current_member_scope();
        if (stg & bitofstg_(s_friend) /*&& !(declflag & TEMPLATE)*/)
            local_scope = enclosing_non_class_scope();

        bgeneric = findbinding(sv, NULL, FB_LOCALS|FB_THISSCOPE);
        /* Should look up at scope where the templatefn is defined! */
        if (bgeneric == NULL && declflag & TOPLEVEL)
            bgeneric = findbinding(sv, NULL, FB_LOCALS|TOPLEVEL);
/* @@@ next line hacks round implicit fns (or memfn implementations)    */
/* being moaned at as 'non-functions!'                                  */
        if (bgeneric && bindstg_(bgeneric) & bitofstg_(s_typedef) &&
              bindstg_(bgeneric) & u_implicitdef)
          bgeneric = 0;

        if (bgeneric == NULL || h0_(bindtype_(bgeneric)) == t_ovld)
        /* overload extension and resolution here.                      */
        {   TypeExpr *bt;
            TypeExpr *dt = princtype(d->decltype);

            if (d->declrealname != NULL)
                sv = d->declrealname;
            d->declname = (declflag & TEMPLATE || contains_typevars(dt)) ?
                ovld_function_template_name(sv, dt) : ovld_instance_name(sv, dt);
            if (bgeneric != NULL && strcmp(sv->symname, "__dl") == 0 &&
                h0_(princtype(dt)) == t_fnap)
            {   FormTypeList *f = typefnargs_(dt);
                if (!isvoidtype(typearg_(dt)) ||
                    f == NULL || !isptrtovoidtype(f->fttype) ||
                    f->ftcdr != NULL)
                {   cc_rerr(xbind_rerr_bad_global_dl_type);
                    d->declname = sv = gensymval(1); /* hide name to recover */
                    bgeneric = 0;
                }
            }

/* Maybe some of this code should move to cppfe/overload.c              */
            if (bgeneric == 0)
            {   DeclRhsList *d = mkDeclRhsList(sv,
                    (TypeExpr *)global_list4(SU_Type, t_ovld, 0, 0, 0), b_fnconst);
                bgeneric = instate_declaration_1(d, declflag);
            }
            bt = bindtype_(bgeneric);
            if (bindactuals_(bgeneric) != NULL)
                declflag |= SPECIALIZE;

            if (declflag & TEMPLATE)
            {   BindList *bl;
                bspecific = instate_declaration_1(d, declflag);
                for (bl = bindftlist_(bgeneric); bl; bl = bl->bindlistcdr)
                    if (bindsym_(bl->bindlistcar) == bindsym_(bspecific))
                    {   binduses_(bspecific) |= binduses_(bl->bindlistcar);
                        bindinstances_(bl->bindlistcar) = bindinstances_(bspecific);
                        bl->bindlistcar = bspecific;
                        break;
                    }
                if (!bl)
                    bindftlist_(bgeneric) = (BindList *)
                        global_cons2(SU_Bind, bindftlist_(bgeneric), bspecific);
            }
            else if (declflag & (SPECIALIZE|INSTANTIATE))
            {   BindList *tempts = NULL;
                Binder *ftemp = NULL;
                ExprList *l = NULL;
                FormTypeList *ft = typefnargs_(d->decltype);
                for (; ft; ft = ft->ftcdr)
                    l = mkExprList(l, (Expr *)gentempbinder(ft->fttype));
                l = (ExprList *)dreverse(l);
                if (d->declstg & bitofstg_(s_friend))
                {   if (parent && tagprimary_(parent) && tagprimary_(parent)->friends)
                    {   Friend *f = tagprimary_(parent)->friends;
                        int sl;
                        BindList *bl;
                        ExprList *tactuals = NULL;
                        Binder *b;
                        for (; f != NULL; f = f->friendcdr)
                        {   Binder *ffn = f->u.friendfn;
                            if (h0_(ffn) != s_binder) continue;
                            bl = bindftlist_(bgeneric);
                            for (; bl != NULL; bl = bl->bindlistcdr)
                                if (bl->bindlistcar == ffn)
                                    tempts = binder_cons2(tempts, ffn);
                        }
                        for (b = tagactuals_(parent); b != NULL; b = bindcdr_(b))
                        {   tactuals =
                                binder_cons2(tactuals, (bindconst_(b) != NULL) ?
                                             bindconst_(b) :
                                             mk_expr1(s_typespec, bindtype_(b), NULL));
                        }
                        tactuals = dreverse((List *)tactuals);
                        sl = push_var_scope(NULL, Scope_TemplateArgs);
                        tempts = temp_reduce(tempts, l, tactuals, NULL);
                        pop_scope_no_check(sl);
                        f = tagprimary_(parent)->friends;
                        for (; f != NULL; f = cdr_(f))
                        {   Binder *ffn = f->u.friendfn;
                            bl = typeovldlist_(bindtype_(bgeneric));
                            for (; bl != NULL; bl = bl->bindlistcdr)
                                if (bl->bindlistcar == ffn)
                                    tempts = binder_cons2(tempts, ffn);
                        }
                    }
                    else
                    {   BindList *bl = typeovldlist_(bindtype_(bgeneric));
                        tempts = bindftlist_(bgeneric);
                        for (; bl != NULL; bl = bl->bindlistcdr)
                            if (bindsym_(bl->bindlistcar) == d->declname)
                                tempts = binder_cons2(tempts, bl->bindlistcar);
                    }
                }
                else
                    tempts = temp_reduce(NULL, l, NULL, bgeneric);
                if (length((List *)tempts) == 1)
                {   bool has_failed = NO;
                    ScopeSaver env;
                    TypeExpr *t;

                    ftemp = tempts->bindlistcar;
                    if (declflag & INSTANTIATE && bindstg_(ftemp) & b_undef)
                        cc_err(xbind_err_template_undef, ftemp);

                    if (d->declstg & bitofstg_(s_friend))
                        bspecific = ftemp;
                    else {
                        Symstr *newsv;
                        if (declflag & SPECIALIZE)
                        {   BindList *ins = NULL;
                            for (ins = bindinstances_(ftemp); ins; ins = ins->bindlistcdr)
                            {   if (bindsym_(ins->bindlistcar) != d->declname) continue;
                                if (!(bindstg_(ins->bindlistcar) & b_undef) &&
                                    !(d->declstg & b_undef))
                                    cc_err(xbind_err_template_specialize_after);
                                break;
                            }
                        }
                        env = bindformals_(ftemp);
                        t = type_deduction(bindtype_(ftemp), l,
                                           bindactuals_(bgeneric), &env, YES, &has_failed);
                        if (has_failed)
                            syserr("type deduction failed: shouldn't happen");
                        newsv = ovld_tmptfn_instance_name(bindsym_(ftemp), env);
                        d->declname = ovld_instance_name(newsv, dt);
                        bspecific = instate_declaration_1(d, declflag);

                        if ((contains_typevars(d->decltype) && (l || bindactuals_(bgeneric))) ||
                            declflag & INSTANTIATE)
                        {   bindenv_(bspecific) = env = globalize_env(env);
                            bindtype_(bspecific) = t = globalize_typeexpr(t);
                            fixup_template_arg_type(bindtype_(bspecific), env);
                            if (declflag & INSTANTIATE && !(bindstg_(ftemp) & b_undef))
                                add_pendingfn(bindsym_(bgeneric), newsv, t,
                                              (bindstg_(bspecific)&~b_undef), NULL, NULL,
                                              bindtext_(ftemp), env, YES);
                        }
                        if (declflag & SPECIALIZE)
                            add_instance(bspecific, &bindinstances_(ftemp), YES);
                        add_instance(bspecific, &typeovldlist_(bt), NO);
                    }
                }
                else
                {   cc_err((tempts == NULL) ? xbind_err_template_none :
                           xbind_err_template_ambiguous);
                    bspecific = global_mk_binder(NULL, d->declname, d->declstg, d->decltype);
                }
                bindactuals_(bgeneric) = NULL;
            }
            else
            {   BindList *bl;
/* Replace existing (necessary?  match topbindingchain?) or add...      */
                bspecific = instate_declaration_1(d, declflag);
                stg = d->declstg;
                bindstg_(bspecific) |= stg & b_clinkage;
                bt = bindtype_(bgeneric);
                for (bl = typeovldlist_(bt); bl != NULL; bl = bl->bindlistcdr)
                {   Binder *b = bl->bindlistcar;
                    if (bindsym_(b) == bindsym_(bspecific))
                    {   bl->bindlistcar = bspecific;
                        bt = 0;
                    }
                    else if ((stg & b_clinkage) && (bindstg_(b) & b_clinkage))
                    {   cc_rerr(xbind_rerr_more_than_one_C_linkage, sv);
                        stg &= ~b_clinkage;
                        bindstg_(bspecific) &= ~b_clinkage;
                    }
                }
                if (bt)
                    typeovldlist_(bt) = (BindList *)
                        global_cons2(SU_Type, typeovldlist_(bt), bspecific);
                if ((stg & b_clinkage) && realbinder_(bspecific) == 0)
                {   realbinder_(bspecific) =
                        global_mk_binder(0, sv,
                            bindstg_(bspecific), bindtype_(bspecific));
                    bindstg_(bspecific) |= b_impl;
                }
            }
            local_scope = save_scope;
            return bspecific;
        }
        else
            cc_rerr(xbind_rerr_ovld_non_fn, bgeneric);
        local_scope = save_scope;
    }
    return instate_declaration_1(d, declflag);
}

static int s_contents_in(Expr *e)
{   if (e == NULL)
        return 0;
    if (h0_(e) == s_dot || h0_(e) == s_content)
        return s_contents_in(arg1_(e)) + (h0_(e) == s_content ? 1 : 0);
    return 0;
}

static Binder *implicit_decl_cpp(Symstr* sv)
{
    DeclRhsList d;
    TypeExpr *t = te_int;
    TypeExprFnAux s;

    d.declcdr = NULL;
    d.declname = sv;
    d.u.init = NULL;
    d.decltype = g_mkTypeExprfn(t_fnap, t, 0, 0,
                  packTypeExprFnAux(s, 0, 1999, 0, 0,
                   fpregargs_disabled ? f_nofpregargs : 0));   /* minargs_ */
    d.declstg = bitofstg_(s_extern)|b_clinkage|b_fnconst|b_undef;
    d.fileline = curlex.fl;
    d.declbind = NULL;
    d.declrealname = NULL;
    d.tentative = NULL;
    return instate_declaration_cpp(&d, TOPLEVEL);
}

static Expr *simpler_path_of(Expr *e1, Expr *e2)
{
/* e1 and e2 are a tower of '.' and '*' operators. Choose whichever   */
/* has fewer '*' operators (the '.'s get coalesced later...).         */
   return s_contents_in(e1) < s_contents_in(e2) ? e1 : e2;
}

/* The following provide for-style iterators for C++ classes which      */
/* can steer round CB_CORE etc.  See mip/bind.h.                        */
ClassMember *ClassMemo_next(ClassMemo *m)
{   ClassMember *p;
    if ((p = m->core) != 0) return (m->core = memcdr_(p), p);
    if ((p = m->outer) != 0) return (m->outer = memcdr_(p), p);
    return 0;
}

ClassMember *ClassMemo_first(ClassMemo *m, ClassMember *p)
{   m->core = 0, m->outer = p;
    if (p && attributes_(p) & CB_CORE)
    {   TypeExpr *t = memtype_(p);
        if (h0_(t) == s_typespec && typespecmap_(t) & CLASSBITS)
        {   TagBinder *tb = typespectagbind_(t);
            ClassMember *q = tagbindmems_(tb);
            m->core = q, m->outer = memcdr_(p);
        }
        else
            syserr("ClassMemo_first");
    }
    return ClassMemo_next(m);
}

/* This routine is used to PUSH scopes A and B for definitions like     */
/*    int A::B::x = a+b;   or  int A::B::f() { return a+b; }            */
/* where A::a and B::b.                                                 */
int push_multi_scope(TagBinder *cl)
{   int x = scope_level;
    if (cl)
    {   push_multi_scope(cl->tagparent);
        if (tagbindbits_(cl) & TB_TEMPLATE)
            push_var_scope(tagformals_(cl), Scope_TemplateArgs);
        push_scope(cl, Scope_Ord);
    }
    return x;
}

static Expr *path_to_member_2(ClassMember *member, TagBinder *b, int flags,
        ClassMember *vbases, TagBinder *privately_deriving_class)
{   ClassMember *l = tagbindmems_(b);
    if (l != NULL && (attributes_(l) & CB_CORE))
    {   Expr *e;
/* This section is both useful for testing (in effect implementing a   */
/* language extension allowing access to bases by name) and used by    */
/* pointercast() which generates casts between base and derived types. */
        e = path_to_member_1(member, b, (flags & ~FB_INHERIT),
                NULL, privately_deriving_class);
        if (e != NULL) return e;
        b = typespectagbind_(memtype_(l));
        if (b == 0) syserr("path_to_core_member(0,...)");
    }
    return path_to_member_1(member, b, flags, vbases, privately_deriving_class);
}

int derivation_level;

ClassMember *derived_from(TagBinder *base, TagBinder *scope)
{   ClassMember *l, *ll;
    if (debugging(DEBUG_BIND)) cc_msg("derived_from($b,$b)\n", base, scope);
    derivation_level++;
/* For why the next line is present consider:                           */
/*    class A{}; class B:virtual A{}; class C:B {};                     */
/* without it C does not appear derived from B, only core(B).           */
    if ((l = tagbindmems_(base)) != NULL && attributes_(l) & CB_CORE)
        return derived_from(typespectagbind_(princtype(memtype_(l))), scope);
/* But we also need to do the same to scope so that we never have       */
/* derived_from(C,C) being true:                                        */
/* Maybe the correct thing to use is a 'path_to_baseclass' function     */
/* since used as a predicate or to get a name for path_to_member...     */
    if ((l = tagbindmems_(scope)) != NULL && attributes_(l) & CB_CORE)
        return derived_from(base, typespectagbind_(princtype(memtype_(l))));
    for (l = tagbindmems_(scope);  l != NULL;  l = memcdr_(l))
        if (attributes_(l) & (CB_BASE | CB_VBPTR))
        {   TypeExpr *t = princtype(memtype_(l));
            if (attributes_(l) & CB_VBPTR) t = princtype(typearg_(t));
            if (base == typespectagbind_(t)) return l;
        }
    for (l = tagbindmems_(scope);  l != NULL;  l = memcdr_(l))
        if (attributes_(l) & (CB_BASE | CB_VBPTR))
        {   TypeExpr *t = princtype(memtype_(l));
            if (attributes_(l) & CB_VBPTR) t = princtype(typearg_(t));
            if ((ll = derived_from(base, typespectagbind_(t))) != NULL)
                return ll;
        }
    return 0;
}

bool derived_fromeq(TagBinder *base, TagBinder *scope)
{
    return core_class(base) == core_class(scope) ||
        derived_from(base, scope) != NULL;
}

/* Vblist is the list of members at the top level of the derivation -   */
/* starting with the core member and followed by the vbases. Off is the */
/* offset of the base member l if it is not virtual, the offset of the  */
/* virtual base pointer member l if it is. Return a cheat s_invisible   */
/* Expr containing an extra field with the base offset in it.           */

static Expr *base_and_offset(ClassMember *l, ClassMember *vblist, int32 off,
        TypeExpr *t)
{   if (attributes_(l) & CB_VBPTR)
    {   TypeExpr *t = typearg_(memtype_(l));
        ClassMember *vb;
        for (vb = vblist;  vb != NULL;  vb = memcdr_(vb))
        {   if (equivtype(memtype_(vb), t) == 2)
            {   l = vb;
                off = memwoff_(l);
                break;
            }
        }
        if (vb == NULL)
            syserr("Can't find VBASE for VBPTR $r", memsv_(l));
    }
    return mk_expr3(s_invisible, t, (Expr *)l, NULL, (Expr *)(IPtr)off);
}

static int is_vbasetype(TypeExpr *t, ClassMember *vblist)
{   ClassMember *vb;
    TypeExpr *pt = princtype(t);
    if (isclasstype_(pt))
        for (vb = vblist;  vb != NULL;  vb = memcdr_(vb))
            if (equivtype(memtype_(vb), t) == 2)
                return 1;
    return 0;
}

static bool is_dependent_base(TypeExpr *t, ScopeSaver actuals)
{
    for (; actuals; actuals = bindcdr_(actuals))
        if (equivtype(t, bindtype_(actuals)))
            return YES;

    /* base class B<T> is defined at the point of defn */
#if 0
    if (tagactuals_(typespectagbind_(princtype(t))) != NULL)
        return YES;
#endif
    return NO;
}

static Expr *path_to_base_member(ClassMember *member, TagBinder *b,
    int flags, ClassMember *vbases, TagBinder *privately_deriving_class)
{   ClassMember *l;
    Expr *path = NULL, *tmp, *tmpi, *e;

    /* search the inherited base classes for a name match... */
    for (l = tagbindmems_(b); l != NULL; l = memcdr_(l))
    {   TypeExpr *t;
        if (!is_datamember_(l) ||
            !(attributes_(l) & (CB_BASE | CB_VBPTR))) break;
        t = memtype_(l);

        /* Ignore dependent base if it is an instantiation */
        if ((flags == ALLSCOPES) && has_template_arg_scope() &&
            is_dependent_base(t, tagactuals_(b)))
            continue;

        if (attributes_(l) & CB_VBPTR) t = typearg_(t);
        tmp = path_to_member_2(member, typespectagbind_(t), flags, vbases,
                (attributes_(l) & bitofaccess_(s_private)) ? b :
                    privately_deriving_class);

        if (tmp == NULL || tmp == errornode) continue;
            /* not found, or error already diagnosed */

        /* Record the base member containing the found entity, unless */
        /* already recorded at a deeper level of recursion.           */
        if (h0_(tmp) == s_invisible)
        {   tmpi = tmp;
            tmp = arg2_(tmpi);
        }
        else
            tmpi = base_and_offset(l, vbases, memwoff_(l), t);

        if (h0_(tmp) == s_dot || h0_(tmp) == s_content)
        {   e = mk_exprwdot(s_dot, memtype_(l),
                        nullbinder(bindparent_(l)), memwoff_(l));
            if (attributes_(l) & CB_VBPTR) e = mk_expr1(s_content, t, e);
            tmp = rooted_path(tmp, 0, e);
        }
        arg2_(tmpi) = tmp;

        if (path == NULL)  {path = tmpi;  continue;}

        if (accessOK & 4) break;        /* already found to be ambiguous */

        /* Check for ambiguity between path and tmpi: the arg2_() field  */
        /* is an exprdotmemfn, a (Binder *) or an (Expr *) representing  */
        /* a path to a member. Identical (Binder *)s are unambiguous;    */
        /* exprdotmemfns and path expressions cannot be identical...     */
        if (arg2_(path) == tmp) continue;

        /* Second, check for paths to the same (virtual) base member...  */
        /* LDS @@@ 14-Oct-94 OR same virtual base pointer...             */
        /* NB if the containing members are identical and the entity     */
        /* reprns are not, then the entities are represented by path     */
        /* exprns and, hence, are data members/exprdotmemfns.            */
        if (arg1_(path) == arg1_(tmpi)
            ||
            h0_(tmp) == s_dot && h0_(arg2_(path)) == s_dot &&
                type_(tmp) == type_(arg2_(path)) &&
                h0_(type_(tmp)) == t_content &&
                is_vbasetype(typearg_(type_(tmp)), vbases))
        {   arg2_(path) = simpler_path_of(arg2_(path), tmp);
            continue;
        }

        /* Third, see whether path dominates tmpi or vice versa. If so,  */
        /* retain the dominant entity and discard the other.             */

        if (type_derived_from(memtype_((ClassMember *)arg1_(path)),
                              memtype_((ClassMember *)arg1_(tmpi))))
        {   /* the name of the entity described by tmpi dominates that   */
            /* of the entity described by path, so retain tmpi.          */
            path = tmpi;
            continue;
        }

        if (type_derived_from(memtype_((ClassMember *)arg1_(tmpi)),
                              memtype_((ClassMember *)arg1_(path))))
        {   /* the name of the entity described by path dominates that   */
            /* of the entity described by tmpi, so discard tmpi.         */
            continue;
        }

        /* CHECK_INHERITED_VIRTUAL is now (03-Oct-1997) a misnomer;
           it now finds the virtual base member instead, if existed and
           left-most preferred.
         */
        if (flags & CHECK_INHERITED_VIRTUAL)
        {   Binder *b1 = exb_(arg2_(path));
            Binder *b2 = exb_(arg2_(tmpi));
            if (h0_(b1) == s_binder && h0_(b2) == s_binder &&
                isfntype(bindtype_(b1)) && isfntype(bindtype_(b2)))
            {
#if 0
                if ((bindstg_(b1) & bitofstg_(s_virtual)) !=
                    (bindstg_(b2) & bitofstg_(s_virtual)))
                    cc_rerr(xbind_rerr_both_virtual_and_nonvirtual,
                        (Symstr *)member, b);
#endif
                if (!(bindstg_(b1) & bitofstg_(s_virtual)) &&
                    bindstg_(b2) & bitofstg_(s_virtual))
                    path = tmpi;
                continue;
            }
        }

        {   Symstr *sv = h0_(member) == s_identifier ?
                (Symstr *)member : memsv_(member);
/* if b is a CORE class, use the class containing b, so that 'class C'   */
/* rather than 'class __K_C' will occur in the diagnostic                */
            TagBinder *cl = tagbindbits_(b) & TB_CORE ? b->tagparent : b;
            cc_rerr(xbind_rerr_is_ambiguous_name, sv, cl);
            accessOK |= 4;       /* suppress all but the first complaint */
            break;               /* and terminate the search now...      */
        }
    }
    return path;
}

TagBinder *current_member_scope(void)
{   Scope *scope;
    for (scope = local_scope;  scope != NULL;  scope = scope->prev)
        if (scope->class_tag != NULL) return scope->class_tag;
    return NULL;
}

static Binder *accessing_fn;
static TagBinder *accessing_class;

TagBinder *set_access_context(TagBinder *cl, Binder *fn)
{   TagBinder *tb = accessing_class;
    if (cl == NULL && fn == NULL)
    {   accessing_class = 0;
        accessing_fn = 0;
    }
    else
    {   if (cl != NULL) accessing_class = cl;
        if (fn != NULL) accessing_fn = fn;
    }
    return tb;
}

static bool accessor_is_friendof(TagBinder *ofclass)
{   Friend * f;
    for (f = ofclass->friends;  f != NULL;  f = f->friendcdr)
    {   Binder *friendfn = f->u.friendfn;
        TagBinder *friendclass = f->u.friendclass;
        /* /* template member fn not done e.g. t14c.dir/_1453W31.cpp */
        if (accessing_class == friendclass ||
            accessing_fn == friendfn ||
            (h0_(friendfn) == s_binder && bindformals_(friendfn) &&
             is_an_instance(bindinstances_(friendfn), accessing_fn)) ||
            (h0_(friendclass) == s_tagbind && tagbindbits_(friendclass) & TB_TEMPLATE &&
             is_an_instance(taginstances_(friendclass), (Binder *)accessing_class)))
            return 1;
    }
    return 0;
}

void mk_friend_class(TagBinder *classtag, TagBinder *ofclass)
{   Friend *f;
    if (debugging(DEBUG_BIND))
    {   if (h0_(classtag) == s_tagbind)
            cc_msg("adding friend $c to $c\n", classtag, ofclass);
        else
            cc_msg("added friend fn $b to $c\n", classtag, ofclass);
    }
    if (!(tagbindbits_(ofclass) & TB_BEINGDEFD))
        syserr("adding friend to completed scope $c", ofclass);
    for (f = ofclass->friends;  f != NULL;  f = f->friendcdr)
    {   if (f->u.friendclass == classtag) return;
    }
    f = (Friend *) GlobAlloc(SU_Other, sizeof(Friend));
        /* @@@ Could Fix the storage class better here... */
    f->friendcdr = ofclass->friends;
    ofclass->friends = f;
    f->u.friendclass = classtag;
}

void mk_friend_fn(Binder *bspecific, TagBinder *ofclass)
{   mk_friend_class((TagBinder *)bspecific, ofclass);
}

/* Access control: (i) whether access is permitted or not is a property */
/* of a path through a derivation and (ii) if there are multiple paths  */
/* to the same entity then access is permitted if at least one path     */
/* allows access. Below, FB_PRIVATELY_DERIVED is set when searching a   */
/* privately derived base class.                                        */

void check_access(ClassMember *m, TagBinder *privately_deriving_class)
{   TagBinder *tb = bindparent_(m);

    if (accessOK) return;   /* already determined or more serious error */

    if (privately_deriving_class == 0 &&
        (attributes_(m) & bitofaccess_(s_public)))
            accessOK = 1;
    else if (accessing_class != NULL)
    {   if ((attributes_(m) & bitofaccess_(s_private)))
        {   if (core_class(accessing_class) == core_class(tb) ||
                tagbindsym_(accessing_class) == bindsym_(m)) accessOK =1;
        }
        else
        {
/* A protected member or a privately derived public or protected member */
/* Access is OK if the accessing class is derived_fromeq this class and */
/* the privately deriving class is derived_fromeq the accessing class.  */
            if (derived_fromeq(tb, accessing_class) &&
                (HasFeature(Feature_CFront) ||
                 (!accessing_fn || rootOfPath == NULL ||
                  rootOfPath->bindlistcdr->bindlistcar == NULL ||
                  /* only interested in the leftScope, if there is one */
                  derived_fromeq(accessing_class,
                                 (TagBinder *)rootOfPath->bindlistcdr->bindlistcar)) &&
                 (privately_deriving_class == 0 ||
                  derived_fromeq(accessing_class, privately_deriving_class))))
                accessOK = 1;
        }
    }
    if (!accessOK && (accessor_is_friendof(tb) ||
                      (rootOfPath != NULL &&
                       (rootOfPath->bindlistcar == NULL ||
                        accessor_is_friendof((TagBinder *)rootOfPath->bindlistcar)) &&
                       (rootOfPath->bindlistcdr->bindlistcar == NULL ||
                        accessor_is_friendof((TagBinder *)rootOfPath->bindlistcdr->bindlistcar)))))
        accessOK = 1;
}

bool no_access_context(void)
{   return (!accessing_class && !accessing_fn);
}

void check_access_1(ClassMember *l, TagBinder *scope)
{   TagBinder *old_accessing_class = accessing_class;
    int old_accessOK = accessOK;

    if (!scope && attributes_(l) &
            (bitofaccess_(s_private)|bitofaccess_(s_protected)) &&
                !accessor_is_friendof(bindparent_(l)))
    {   diagnose_access(bindsym_(l), bindparent_(l));
        return;
    }
    accessing_class = scope;
    accessOK = 0;
    check_access(l, 0);
    accessing_class = old_accessing_class;
    accessOK = old_accessOK;
}

Binder *instate_classname(DeclRhsList *d, TagBinder *tb)
/* Instate a classname typedef in the same scope as its tagbinder */
/* Note: findtag_in_members() finds tb by address, not by name.   */
{   Binder *b;
    Scope *saved_scope = local_scope, *scope;

    for (scope = local_scope;  scope != NULL;  scope = scope->prev)
    {   ClassMember *l;
        TagBinder *cl = scope->class_tag;
        if (cl != NULL)
            l = tagbindmems_(core_class(cl));
        else
            l = scope->scopemems;
        if (findtag_in_members((Symstr *)tb, l) != 0) break;
    }

    local_scope = scope;
    b = instate_declaration(d, scope == NULL ? TOPLEVEL :
                            (tagbindbits_(tb) & TB_TEMPLATE) ? GLOBALSTG : LOCALSCOPE);
    local_scope = saved_scope;
    return b;
}

bool is_two_arg_delete(Binder* delgeneric)
{   if (bindparent_(delgeneric) == 0) return NO;
  { TypeExpr *bt = bindtype_(delgeneric);
    BindList *bl;
    FormTypeList *f;
    if (h0_(bt) != t_ovld) syserr("$b is not a member function?", delgeneric);
    bl = typeovldlist_(bt);
    bt = princtype(bindtype_(bl->bindlistcar));
    if (h0_(bt) != t_fnap) syserr("overloaded non-function $b?", bl->bindlistcar);
    f = typefnargs_(bt);
    return f->ftcdr != NULL;
  }
}

/* Caution: this is not of general utility; see syserr below. */
bool is_local_binder(Binder *b)
{   Scope *scope = local_scope;
    TagBinder *cl;
    if (scope == NULL || scope->kind == Scope_Args)
        return NO;
    cl = current_member_scope();
    if (!cl) syserr("no local class");
    for (; scope && scope->class_tag != cl; scope = scope->prev)
        if (find_scopemember(bindsym_(b), scope->scopemems) != NULL)
            return YES;
    /* now for template actuals */
    scope = scope->prev;
    for (; scope && (scope->kind == Scope_TemplateArgs ||
                     scope->kind == Scope_TemplateDef);
         scope = scope->prev)
        if (find_scopemember(bindsym_(b), scope->scopemems) != NULL)
            return YES;
    return NO;
}

bool is_template_arg_binder(Expr *e)
{   Scope *scope = local_scope;
    Binder *temp, *b;

    if (!e) return NO;
    e = skip_invisible_or_cast(e);
    if (h0_(e) == s_binder) b = exb_(e);
    else return NO;

    for (; scope; scope = scope->prev)
    {   if (scope->kind != Scope_TemplateArgs) continue;
        for (temp = scope->scopemems; temp; temp = bindcdr_(temp))
            if (bindsym_(temp) == bindsym_(b)) return YES;
    }
    return NO;
}

bool has_template_arg_scope(void)
{   Scope *scope = local_scope;
    for(; scope; scope = scope->prev)
        if (scope->kind == Scope_TemplateArgs) return YES;
    return NO;
}

BindList *clone_bindlist(BindList * bl, bool glob)
{   Binder *b;
    TypeExpr *t;
    if (!bl) return NULL;
    b = (Binder *) ((glob) ? GlobAlloc(SU_Bind, sizeof(Binder)) :
                             BindAlloc(sizeof(Binder)));
    memcpy((char *)b, (char *)bl->bindlistcar, sizeof(Binder));
    t = clone_typeexpr(bindtype_(bl->bindlistcar));
    bindtype_(b) = (glob) ? globalize_typeexpr(t) : t;
    return (glob) ? (BindList *)global_cons2(SU_Bind,
                            clone_bindlist(bl->bindlistcdr, glob), b) :
                    mkBindList(clone_bindlist(bl->bindlistcdr, glob), b);
}

ScopeSaver dup_template_scope(void)
{   ClassMember *l;
    ScopeSaver p = NULL, q = NULL;
    Scope *s = local_scope;
    bool glob;
    while (s != NULL && (s->kind == Scope_TemplateArgs || s->kind == Scope_Args))
        s = s->prev;
    glob = (s == NULL);
    l = glob ? topbindingchain : s->scopemems;
    for (; l; l = bindcdr_(l))
        switch (h0_(l)) {
        case s_binder:
          {   ClassMember *b;
              b = (ClassMember *)GlobAlloc(SU_Bind, SIZEOF_NONAUTO_BINDER);
              memcpy((char *)b, (char *)l, SIZEOF_NONAUTO_BINDER);
              if (h0_(bindtype_(l)) == t_ovld)
              { TypeExpr *e;
                e = (TypeExpr *)global_list4(SU_Type, t_ovld, 0, 0, 0);
                typeovldlist_(e) = clone_bindlist(typeovldlist_(bindtype_(b)), YES);
                bindtype_(b) = e;
              }
              else
                bindtype_(b) = globalize_typeexpr(bindtype_(l));
              if (p == NULL) p = q = b; else bindcdr_(q) = b, q = b;
              break;
          }
        case s_tagbind:
            break;
        default:
          syserr("Unrecognizable scope mem");
        }
    return p;
}

void save_labels(LabBind **lc, LabBind **symlabs)
{   int i = 0;
    *lc = labelchain;
    if (length((List *)labelchain) > MAX_SAVED_LABELS)
        syserr("too many labels to save");
    for (; labelchain; labelchain = labelchain->labcdr)
    {   symlabs[i++] = symlab_(labelchain->labsym);
        symlab_(labelchain->labsym) = NULL;
    }
}

void restore_labels(LabBind *lc, LabBind **symlabs)
{   int i = 0;
    labelchain = lc;
    for (; lc; lc = lc->labcdr, i++)
        symlab_(lc->labsym) = symlabs[i];
}

/* end of cppfe/xbind.c */
