/*
 * bind.c: various binding and lexing routines for C compiler
 * Copyright (C) Codemist Ltd., 1987-1992.
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Advanced RISC Machines Limited, 1991-1992.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$  Codemist 55
 * Checkin $Date$
 * Revising $Author$
 */

/* AM memo: @@@ the use of assert(0) in the development of PASCAL is    */
/* untidy but only temporary.                                           */

/* #define DEBUG_TENTATIVE_DEFS 1        -- BUT ONLY during development */

/* AM Dec-90: the BSS code was broken in several interesting ways.      */
/*   Mend it, and move PCC mode nearer to being ANSI code with only     */
/*   local differences.  u_tentative is now dead.                       */
/*   BSS is now merged with tentatives both in ansi and pcc mode.       */
/* AM Jul-87: experiment with memo-ising globalize_typeexpr(). */
/* exports globalize_int(), globalize_typeexpr() */

#ifndef _BIND_H
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
#include "store.h"
#include "vargen.h"         /* for initstaticvar()... */
#include "xrefs.h"          /* for LIT_LABEL */
#include "errors.h"
#include "aeops.h"
/* for C-only compilers... */
#define merge_default_arguments(a,b) 0
#define check_access(a,b) (void)0
#define nullbinder(cl) 0
#define set_linkage(b,l,m) (void)0
#define hiddenmembername(a,b) 0
#define implicit_decl_cpp(a) ((Binder*)0)
#endif
int accessOK;

#include "dump.h"

#ifdef PASCAL
/* for production qualify compilers prefer syserr() over assert().      */
#  include <assert.h>
#endif


static int gensymline, gensymgen;         /* For generating unique syms   */
static Symstr *(*hashvec)[BIND_HASHSIZE]; /* Symbol table buckets         */
const char *sym_name_table[s_NUMSYMS];          /* translation back to strings  */

#define GENSYMV_SEGSIZE 256
#define GENSYMV_MAXSEGS 256
static Symstr ***gensymv;
static uint32 ngensym, gensymlimit;
#define GLOBBINDV_SEGSIZE 256
#define GLOBBINDV_MAXSEGS 256
static Binder ***globbindv;
static uint32 nglobbind, globbindlimit;
#define GLOBTAGV_SEGSIZE 256
#define GLOBTAGV_MAXSEGS 256
static TagBinder ***globtagv;
static uint32 nglobtag, globtaglimit;

#define NO_CHAIN     256

#ifdef PASCAL
/* the following parameterisation allows PASCAL systems to use case-    */
/* insensitive name matching while preserving the original case.        */
#define lang_hashofchar(x) safe_tolower(x)
static int lang_namecmp(char *s, char *t)
{   for (;;)
    {   if (safe_tolower(*s) != safe_tolower(*t)) return 1;
        if (*s == 0) return 0;
        s++, t++;
    }
}
#else
#  define lang_hashofchar(x) (x)
#  define lang_namecmp(a, b) strcmp(a, b)
#endif

#ifdef CALLABLE_COMPILER
#include "dbg_hdr.h"
#include "dbg_hl.h"
#endif

Symstr *sym_lookup(char const *name, int glo)
{   int32 wsize;
    unsigned32 hash, temp;
    char const *s;
    Symstr *next, **lvptr = NULL;
  /*
   * 'glo' ==  SYM_LOCAL  => allocate in Binder store
   *       ==  SYM_GLOBAL => allocate in Global store
   *  glo'  &  NO_CHAIN   => don't chain to symtab buckets
   */
    if (glo & NO_CHAIN)
        glo &= ~NO_CHAIN;
    else
    {
#ifdef CALLABLE_COMPILER
        if ((next = dbg_findhash(name)) != NULL) return next;
#endif
        hash = 1;
        for (s = name; *s != 0; ++s)
        {   temp = just32bits_(hash << 7);
            hash = ((hash >> 25)^(temp >> 1)^(temp >> 4) ^
                                             lang_hashofchar(*s)) & 0x7fffffff;
        }
        lvptr = &(*hashvec)[hash % BIND_HASHSIZE];
        while ((next = *lvptr) != NULL)
        {   if (lang_namecmp(symname_(next), name) == 0) return(next);
            lvptr = &symchain_(next);
        }
    }
#ifdef CALLABLE_COMPILER
    wsize = offsetof(Symstr, symname[0]) + padstrlen(strlen(name)+1);
#else
    wsize = offsetof(Symstr, symname[0]) + padstrlen(strlen(name));
#endif
    next = glo != SYM_LOCAL ? (Symstr *) GlobAlloc(SU_Sym, wsize)
                            : (Symstr *) BindAlloc(wsize);
    memclr(next, (size_t)wsize);
    if (lvptr != NULL)
    {   *lvptr = next;
        symchain_(next) = NULL;
    } else {
        symchain_(next) = next;         /* non-hashed: see isgensym().  */
        if (glo != SYM_LOCAL && (dump_state & DS_Dump)) {
            uint32 segno = ngensym / GENSYMV_SEGSIZE,
                   segix = ngensym % GENSYMV_SEGSIZE;
            if (ngensym >= gensymlimit) {
                if (GENSYMV_MAXSEGS <= segno)
                    syserr("Too many gensyms to dump");
                gensymv[segno] = (Symstr **)GlobAlloc(SU_Other, sizeof(Symstr *) * GENSYMV_SEGSIZE);
                gensymlimit += GENSYMV_SEGSIZE;
            }
            gensymv[segno][segix] = next;
            ngensym++;
        }
    }
    symtype_(next) = s_identifier;
    bind_global_(next) = NULL; symlab_(next) = NULL; next->symtag = NULL;
    symext_(next) = NULL; symfold_(next) = NULL;
#ifdef CALLABLE_COMPILER
    next->symname[0] = strlen(name);
#endif
    strcpy(symname_(next), name);
    return(next);
}

Symstr *sym_insert(char const *name, AEop type)
{   Symstr *p = (sym_lookup)(name, SYM_GLOBAL);
    symtype_(p) = type;
    return(p);
}

Symstr *sym_insert_id(char const *name)
{   return (sym_lookup)(name, SYM_GLOBAL);
}

static void check_extern(Symstr *s)
{   Symstr *p;
/* First an option to check ansi conformance ... */
/* (The return below ensures only one is executed.  Because of room for  */
/* the back pointer only one can be active at once, unfortunately).      */
    if (HasFeature(Feature_6CharMonocase))
    {   char ch, v[6+1];
        int n = 0;
        while ((ch = symname_(s)[n]) != 0 && n < 6) v[n++] = safe_tolower(ch);
        v[n] = 0;
        p = sym_lookup(v, SYM_GLOBAL);
        if (symfold_(p) == 0)
            symfold_(p) = s;
        if (symfold_(p) != s)
            cc_warn(bind_warn_extern_clash, s, symfold_(p));
        return;
    }
/* ... now a compiled-in form for things like 370 linkers */
#ifdef TARGET_HAS_LINKER_NAME_LIMIT    /* e.g. 370 */
    {   char ch, v[LINKER_NAME_MAX+1];
        int n = 0;
        while ((ch = symname_(s)[n]) != 0 && n < LINKER_NAME_MAX)
            v[n++] = LINKER_NAME_MONOCASE ? safe_tolower(ch) : ch;
        v[n] = 0;
        p = sym_lookup(v, SYM_GLOBAL);
        if (symfold_(p) == 0)
            symfold_(p) = s;
        if (symfold_(p) != s)
            cc_err(LINKER_NAME_MONOCASE ? bind_err_extern_clash_monocase,
                                        : bind_err_extern_clash,
                   s, symfold_(p), (long)LINKER_NAME_MAX);
    }
#endif /* TARGET_HAS_LINKER_NAME_LIMIT */
}

Symstr *gensymval(bool glo)
{
    /* Generates a new symbol with a unique name.                    */
    /* (Not quite unique in that line 1 may occur in 2 files, but    */
    /*  we RELY on NO_CHAIN below to treat as unique).               */
    char name[30];
#ifdef TARGET_IS_CLIPPER
    /* the next line is a hack to ensure these gensyms are assemblable */
    /* Note that this HOPEs that the user has no names Intsym_nnn      */
    sprintf(name, "Intsym_%d", ++gensymgen);
#else
    if (gensymline != curlex.fl.l)
        gensymline = curlex.fl.l, gensymgen = 1;
    else
        ++gensymgen;
    sprintf(name, "<Anon%d_at_line_%d>", gensymgen, gensymline);
#endif
    return sym_lookup(name, (glo ? SYM_GLOBAL+NO_CHAIN : SYM_LOCAL+NO_CHAIN));
}

Symstr *gensymvalwithname(bool glo, char const *name)
{
    return sym_lookup(name, (glo ? SYM_GLOBAL+NO_CHAIN : SYM_LOCAL+NO_CHAIN));
}

bool isgensym(Symstr const *sym)      /* actually is-unchained-gensym!        */
{   return symchain_(sym) == sym;
}

static Binder *RecordGlobalBinder(Binder *p)
{   if (dump_state & DS_Dump) {
        uint32 segno = nglobbind / GLOBBINDV_SEGSIZE,
               segix = nglobbind % GLOBBINDV_SEGSIZE;
        if (nglobbind >= globbindlimit) {
            if (GLOBBINDV_MAXSEGS <= segno)
                syserr("Too many global binders to dump");
            globbindv[segno] = (Binder **)GlobAlloc(SU_Other, sizeof(Binder *) * GLOBBINDV_SEGSIZE);
            globbindlimit += GLOBBINDV_SEGSIZE;
        }
        globbindv[segno][segix] = p;
        nglobbind++;
    }
    return p;
}

Binder *global_mk_binder(Binder *b, Symstr *c, SET_BITMAP d, TypeExpr *e)
{
    int32 size = d & (bitofstg_(s_virtual)|b_globalregvar|bitofstg_(s_auto)) ?
                     sizeof(Binder) : SIZEOF_NONAUTO_BINDER;
    Binder *p = (Binder*) GlobAlloc(SU_Bind, size);
 /*
  * This consistency check is removed so that front-ends for languages
  * other than C can create binders for auto variables in global store.
>>> if (d & bitofstg_(s_auto)) syserr("Odd global binder(%lx)", (long)d); <<<
  */
    if (d & bitofstg_(s_extern)) check_extern(c);
    h0_(p) = s_binder;
    bindcdr_(p)=b;
    bindsym_(p)=c;
    attributes_(p) = A_GLOBALSTORE;
    bindstg_(p) = d;
    bindtype_(p) = e;
    bindaddr_(p) = 0;  /* soon BINDADDR_UNSET - remember 'datasegment' */
    bindparent_(p) = 0;         /* local_scope->class_tag? BEWARE member template */
    bindconst_(p) = 0;
    bindinline_(p) = 0;
    bindscope_(p) = 0;
    bindactuals_(p) = 0;
    bindformals_(p) = 0;
    bindinstances_(p) = 0;
    bindtext_(p) = -1;
    bindftlist_(p) = 0;
#ifdef TARGET_HAS_DEBUGGER
    binddbg_(p) = 0;
#endif
#ifdef PASCAL /*ECN*/
    p->bindlevel = 0;
    p->synflags = 0;
#endif
    if (size == sizeof(Binder))
        bindxx_(p) = GAP;
    if (d & bitofstg_(s_auto))
        bindmcrep_(p) = NOMCREPCACHE;

    return RecordGlobalBinder(p);
}

Binder *mk_binder(Symstr *c, SET_BITMAP d, TypeExpr *e)
{
    Binder *p = (Binder*) BindAlloc(
        (d & (bitofstg_(s_auto)|bitofstg_(s_virtual))) ?
            sizeof(Binder) : SIZEOF_NONAUTO_BINDER);
    if (d & bitofstg_(s_extern)) check_extern(c);
    h0_(p) = s_binder;
    bindcdr_(p)=0;
    bindsym_(p)=c;
    attributes_(p) = A_LOCALSTORE;
    bindstg_(p) = d;
    bindtype_(p) = e;
    bindaddr_(p) = BINDADDR_UNSET;
    bindparent_(p) = 0;         /* local_scope->class_tag?, BEWARE member template */
    bindconst_(p) = 0;
    bindinline_(p) = 0;
#ifdef TARGET_HAS_DEBUGGER
    binddbg_(p) = 0;
#endif
#ifdef PASCAL /*ECN*/
    p->bindlevel = 0;
    p->synflags = 0;
#endif
    bindscope_(p) = 0;
    bindactuals_(p) = 0;
    bindformals_(p) = 0;
    bindinstances_(p) = 0;
    bindtext_(p) = -1;
    bindftlist_(p) = 0;
    if (d & bitofstg_(s_auto))
    {   bindxx_(p) = GAP;
        bindmcrep_(p) = NOMCREPCACHE;
    }
    return p;
}

TagBinder *global_mk_tagbinder(TagBinder *b, Symstr *c, AEop d)
{   SET_BITMAP bits = bitoftype_(d);
    TagBinder *p = (TagBinder*) GlobAlloc(SU_Bind, sizeof(TagBinder));
    h0_(p) = s_tagbind;
    tagbindcdr_(p)=b;
    tagbindsym_(p)=c;
    attributes_(p) = A_GLOBALSTORE;
    tagbindbits_(p) = bits;
    tagbindmems_(p) = 0;
    tagbindtype_(p) = globalize_typeexpr(primtype2_(bits, p));
    if (LanguageIsCPlusPlus)
    {   p->friends = NULL;
        p->tagparent = current_member_scope();
    } else
        p->tagparent = NULL;
    taginstances_(p) = NULL;
    tagscope_(p) = NULL;
    tagformals_(p) = NULL;
    tagactuals_(p) = NULL;
    tagtext_(p) = -1;
    tagprimary_(p) = NULL;
    tagmemfns_(p) = NULL;
#ifdef TARGET_HAS_DEBUGGER
    tagbinddbg_(p) = 0;
#endif
    p->typedefname = NULL;
    if (dump_state & DS_Dump) {
        uint32 segno = nglobtag / GLOBTAGV_SEGSIZE,
               segix = nglobtag % GLOBTAGV_SEGSIZE;
        if (nglobtag >= globtaglimit) {
            if (GLOBTAGV_MAXSEGS <= segno)
                syserr("Too many global tagbinders to dump");
            globtagv[segno] = (TagBinder **)GlobAlloc(SU_Other, sizeof(TagBinder *) * GLOBTAGV_SEGSIZE);
            globtaglimit += GLOBTAGV_SEGSIZE;
        }
        globtagv[segno][segix] = p;
        nglobtag++;
    }
    return p;
}

TagBinder *mk_tagbinder(Symstr *c, AEop d)
{   SET_BITMAP bits = bitoftype_(d);
    TagBinder *p = (TagBinder*) SynAlloc(sizeof(TagBinder));
    h0_(p) = s_tagbind;
    tagbindcdr_(p)=0;
    tagbindsym_(p)=c;
    attributes_(p) = A_LOCALSTORE;
    tagbindbits_(p) = bits;
    tagbindmems_(p) = 0;
    tagbindtype_(p) = primtype2_(bits, p);
    if (LanguageIsCPlusPlus)
    {   p->friends = NULL;
        p->tagparent = current_member_scope();
    } else
        p->tagparent = NULL;
    taginstances_(p) = NULL;
    tagscope_(p) = NULL;
    tagformals_(p) = NULL;
    tagactuals_(p) = NULL;
    tagtext_(p) = -1;
    tagprimary_(p) = NULL;
    tagmemfns_(p) = NULL;
#ifdef TARGET_HAS_DEBUGGER
    tagbinddbg_(p) = 0;
#endif
    p->typedefname = NULL;
    return p;
}

extern LabBind *mk_labbind(LabBind *b, Symstr *c)
{
    LabBind *p = (LabBind*) SynAlloc(sizeof(LabBind));
    p->labcdr = b;
    p->labsym = c;
    p->labinternlab = 0;
    p->labuses = 0;
    p->labu.ref = 0;
    return p;
}

/* Binding:
   There are 5 overloading classes, of which 3 (labels, vars, struct tags)
   are bindings in the traditional sense.  All code concerning binding
   and unbinding is in this file.  Access routes are the procedures below:
     Labels:  label_xxx;
     Vars:    instate_declaration, findbinding.
     Tags:    instate_tagbinding, findtagbinding.
     Scopes:  push_scope, pop_scope, clear_stacked_scopes.

   Note that typedef names share the same binding space with variables.

   Labels have function scope and function scopes do not nest. Function
   scopes and the global (file) scope for variables and tags is implemented
   using a hash table of Symstrs with separate Binder, TagBinder and LabBind
   pointer fields.

   Local scopes for Binders and TagBinders are implemented using the 'deep
   binding' strategy, as are C++ class scopes. For each scope there is a
   list of Binders/ TagBinders which can be searched for the matching
   Symstr. If the search fails in each local scope then the global
   binding (if any) is found in O(1) time.

   In a C++ class scope, class members, class-scope Binders and class-scope
   TagBinders exist on a single list, discrimiated by the leading AEop field
   of each entry (s_binder, s_tagbind, s_member).

   APOLOGY: This assumes that Binder, TagBinder and ClassMember all begin:
   {AEop sort;  SelfType *cdr;  Symstr *sv; ...} so we can pun. It can be
   made cleaner with a common initial structure and casts, but this spreads
   the filth over several modules rather than localising it here in bind.c.

   NOTE: binding information persists only for the duration of parsing -
   consequently it makes sense for the parse tree to contain references to
   binding records rather than the main symbol table entries. Toplevel
   binding are allocated in 'global' store which is not reclaimed after each
   top-level phrase.

   NOTE: This also means that local Binders/TagBinders may not be inspected
   during/after register allocation (which reuses syntax store).

*/

/* AM: create a globalized Binder.  For use in rd_decl and
   implicit_decl.  Beware: its components still need globalizing.
   Possible optimisation: overwrite if already there on re-definition.
   Precondition to call: loc must not represent a local binding.
*/
#define topbind2(sv, stg, typ) \
   (bind_global_(sv) = topbindingchain = \
        global_mk_binder(topbindingchain, sv, stg, typ))

static Binder *topbindingchain;                                 /* vars */
static TagBinder *toptagbindchain;                              /* tags */
static LabBind *labelchain;                                     /* labels */

/* FW: 01-Apr-96 definition of Scope published in bind.h */

static Scope *local_scope, *freeScopes;
static bool tag_found_in_local_scope;
static bool tpara_found_in_enclosing_scope;
        /* used to avoid searching twice in instate_xxx... */
static int scope_level;

#ifdef CALLABLE_COMPILER
void set_local_scope(Scope *scope)
{   local_scope = scope;
}
#endif

static int push_init_scope(TagBinder *class_tag, ScopeSaver init,
        ScopeSort kind)
{   Scope *scope = freeScopes;
    if (scope != NULL)
        freeScopes = freeScopes->prev;
    else
        scope = (Scope *) GlobAlloc(SU_Bind, sizeof(Scope));
    if (debugging(DEBUG_BIND))
        cc_msg("push_scope($b) -> %d\n", class_tag, scope_level);
    scope->scopemems = init;
    scope->prev = local_scope;
    local_scope = scope;
    scope->class_tag = class_tag;
    scope->kind = kind;
    return scope_level++;
}

int push_scope(TagBinder *class_tag, ScopeSort kind)
{   return push_init_scope(class_tag, 0, kind);
}

int push_var_scope(ScopeSaver init, ScopeSort kind)
{   return push_init_scope(0, init, kind);
}

/* The pop_scope routines return values giving the (last) popped        */
/* scope so this can be restored for argument scopes in fn defs.        */
static ScopeSaver pop_scope_1(int level, bool check_unrefd)
{   Scope *scope = local_scope;
    ScopeSaver poppling = 0;
    Binder *p;
    if (level > scope_level)
        syserr("pop_scope: level=%d >= scope_level=%d", level, scope_level);
  while (scope_level > level)
  { if (debugging(DEBUG_BIND)) cc_msg("pop_scope(%d)\n", scope_level);
    if (scope == NULL) syserr("pop_scope: NULL scope pointer");
    poppling = scope->scopemems;        /* empty for class scopes       */
    if (scope->class_tag == NULL && check_unrefd)
    {   /* Check for unreferenced names in local scopes */
        Symstr *sv;
        for (p = poppling;  p != 0;  p = bindcdr_(p))
        {   if (h0_(p) != s_binder || h0_(bindtype_(p)) == t_ovld) continue;
            sv = bindsym_(p);
            /* do a bit more in the next line for used/set */
            /* suppress warning for gensym'd vars, which patch up user errs */
            if (!(binduses_(p) & u_referenced) &&
                !isgensym(sv) &&
                !(bindstg_(p) & b_pseudonym))
            {
                if (sv == thissym)
                {   if (!SuppressDB_Has(Suppress_UnusedThis))
                        cc_warn(bind_warn_unused_this_in_member);
                }
                else
                  if (bindstg_(p) & bitofstg_(s_typedef))
                    cc_warn(istypevar(bindtype_(p)) ?
                            bind_warn_typename_not_used : bind_warn_typedef_not_used, p);
                  else if (bindstg_(p) & b_fnconst)
                    cc_warn(bind_warn_function_not_used, p);
                  else
                    cc_warn(bind_warn_variable_not_used, p);
            }
        }
    }
    else
    /* The next line fixes nasties like:                                */
    /* "struct d { struct d { int a; } c; } x;"  by inhibiting the      */
    /* outer setting and so recovering to "struct d { int a; }.         */
    {   TagBinder *b = scope->class_tag;
        scope->class_tag = NULL;                /* @@@ kill... */
        /* This is only for C: C++ has already closed the class (in     */
        /* cpp_end_strdecl). Hence no need to do this for the core class*/
        if (b != NULL && (tagbindbits_(b) & TB_BEINGDEFD))
            tagbindbits_(b) = (tagbindbits_(b) & ~TB_BEINGDEFD) | TB_DEFD;
    }
    local_scope = scope->prev;
    scope->prev = freeScopes;
    freeScopes = scope;
    scope = local_scope;
    --scope_level;
  }
  return poppling;
}

ScopeSaver pop_scope(int level)
{   return pop_scope_1(level, YES);
}

ScopeSaver pop_scope_no_check(int level)
{   return pop_scope_1(level, NO);
}

static Scope *set_local_block_scope(void)
{   Scope *scope0 = local_scope;
    if (!LanguageIsCPlusPlus)
    {   Scope *scope;
        for (scope = scope0;  scope != 0;  scope = scope->prev)
            if (scope->class_tag == 0) break;
        /* Intentionally, if local_scope is 0, instate_declaration_1()  */
        /* will syserr(). Note: this is the ONLY caller...              */
        local_scope = scope;
    }
    return scope0;
}

static TagBinder *findtag_in_members(Symstr *sv, ClassMember *ll)
{   TagBinder *l = (TagBinder *)ll;
    for (; l != NULL;  l = tagbindcdr_(l))
    {   if (debugging(DEBUG_BIND))
            cc_msg("findtag try $r %lx\n", memsv_(l), (long)attributes_(l));
        if (h0_(l) == s_tagbind &&
            (h0_(sv)==s_tagbind && l == (TagBinder *)sv || tagbindsym_(l)==sv))
                break;
        /* this happens only in template arg scope where the tagbinders
           were deliberately lost.
         */
        if (tagbindsym_(l) == sv && isclasstype_(princtype(tagbindtype_(l))))
        {   Expr *deftexpr = bindconst_((ClassMember *)l);
            TagBinder *res = typespectagbind_(princtype(tagbindtype_(l)));
            if (local_scope->class_tag != NULL &&
                !(tagbindbits_(local_scope->class_tag) & TB_TEMPLATE) &&
                deftexpr != NULL)
            {   if (!isclasstype_(princtype(type_(deftexpr))))
                    syserr("default class type expected");
                res = typespectagbind_(princtype(type_(deftexpr)));
            }
            return res;
        }
    }
    return l;
}

/* @@@ no access control? */
TagBinder *findtagbinding(Symstr *sv, TagBinder *cl, int fbflags)
{   Scope *scope;
    bool first = 1;
    tag_found_in_local_scope = 0;
    tpara_found_in_enclosing_scope = NO;
    if (!LanguageIsCPlusPlus && cl != NULL)
        syserr("strange findtagbinding for C");
    /* @@@ note that we don't inherit classes via bases!                */
    if (cl != NULL)
    {   if (tagbindbits_(cl) & TB_TEMPLATE)
        {   Binder *b = tagformals_(cl);
            for (; b; b = bindcdr_(b))
                if (bindsym_(b) == sv && istypevar(bindtype_(b)))
                {   tpara_found_in_enclosing_scope = YES;
                    break;
                }
        }
        return findtag_in_members(sv, tagbindmems_(core_class(cl)));
    }

    if (fbflags == ALLSCOPES)
        for (scope = local_scope;  scope != NULL;  scope = scope->prev)
        {   ClassMember *l;
            TagBinder *b;
            if ((cl = scope->class_tag) != NULL)
            {   if (LanguageIsCPlusPlus)
                    l = tagbindmems_(core_class(cl));
                else
                    continue;           /* C class scopes don't nest.   */
            }
            else
                l = scope->scopemems;
            if ((b = findtag_in_members(sv, l)) != 0)
                return (tag_found_in_local_scope = first, b);
            first = 0;
        }
    return tag_global_(sv);
}

/* routine finds both members and binders -- in C these can be checked  */
/* to be consistent by caller.  In C++ they are equivalent.             */
/* find_scopemember finds ANY suitably named member, but will get       */
/* the nearest in case of ambiguity.                                    */
/* For anonymous unions it returns the whole union, not the element.    */
static ClassMember *find_scopemember(Symstr *sv, ClassMember *p)
{   ClassMember *l;
    TagBinder *cl = NULL;
    for (l = p;  l != NULL;  l = memcdr_(l))
    {   if (debugging(DEBUG_BIND))
            cc_msg("findscopemember try $r %lx\n",
                memsv_(l), (long)attributes_(l));
        if ((h0_(l) == s_member || h0_(l) == s_binder) && memsv_(l) == sv)
            return l;
    }

    if (LanguageIsCPlusPlus && (local_scope->kind == Scope_TemplateArgs ||
        ((cl = local_scope->class_tag) != NULL && tagbindbits_(cl) & TB_TEMPLATE)))
    {   Scope *scope = local_scope;
        Binder *temp;
        for (; scope; scope = scope->prev)
        {   if (scope->kind != Scope_TemplateArgs) continue;
            for (temp = scope->scopemems; temp; temp = bindcdr_(temp))
                if (memsv_(temp) == sv) return temp;
        }
    }
    return 0;
}

static TagBinder *qualifyingBase;   /* extra IN arg to path_to_member_1 */
static TagBinder *startScope;       /* another one */

static Expr *path_to_member_1(ClassMember *member, TagBinder *tb, int flags,
        ClassMember *vbases, TagBinder *privately_deriving_class)
{   ClassMember *l;

    /* This can never happen C-only... */
    if (qualifyingBase != 0 &&
        (qualifyingBase == tb || core_class(qualifyingBase) == tb))
            flags &= ~FB_NOTYET;

if (!(flags & FB_NOTYET))
{   if ((tagbindbits_(tb) & TB_DEFD) && !(tagbindbits_(tb) & TB_SIZECACHED))
    {   SET_BITMAP opaque = tagbindbits_(tb) & TB_OPAQUE;
        /* mometarily not opaque so we can look up mem fns */
        tagbindbits_(tb) &= ~TB_OPAQUE;
        (void)sizeofclass(tb, NULL);
        tagbindbits_(tb) |= opaque;
    }

    for (l = tagbindmems_(tb);  l != NULL;  l = memcdr_(l))
    {   if (debugging(DEBUG_BIND))
            cc_msg("see $r %lx in $c\n", memsv_(l), (long)attributes_(l), tb);
        if (h0_(member) == s_identifier)
        {   Symstr *sv = (Symstr *)member;
            if (memsv_(l) != sv) continue;
        }
        else if (l != member)
            continue;

/* The next line avoids spurious errors for class-within-class defn.    */
/* (path_to_member() ignores s_tagbind's.)                              */
        if (h0_(l) == s_tagbind) continue;

        if (startScope != NULL && core_class(startScope) != tb &&
            h0_(l) == s_member &&
            !derived_from(tb, core_class(startScope)))
        {   cc_err(bind_err_cant_use_outer_member, tb, memsv_(l));
            return (Expr*)implicit_decl(memsv_(l), 0);
        }

        curlex_member = l;  /* this saves some searching and helps with */
                            /* diagnosing access faults.                */
        if (LanguageIsCPlusPlus)
        {   if (memtype_(l) == ACCESSADJ) /* access decl */
            {   accessOK = 1;
                continue;
            }
            check_access(l, privately_deriving_class);
        }
        /* the following save store when searching for tyenames...      */
        if (flags & (FB_CLASSNAME|FB_TYPENAME|FB_FNBINDER))
            return (Expr *)l;

        if (LanguageIsCPlusPlus)
        {   if (h0_(l) == s_binder)
            {   Binder *b = (Binder *)l;
                if (bindstg_(b) & b_pseudonym) b = realbinder_(b);
                if (!(flags & FB_FNBINDER)
                    &&
                    /* BEWARE: a local memfn_a is static... */
                    ( (bindstg_(b) & b_memfna) ||
                     !(bindstg_(b) & (bitofstg_(s_static)|bitofstg_(s_typedef)))
                    )
                    &&
                /* overloaded fns can't be typedefs; use ovld-stg bit?  */
                /* match both generic and specific functions.           */
                    (h0_(bindtype_(b)) == t_ovld || h0_(bindtype_(b)) == t_fnap)
                   )
                    /* exprdotmemfn_() */
                    return mk_exprwdot(s_dot, bindtype_(b),
                        nullbinder(bindparent_(b)), (IPtr)b);
                /* Otherwise: a typedef name, static member, enumerator */
                /* or a function binder was requested via FB_FNBINDER.  */
                return (Expr *)b;
            }
        }
        /* Assert: h0_(l) == s_member, whether C or C++ */
        if (tagbindbits_(tb) & TB_OPAQUE)
            cc_rerr(bind_rerr_mem_opaque, l);
        {   int32 n = 0;
            if (membits_(l) != 0) {
                if (target_lsbitfirst) {
                    int32 maxsize = MAXBITSIZE;
                    if (int_islonglong_(typespecmap_(memtype_(l)))) maxsize = sizeof_longlong*8;
                    n = (membits_(l)+memboff_(l)) % maxsize;
                    if (n != 0) n = maxsize - n;
                } else
                    n = memboff_(l);
            }
            return mk_exprbdot(s_dot, memtype_(l), nullbinder(tb), memwoff_(l), membits_(l), n);
        }
    }
}
    if (LanguageIsCPlusPlus && (flags & FB_INHERIT))
        return path_to_base_member(member, tb, flags, vbases, privately_deriving_class);
    else {
        IGNORE(vbases); IGNORE(privately_deriving_class);
    }
    return NULL;
}

Expr *path_to_member(ClassMember *member, TagBinder *b, int flags)
{   Expr *e;
    if (b == 0 || !isclasstagbinder_(b))
        syserr("path_to_member of no or non-class tagbinder");
    if (member == NULL) return NULL;
    if (debugging(DEBUG_BIND))
    {   Symstr *sv = h0_(member) == s_identifier ?
            (Symstr *)member : memsv_(member);
        cc_msg("path_to_member($r, $b, 0x%.3x) at $l\n", sv, b, flags);
    }
    if (LanguageIsCPlusPlus)
    {   accessOK = 0;
        curlex_member = 0;
        {   ClassMember *l = tagbindmems_(b);
            if (l != NULL && !(attributes_(l) & CB_CORE)) l = NULL;
            e = path_to_member_2(member, b, flags, l, NULL);
        }
        if (e != 0 && h0_(e) == s_invisible && !(flags & FB_KEEPI))
            e = arg2_(e);
    }
    else
        e = path_to_member_1(member, b, flags, NULL, NULL);
    return e;
}

Expr *findpath(Symstr *sv, TagBinder *cl, int flags, TagBinder *inBase)
{   Scope *scope;
    Binder *b = NULL;
    ClassMember *member = (ClassMember *)sv;
    if ((qualifyingBase = inBase) != NULL) flags |= FB_NOTYET;
    if (cl != NULL)
        return path_to_member(member, cl, flags);

    for (scope = local_scope; scope != NULL; scope = scope->prev)
        if ((startScope = scope->class_tag) != NULL) break;

    for (scope = local_scope;  scope != NULL;  scope = scope->prev)
    {
        b = NULL;
        cl = scope->class_tag;
        if (cl != NULL && (flags & FB_CLASSES))
            b = (Binder *)path_to_member(member, cl, flags);
        else if (cl == NULL && (flags & FB_LOCALS))
            b = find_scopemember(sv, scope->scopemems);
        if ((flags & FB_THISSCOPE)
            ||
            b != NULL && (
             LanguageIsCPlusPlus &&
             ((flags & FB_CLASSNAME) == 0 ||
               h0_(b) == s_binder && (bindstg_(b) & bitofstg_(s_typedef)) &&
               isclasstype_(princtype(bindtype_(b)))
             )
             ||
            !LanguageIsCPlusPlus &&
             ((flags & FB_TYPENAME) == 0 ||
              (cl == NULL) ||
              h0_(b) == s_binder && (bindstg_(b) & bitofstg_(s_typedef))
             )
           ))
            break;
    }
    startScope = 0;
    /* The following code is extremely curious. It has the effect of looking
       up a base class name! And only if there is no curlex_scope. */
    /* This ignores 'flags' -- even FB_GLOBAL */
    return (Expr *)((scope != NULL) ? b : bind_global_(sv));
}

Binder *findbinding(Symstr *sv, TagBinder *cl, int flags)
{   return (Binder *)findpath(sv, cl, flags | FB_FNBINDER, 0);
}

void add_toplevel_binder(Binder *b)
{   bind_global_(bindsym_(b)) = b;
    bindcdr_(b) = topbindingchain;
    topbindingchain = b;
}

static Binder **insertionpoint(Scope *scope)
{
/* Now we are supposedly about to ADD to a partially made scope.        */
/* Hence we must have either a local scope or a TB_BEINGDEFD class.     */
/* We need to worry about CB_CORE for partially made class scopes...    */
    TagBinder *cl = scope->class_tag;
/* duplicate names must be seen first for local (auto) scopes since     */
/* argument narrowing relies on it, similarly members must be placed    */
/* in proper order (at least eventually):                               */
    if (cl == 0)
    {   if (/*scope->kind == Scope_TemplateArgs ||*/ scope->kind == Scope_TemplateDef)
            syserr("attempt to insert into read-only scope");
        return &scope->scopemems;
    }
    else
    {   ClassMember **q, *l;
        if (!(tagbindbits_(cl) & TB_BEINGDEFD))
            syserr("adding to completed scope $c", cl);
        cl = core_class(cl);
        q = &tagbindmems_(cl);
        while ((l = *q) != NULL) q = &bindcdr_(l);
        return q;
    }
}

static void add_local_binder(Binder *b)
{   Scope *scope = local_scope;
    Binder **p = insertionpoint(scope);
#if 0
    /* only generics binders */
    if (isfntype(bindtype_(b))) return;
#endif
    if (debugging(DEBUG_BIND))
    {   cc_msg("add_local_binder($b) in scope %p\n", b, scope);
        if (debugging(DEBUG_TYPE))
            cc_msg("princtype %ld\n", h0_(bindtype_(b)));
    }
    bindcdr_(b) = *p;
    *p = b;
}

static void add_local_tagbinder(TagBinder *b, bool implicit)
/* Note that in C, class scopes don't nest; see also findtagbinding().  */
/* 'implicit' is set when we have a non-explicit declaration which is   */
/* not a definition of a class tag, within another class or a formal    */
/* parameter list. Lift to first unnamed scope.                         */
{   Scope *scope = local_scope;
    if (implicit || !LanguageIsCPlusPlus)
        while (scope && (scope->class_tag != NULL ||
                         (LanguageIsCPlusPlus &&
                          (scope->kind == Scope_Args ||
                           scope->kind == Scope_TemplateDef ||
                           scope->kind == Scope_TemplateArgs))))
            scope = scope->prev;
    if (scope == NULL)
    {   if (!LanguageIsCPlusPlus) syserr("add_local_tagbinder");
        tagbindcdr_(b) = toptagbindchain;
        tag_global_(tagbindsym_(b)) = toptagbindchain = b;
    }
    else
    {   TagBinder **p = (TagBinder **)insertionpoint(scope);
        tagbindcdr_(b) = *p;
        *p = b;
        if (scope->kind == Scope_Args)
            cc_warn(bind_warn_new_tag_in_formals, b);
    }
    if (LanguageIsCPlusPlus)
    {   /* local classes MUST have INTERNAL linkage... */
        while (scope && (scope->class_tag != NULL || scope->kind == Scope_Args ||
                         scope->kind == Scope_TemplateArgs))
            scope = scope->prev;
        if (scope != NULL) set_linkage((Binder *)b, A_NOLINKAGE, NULL);
    }
}

static void add_member(ClassMember *m)
{   Scope *scope = local_scope;
    ClassMember **p = insertionpoint(scope);
    if (debugging(DEBUG_BIND))
        cc_msg("add_member($r) in scope %p\n", memsv_(m), scope);
    memcdr_(m) = *p;
    *p = m;
}

static ClassMember *instate_member_1(DeclRhsList *d, int bindflg)
{   ClassMember *m, *oldm;
    int32 bitsize;
    TypeExpr *t;
    bool implicit_typedef_exists = NO;
    Symstr *sv = d->declname;
    SET_BITMAP access = attribofstgacc_(d->declstg);
/* note: other users of d->declstg should use killstgacc_(d->declstg).  */
    if (access==0) syserr("instate_member(access==0)");
    oldm = m = (sv == NULL) ? NULL :
        find_scopemember(sv, tagbindmems_(local_scope->class_tag));
        /* LDS: 29-Mar-95: Changed (O(N**2) performance reasons) from:  */
        /*      findbinding(sv, local_scope->class_tag, INCLASSONLY);   */
    if (m != NULL)
    {   if (bindstg_(m) & d->declstg & bitofstg_(s_typedef))
        {   if ((d->declstg & bitofstg_(s_typedef)) &&
                (d->declstg & u_implicitdef))
                return NULL;
            else if ((bindstg_(m) & bitofstg_(s_typedef)) &&
                     (bindstg_(m) & u_implicitdef))
                /* supercede it... */
                bindstg_(m) |= u_referenced;
            else
                syserr("instate_member_1");
        } else if (bindstg_(m) & bitofstg_(s_typedef) &&
                     bindstg_(m) & u_implicitdef)
            implicit_typedef_exists = YES;
        else
        {   if (istypevar(bindtype_(m)))
                cc_rerr(syn_rerr_temp_para_redefinition, m);
            else
                cc_rerr(syn_rerr_duplicate_member(m));
            d->declname = gensymval(1);
        }
    }
/* bindflg is set so that all structs are globalized except within fns. */
/* This includes structs declared in formal parameter lists whose scope */
/* is only the function.                                                */
    t = d->decltype;
/*/* @@@ LDS 05-Oct-94: the first ! was missing - what is really meant? */
/* Do we still need to globalize for local classes??                    */
    if (!LanguageIsCPlusPlus && !(bindflg & (GLOBALSTG|TOPLEVEL)))
    {   m = (ClassMember *)BindAlloc(SIZEOF_CLASSMEMBER);
    }
    else
    /* always allocate globally for C++ local class memfns.             */
    {   m = (ClassMember *)GlobAlloc(SU_Bind, SIZEOF_CLASSMEMBER);
        RecordGlobalBinder(m);
        t = globalize_typeexpr(t);
    }
    /* We now evaluate a bitfield's size here, rather than later: by so */
    /* doing, membits no longer tells us whether a member is a bitfield */
    /* but this is only a consistency check since memtype & BITFIELD is */
    /* what really distinguishes bitfields.                             */
    bitsize = (declbits_(d) == NULL) ? 0 : evaluate(declbits_(d));
    h0_(m) = s_member;
    memcdr_(m) = NULL;
    memsv_(m) = sv;                    /* 0 for padding (:0) bit fields */
    memtype_(m) = t;
    memwoff_(m) = OFFSET_UNSET; memboff_(m) = 0; membits_(m) = (uint8)bitsize;
    attributes_(m) = access;
    bindstg_(m) = 0;                    /* b_member? */
    bindparent_(m) = local_scope->class_tag;
    if (implicit_typedef_exists)
    {   ClassMember *l = tagbindmems_(local_scope->class_tag);
        for (; l != NULL; l = memcdr_(l))
            if (memcdr_(l) == oldm) break;
        if (l == NULL) syserr("lost in instate_member_1");
        memcdr_(l) = m; memcdr_(m) = memcdr_(oldm);
        memcdr_(oldm) = NULL;
        add_member(oldm);
    }
    else
        add_member(m);
    return m;
}

/* struct/union/enum tag bindings ... */

TagBinder *instate_tagbinding(Symstr *sv, AEop s, TagDefSort defining,
            int bindflg, bool *newtag)
{   TagBinder *b;
    if (sv == 0)
    {   sv = gensymval(1);
        defining = TD_ContentDef;
    }
    *newtag = NO;
    if (bindflg & TOPLEVEL)
    {   b = tag_global_(sv);
        if (b == 0 || defining != TD_NotDef)
        {   /* new tag or tag being defined... */
            if (debugging(DEBUG_BIND))
                cc_msg("top level struct $r@%p\n", sv, (VoidStar)b);
            if (b == 0)
                /* introduction of new tag */
            {   *newtag = YES;
                tag_global_(sv) = toptagbindchain = b =
                    global_mk_tagbinder(toptagbindchain,sv,s);
                if (tagbindparent_(b) != 0 && !(bindflg & TEMPLATE))
                        syserr("instate_tagbinding($b)", b);
                if (!LanguageIsCPlusPlus &&
                    defining != TD_NotDef &&
                    local_scope != 0 &&
                    !isgensym(sv) &&
                    !SuppressDB_Has(Suppress_Future))
                    cc_warn(bind_warn_cpp_scope_differ, b);
            }
            else if (defining != TD_Decl && (tagbindbits_(b) & (TB_DEFD|TB_BEINGDEFD)))
                cc_err(bind_err_duplicate_tag, tagbindsort(b),b);
        }
    }
    else
    {   b = findtagbinding(sv, 0, ALLSCOPES);
        if (b == 0 || defining != TD_NotDef)
        {   /* new tag or tag being defined... */
            bool implicit = 0;
            if (debugging(DEBUG_BIND))
                cc_msg("local struct $r@%p\n", sv, (VoidStar)b);

            if (LanguageIsCPlusPlus && tpara_found_in_enclosing_scope)
            {   cc_err(bind_err_template_tpara_redeclared, sv);
                b = NULL;
            }

            if (b != 0 && tag_found_in_local_scope &&
                (((tagbindbits_(b) & TB_DEFD) && defining != TD_Decl)
                 ||  /* re-definition */
                 (tagbindbits_(b) & TB_BEINGDEFD)))
            {
                cc_err(bind_err_duplicate_tag, tagbindsort(b), b);
                b = 0;
            }
            if (b == 0 ||
                defining == TD_ContentDef && !tag_found_in_local_scope)
            {   *newtag = YES;
/* bindflg & GLOBALSTG refers to tags in formals: these need careful    */
/* treatment in that they are somewhat visible.  e.g. equivtype needs   */
/* to see "f(struct a { int b,c;})" differing from g of similar type.   */
/* For C++, always allocate even local structs in global store since    */
/* they may have member fns.                                            */
                b = (bindflg & GLOBALSTG) || LanguageIsCPlusPlus ?
                    global_mk_tagbinder(0, sv, s) : mk_tagbinder(sv, s);
                if (bindflg & TEMPLATE)
                    tagbindbits_(b) |= TB_TEMPLATE;
/* The next lines avoids 'true' scoping as a hack to make B=B in:       */
/*      class A { class B *p; }; class B { whatever };                  */
/* Also in class A {friend class B; }; class B { whatever };            */
                if (defining == TD_NotDef && !(bindflg & TEMPLATE))
                    implicit = 1;
                else if (!LanguageIsCPlusPlus)
/* @@@ the following can't be right for C compilers:  current_member_scope() is always NULL */
                {   if (!isgensym(sv) && current_member_scope() != 0 && !SuppressDB_Has(Suppress_Future))
                        cc_warn(bind_warn_cpp_scope_differ, b);
                    implicit = 1;
                }
                if (implicit) b->tagparent = 0;
                add_local_tagbinder(b, implicit);
            }
        }
    }
    if ((tagbindbits_(b) & ENUMORCLASSBITS) != bitoftype_(s) &&
        ((tagbindbits_(b) & (bitoftype_(s_union)|bitoftype_(s_enum)))
         || s == s_union || s == s_enum))
        cc_err(bind_err_reuse_tag, tagbindsort(b), b, s);
    if (defining == TD_ContentDef)
        tagbindbits_(b) = (tagbindbits_(b) & ~ENUMORCLASSBITS) | bitoftype_(s);
/* AM: the next test was != TD_NotDef but BEINGDEFD should not be set   */
/* after "struct A;" (to match with "struct A *p").                     */
/* Has anyone started using TB_BEINGDEFD to distinguish?                */
    if (defining == TD_ContentDef) tagbindbits_(b) |= TB_BEINGDEFD;
    return b;
}

/* variable and typedef bindings... */

Binder *implicit_decl(Symstr *a, int32 fn)
{
/* implicit declaration of 'extern int x' or 'extern int f()'  */
/* N.B. the information has to be generated in the global heap */
    if (LanguageIsCPlusPlus && fn)
        return implicit_decl_cpp(a);

    {   TypeExpr *t = te_int;
        TypeExprFnAux s;
        if (fn)
            t = g_mkTypeExprfn(t_fnap, t, 0, 0,
                packTypeExprFnAux(s, 0, 999, 0, 0,
                    fpregargs_disabled ? f_nofpregargs : 0));   /* minargs_ */
        topbind2(a, (fn ? bitofstg_(s_extern)|b_undef|b_fnconst :
                    bitofstg_(s_extern)|b_undef), t);
        binduses_(topbindingchain) |= u_implicitdef;
        return topbindingchain;
    }
}

/*
 * Used below and in instate_declaration for tentative Ansi definitions.
 * To say that this code is NASTY is a gross understatement. In fact,
 * it is hard to describe its nastiness in mere words.
 * @@@ AM (Sep 89) wants to re-work all this structure soon.
 */
struct TentativeDefn
{
    TentativeDefn *next;
    DataAreaSort datasort;
    DataDesc   data;
    int32      size, align;
    int32      elt_size;                              /* for open array */
/* When TARGET_HAS_BSS is NOT set, maybebss=1 <==> size=0.              */
    bool       maybebss;
    bool       statik;
    Symstr     *sv;
};

static TentativeDefn *tentative_defs;     /* also init'd by bind_init */

static DataInit *datahead,
                *datasplice,
                *datatail;
static TentativeDefn saved_vg_state;

void save_vargen_state(TentativeDefn *td)
{
    td->datasort = SetDataArea(DS_None);
    td->data.head = get_datadesc_ht(YES); td->data.tail = get_datadesc_ht(NO);
    td->data.size = get_datadesc_size();
}

static void restore_vargen_state(TentativeDefn *td)
{
    SetDataArea(td->datasort);
    set_datadesc_ht(YES, td->data.head); set_datadesc_ht(NO, td->data.tail);
    set_datadesc_size(td->data.size);
}


/*
 * Used to make a tentative defns list for the following routines.
 * Basically, this routine is called to record information about
 * the state of vargen.c before a zero initialiser for a tentative
 * static is processed.
 * It also holds whether we hope to allocate a top-level variable in bss.
 */
static bool addTentativeDefn(
    Symstr *sv, int32 size, int32 elt_size, int32 align, DeclRhsList *d)
{
    TentativeDefn *td = NULL;
    for (td = tentative_defs; td != NULL; td = td->next)
        if (td->sv == sv) break;
    if (td == NULL)
    {   td = (TentativeDefn *) GlobAlloc(SU_Other, sizeof(TentativeDefn));
        td->data.head = td->data.tail = (DataInit *)DUFF_ADDR;
        td->data.size = 0;
        td->datasort  = DS_None;
        td->next      = tentative_defs;
        td->size      = 0;
        td->elt_size  = elt_size;
        td->align     = align;
        td->sv        = sv;
        td->maybebss  = YES;
        td->statik    = (d->declstg & bitofstg_(s_static)) != 0;
        tentative_defs= td;
    }
/* The following test fills in the size details in:  int a[],a[100];    */
    if (size != 0)
    {   td->size = size;
#ifdef TARGET_HAS_BSS
        td->maybebss = HasFeature(Feature_PCC) || (size > BSS_THRESHOLD);
#else
        td->maybebss = 0;
#endif
#if 0
        /* We now defer the saving of vargen's state until after we know */
        /* whether the variable is to go in read-write or const data     */
        SetDataArea(stg & u_constdata ? DS_Const : DS_ReadWrite);
        save_vargen_state(td); /* size = 0 => tentative foo[] */
#endif
        d->tentative = td;
    }
#ifdef DEBUG_TENTATIVE_DEFS
if (debugging(DEBUG_BIND)) cc_msg(
"addTentativeDefn %lx, %lx next %lx (%s) head %lx tail %lx loc %ld name %s size %ld\n",
    (int32)get_datadesc(),
    (int32) td, (int32) td->next, (td->next) ? symname_(td->next->sv) : "",
    (int32)get_datadesc_ht(YES), (int32)get_datadesc_ht(NO),
    (int32)get_datadesc_size(), symname_(sv), size);
#endif
    return td->maybebss;
}

#ifdef DEBUG_TENTATIVE_DEFS

static void show_vargen_state(char *when)
{
    if (debugging(DEBUG_BIND))
    {   DataInit *tmpdataq;
        cc_msg("vargen state %lx %s restoration:-\n", (int32)get_datadesc(), when);
        for (tmpdataq = get_datadesc_ht(YES); tmpdataq != 0; tmpdataq = tmpdataq->datacdr)
        {
            cc_msg(
                "DataInit %lx: cdr %lx rpt %ld sort %lx len %ld val %ld\n",
                (int32) tmpdataq, (int32) tmpdataq->datacdr, tmpdataq->rpt,
                tmpdataq->sort, tmpdataq->len, tmpdataq->val);
        }
        cc_msg("head = %lx tail = %lx size = %ld\n\n",
            (int32)get_datadesc_ht(YES), (int32)get_datadesc_ht(NO), get_datadesc_size());
    }
}

#endif
/*
 * The following routines are the ones that do the messing around with
 * vargen pointers in order to throw away old (zero) tentative initialisers
 * and replace them with new initialisers.
 */
static bool is_tentative(Symstr *sv)
{
    TentativeDefn *td = tentative_defs, *prev;

    for (prev = NULL;  td != NULL;  prev = td, td = td->next)
    {   if (td->sv == sv)
        {   /* we are going to return TRUE at the end of this iteration.  */
            int32 count=0;
            DataInit *tmpdataq;
            /*
             * Found a tentative definition so let's reset vargen's state
             * ready for the initialiser... but only if (old) size != 0.
             * @@@ the 'size' test next is becoming subsumed by the bss test.
             */
            if (td->size != 0 && !td->maybebss)
            {   SetDataArea(td->datasort);
                save_vargen_state(&saved_vg_state);
#ifdef DEBUG_TENTATIVE_DEFS
if (debugging(DEBUG_BIND)) show_vargen_state("before");
#endif
                /* Restore vg's state to that before reading the initialiser */
                restore_vargen_state(td);
                datahead = td->data.head;
#ifdef DEBUG_TENTATIVE_DEFS
if (debugging(DEBUG_BIND)) show_vargen_state("after");
#endif
                /*
                 *  Throw away old tentative (zero) initialiser ready for
                 *  replacement by genstaticparts().
                 */
                if (get_datadesc_ht(YES) == 0)
                    tmpdataq = saved_vg_state.data.head;
                else
                {   /* FW: It used to say data.tail->datacdr here,
                       but I think it meant datap */
                    tmpdataq = get_datadesc_ht(NO)->datacdr;
                    get_datadesc_ht(NO)->datacdr = 0;
                }
                while (count < td->size)
                {
                    if (tmpdataq == NULL)
                        syserr(syserr_tentative);
                    /* skip labels in static init chain */
                    if (tmpdataq->sort != LIT_LABEL)
                    {
/* AM: insert check for ->len field being valid (i.e. not LABEL/ADCON   */
/* maybe this cannot happen, but AM gets very worried by this sort      */
/* of 'if not LABEL then nice' reasoning.                               */
                        if (tmpdataq->sort == LIT_ADCON)
                            syserr(syserr_tentative1);
                        count += tmpdataq->rpt * tmpdataq->len;
                        datasplice = tmpdataq;
                    }
                    tmpdataq = tmpdataq->datacdr;
                }
                if (count != padsize(td->size,alignof_toplevel_static))
                    syserr(syserr_tentative2);
                datatail = tmpdataq;
                /* set flag for reset_vg_after_init_of_tentative_defn() */
                saved_vg_state.size = td->size;
            }
            else
            {
if (debugging(DEBUG_BIND)) cc_msg("maybebss found\n");
            }
            /* remove entry from tentative list */
            if (prev == NULL)
                tentative_defs = td->next;
            else
                prev->next = td->next;
            return YES;
        }
    }
    return NO;
}

void reset_vg_after_init_of_tentative_defn(void)
{
    TentativeDefn *td;
    if (saved_vg_state.size == 0) return;
    /*
     * Vargen has now inserted the new initialiser just where we want it.
     * Hum, however I might have removed an item from the list which I
     * have in my own tables.  Check for this and update any items found.
     */
    for (td = tentative_defs;  td != 0;  td = td->next)
        if (td->data.tail == datasplice) td->data.tail = get_datadesc_ht(NO);

    /* link new initialiser to the rest of the chain */
    get_datadesc_ht(NO)->datacdr = datatail;

    /*
     * Reset all the pointers so that vargen does not realise that its
     * internal lists have been modified.
     */
    if (datahead != 0) set_datadesc_ht(YES, saved_vg_state.data.head);
    if (datatail != 0) set_datadesc_ht(NO, saved_vg_state.data.tail);
    set_datadesc_size(saved_vg_state.data.size);

    saved_vg_state.size = 0; /* unset flag to prevent recall */
}

static void check_for_incomplete_tentative_defs(TentativeDefn *td)
{
    for (; td != NULL;  td = td->next) {
        if (td->size == 0) {
        /* Variable had an incomplete type when defined: see whether   */
        /* it's still incomplete (tentatives are always toplevel       */
        /* objects, so bind_global_() and bindtype_() are legal.       */
            Binder *b = bind_global_(td->sv);
            if (sizeoftypelegal(bindtype_(b)))
                td->size = sizeoftype(bindtype_(b));
            else {
                if (td->elt_size == 0 || td->statik) {
                    cc_err(bind_err_incomplete_tentative, td->sv);
                    continue;
                }
                td->size = td->elt_size;
            }
            td->maybebss = YES; /* Bodge: need to sort out allocation into
                                   data area (for fwd-refd struct too) */
        }
#ifdef TARGET_HAS_BSS
        if (td->maybebss)
            addbsssym(td->sv, td->size, td->align, td->statik, 0);
#endif
    }
}

static void check_for_fwd_static_decl(Binder *b, Symstr *sv)
{
    /* The following feature optionally enables spurious forward */
    /* static declarations to be weeded out.                     */
    if (HasFeature(Feature_Predeclare) &&
        !(binduses_(b) & u_referenced) &&
        bindstg_(b) & bitofstg_(s_static))
        cc_warn(bind_warn_unused_static_decl, sv);
}

static void check_ansi_linkage(Binder *b, DeclRhsList *d)
{
    if ((bindstg_(b) ^ d->declstg) & PRINCSTGBITS)
    {   /* Linkage clash, but do not moan about stray 'extern type name's */
        if ((d->declstg & b_globalregvar) ||
            (d->declstg & bitofstg_(s_static)) &&
                 !(d->declstg & b_implicitstg) ||
            (d->declstg & bitofstg_(s_extern)) &&
                   (d->declstg & b_implicitstg) ||
            ((bindstg_(b) ^ d->declstg) & bitofstg_(s_weak)))
        {   /* Oldest linkage wins... */
            SET_BITMAP oldstg = bindstg_(b) & (bitofstg_(s_static)|bitofstg_(s_extern)|bitofstg_(s_weak));
            if (oldstg == 0)
                oldstg = d->declstg & (b_implicitstg|bitofstg_(s_static)|bitofstg_(s_extern)|bitofstg_(s_weak));

/* ECN - convert errors about different linkage types to warnings */
            if (SuppressDB_Has(Suppress_Linkage))
              cc_warn(bind_rerr_linkage_disagreement,
                      d->declname, oldstg);
            else
              cc_rerr(bind_rerr_linkage_disagreement,
                      d->declname, oldstg);
            /* patch d->declstg to a compatible tentative type... */
            d->declstg = (d->declstg & ~(b_implicitstg|bitofstg_(s_static)|bitofstg_(s_extern)|bitofstg_(s_weak))) |
                         oldstg;

        } else if (bindstg_(b) & bitofstg_(s_static))
            /* test is needed because of global register variables */
            /* /* Explicit extern here, previous was static.
                  Change d to say static and no longer extern, implicit nor C linkage
                  Check OK for C++ */
            d->declstg = (d->declstg & ~(b_implicitstg|b_clinkage|bitofstg_(s_static)|bitofstg_(s_extern)|bitofstg_(s_weak))) |
                         (bindstg_(b) & (bitofstg_(s_static) | bitofstg_(s_extern) | bitofstg_(s_weak)));
        else if (bindstg_(b) & bitofstg_(s_extern))
            /* test is needed because of global register variables */
            /* /* Implicit static here, previous was extern.
                  Change d to say extern and no longer static.
                  Check OK for C++ */
            d->declstg = (d->declstg & ~(bitofstg_(s_static)|bitofstg_(s_extern)|bitofstg_(s_weak))) |
                         (bindstg_(b) & (bitofstg_(s_static) | bitofstg_(s_extern) | bitofstg_(s_weak)));
    }
    else check_for_fwd_static_decl(b, d->declname);
}

static TypeExpr *is_openarray(TypeExpr *t)
{
    t = princtype(t);                          /* skip leading typedefs */
    if (h0_(t) == t_subscript &&
        (typesubsize_(t) == 0 || h0_(typesubsize_(t)) == s_binder))
        return typearg_(t);
    return NULL;
}

void instate_alias(Symstr *a, Binder *b)
/*
 * Make the symbol a an alias for b. This curious facility is used to
 * provide local pseudonyms ___first_arg and ___last_arg which share
 * binders with the first and last args in a function's definition, and
 * which are sometimes useful when implementing va_args on awkward machines.
 * Note that pop_varenv (qv) will not moan if the symbols I use as aliases
 * are unused.
 */
{   /* should take care over storage lifetimes here... */
    Binder *pseudonym = mk_binder(a, bindstg_(b)|b_pseudonym, bindtype_(b));
    realbinder_(pseudonym) =    /* cautious: shouldn't ever happen now. */
        (bindstg_(b) & b_pseudonym) ? realbinder_(b) : b;
    add_local_binder(pseudonym);
}

#ifdef FOR_ACORN
#ifndef PASCAL
#ifndef FORTRAN
static int cfront_special_name(Binder *b)
{   char *s;
    s = symname_(bindsym_(b));
    if (s[0] == '_' && s[1] == '_')
    {   s += 2;
        if (isdigit(*s))
        {   while (isdigit(*++s));
            if (s[0] == '_' && s[1] == '_') return 1;
        }
        else if (strcmp(s, "link") == 0) return 1;
    }
    return 0;
}
#endif
#endif
#endif

static Binder *instate_declaration_1(DeclRhsList *d, int declflag)
/* only the TOPLEVEL and DUPL_OK bits of declflag are examined */
{
/* I have just parsed a declarator, and in that identifiers are held    */
/* as Symstr *'s which contain an h0 of s_identifier.  Instate the      */
/* declaration, returning the Binder record hung off the symbind_ entry.*/
    Symstr *sv = d->declname;
    Binder *b;
    int32 olduses = 0;
    bool maybebss = 0;
#ifdef PASCAL /*ECN*/
    int level = declflag >> 2;
    declflag &= 3;
#endif
    if (sv == 0 || h0_(sv) != s_identifier)     /* check/remove*/
    {   syserr(syserr_instate_decl, (long)(sv==0 ? 0 : h0_(sv)));
        return 0;
    }
    if (attribofstgacc_(d->declstg)) syserr("instate_decl(access!=0)");
    if (debugging(DEBUG_BIND))
    {   cc_msg("instate_declaration(%x, %lx): $r\n", declflag, d->declstg, sv);
        pr_typeexpr(d->decltype, sv); cc_msg("\n");
    }
/* No need to prunetype as inner typedef would have already been used:  */
    if (LanguageIsCPlusPlus &&
        (d->declstg & bitofstg_(s_typedef)) &&
            isprimtypein_(d->decltype, ENUMORCLASSBITS))
    {   TagBinder *tb = typespectagbind_(d->decltype);
        if (isgensym(tagbindsym_(tb)))
        {   tagbindsym_(tb) = sv;
            if (declflag & TOPLEVEL) tag_global_(sv) = tb;
        }
    }
    if (declflag & TOPLEVEL)
/* Top level declarations may only surplant previous top level extern decls */
/* Really we should also unify 'local' extern decls.  @@@ not done yet.     */
    {   TypeExpr *glotype = 0;
        b = bind_global_(sv);
#ifdef PASCAL /*ECN*/
        if (b && (bindstg_(b) & b_synbit1)) b = 0;
#endif
        if (b != 0) {
            if (bindstg_(b) & bitofstg_(s_typedef))
            {   if (LanguageIsCPlusPlus && d->declstg & bitofstg_(s_typedef) &&
                    !(d->declstg & u_implicitdef) &&
                    equivtype(bindtype_(b), d->decltype) != 2)
                {   cc_err(bind_err_type_disagreement, sv);
                    b = 0;
                } else if (bindstg_(b) & u_implicitdef)
                    b = 0;
            } else if (d->declstg & bitofstg_(s_typedef) &&
                       d->declstg & u_implicitdef)
            {   Binder *bnew = topbind2(sv, d->declstg,
                                    globalize_typeexpr(d->decltype));
                Binder *mem = topbindingchain;
                for (; mem != NULL; mem = bindcdr_(mem))
                    if (bindcdr_(mem) == b) break;
                if (mem == NULL) syserr("lost in instate_declaration_1");
                bindcdr_(mem) = bindcdr_(b);
                bindcdr_(b) = topbindingchain;
                bind_global_(sv) = topbindingchain = b;
                return bnew;
            }
        }
        if (b != 0)
        {   bool discardb = NO;
            olduses = binduses_(b);
            /* check the types match */
            if (h0_(bindtype_(b)) == t_fnap && h0_(d->decltype) == t_fnap)
            {   /* propagate #pragma -v and -y info from decl to defn */
                if (typefnaux_(d->decltype).variad == 0)
                    typefnaux_(d->decltype).variad =
                        typefnaux_(bindtype_(b)).variad;
                typefnaux_(d->decltype).flags |=
                    typefnaux_(bindtype_(b)).flags &
                    ~typefnaux_(d->decltype).flags;
                if ((d->declstg & bitofstg_(s_inline)) &&
                    (bindstg_(b) & b_maybeinline))
                        bindstg_(b) = (bindstg_(b) & ~bitofstg_(s_extern)) |
                            bitofstg_(s_static);
                bindstg_(b) &= ~b_maybeinline;
/* /* @@@ old-style bit here. */
            }
            switch (equivtype(bindtype_(b), d->decltype))
            {   default:
                         if (SuppressDB_Has(Suppress_MPWCompatible) &&
                             widened_equivtype(b->bindtype, d->decltype))
                             /* f(char) incompatibility with f(int)     */
                             /* (or f(c) char c; {}) gets just a warning*/
                             cc_warn(bind_err_type_disagreement, sv);
                         else
                         {   TypeExpr *bt = princtype(bindtype_(b));
                             TypeExpr *dt = princtype(d->decltype);
/* The next line helps the 'SPECMARK' suite...                          */
                             if (h0_(bt) == t_fnap && h0_(dt) == t_fnap)
                                 cc_rerr(bind_err_type_disagreement, sv);
                             else
                                 cc_err(bind_err_type_disagreement, sv);
                             discardb = YES;
                             /* new one wins (or trouble if old was a fn
                                declaration and this is a var definition
                              */
                         }
                         break;
                case 2:  glotype = bindtype_(b); /* d->decltype;  /* IDENTICAL */
                case 1:
                         if (LanguageIsCPlusPlus &&
                             h0_(bindtype_(b)) == t_fnap &&
                             merge_default_arguments(bindtype_(b), d->decltype) == 2)
                             glotype = bindtype_(b); /* d->decltype;  /* IDENTICAL */
                         break;
            }
/* It would be nice to merge the type/stgclass errors so we don't get   */
/* 2 errors for 'typedef int a; extern double a;'                       */
            /* Check for duplicate and conflicting definitions */
            if ((bindstg_(b) | d->declstg) & bitofstg_(s_typedef))
            {   if ((bindstg_(b) & d->declstg) & bitofstg_(s_typedef))
                {   /* can duplicate a typedef in C++, not in C */
                    if (!LanguageIsCPlusPlus)
                        cc_rerr(bind_rerr_duplicate_typedef, sv);
                }
                else
                {   if ((d->declstg & bitofstg_(s_typedef)) &&
                        (d->declstg & u_implicitdef))
                        return NULL;
                    else if ((bindstg_(b) & bitofstg_(s_typedef)) &&
                             (bindstg_(b) & u_implicitdef))
                        discardb = 1;
                    else
                        cc_err(bind_err_duplicate_definition, sv);
                }
            }
/* The next two tests are perhaps more natural the other way round --   */
/* if we have two *definitions* then fault (unless one is tentative),   */
/* otherwise essentially ignore one of the *declarations*.              */
/* It is arguable the PCC case should make a more careful test on u_bss */
/* but this is compatible with previous version.                        */
            else if (bindstg_(b) & b_undef  &&
                     !(bindstg_(b) & u_bss) &&
                      (HasFeature(Feature_PCC) ||
                        !(bindstg_(b) & bitofstg_(s_extern) &&
                          bindstg_(b) & b_implicitstg &&
                          is_openarray(bindtype_(b)))
                      ) || d->declstg & b_undef)
            {   /* At least one of the declarations has no initialiser. */
                /* N.B. an existing static declaration will appear to   */
                /*    have an initialiser, as do ansi tentatives.       */
                /*    (Provisional) BSS tentatives have b_undef but     */
                /*    they also have u_bss, which we avoid.  Messy!     */
                /*    The delicate case: plain int [] has b_undef.      */
                if (HasFeature(Feature_PCC))
                {   /* pcc/as faults b is static or initialised plain,  */
                    /* d is static or plain (whether or not init'd).    */
                    if (!(bindstg_(b) & b_undef) &&
                         (d->declstg & bitofstg_(s_static) ||
                          d->declstg & bitofstg_(s_extern) &&
                          d->declstg & b_implicitstg))
                        cc_err(bind_err_duplicate_definition, sv);
                    else
                        check_for_fwd_static_decl(b, sv);
                }
                else if (LanguageIsCPlusPlus &&
                         !(h0_(bindtype_(b)) == t_fnap) &&
                         (bindstg_(b) & b_implicitstg) &&
                         (d->declstg & b_implicitstg))
                    cc_err(bind_err_duplicate_definition, sv);
                else
                    check_ansi_linkage(b, d);
            }
            else if (!(bindstg_(b) & b_fnconst) &&
                     !(d->declstg  & b_fnconst) &&
                     !HasFeature(Feature_PCC)   &&
                     is_tentative(sv))
                check_ansi_linkage(b, d);
            else
                cc_err(bind_err_duplicate_definition, sv);

            if (!(bindstg_(b) & b_clinkage) && (d->declstg & b_clinkage))
                cc_rerr(bind_rerr_linkage_previously_c,b);

            if (discardb) {
                binduses_(b) |= u_superceded;
                b = 0;
            }
        }
        else
        { if (HasFeature(Feature_Predeclare))
          { /* The following is a feature to enable policing of a software */
            /* quality policy which says "only objects previously DECLARED */
            /* as extern (presumably in a header) may be DEFINED extern".  */
            if ((d->declstg & bitofstg_(s_extern)) &&
                (!(d->declstg & b_undef) || (d->declstg & b_implicitstg)) &&
                sv != mainsym)
                cc_warn(bind_warn_not_in_hdr, sv);
          }
          if ((d->declstg & bitofstg_(s_typedef)) &&
              isprimtypein_(d->decltype, ENUMORCLASSBITS))
          {   TagBinder *tb = typespectagbind_(d->decltype);
              tb->typedefname = sv;
          }
          if (LanguageIsCPlusPlus && h0_(d->decltype) == t_fnap)
              (void) merge_default_arguments(d->decltype, d->decltype);
        }
        /* Maybe we wish to turn off the following for non-hosted system.  */
        if (sv == mainsym && (d->declstg & bitofstg_(s_extern)))
        {   TypeExpr *t = princtype(d->decltype);
            /* check args here too one day? */
            if (h0_(t) != t_fnap || !equivtype(typearg_(t), te_int))
                if (!HasFeature(Feature_PCC) || HasFeature(Feature_Fussy))
                    cc_warn(bind_warn_main_not_int);
        }

        if (HasFeature(Feature_PCC))
        {    if ((d->declstg &
                  (bitofstg_(s_static)|b_fnconst|b_globalregvar|bitofstg_(s_typedef))
                 ) == bitofstg_(s_static) && (d->declstg & b_undef))
            {   maybebss = addTentativeDefn(sv, sizeoftype(d->decltype), 0,
                                   alignoftype(d->decltype),
                                   d)
#ifdef CONST_DATA_IN_CODE
                        && !(d->declstg & u_constdata)
#endif
                           ;
                if (!maybebss) d->declstg &= ~b_undef;
            }
        }
        else
        {   if ((b == 0 || bindstg_(b) & b_undef)
                && !(d->declstg & (b_fnconst|b_globalregvar|bitofstg_(s_typedef)))
                && (d->declstg & b_undef)
                && ((d->declstg & bitofstg_(s_static))
                    || ((d->declstg & bitofstg_(s_extern))
                        && (d->declstg & b_implicitstg))))
            {
                /* no pre-exisiting defn and not a function defn and    */
                /* no initializer and (static blah... or plain blah...) */
                TypeExpr *elt_t = is_openarray(d->decltype);
                int32 size, elt_size;
                if (elt_t == NULL) {
                  size = 0;
                  if (LanguageIsCPlusPlus
                        /* C++ doesn't allow tentative definitions with */
                        /* incomplete type                              */
                      || (d->declstg & bitoftype_(s_static))
                        /* Nor does C if they have internal linkage     */
                      || sizeoftypelegal(d->decltype))
                        /* But it does for external linkage (DR16)      */
                    size = sizeoftype(d->decltype);
                  elt_size = 0;
                } else
                    size = 0, elt_size = sizeoftype(elt_t);
                if (disallow_tentative_statics && (d->declstg &
                    (bitofstg_(s_static) | b_undef | u_constdata) == bitofstg_(s_static) | b_undef))
                {
                    maybebss = sizeoftype(d->decltype) > BSS_THRESHOLD;
                }
                else
                {
                    maybebss = addTentativeDefn(sv, size, elt_size,
                                   alignoftype(d->decltype),
                                   d)
#ifdef CONST_DATA_IN_CODE
                        && !(d->declstg & u_constdata)
#endif
                           ;
                }
                if (!maybebss) d->declstg &= ~b_undef;
            }
        }

        /*
         * Decls such as 'extern int a;' may be superceded by decls such
         * as 'extern int a=1;'.  However, decls such as 'extern int a=1;'
         * may not be superceded (but useless decls such as 'extern int a;'
         * will still be accepted). BUT BEWARE: 'extern int foo[]' MUST be
         * superceded by [extern] int foo[FOOSIZE] or chaos will ensue in
         * -pcc mode (only the size distinguishes Common Def from Ext Ref).
         */
        if ((b != 0) && (glotype == 0))
        {   /*
             * Assert: glotype == 0 iff equivtype(b, d->...) == 1
             *         equivtype(b,d...) == 1 iff one of b, d is blah[].
             * No: could be (int (*b)()) and (int (*d)(int)).
             * Now check for b (the original decl) being an open array.
             */
            if (is_openarray(bindtype_(b)))
            {   binduses_(b) |= u_superceded;
                b = 0;    /* force treatment of d, below, as if new */
            }
        }
        if (b == 0 || !(d->declstg & b_undef))
        {
#ifdef PASCAL /*ECN*/
            TypeExpr *gt = glotype ? glotype : d->decltype;
#else
            TypeExpr *gt = glotype ? glotype : globalize_typeexpr(d->decltype);
#endif
#ifndef OLD_VSN
/* This code updates the old binder when a DEFINITION supercedes a      */
/* DECLARATION.  Thus bind_global_(sv) is set (init. 0) at most once.   */
/* (except for the is_openarray() supercession above.).                 */
            if (b == 0)
                b = topbind2(sv, d->declstg, gt);
            else if (!(bindstg_(b) & b_globalregvar))
            {   /* Assert: !(d->declstg & b_undef) */
                bindstg_(b) = d->declstg |
                  (bindstg_(b) &
                   (bitofstg_(s_virtual)|bitofstg_(s_inline)|b_impl|b_purevirtual));
                bindtype_(b) = gt;      /* @@@ bindstg/bindconst too?   */
            }
#else /* !OLD_VSN */
            /* suppress new DECLARATION if already DEFINED.             */
            if (b != 0) binduses_(b) |= u_superceded;
            topbind2(sv, d->declstg, gt);      /* sets bind_global_(sv) */
            b = bind_global_(sv);
#endif
        }
#ifdef TARGET_HAS_BSS
        if (maybebss)
        {   /* addbsssym() now called when we know for certain. */
            TypeExpr *t = bindtype_(b);
            if (disallow_tentative_statics)
            {
                bindstg_(b) &= ~b_undef;
                bindaddr_(b) = addbsssym(sv, sizeoftype(t), alignoftype(t),
                                (bindstg_(b) & bitofstg_(s_static)) != 0, YES);
            }
            else
                bindaddr_(b) = BINDADDR_UNSET;
        }
#endif
    }
    else
    {   /* NOT a top-level declaration */
        Binder *bnew;
        Scope *saved_local_scope = set_local_block_scope();
        if (local_scope == NULL)
            syserr("instate_declaration_1 - no local scope/local block scope");
        if ((b = find_scopemember(sv, local_scope->scopemems)) != NULL)
        {   if ((bindstg_(b) | d->declstg) & bitofstg_(s_typedef))
            {   if ((bindstg_(b) & d->declstg & bitofstg_(s_typedef)) &&
                    (d->declstg & u_implicitdef))
                {   if (!(d->declstg & b_undef))
                    {   bindstg_(b) = d->declstg | (bindstg_(b) &
                                (bitofstg_(s_virtual)|bitofstg_(s_inline)));
                        bindtype_(b) = globalize_typeexpr(d->decltype);
                    }
                    return NULL;
                }
                else if (bindstg_(b) & bitofstg_(s_typedef))
                {    if (bindstg_(b) & u_implicitdef) declflag |= DUPL_OK;
                } else
                {   Binder *bnew = global_mk_binder(NULL, sv, d->declstg,
                                        globalize_typeexpr(d->decltype));
                    Binder *mem;
                    add_local_binder(bnew);
                    mem = local_scope->scopemems;
                    for (; mem != NULL; mem = bindcdr_(mem))
                        if (bindcdr_(mem) == b) break;
                    if (mem == NULL) syserr("lost in instate_declaration_1");
                    bindcdr_(mem) = bindcdr_(b);
                    bindcdr_(b) = local_scope->scopemems;
                    local_scope->scopemems = b;
                    return bnew;
                }
            }
            if (!(declflag & DUPL_OK))
            {   if (!(bindstg_(b) & d->declstg & bitofstg_(s_extern) ||
                      (LanguageIsCPlusPlus &&
                       bindstg_(b) & d->declstg & bitofstg_(s_typedef))))
                {   if (istypevar(bindtype_(b)))
                        cc_rerr(syn_rerr_temp_para_redefinition, b);
                    else
                        cc_err(bind_err_duplicate_definition, sv);
                }
                else if (equivtype(d->decltype, bindtype_(b)) == 0)
                    cc_err(bind_err_duplicate_definition, sv);
                else if (LanguageIsCPlusPlus && h0_(bindtype_(b)) == t_fnap)
                    (void)merge_default_arguments(bindtype_(b), d->decltype);
            }
            /* flag old one as referenced to avoid spurious warns:  */
            binduses_(b) |= u_referenced;
        }
        else
          if (LanguageIsCPlusPlus && h0_(d->decltype) == t_fnap)
              (void) merge_default_arguments(d->decltype, d->decltype);
/* AM: at some time we may wish to check or export C 'local' extern     */
/* decls for checking purposes.  At that point we must ensure           */
/* that d->decltype is globalize()d.                                    */
        if (b != NULL && !(declflag & DUPL_OK))
            bnew = b;
        else
        {   if (declflag & GLOBALSTG)     /* TOPLEVEL doesn't come here.  */
                bnew = global_mk_binder(NULL, sv, d->declstg,
                           d->decltype = globalize_typeexpr(d->decltype));
            else
                bnew = mk_binder(sv, d->declstg, d->decltype);
            add_local_binder(bnew);
/* stop regalloc moan about typefnaux */
            if (d->declstg & bitofstg_(s_extern) && isfntype(bindtype_(bnew)))
                bindtype_(bnew) = globalize_typeexpr(bindtype_(bnew));
        }
/* If a local extern is already bound, try to find on topbindingchain:  */
        if ((d->declstg & b_undef) &&
            ((d->declstg & (bitofstg_(s_extern))) ||
             ((d->declstg & (bitofstg_(s_static))) &&
               (h0_(d->decltype) == t_fnap))))
        {
/* The following lines are written to cope with curios like:            */
/*    extern int i=0; void f() { auto i; { extern int i; ...            */
/* However, note ANSI ambiguities in:                                   */
/*    typedef int i; void f() { auto int i; { extern int i; ...         */
/* and                                                                  */
/*    void g(double); void f() { extern void g(); g(1); }               */
            Binder *btop = 0, *t;
            for (t = topbindingchain; t != NULL; t = bindcdr_(t))
                if (bindsym_(t) == sv && !(binduses_(t) & u_superceded))
                    btop = t;
            if (btop)
            {   if (!equivtype(bindtype_(btop), d->decltype) ||
                        bindstg_(btop) & bitofstg_(s_typedef))
                    /* warn about above ambiguities?                    */
                    cc_rerr_cppwarn(bind_rerr_local_extern, sv);
/* The following lines specifically please INMOS, but are otherwise OK. */
/* Update the storage class/bindaddr field, but NOT type (ambiguity):   */
/* @@@ what about local externs to register globals (extension)?        */
                else
                {   /* Inherit old storage class:                       */
                    bindstg_(bnew) = bindstg_(bnew) & ~(STGBITS | u_loctype) |
                                     bindstg_(btop) & (STGBITS | u_loctype);
                    if (!(bindstg_(btop) & b_undef))
                    {   /* change undef extern to this-module-defd.     */
                        bindaddr_(bnew) = bindaddr_(btop);
                        bindstg_(bnew) &= ~b_undef;
                    }
                }
            }
        }
        if (h0_(d->decltype) != t_fnap &&
            (d->declstg & bitofstg_(s_static))) {
#ifdef TARGET_HAS_BSS
/* Note that that this BSS_THRESHOLD applies in PCC mode too.           */
            if ( (d->declstg & b_undef) &&
                 sizeoftype(d->decltype) > BSS_THRESHOLD &&
                 !(d->declstg & u_constdata) )
                maybebss = YES;
            else
#endif
                d->declstg &= ~b_undef, bindstg_(bnew) &= ~b_undef;
        }
        b = bnew;
#ifdef TARGET_HAS_BSS
        if (maybebss)
        {   TypeExpr *t = bindtype_(b);
            bindaddr_(b) = addbsssym(sv, sizeoftype(t), alignoftype(t),
                                (bindstg_(b) & bitofstg_(s_static)) != 0, YES);
        }
#endif
        local_scope = saved_local_scope;
    } /* not a top-level declaration */

    /*
     * Make sure information about old definitions and previous references
     * gets carried over from the old binder to the new binder.
     * (ie. '{f();}; f(){}').
     */
#ifdef PASCAL /*ECN*/
    b->bindlevel = level;
    b->synflags = d->synflags;
#endif
    binduses_(b) |= olduses & u_referenced | (d->declstg & u_constdata)
#ifdef TARGET_HAS_BSS
/* @@@ Dec 90: when does the u_bss get removed if later init'ed?        */
                                          | (maybebss ? u_bss : 0)
#endif
                                          ;
#ifdef  FOR_ACORN
#ifndef PASCAL
#ifndef FORTRAN
    if (cplusplus_flag && cfront_special_name(b)) binduses_(b) |= u_referenced;
#endif
#endif
#endif

    return b;
}

ClassMember *instate_member(DeclRhsList *d, int bindflg)
{   return LanguageIsCPlusPlus ? instate_member_cpp(d, bindflg) :
                                 instate_member_1(d, bindflg);
}

Binder *instate_declaration(DeclRhsList *d, int declflag)
{   return LanguageIsCPlusPlus ? instate_declaration_cpp(d, declflag) :
                                 instate_declaration_1(d, declflag);
}

/* label bindings... */

static LabBind *label_create(Symstr *id)
/* Called when a label is referenced - arranges for a check to be made   */
/* at the end of the block to ensure that the label is properly defined. */
{   LabBind *x = symlab_(id);
    if (x == 0) labelchain = symlab_(id) = x = mk_labbind(labelchain, id);
    return x;
}

LabBind *label_define(Symstr *id)
/* Called when a label is defined.  NULL return iff duplicate */
{   LabBind *x = label_create(id);
    if (x->labuses & l_defined)
    {   cc_err(bind_err_duplicate_label, id);
        return 0;
    }
    x->labuses |= l_defined;
    return x;
}

LabBind *label_reference(Symstr *id)
/* Called when a label is referenced - arranges for a check to be made   */
/* at the end of the block to ensure that the label is properly defined. */
{   LabBind *x = label_create(id);
    x->labuses |= l_referenced;
    return x;
}

void label_resolve(void)
{
    LabBind *lc;
    for (lc = labelchain; lc!=NULL; lc = lc->labcdr)
    {   Symstr *id = lc->labsym;
        symlab_(id) = NULL;
        if (!(lc->labuses & l_defined))
            cc_err(bind_err_unset_label, id);
/* NB the CG or SEM should ignore goto's to label 0 (undef'd). */
        if (!(lc->labuses & l_referenced))
            cc_warn(bind_warn_label_not_used, id);
    }
    labelchain = NULL;
}

#ifndef NO_DUMP_STATE
void Bind_LoadState(FILE *f) {
  union { uint16 h[8]; uint32 w[8]; } x;
  uint32 i, j;
  Dump_Init(Dump_Load, f);

  for (i = 1; i < dump_loadstate.ngensym; i++) {
    Symstr *sym;
    fread(x.h, sizeof(uint16), 1, f);
    sym = Dump_LoadSym(x.h[0], f);
    symchain_(sym) = sym;
  }
  for (j = 0; j < BIND_HASHSIZE; j++) {
    Symstr **tailp = &(*hashvec)[j];
    for (;;) {
      Symstr *sym;
      fread(x.h, sizeof(uint16), 1, f);
      if (x.h[0] == 0) break;
      sym = Dump_LoadSym(x.h[0], f);
      *tailp = sym;
      tailp = &symchain_(sym);
    }
    *tailp = NULL;
  }

  for (i = 1; i < dump_loadstate.nglobbind; i++) {
    Binder *b = Dump_LoadedBinder(i);
    fread(x.w, sizeof(uint32), 6, f);
    h0_(b) = x.w[0];
    bindsym_(b) = Dump_LoadedSym(x.w[1]);
    bindcdr_(b) = Dump_LoadedTagOrBinder(x.w[2]);
    attributes_(b) = x.w[3];
    bindstg_(b) = x.w[4];
    bindparent_(b) = Dump_LoadedTag(x.w[5]);
    if (bindstg_(b) & b_bindaddrlist) {
      fread(x.w, sizeof(uint32), 1, f);
      bindbl_(b) = Dump_LoadedSharedBindList(x.w[0]);
    } else if (attributes_(b) & (CB_ANON|CB_HASCOREFN)
               || bindstg_(b) & (b_impl|b_pseudonym)) {
      fread(x.w, sizeof(uint32), 1, f);
      realbinder_(b) = Dump_LoadedBinder(x.w[0]);
    } else
      fread(&bindaddr_(b), sizeof(IPtr), 1, f);

    if (h0_(b) == s_member) {
      fread(&memwoff_(b), sizeof(uint32), 1, f);
      fread(&membits_(b), sizeof(uint8), 1, f);
      fread(&memboff_(b), sizeof(uint8), 1, f);
    } else {
      bindconst_(b) = (bindstg_(b) & bitofstg_(s_inline)) ? NULL
          : Dump_LoadExpr(f);
    }
    fread(x.w, sizeof(int32), 1, f);
    if (bindstg_(b) & bitofstg_(s_auto)) {
      bindmcrep_(b) = x.w[0];
      fread(&bindxx_(b), sizeof(VRegnum), 1, f);
    }
    bindtype_(b) = (x.w[0] != (uint32)NOMCREPCACHE) ?
        (TypeExpr *)DUFF_ADDR : Dump_LoadType(f);
    bindinline_(b) = NULL;
  }
  for (i = 1; i < dump_loadstate.nglobtag; i++) {
    TagBinder *b = Dump_LoadedTag(i);
    fread(x.w, sizeof(uint32), 8, f);
    h0_(b) = x.w[0];
    tagbindsym_(b) = Dump_LoadedSym(x.w[1]);
    tagbindcdr_(b) = (TagBinder *)Dump_LoadedTagOrBinder(x.w[2]);
    attributes_(b) = x.w[3];
    tagbindbits_(b) = x.w[4];
    tagbindparent_(b) = Dump_LoadedTag(x.w[5]);
    b->cachedsize = x.w[6];
    b->typedefname = Dump_LoadedSym(x.w[7]);
    if (tagbindbits_(b) & bitoftype_(s_enum))
      tagbindenums_(b) = Dump_LoadBindList(f);
    else {
      fread(x.w, sizeof(uint32), 1, f);
      tagbindmems_(b) = Dump_LoadedTagOrBinder(x.w[0]);
    }
    b->friends = Dump_LoadFriends(f);
    tagbindtype_(b) = Dump_LoadType(f);
  }
  for (i = 1; i < dump_loadstate.nsym; i++) {
    Symstr *sym = Dump_LoadedSym(i);
    symfold_(sym) = Dump_LoadedSym((IPtr)symfold_(sym));
  }
  Inline_LoadState(f);
  for (i = 1; i < dump_loadstate.nbindlist; i++) {
    BindList *bl = Dump_LoadedSharedBindList(i);
    fread(x.w, sizeof(uint32), 2, f);
    bl->bindlistcdr = Dump_LoadedSharedBindList(x.w[0]);
    bl->bindlistcar = Dump_LoadedBinder(x.w[1]);
  }
  Builtin_LoadState(f);
}

void Bind_DumpState(FILE *f) {
  uint32 i, symno;
  TagBinder **bindersave[GLOBBINDV_MAXSEGS];
  TagBinder **tagbindersave[GLOBTAGV_MAXSEGS];
  long headerpos;
  Dump_Init(Dump_Dump, f);

  for (i = 1; i < ngensym; i++) {
    uint32 segno = i / GENSYMV_SEGSIZE,
           segix = i % GENSYMV_SEGSIZE;
    Symstr *sym = gensymv[segno][segix];
    symlab_(sym) = (LabBind *)(IPtr)i;
  }
  for (symno = ngensym, i = 0; i < BIND_HASHSIZE; i++) {
    Symstr *sym = (*hashvec)[i];
    for (; sym != 0; sym = symchain_(sym))
      symlab_(sym) = (LabBind *)(IPtr)symno++;
  }
  for (i = 0; i < globbindlimit; i += GLOBBINDV_SEGSIZE)
    bindersave[i / GLOBBINDV_SEGSIZE] =
      (TagBinder **)SynAlloc(sizeof(TagBinder *) * GLOBBINDV_SEGSIZE);

  for (i = 0; i < globtaglimit; i += GLOBTAGV_SEGSIZE)
    tagbindersave[i / GLOBTAGV_SEGSIZE] =
      (TagBinder **)SynAlloc(sizeof(TagBinder *) * GLOBTAGV_SEGSIZE);

  for (i = 1; i < nglobbind; i++) {
    uint32 segno = i / GLOBBINDV_SEGSIZE,
           segix = i % GLOBBINDV_SEGSIZE;
    Binder *b = globbindv[segno][segix];
    bindersave[segno][segix] = bindparent_(b);
    bindparent_(b) = (TagBinder *)(IPtr)i;
  }
  for (i = 1; i < nglobtag; i++) {
    uint32 segno = i / GLOBTAGV_SEGSIZE,
           segix = i % GLOBTAGV_SEGSIZE;
    TagBinder *b = globtagv[segno][segix];
    tagbindersave[segno][segix] = tagbindparent_(b);
    tagbindparent_(b) = (TagBinder *)(IPtr)i;
  }
  { union { uint16 h[8]; uint32 w[8]; } x;
    headerpos = ftell(f);
    x.w[0] = ngensym;
    x.w[1] = symno - ngensym;
    x.w[2] = nglobbind;
    x.w[3] = nglobtag;
    x.w[4] = 0;  /* rewritten with dump_loadstate.nbindlist at end */;

    fwrite(x.w, sizeof(uint32), 5, f);
    for (i = 1; i < ngensym; i++) {
      uint32 segno = i / GENSYMV_SEGSIZE,
             segix = i % GENSYMV_SEGSIZE;
      Dump_Sym(gensymv[segno][segix], f);
    }
    for (i = 0; i < BIND_HASHSIZE; i++) {
      Symstr *sym = (*hashvec)[i];
      for (; sym != 0; sym = symchain_(sym))
         Dump_Sym(sym, f);
      x.h[0] = 0;
      fwrite(x.h, sizeof(uint16), 1, f);
    }
    for (i = 1; i < nglobbind; i++) {
      uint32 segno = i / GLOBBINDV_SEGSIZE,
             segix = i % GLOBBINDV_SEGSIZE;
      Binder *b = globbindv[segno][segix];
      x.w[0] = h0_(b);
      x.w[1] = Dump_SymRef(bindsym_(b));
      x.w[2] = Dump_TagOrBinderRef(bindcdr_(b));
      x.w[3] = attributes_(b);
      x.w[4] = bindstg_(b);
      x.w[5] = Dump_TagRef(bindersave[segno][segix]);
      fwrite(x.w, sizeof(uint32), 6, f);
      if (bindstg_(b) & b_bindaddrlist) {
        x.w[0] = Dump_NoteSharedBindList(bindbl_(b));
        fwrite(x.w, sizeof(uint32), 1, f);
      } else if (attributes_(b) & (CB_ANON|CB_HASCOREFN)
               || bindstg_(b) & (b_impl|b_pseudonym)) {
        x.w[0] = Dump_BinderRef(realbinder_(b));
        fwrite(x.w, sizeof(uint32), 1, f);
      } else
        fwrite(&bindaddr_(b), sizeof(IPtr), 1, f);

      if (h0_(b) == s_member) {
        fwrite(&memwoff_(b), sizeof(uint32), 1, f);
        fwrite(&membits_(b), sizeof(uint8), 1, f);
        fwrite(&memboff_(b), sizeof(uint8), 1, f);
      } else if (!(bindstg_(b) & bitofstg_(s_inline))) {
        Dump_Expr(bindconst_(b), f);
      }
      if (bindstg_(b) & bitofstg_(s_auto)) {
        x.w[0] = bindmcrep_(b);
        x.w[1] = bindxx_(b);
        fwrite(x.w, sizeof(uint32), 2, f);
      } else {
        x.w[0] = NOMCREPCACHE;
        fwrite(x.w, sizeof(uint32), 1, f);
      }
      if (x.w[0] == (uint32)NOMCREPCACHE)
        Dump_Type(bindtype_(b), f);
    }
    for (i = 1; i < nglobtag; i++) {
      uint32 segno = i / GLOBTAGV_SEGSIZE,
             segix = i % GLOBTAGV_SEGSIZE;
      TagBinder *b = globtagv[segno][segix];
      x.w[0] = h0_(b);
      x.w[1] = Dump_SymRef(tagbindsym_(b));
      x.w[2] = Dump_TagOrBinderRef((Binder *)tagbindcdr_(b));
      x.w[3] = attributes_(b);
      x.w[4] = tagbindbits_(b);
      x.w[5] = Dump_TagRef(tagbindersave[segno][segix]);
      x.w[6] = b->cachedsize;
      x.w[7] = Dump_SymRef(b->typedefname);
      fwrite(x.w, sizeof(uint32), 8, f);
      if (tagbindbits_(b) & bitoftype_(s_enum))
        Dump_BindList(tagbindenums_(b), f);
      else {
        x.w[0] = Dump_TagOrBinderRef(tagbindmems_(b));
        fwrite(x.w, sizeof(uint32), 1, f);
      }
      Dump_Friends(b->friends, f);
      Dump_Type(tagbindtype_(b), f);
    }
  }
  Inline_DumpState(f);
  Dump_SharedBindLists(f);
  Builtin_DumpState(f);
  fseek(f, headerpos + 4*sizeof(Uint), SEEK_SET);
  fwrite(&dump_loadstate.nbindlist, sizeof(uint32), 1, f);
  for (i = 1; i < nglobbind; i++) {
    uint32 segno = i / GLOBBINDV_SEGSIZE,
           segix = i % GLOBBINDV_SEGSIZE;
    Binder *b = globbindv[segno][segix];
    bindparent_(b) = bindersave[segno][segix];
  }
  for (i = 1; i < nglobtag; i++) {
    uint32 segno = i / GLOBTAGV_SEGSIZE,
           segix = i % GLOBTAGV_SEGSIZE;
    TagBinder *b = globtagv[segno][segix];
    tagbindparent_(b) = tagbindersave[segno][segix];
  }
}
#endif /* NO_DUMP_STATE */

void bind_cleanup(void)
/* see comment on unbindlocals */
{   TagBinder *p;
    Binder *b;

    for (p = toptagbindchain; p != 0; p = tagbindcdr_(p))
    {   Symstr *sv = bindsym_(p);
        if (debugging(DEBUG_BIND))
            cc_msg("top struct unbind $r of %p\n",
                sv, (VoidStar)tag_global_(sv));
        tag_global_(sv) = 0;             /* restore previous binding */
    }
    toptagbindchain = 0;             /* just for tidyness */

    check_for_incomplete_tentative_defs(
        (TentativeDefn *) dreverse((List *)tentative_defs));

    for (b = topbindingchain; b != 0; b = bindcdr_(b))
    {   Symstr *sv = bindsym_(b);
        bind_global_(sv) = 0;            /* restore previous binding */
        if (!(binduses_(b) & u_superceded)
            && (bindstg_(b) & bitofstg_(s_static)))
        {   if (!(qualifiersoftype(bindtype_(b)) & bitoftype_(s_const))
                || (bindstg_(b) & b_generated)) /* ignore un-generated consts */
            {   if (binduses_(b) & u_referenced)
                {   if (bindstg_(b) & b_undef)
                    {   /* surely b_undef static MUST be fnconst after  */
                        /* tentative resolution?  u_bss?                */
                        /* @@@ check_for_imcomplete_tentative_defs()    */
                        /* does not unset b_undef for [] nor bss!       */
                        if (bindstg_(b) & b_fnconst)
                        {   if (SuppressDB_Has(Suppress_Linkage)) /* @@@ this should probably be removed now */
                                cc_warn(bind_err_undefined_static, b);
                            else
                                cc_pccwarn(bind_err_undefined_static, b);
                        }
                    }
                }
                else if (!(bindstg_(b) & bitofstg_(s_inline)))
                    cc_warn(bind_warn_static_not_used, b);
            }
        }
        else if (HasFeature(Feature_NoUse))
        {   if (!(binduses_(b) & u_referenced) &&
                !(bindstg_(b) & bitofstg_(s_typedef))) {
              if (bindstg_(b) & b_fnconst) {
                cc_warn(bind_warn_function_not_used, b);
              } else {
                cc_warn(bind_warn_variable_not_used, b);
              }
            }
        }
    }
    topbindingchain = 0;             /* just for tidyness */
}

void bind_init(void)
{   int i;
    topbindingchain = 0, toptagbindchain = 0, labelchain = 0;
    freeScopes = local_scope = NULL;
    tag_found_in_local_scope = NO;
    scope_level = 0;
    tentative_defs = 0;
    saved_vg_state.size = 0;
    if (dump_state & DS_Dump) {
        ngensym = 1; gensymlimit = 0;
        nglobbind = 1; globbindlimit = 0;
        nglobtag = 1; globtaglimit = 0;
        gensymv = (Symstr ***)GlobAlloc(SU_Other, sizeof(Symstr **) * GENSYMV_MAXSEGS);
        globbindv = (Binder ***)GlobAlloc(SU_Other, sizeof(Binder **) * GLOBBINDV_MAXSEGS);
        globtagv = (TagBinder ***)GlobAlloc(SU_Other, sizeof(TagBinder **) * GLOBTAGV_MAXSEGS);
    }
    gensymline = gensymgen = 0;
    hashvec = (Symstr *((*)[BIND_HASHSIZE]))
        GlobAlloc(SU_Other, sizeof(*hashvec));
    for (i = 0; i < BIND_HASHSIZE; i++) (*hashvec)[i] = NULL;
}

/* end of bind.c */
