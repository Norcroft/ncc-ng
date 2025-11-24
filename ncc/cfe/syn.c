/*
 * cfe/syn.c: syntax analysis phase of C/C++ compiler.
 * Copyright (C) Codemist Ltd., 1988-1993
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Advanced RISC Machines Limited, 1992.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$ Codemist 188
 * Checkin $Date$
 * Revising $Author$
 */

/* ************* NASTY HACK, PLEASE FIX ME *************************** */
#define errname_templateformal errname_formalarg

/* AM memo: Jan 93: need to fix lookahead w.r.t. '#if' (re-entrancy).   */

/* Discussion by AM: function call extension syntax (prefix/postfix).  */
/* Currently there are various C extensions to function call syntax.   */
/* e.g. extern int __pure __swi(3) (*f(int g()))(int h());             */
/* There are also #pragma's which can also specify some of these.      */
/* __pure and __swi above have never affected g() and h(), but the     */
/* #pragma versions do.  Moreover, until 6 Apr 93, there was a bug in  */
/* that __pure and __swi were placed on the result of f(), not on f    */
/* itself.  Such qualifiers are now placed on BOTH (but still not      */
/* on g or h).  mip/cg.c ignores __swi when not on a fn constant.      */
/* Since C++ has syntax (e.g.) "int f() const;" to qualify the fn call */
/* then we can extend this notation to allow:                          */
/*    int (*f(int) __pure)(void) __swi(6);                             */
/* to denote that f is implemented by swi 6 but always returns a pure  */
/* function.  In the meantime, PREFIX (as before) __pure and __swi     */
/* apply to both a function AND any function result(s), but NOT to     */
/* its arguments.                                                      */
/* Note that C++ 'extern "C" int (*f)();' has similar properties and   */
/* treatment of the various features should really all be unified!     */

/* AM Memo: TypeFnAux (e.g. oldstyle) may enable us to kill the        */
/*          dreadful uses of 999 and 1999 in the following.            */
/* AM Memo: reconsider the uses of FileLine fl, in particular the      */
/* possibility of having a FileLine field in DeclRhsList.              */
/* AM Jan 90: rework 'declflag' contexts; fix register syntax,         */
/*            fn-type parsing in formals/casts and 'void' formals.     */
/* AM Sep 89: Rework 'incomplete type' code.  Kill some Parkes hacks.  */
/* AM Sep 89: re-work s_typestartsym so that it may only occur in      */
/*            contexts in which macros may reasonably use it.          */
/* AM, Mar 89: rework rd_declarator now that ANSI have ruled on [] and */
/*             () combinations in declarators.  Fix bugs whereby       */
/*             bad combinations of () and [] via typedef were missed.  */

#ifndef _SYN_H
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

/* It seems better to forbid "int a{2};" etc in C++.                  */
#define archaic_init(s) ((s) == s_lbrace)

/* and for C-only compilers... */
#define rd_cpp_name(x) (void)0
#define rd_handler() 0
#define rd_compound_statement(op) 0
#define rd_template_formals() 0
#define rd_template_postfix(a, b) ((void)0)
#define rd_template_actuals(a) ((ExprList *)0)
#define push_template_args(a,b) 0
#define rd_meminit(a, b, c, d, e) 0
#define rd_qualifying_name(xscope, FB_GLOBAL) 0
#define rd_pseudo(xscope) 0
#define rd_cplusplus_for(fl) 0
#define rd_cppcast() 0
#define rd_classdecl(b) (void)0
#define rd_dtor(sv) (void)0
#define cmd_rescope(s,ss,c) (c)
#define syn_setlab(l, s) (void)0
#define syn_reflab(l, s, c) (c)
#define reverse_SynBindList(x) (SynBindList *)dreverse((List *)x)
#define cpp_mkunaryorop(op, a) 0
#define cpp_mkbinaryorop(op, a, b) 0
#define cpp_mkfnaporop(e, l) 0
#define instate_classname_typedef(b, fl) 0
#define syn_embed_if(x) 0
#define fixup_special_member(declarator, type, convtype, scope, stg) 0
#define use_classname_typedef(basictype) (void)0
#define memfn_typefix(temp, scope) (void)0
#define cpp_special_member(d) 0
#define reinvent_fn_DeclRhsList(a,b,c,d) 0
#define push_multi_scope(b) 0
#define cpp_end_strdecl(b) (void)0
#define syn_pop_linkage() (void)0
#define syn_memdtor(a, b, c, d) (void *)0
#define ispurefnconst(e) 0
#define gen_reftemps() (void)0
#define instate_anonu_members(d, b) (void)0
#define ovld_match_def(b, t, l, p, d) 0
#define rd_cpp_prefixextra(op) 0
#define set_access_context(a, b) 0
#define rd_access_adjuster(a,b) (void)0
#define cg_topdecl(a,b) ((void)0)
#define cg_reinit() ((void)0)
#define syn_dtorinit(b) 0
#define syn_dtorfinal(b) 0
#define generate_core_part(b, c) 0
#define is_declaration(n) 0
#define is_type_id() 0
#define rd_declrhs_exec_cpp(d, initflag) 0
#define conditionalised_delete(t, d, p) 0
#define xsyn_init() ((void)0)
#define add_memfn_template(a,b,c,d,e,f,g,h,i) ((void)0)
#define inst_template_begin(a,b) ((void)0)
#define inst_template_end() ((void)0)
#define syn_implicit_instantiate(a,b) ((void)0)
#define save_pendingfns(a) ((void)0)
#define restore_pendingfns(a) ((void)0)
#define save_curfn_misc(a) ((void)0)
#define restore_curfn_misc(a) ((void)0)
#define rd_exception_spec() ((void)0)
#endif /* _SYN_H */

#ifdef TARGET_HAS_INLINE_ASSEMBLER
#  include "inlnasm.h"
#endif

struct SynScope {
  struct SynScope *cdr;
  SynBindList *car;
  int32 scopeid;
};
#define mkSynScope(a,b,c) (SynScope *)syn_list3(a,b,c)
#define discardSynScope(p) discard3(p)

struct SynGoto {
  struct SynGoto *cdr;
  Cmd *gotocmd;
  SynScope *gotoscope;
};
#define mkSynGoto(a,b,c) (SynGoto *)syn_list3(a,b,c)

enum blk_flavour { blk_BODY,            /* for rd_block(function body)  */
                   blk_INNER,           /* for rd_block(inner block)    */
                   blk_IMPLICIT,        /* for rd_block(C++ decl)       */
                   blk_STMTSEQ,         /* for Cfront compatibilty      */
                   blk_SSTMT };         /* for Cfront compatibility     */

/* The next line is in flux, but flags code which is invented, and     */
/* does not correspond to a user written action.  E.g. narrowing in    */
/* f(x) float x; {...}.  Note that x = 1 in { int x = 1; is not so.    */
static FileLine syn_invented_fl = { 0, 0, 0 };
/* Code may test for invented FileLines by testing (fl.f == 0)!!!      */

static SynBindList *syn_reftemps;       /* syn_reftemps is sort-of an extra item in synscope. */

static bool chk_for_auto = NO;

#define syn_current_linkage() \
    (syn_linkage == 0 ? LINK_CPP : syn_linkage->linkcar)

typedef struct PendingFnList {
    struct PendingFnList *pfcdr;
    Symstr *pfname, *pfrealname;        /* maybe a binder soon, see declarator_name */
    TypeExpr *pftype;
    SET_BITMAP pfstg;           /* MEMFNBITS */
    TagBinder *pfscope;
    ScopeSaver pf_formaltags;
    int pf_toklist_handle;
    ScopeSaver pf_templateformals;
    bool pf_tfn;
} PendingFnList;
static PendingFnList *syn_pendingfns;

typedef struct GenFnList {
    struct GenFnList *cdr;
    TopDecl *d;
    Mark* mark;
} GenFnList;
static GenFnList *syn_generatedfns;

enum LinkSort { LINK_C, LINK_CPP };
typedef struct Linkage {
    struct Linkage *linkcdr;
    enum LinkSort linkcar;
} Linkage;
static Linkage *syn_linkage, *syn_linkage_free;

typedef struct FuncMisc {
    Cmd *switchcmd;
    SynScope *loopscope, *switchscope;
    AEop kaerb;
    TypeExpr *resttype, *switchtype;
    bool is_ctor, is_dtor;
    Binder *structresult;
    CurrentFnDetails curfndetails;
    LabBind *labels;
    LabBind *labsyms[MAX_SAVED_LABELS];
    int recurse;
} FuncMisc;

#ifdef CPLUSPLUS
static enum LinkSort linkage_of_string(String *s);
static void save_pendingfns(PendingFnList **old_pendingfns);
static void restore_pendingfns(PendingFnList *old_pendingfns);
static void save_curfn_misc(FuncMisc *tmp);
static void restore_curfn_misc(FuncMisc *tmp);
#else
static enum LinkSort linkage_of_string(String *s) { IGNORE(s); return LINK_C; }
#endif

/* forward references within this file - reorganise to reduce */
static void ensure_formals_typed(DeclRhsList *d,bool proto);
static TypeExpr *rd_typename(int declflag);
static Expr *rd_prefixexp(int n);
#ifdef EXTENSION_VALOF
static Cmd *rd_block(enum blk_flavour f, bool real_block);
#endif
static Cmd *rd_command(bool declposs);
static DeclRhsList *rd_decllist(int declflag);
static void rd_enumdecl(TagBinder *tb);
static void rd_classdecl_(TagBinder *tb);
static DeclRhsList *rd_decl2(int, SET_BITMAP);

/* newer comments...
 * 2. (7-apr-86 further change):
 *      Extra field (a BindList) of formal params added to s_fndef
 *      (think of as like lambda).  It has s_binder entries.
 * 3. Diads (incl fnap) and monads have a type field type_() at offset 1.
 *    Use arg1_ and arg2_ to get args.
 *  1. declarators are now turned into type expressions a la Algol68.
 *  3. sizeof is turned into an integer constant by the parser.
 *     s_integer has therefore a intorig_() node showing the original
 *     expression for error messages (e.g. "sizeof(int) = 9;")
 */

/* some general comments...
   0.  AE tree nodes have an h0_() field specifying which AEop (small int)
       they contain and then several pointers representing subtrees.
   1.  list types in general (like actual parameters, block declarations
       block commands) are stored without tag fields, in the usual lisp
       form.  Use cdr_() = h0_() for CDR.  0 denotes the end.
       They are read using tail pointers to avoid excess recursion.
   2.  Missing, or empty expressions or commands are stored as 0.
       E.g. "for (;;)" or "if e then c;".
       Note that the empty statement ";" is also stored as 0 and
       hence "if e then c else;" is indistiguishable from the above.
   3.  Note the curious format of string constants - for ANSI
       implicit string constant concatenation - we have
       a string node has a pointer to a LIST of string elements.
   4.  Note that labelled statements require 1 symbol of lookahead
       to distinguish them from expression statements.
       See POSSLABEL uses below.
   5.  The allocators list1, ..., list6 create the parse tree.
       Moreover no permanent structure is allocated in them
       so that the allocator free pointer can be reset after reading
       and code-generating each top-level phrase.
*/

bool implicit_return_ok;
#define tagparent_(p) ((p)->tagparent)

/* The values for 'declflag' below (with the exception of DUPL_OK which */
/* may be or'ed in) are private to parsing.  They represent CONTEXTS    */
/* (e.g. FORMAL) for declarators, abstract declarators, typenames, etc. */
/* The values are 'sparse' to allow quick testing for membership of     */
/* sets like CONC_DECLARATOR.                                           */

/* #define DUPL_OK            0x001 */      /* defined in bind.h */
/* #define TOPLEVEL           0x002 */      /* defined in bind.h */
/* #define GLOBALSTG          0x004 */      /* defined in bind.h */
#define MEMBER             0x008  /* i.e. in struct/union */
#define BLOCKHEAD          0x010
#define ARG_TYPES          0x020  /* declaring formals, after e.g. 'f(x)'  */
#define FORMAL             0x040  /* inside ()'s: both (int a) and (a) OK. */
#define TYPENAME           0x080  /* i.e. typename for case/sizeof.        */
#define SIMPLETYPE         0x100  /* C++ casts like "int(3)" etc.          */
#define CONVERSIONTYPE     0x200  /* C++ "operator int * ();"              */
#define NEW_TYPENAME       0x400  /* C++ new-type-name [ES].               */
#define FLEX_TYPENAME      0x800  /* C++ 'new' TYPENAME, [var] ok [ES].    */
/* #define TEMPLATE          0x1000 */  /* defined in bind.h */

#define CATCHER           0x2000  /* C++ 'catch' context.                  */
#define ANONU             0x4000  /* OR-able with MEMBER/BLOCKHEAD etc.    */
#define TFORMAL           0x8000  /* template formal.                      */
/* contexts in which 'storage classes' are allowed (vestigial):         */
/* [ES] seems to disallow "catch(register int x) { ... }". We don't.    */
#define STGCLASS_OK        (TOPLEVEL|BLOCKHEAD|FORMAL|ARG_TYPES|CATCHER)
/* contexts in which a type is REQUIRED (typename and struct member):   */
#define TYPE_NEEDED (LanguageIsCPlusPlus ?\
                      (TYPENAME|FLEX_TYPENAME|NEW_TYPENAME|CATCHER) :\
                      (TYPENAME|FLEX_TYPENAME|NEW_TYPENAME|MEMBER|CATCHER))
/* contexts in which declarators must be ABSTRACT or CONCRETE.          */
#define CONC_DECLARATOR    (TOPLEVEL|BLOCKHEAD|ARG_TYPES|MEMBER)
#define ABS_DECLARATOR     (TYPENAME|FLEX_TYPENAME|NEW_TYPENAME)

/* parsing table initialisation... */
static int32 illtypecombination[NUM_OF_TYPES];

static int bind_scope;           /* TOPLEVEL, GLOBALSTG, or LOCALSCOPE */
static AEop access;

/* Operator priority for rd_expr(): we use even priorities for           */
/* left-associative operators and odd priorities for right-association.  */
/* This means that we can get right-priority simply by or-ing one into   */
/* the left-priority.                                                    */
/* Other things could added to lpriovec, such as 'needs lvalue' etc.     */
static char lpriovec[s_NUMSYMS];
#define lprio_(op) lpriovec[op]
#define rprio_(op) (lpriovec[op] | 1)

/* Peter Armistead - Make it compile */
#ifdef CALLABLE_COMPILER
Expr *rd_asm_decl(void)
{
    return (Expr*) 0;   /* Temporary - currently asm is implemented as a command rather then a declaration... */
}
#endif

static void initpriovec(void)
{   AEop s,t;
    AEop i;
    for (s = s_bool; istypestarter_(s); s++)
        illtypecombination[shiftoftype_(s)] = ~0;
    illtypecombination[shiftoftype_(s_signed)] =
    illtypecombination[shiftoftype_(s_unsigned)] =
        ~(bitoftype_(s_int) | bitoftype_(s_char) | bitoftype_(s_longlong) |
          bitoftype_(s_long) | bitoftype_(s_short) |
          CVBITS);
    illtypecombination[shiftoftype_(s_long)] =
        ~(bitoftype_(s_int) | bitoftype_(s_signed) | bitoftype_(s_unsigned) |
          bitoftype_(s_double) | bitoftype_(s_float) |
          CVBITS);
    if (!HasFeature(Feature_Fussy)) {
        illtypecombination[shiftoftype_(s_long)] &= ~bitoftype_(s_long);
        illtypecombination[shiftoftype_(s_longlong)] =
            ~(bitoftype_(s_int) | bitoftype_(s_signed) | bitoftype_(s_unsigned) |
              CVBITS);
    }
    illtypecombination[shiftoftype_(s_short)] =
        ~(bitoftype_(s_int) | bitoftype_(s_signed) | bitoftype_(s_unsigned) |
          CVBITS);
    illtypecombination[shiftoftype_(s_const)] = bitoftype_(s_const);
    illtypecombination[shiftoftype_(s_volatile)] = bitoftype_(s_volatile);
    illtypecombination[shiftoftype_(s_unaligned)] =
          bitoftype_(s_unaligned) | bitoftype_(s_double) | bitoftype_(s_float);
    /* now symmetrise: */
    for (s = s_bool; istypestarter_(s); s++)
      for (t = s_bool; istypestarter_(t); t++)
        if (!(illtypecombination[shiftoftype_(s)] & bitoftype_(t)))
          illtypecombination[shiftoftype_(t)] &= ~bitoftype_(s);

    for (i=0; i<s_NUMSYMS; i++)
        lpriovec[i] = (isassignop_(i) ? 13 : 0);
    lpriovec[s_comma] = 10;
    lpriovec[s_assign] = 13;
    lpriovec[s_cond] = 15;
    lpriovec[s_oror] = 16;
    lpriovec[s_andand] = 18;
    lpriovec[s_or] = 20;
    lpriovec[s_xor] = 22;
    lpriovec[s_and] = 24;
    lpriovec[s_equalequal] =
    lpriovec[s_notequal] = 26;
    lpriovec[s_less] =
    lpriovec[s_greater] =
    lpriovec[s_lessequal] =
    lpriovec[s_greaterequal] = 28;
    lpriovec[s_leftshift] =
    lpriovec[s_rightshift] = 30;
    lpriovec[s_plus] =
    lpriovec[s_minus] = 32;
    lpriovec[s_times] =
    lpriovec[s_div] =
    lpriovec[s_rem] = 34;
    lpriovec[s_dotstar] =
    lpriovec[s_arrowstar] = 36;
}

/* check_bitsize and check_bittype get prunetype'd types.               */
static Expr *check_bitsize(Expr *e, TypeExpr *t, Symstr *sv)
{   uint32 n = evaluate(e);
    uint32 size = MAXBITSIZE;
    /*
     * In C++/PCC mode bit fields may be 'char', 'short', 'long' or 'enum'.
     * In ANSI mode bit fields must (else undefined) be 'int'.
     */
    if (h0_(t) == s_typespec)
    {   if (typespecmap_(t) & bitoftype_(s_char)) size = 8;
        else if (int_islonglong_(typespecmap_(t))) size = 8*sizeof_longlong;
        else if (typespecmap_(t) & bitoftype_(s_short)) size = 8*sizeof_short;
        else if (typespecmap_(t) & bitoftype_(s_long)) size = 8*sizeof_long;
        /* else treat enum as 'int'.                                    */
        /* @@@ Sept 91: we should check enum range against bit size,    */
        /* and even add signedness info to ensure happyness!            */
    }
    if (n > size /* unsigned! */) cc_err(syn_err_bitsize, (long)n);
    else if (n==0 && sv!=NULL) n = (uint32)-1, cc_err(syn_err_zerobitsize);
    if (n > size || h0_(e) != s_integer) e = globalize_int(1);
    return e;
}

/* check_bitsize and check_bittype get prunetype'd types.               */
static TypeExpr *check_bittype(TypeExpr *t)
{   /* In ANSI C, only int bitfields are allowed, C++ also allows
     * bool/char/short/long/enum (like PCC mode).
     * In PCC mode, it's important NOT to translate char and short
     * types to int, because they are packed differently.
     * Also C++ typechecking requires 'enum' not to be translated to int.
     * C++: wchar_t is also allowed (when we support it)
     */
#define OKbittypes       (bitoftype_(s_int)|bitoftype_(s_bool)| \
                          bitoftype_(s_char)|bitoftype_(s_short)| \
                          bitoftype_(s_enum)|bitoftype_(s_long)|  \
                          bitoftype_(s_unsigned)|bitoftype_(s_signed)| \
                          bitoftype_(s_const)|bitoftype_(s_volatile))
    if (h0_(t) != s_typespec || typespecmap_(t) & ~OKbittypes)
    {   cc_err(syn_rerr_bitfield, t);
        t = te_int;
    }
    if (!HasFeature(Feature_PCC)
        && (typespecmap_(t) & (bitoftype_(s_char)|bitoftype_(s_short)|
                               bitoftype_(s_enum)|bitoftype_(s_long))))
    {
        if (HasFeature(Feature_Fussy)) {
            cc_rerr(syn_rerr_ANSIbitfield, t);
            t = te_int;
        } else if (!HasFeature(Feature_PCC))
        /* @@@ warn for any non-ANSI C bitfield type, but leave alone!  */
            cc_warn(syn_rerr_ANSIbitfield, t);
    }
/* sem.c is responsible for the interpretation of 'plain' int bitfields     */
/* as signed/unsigned (q.v. under Feature_SignedChar).                      */
/* It is vital that 'BITFIELD' on the next line does not qualify a typedef. */
    return primtype2_(typespecmap_(t) | BITFIELD, typespecbind_(t));
}

static Expr *check_arraysize(Expr *e)
{   unsigned32 n;
    if (is_template_arg_binder(e)) return e;
    n = evaluate(e);
    if (n == 0 && !(suppress & D_ZEROARRAY)) cc_pccwarn(syn_rerr_array_0);
/* The limit imposed here on array sizes is rather ARBITRARY, but char */
/* arrays that consume over 16Mbytes seem silly at least in 1988/89!   */
    if (n > 0xffffff) cc_err(syn_err_arraysize, (long)n);
    if (n > 0xffffff || h0_(e) != s_integer) e = globalize_int(1);
    return e;
}

static const char *ctxtofdeclflag(int f)
{
   if (f & TOPLEVEL)       return msg_lookup(errname_toplevel);
   if (f & MEMBER && !(f & TEMPLATE))
                           return msg_lookup(errname_structelement);
   if (f & TEMPLATE) {
       if (f & MEMBER)     return msg_lookup(errname_membertemplate);
       else                return msg_lookup(errname_classtemplate);
   }
   if (f & FORMAL)         return msg_lookup(errname_formalarg);
   if (f & ARG_TYPES)      return msg_lookup(errname_formaltype);
   if (f & BLOCKHEAD)      return msg_lookup(errname_blockhead);
   if (f & TYPENAME)       return msg_lookup(errname_typename);
   if (f & SIMPLETYPE)     return msg_lookup(errname_simpletype) /* <simple type> */;
   if (f & CONVERSIONTYPE) return msg_lookup(errname_conversiontype) /* <conversion type> */;
   if (f & (FLEX_TYPENAME|NEW_TYPENAME))
                           return msg_lookup(errname_new_type_name) /* <new-type-name> */;
   if (f & CATCHER)        return msg_lookup(errname_catch_name) /* <catch name> */;
   if (f & TFORMAL)        return msg_lookup(errname_templateformal);
                           return msg_lookup(errname_unknown);
}

AEop peepsym(void)
{   AEop s;
    nextsym();
    s = curlex.sym;
    ungetsym();
    return s;
}

void checkfor_ket(AEop s)
{
/* The next lines are a long-stop against loops in error recovery */
    if (errs_on_this_sym >= 4)
    {   cc_err(syn_err_expecteda, s);
        nextsym();
    }
    else if (curlex.sym == s) nextsym();
    else
    {   cc_err(syn_err_expected, s);
        ++errs_on_this_sym;
    }
}

void checkfor_delimiter_ket(AEop s, msg_t expected1, msg_t expected1a)
                            /* as checkfor_ket but less read-ahead */
{
/* The next lines are a long-stop against loops in error recovery */
    if (errs_on_this_sym >= 4)
    {   cc_err(expected1a, s);
        nextsym();
    }
    else if (curlex.sym == s) curlex.sym = s_nothing;
    else
    {   cc_err(expected1, s);
        ++errs_on_this_sym;
    }
}

void checkfor_2ket(AEop s, AEop t)
{
/* The next lines are a long-stop against loops in error recovery */
    if (errs_on_this_sym >= 4)
    {   cc_err(syn_err_expected2a, s, t);
        nextsym();
    }
    else if (curlex.sym == s) nextsym();
    else
    {   cc_rerr(syn_err_expected2, s, t, s);
        ++errs_on_this_sym;
    }
}

void checkfor_delimiter_2ket(AEop s, AEop t)
{
    if (curlex.sym == s) curlex.sym = s_nothing;
    else checkfor_2ket(s, t);
}

/* now to get on with it. */

Expr *rd_ANSIstring(void)
{
    AEop op = curlex.sym;              /* s_string or s_wstring */
    StringSegList *p,*q;
/* Note that the list of string segments must last longer than most     */
/* other parts of the parse tree, hence use binder_list3() here.        */
    q = p = (StringSegList *) binder_list3((StringSegList *)0,
                curlex.a1.s, curlex.a2.len);
    while (nextsym(), isstring_(curlex.sym))
        if (curlex.sym == op)
            q = q->strsegcdr =
                (StringSegList *) binder_list3((StringSegList *)0,
                    curlex.a1.s, curlex.a2.len);
        else
            cc_err(syn_err_mix_strings);
    return (Expr *)syn_list2(op, p);
}

static ExprList *rd_exprlist_opt(void)
{   ExprList *p = 0, *q = 0, *temp;
    if (curlex.sym != s_rpar)
        for (;;)
        {   temp = mkExprList(0, rd_expr(UPTOCOMMA));
            if (p == 0) p = q = temp; else cdr_(q) = temp, q = temp;
            if (curlex.sym != s_comma) break;
            nextsym();
        }
    checkfor_2ket(s_rpar, s_comma);
    return p;
}

/* Notionally, rd_primary and rd_prefixexp should take no argument.
   However, it is most convenient to give it an argument 'labelhack'
   which we set to POSSLABEL to indicate statement contexts.
   In such contexts the possible expressions are 'label:' or <expression>.
   This is necessary to enable lookahead past s_identifier's in statement
   context to see if there is a colon, with represents a label, or an
   operator like '='.  Consider "a:b=c;" or "a:b++;".
   Note that this must be done by rd_primary since labels and variables
   have different environments.
   Doing this re-entrantly is important since "#if..." happens rather
   asynchronously.
*/

#define NOLABEL   PASTCOMMA        /* for clarity */
#define POSSLABEL (PASTCOMMA-2)    /* lower (= same) priority as PASTCOMMA */

/* SynScope duplicates some of the functionality in bind.c, but         */
/* currently it is simpler to use an alternative structure.             */
static SynScope *synscope;
static int32 synscopeid;
static bool elselast;   /* private to rd_command(), cleared by valof.   */
static Cmd *cur_switchcmd;
static SynScope *cur_loopscope, *cur_switchscope;
static AEop cur_break;   /* what 'break' means i.e. s_break or s_endcase */
static TypeExpr *cur_restype, *cur_switchtype;
static bool cur_fn_is_ctor, cur_fn_is_dtor;
static Binder *cur_structresult;       /* non-NULL if struct fn.        */
#ifdef EXTENSION_VALOF
static TypeExpr *valof_block_result_type;
#endif

ClassMember *curlex_member;
    /* The currently found member. @@@ Think: declared in bind.h...     */
static TagBinder *curlex_scope;
    /* Valid if (curlex.sym & s_qualified); curlex_scope is the scope   */
    /* named by the last nested-name-specifier read; 0 means global.    */
static Binder *curlex_binder;
    /* Non-0 if the named entity read is a bound entity. Set in C too.  */
static Binder *curlex_typename;
    /* Non-0 if curlex_binder binds a type name; set in C too.          */
static TypeExpr *curlex_optype;
    /* Valid when the post-condition (curlex.sym == s_pseudoid) holds.  */
    /* Non-0 when the named entity is a conversion-type-name (C++).     */
static Expr *curlex_path;
    /* Non-0 if the name names a class data member (C struct member);   */
    /* it is an expr locating the member relative to the object's base. */
static TagBinder *syn_class_scope;
static BindList *cur_template_formals;
static ExprList **cur_template_actuals;

static void rd_c_name(TagBinder *leftScope, int typenameflag)
{   if (curlex.sym != s_identifier) return;
    curlex_scope = 0;
    curlex_binder = curlex_typename = 0;
    /* NB: leftScope != 0  means "only in leftScope"... */
    curlex_path = findpath(curlex.a1.sv, leftScope,
                           typenameflag|FB_LOCALS|FB_GLOBAL, 0);
    if (leftScope != 0)
    {   if (curlex_path == 0 || h0_(curlex_path) != s_dot)
        {   cc_err(syn_err_not_found_named_member,
                curlex.a1.sv, leftScope);
            curlex_path = errornode;
        }
        return;
    }
    if (curlex_path != 0 && h0_(curlex_path) == s_binder)
    {   curlex_binder = exb_(curlex_path);
        curlex_path = 0;
    }
/* don't recognise typedefs in #if even if extension "keywords in #if"! */
    if (pp_inhashif) return;
    if (curlex_binder != 0 && (bindstg_(curlex_binder) & bitofstg_(s_typedef)))
        curlex_typename = curlex_binder;
}

static void rd_dname(void)
{   if (LanguageIsCPlusPlus)
        rd_cpp_name(&DNAME);       /* NO access checks hack... */
    else
        rd_c_name(0, 0);
}

static void rd_name(TagBinder *leftScope)
{   if (LanguageIsCPlusPlus)
        rd_cpp_name(leftScope);
    else
        rd_c_name(leftScope, 0);
}

static void rd_type_name(void)
{   if (LanguageIsCPlusPlus)
        rd_cpp_name(0);
    else
        rd_c_name(0, FB_TYPENAME);
}

static bool isexprstarter(AEop op)
/* implement as macro using bool array? */
{   switch (op & ~s_qualified)
    {   default: return 0;
        case s_lpar:    /* primary expression starters */
        case_s_any_string
        case s_integer: case s_true: case s_false: case s_floatcon: case s_int64con:
        case s_identifier:
        case s_pseudoid:
        /* rd_cpp_name() swallowed s_coloncolon and s_operator. */
        case s_this:
        case s_new:  case s_delete:
        case s_throw:
        case s_const_cast: case s_reinterpret_cast: case s_static_cast:
        case s_dynamic_cast: case s_typeid:
        case s_and:     /* prefix expression starters */
        case s_times: case s_plus: case s_minus:
        case s_plusplus: case s_minusminus:
        case s_bitnot: case s_boolnot: case s_sizeof:
                 return 1;
    }
}

/* Calling rd_type_name() must always precede isdeclstarter2_(). */
#define isdeclstarter2_(curlex) \
    (isdeclstarter_(curlex.sym) || \
     (curlex.sym & ~s_qualified) == s_identifier && curlex_typename != 0)

/* Ditto for isdeclstarter3_() which is currently rather a placeholder. */
#define isdeclstarter3_(curlex) \
    ((isdeclstarter2_(curlex) && (!LanguageIsCPlusPlus || is_declaration(PASTCOMMA))) || \
     (curlex.sym == s_asm && peepsym() == s_lpar) || curlex.sym == s_template)

static Expr *mkunaryorop(AEop op, Expr *a)
{   if (h0_(a) == s_error) return errornode;    /* @@@ correct placing? */
    return LanguageIsCPlusPlus ? cpp_mkunaryorop(op, a) :
                                 mkunary(op, a);
}

static Expr *mkbinaryorop(AEop op, Expr *a, Expr *b)
{   if (h0_(a) == s_error || h0_(b) == s_error) return errornode;
    return LanguageIsCPlusPlus ? cpp_mkbinaryorop(op, a, b) :
                                 mkbinary(op, a, b);
}

static Expr *mkfnaporop(Expr *e, ExprList *l)
/* Here I have special processing for a pseudo-function-call to
 * ___assert(bool, string) which (at this very early stage) is turned into
 * (void)0, but if the boolean is not a compile time nonzero constant
 * the string is used to generate a diagnostic.
 * Feb 93: for va_arg a ___cond(a,b,c) and ___fail(string) could be more
 * useful separated.
 */
{   if (h0_(e) == s_binder && bindsym_(exb_(e)) == assertsym)
    {   Expr *a1, *a2;
        ExprList *ll = l;
        if (ll != NULL)
        {   a1 = optimise0(exprcar_(ll));
            ll = cdr_(ll);
            if (ll != NULL) a2 = optimise0(exprcar_(ll));
            else a2 = 0;
        }
        else a1 = a2 = 0;
        if (a1 == 0 || h0_(a1) != s_integer || intval_(a1) == 0)
            cc_err(syn_err_assertion, a2);
/* map the assert() into (void)0 */
        return mkcast(s_cast, mkintconst(te_int, 0, e), te_void);
    }
    if (h0_(e) == s_error) return errornode;
    return LanguageIsCPlusPlus ? cpp_mkfnaporop(e, l) :
                                 mkfnap(e,l);
}

#define is_globalbinder_(b) (bind_global_(bindsym_(b)) == b)

static Expr *rd_idexpr(int labelhack)
/* @@@ merge in operator/::operator?                                    */
{   Expr *a;
    Binder *b;
    Symstr *sv;
/* @@@ surely we can do better than the following!  stop S::* here too. */
    if ((curlex.sym & ~s_qualified) != s_identifier) syserr("rd_idexpr");
    sv = curlex.a1.sv;
    if (labelhack == POSSLABEL && curlex.sym == s_identifier
                               && peepsym() == s_colon)
    {   nextsym();
/* Here curlex.sym==s_colon so postfix forms won't be considered.       */
        return (Expr *)syn_list2(s_colon, sv);
    }

    if ((b = curlex_binder) == NULL && curlex_path == NULL)
    {   AEop peek = peepsym();
        if (!has_template_arg_scope())
        {   if (peek == s_lpar)
            {   if (LanguageIsCPlusPlus)
                    cc_rerr(syn_rerr_undeclared_fn, symname_(sv));
                else if (warn_implicit_fns)
                    cc_warn(syn_warn_invent_extern, symname_(sv));
                else xwarncount++;
            }
            else
                cc_rerr(syn_rerr_undeclared, symname_(sv));
        }
        a = (Expr *) (b = curlex_binder = implicit_decl(sv, peek==s_lpar));
    }
    else if ((a = curlex_path) != 0 && curlex_binder != 0)
        /* exprdotmemfn - a is already in usable form */;
    else if (a != 0)
    {   if (a == errornode) {nextsym(); return a;}
        /* Ordinary data member access...                               */
        /* In C++, &A::a may be valid even when x = A::a isn't, hence   */
        /* defer any test for 'this' until we know the context, i.e. in */
        /* coerceunary() etc. For non-qualified names there is no such  */
        /* problem. See [ES, p55]. Note also that in C, curlex.sym      */
        /* cannot have s_qualified set.                                 */
        if (curlex.sym & s_qualified)
        {   /* We ignore the class prefix because of [ES,p55,note1].    */
/* @@@ note the potential user disaster in that &D::i has type          */
/* (int B::*), not (int D::*).  This will cause pain as unchecked       */
/* parameters, else implicit casts will save us.                        */
            if (h0_(a) != s_dot)
                syserr("rd_idexpr(non-dot data member access)");
/* LDS 06-Sep-94: Smash unshared tree in place - sorry...               */
/* NB - arg1_(a) is now guaranteed to exist by path_to_member_1() which */
/* initialises it to nullbinder(class)... rooted_path() also recognises.*/
            type_(a) = (TypeExpr *)syn_list3(t_coloncolon, type_(a),
                typespectagbind_(princtype(typeofexpr(arg1_(a)))));
        }
        else
            /* arguably we should defer this (for sizeof).              */
            a = thisify(a);
    }
    else if (bindstg_(b) & bitofstg_(s_typedef))
    {
        if (LanguageIsCPlusPlus && (a = rd_cppcast()) != 0) return a;
        cc_err(syn_err_typedef, sv);
        a = errornode;
    }
    else if (isenumconst_(b))
        /* Map enum const binders to values. */
        /* @@@ move this code to coerceunary with C++ bindconst?        */
        a = mkintconst(bindtype_(b),bindaddr_(b),(Expr *)b);
    else
    {   /* use current 'variable' binding */
        if (bindstg_(b) & b_pseudonym) b = realbinder_(b);
        a = (Expr *)b;
        binduses_(b) |= u_referenced;
        if (chk_for_auto && !is_local_binder(b) && !is_template_arg_binder((Expr *)b) &&
            !is_globalbinder_(b) && !(bindstg_(b) & bitofstg_(s_static)) &&
            !(bindstg_(b) & bitofstg_(s_extern)) &&
            (h0_(bindtype_(b)) != t_ovld))
        {   cc_err(syn_rerr_local_default, b);
            a = errornode;
        }
    }
    nextsym();
    return a;
}



/* rd_primary is called with rd_name having been called     */
/* on curlex.sym.  (In rd_prefixexp() if not earlier.)                  */
static Expr *rd_primaryexp(int labelhack)
{
    Expr *a;
    switch (curlex.sym & ~s_qualified)
    {
defaultcase:
default:
        /* rd_idexpr() parses C++ casts/constructors fns via typedef.   */
        if (LanguageIsCPlusPlus &&
            isdeclstarter_(curlex.sym) && (a = rd_cppcast()) != 0)
            return a;
        cc_err(syn_err_expected_expr);
        return errornode;
case s_lpar:
        nextsym();
        rd_type_name();
        if (isdeclstarter2_(curlex) && /* rd_declspec(stgclass) moans   */
            (!LanguageIsCPlusPlus || is_type_id()))
        {   TypeExpr *t;
/* The next line supports a keyword "__type" which is treated           */
/* almost as whitespace here, but which is used by a few macros as a    */
/* clue to the parser that certain parenthesised expressions are casts  */
/* and not just arithmetic.  This (only) aids error recovery.           */
            if (curlex.sym == s_typestartsym) nextsym();
/*
            if (LanguageIsCPlusPlus)
            {   if ((a = rd_cppcast()) != 0)
                {   checkfor_ket(s_rpar);
                    return a;
                }
            }
*/
            t = rd_typename(TYPENAME);
            checkfor_ket(s_rpar);
#ifdef EXTENSION_VALOF
            /* invalidate syntactically top level "int a = (int){...};" */
            if (curlex.sym == s_lbrace && cur_restype)
            {   Cmd *c;
                TypeExpr *saver = valof_block_result_type;
                if ((suppress & D_VALOFBLOCKS) == 0)
                   cc_err(syn_err_valof_block);
/* Set a flag so that 'resultis' is recognized as such */
                if (equivtype(t, te_void))
                {   cc_rerr(syn_rerr_void_valof);
                    t = te_int;     /* Fixup to be type int */
                }
                inside_valof_block++;
                valof_block_result_type = t;
                c = rd_block(blk_INNER, YES);
                elselast = 0;
                inside_valof_block--;
                valof_block_result_type = saver;
                nextsym();
                return mk_expr_valof(s_valof, t, c);
            }
            else
#endif
            return mkcast(s_cast, rd_prefixexp(NOLABEL), t);
        }
        a = rd_expr(PASTCOMMA);
        checkfor_ket(s_rpar);
        break;
case_s_any_string   /* cope with ANSI juxtaposed concatenation */
        a = rd_ANSIstring();
        break;
#ifdef CPLUSPLUS
case s_this:
    if (!LanguageIsCPlusPlus) goto defaultcase;
    {   Binder *b = findbinding(thissym, NULL, LOCALSCOPES);
        a = (b && h0_(b) == s_binder) ?
                (binduses_(b) |= u_referenced, (Expr *)b) :
                (cc_err(syn_err_ill_this), errornode);
        nextsym();
        return a;
    }

case s_const_cast:
case s_dynamic_cast:
case s_reinterpret_cast:
case s_static_cast:
    if (!LanguageIsCPlusPlus) goto defaultcase;
    {
      /* Temporary implementation accepting correct syntax but with
       * incorrect behaviour: transmute into vanilla cast. A warning that
       * the behaviour may be incorrect will have already been given.
       * AC 970416.
       */
      TypeExpr *t;
      nextsym();
      checkfor_ket(s_less);
      t = rd_typename(TYPENAME);
      checkfor_ket(s_greater);
      checkfor_ket(s_lpar);
      a = rd_expr(PASTCOMMA);
      checkfor_ket(s_rpar);
      return mkcast(s_cast, a, t);
    }
case s_typeid:
  /* Temporary implementation accepting correct syntax but with
   * incorrect behaviour. A warning that the behaviour may be incorrect will
   * have already been given. AC 970417.
   * Get the type of the argument, check the type_info class has a constructor
   * (if not, probably forgot to include the header file), and call it on the
   * type name. Use of exception_name here to get the type name is gross and
   * should be tidied up when typeid is implemented properly.
   */
  if (!LanguageIsCPlusPlus) goto defaultcase;
  {
    TypeExpr *t;
    Symstr *sv;
    Binder *b;
    nextsym();
    checkfor_ket(s_lpar);
    rd_type_name();
    if (isdeclstarter2_(curlex)) {
      t = rd_typename(TYPENAME);
    } else {
      t = typeofexpr(rd_expr(PASTCOMMA));
    }
    checkfor_ket(s_rpar);

    /* Find constructor */
    sv = sym_lookup("type_info", SYM_GLOBAL);
    b = findbinding(sv, NULL, ALLSCOPES);
    if (b == NULL || h0_(b) != s_binder ||
        (bindstg_(b) & bitofstg_(s_typedef)) == 0 ||
        !isclasstype_(princtype(bindtype_(b)))) {
      cc_err(syn_err_classname_not_found, sv);
      return errornode;
    }
    return mkctor_t(bindtype_(b), mkExprList(0, (Expr *)exception_name(t)));
  }

#endif
case s_pseudoid:
        if (!LanguageIsCPlusPlus) goto defaultcase;
        a = (Expr *)curlex_binder;
        if (a == 0) syserr("binder of name $r == 0", curlex.a1.sv);
        nextsym();
        return a;
case s_identifier:
        if (pp_inhashif)
        {   /* the following warning is a good idea - consider:
               enum foo { a,b }; #if a==b ... */
            cc_warn(syn_warn_hashif_undef, symname_(curlex.a1.sv));
                /* @@@ - LDS 11-Nov-92: why the @@@? */
            nextsym();
            a = lit_zero;
        }
        else
            a = rd_idexpr(labelhack);
        break;
case s_floatcon:
        a = (Expr *)curlex.a1.fc;
        nextsym();
        break;
case s_int64con:
        a = (Expr *)curlex.a1.i64;
        nextsym();
        break;
case s_true:
case s_false:
        a = ((curlex.sym & ~s_qualified) == s_true) ? lit_true : lit_false;
        nextsym();
        break;
case s_integer:            /* invent some more te_xxx for the next line? */
        a = mkintconst((curlex.a2.flag == bitoftype_(s_int) ? te_int :
                                          primtype_(curlex.a2.flag)),
                       curlex.a1.i, 0);
        nextsym();
        break;
    }
    return a;
}

static Expr *rd_postfix(Expr *a)
{   AEop op;
    for (;;) switch (op = curlex.sym)
    {
default:
#ifdef CPLUSPLUS
        rootOfPath = NULL;
#endif
        return a;
case s_plusplus:
case s_minusminus:
        nextsym();
        a = mkunaryorop(postop_(op), a);
        break;
case s_lpar:
        nextsym();
        a = mkfnaporop(a, rd_exprlist_opt());
        break;
case s_lbracket:
        nextsym();
        a = mkbinaryorop(s_subscript, a, rd_expr(PASTCOMMA));
        checkfor_ket(s_rbracket);
        break;
case s_arrow:
        if (LanguageIsCPlusPlus) a = mkunaryorop(s_arrow, a);
        /* drop through */
case s_dot:
        nextsym();
        {
            TypeExpr *t = princtype(typeofexpr(a));
            TypeExpr *tt = h0_(t) == t_ref ? princtype(typearg_(t)) :
                           h0_(t) == t_content ? princtype(typearg_(t)) : t;
            TagBinder *scope = isclasstype_(tt) ? typespectagbind_(tt) : 0;
            bool istemplate = (curlex.sym == s_template);

            if (istemplate) nextsym();
            if (scope && !(tagbindbits_(scope) & TB_DEFD)
                && tagprimary_(scope) != NULL)
                syn_implicit_instantiate(tagprimary_(scope), scope);
            rd_name(scope);
            if ((curlex.sym & ~s_qualified) == s_identifier ||
                     (curlex.sym & ~s_qualified) == s_pseudoid)
            {
                if (curlex_path == errornode)
                    /* C/C++ error already diagnosed... */
                    a = errornode;
                else if (scope == 0)
                    /* diagnose a field selection error */
                    a = mkfieldselector(op, a, (ClassMember *)curlex.a1.sv);
                else if (LanguageIsCPlusPlus && curlex_path == 0)
                {   if (curlex_binder != 0 && curlex_typename == 0)
                        /* static member or enumerator binder */
                    {   Expr *tmp;
                        if (isenumconst_(curlex_binder))
                            tmp = mkintconst(bindtype_(curlex_binder),
                                bindaddr_(curlex_binder),(Expr *)curlex_binder);
                        else
                            tmp  = (Expr *)curlex_binder;
                        /* retain prefix expr for side-effect; relies
                           on dead-code elimination otherwise
                        */
                        a = mkbinary(s_comma, a, tmp);
                    }
                    else
                    {   if (!is_dependent_type(t))
                            cc_err(syn_err_not_member, scope);
                        a = errornode;
                    }
                }
                else
                {   if (istemplate && curlex_binder != NULL &&
                        h0_(bindtype_(curlex_binder)) == t_ovld)
                    {   if (bindftlist_(curlex_binder) == NULL)
                            cc_err(syn_err_template_member);
                        else
                            rd_template_postfix(NULL, YES);
                    }
                    a = mkfieldselector(op, a, (ClassMember *)curlex_path);
                }
                nextsym();
            }
            else
            {   if (curlex_path != errornode)
                    cc_err(syn_err_expected_member);
                /* C/C++ error diagnosed by rd_*_name() or above */
                a = errornode;
            }
        }
        break;
    }
}

static int32 codeoftype(TypeExpr *x)
/*
 * This concocts an integer to return as the value of ___typeof(xx)
 * where ___typeof can be used wherever sizeof can. The objective is to make
 * it possible to (mostly) stdarg.h to make more checks and tests to
 * spot errors and generate code that depends in fine ways on the types
 * of objects.  The coding used here at present is NO GOOD, and needs to be
 * thought out...  I rather suspect that the best fixup here is to hand
 * back a type descriptor as defined for use with coff.
 */
{
    x = prunetype(x);
    switch (h0_(x))
    {
case s_typespec:
        {   SET_BITMAP m = typespecmap_(x);
/* Some code here to preserve the magic numbers in <stdarg.h>            */
/* Must be maintained if more type bits are added to aeops.h             */
            /* Map bool to int */ /*/* char might be better since this is used
               to detect illegal types to va_arg */
            if (m & bitoftype_(s_bool))
                m ^= (bitoftype_(s_int)|bitoftype_(s_bool));
            /* map long long to long */
            if ((m & ts_longlong) == ts_longlong)
                m = (m ^ ts_longlong) | bitoftype_(s_long) | bitoftype_(s_int);
            /* Note the following must be done from highest numbered bit */
            /* down                                                      */
            /* Remove longlong's bit from the bitmap                     */
            m = (m & (bitoftype_(s_longlong)-1)) |
                (m & -bitoftype_(s_longlong+1)) >> 1;
            /* map class to struct, and remove its bit from the bitmap   */
            m = (m & (bitoftype_(s_class)-1)) |
                (m & -bitoftype_(s_class)) >> 1;
            return m >> 1;      /* Preserve pre-bool numbering           */
        }
case t_ref:
case t_content:
case t_subscript:
        return 0x10000000;
case t_fnap:
        return 0x20000000;
default:
        syserr(syserr_codeoftype);
        return 0x40000000;
    }
}

static int32 cpp_sizeoftype(TypeExpr *t)
{
    t = princtype(t);   /* elide typedef's maybe losing qualifiers.     */
    /* There are no refs of refs, but the following code looks neater.. */
    while (h0_(t) == t_ref) t = princtype(typearg_(t));
    return sizeoftype(t);
}

static Expr *expr_dtors;
static Expr *rd_prefixexp(int labelhack)
{   AEop op;
    Expr *a;

/* Jul-94: The following rd_name(0) <is> now needed in C <and> C++.     */
/* Its placement is curious, but it's a no-op for all but a few values  */
/* of curlex.sym (in C, curlex.sym == s_identifier).                    */
    rd_name(0);

/* Note ::new and ::delete are valid, but neither S::* nor S::~.        */
    switch (op = curlex.sym)
    {
case s_plus:    if (HasFeature(Feature_PCC))
                   cc_warn(syn_warn_unary_plus);
case s_and:
case s_times:   /* N.B. not s_qualified+s_times.                        */
case s_minus:   op = unaryop_(op);      /* drop through */
case s_plusplus:
case s_minusminus:
case s_bitnot:
case s_boolnot: nextsym();
                return mkunaryorop(op, rd_prefixexp(NOLABEL));
case s_typeof:  /* ncc extension keyword */
case s_sizeof:
        nextsym();
/* N.B. Ansi require sizeof to return an unsigned integer type */
        if (curlex.sym == s_lpar)
        {   nextsym();
            rd_type_name();
            if (isdeclstarter2_(curlex)) /* rd_declspec(stgclass) moans */
            {   TypeExpr *t;
                if (curlex.sym == s_typestartsym) nextsym();
                t = rd_typename(TYPENAME);
                checkfor_ket(s_rpar);
                return mkintconst(
                    te_size_t,
                    op == s_sizeof ? cpp_sizeoftype(t) : codeoftype(t),
                    (Expr *)syn_list2(op == s_sizeof ? s_sizeoftype :
                                                       s_typeoftype,    t));
            }
            a = rd_expr(PASTCOMMA);
            checkfor_ket(s_rpar);
            a = rd_postfix(a);   /* for sizeof (f)() etc */
        }
        else a = rd_prefixexp(NOLABEL);
        return mkintconst(
            te_size_t,
            op == s_sizeof ? expr_dtors = NULL, cpp_sizeoftype(typeofexpr(a)) :
                             codeoftype(typeofexpr(a)),
            (Expr *)syn_list2(op == s_sizeof ? s_sizeofexpr :
                                               s_typeofexpr,   a));
case s_new:    case s_qualified+s_new:
case s_delete: case s_qualified+s_delete:
case s_throw:
        if (LanguageIsCPlusPlus) return rd_cpp_prefixextra(op);
default:
        return rd_postfix(rd_primaryexp(labelhack));
    }
}

/* AM still needs to be convinced of the worthiness of this (as it      */
/* significantly obscures the code).                                    */
/* After all, perhaps we should ensure that each tree expr node has     */
/* room for an FileLine field?                                          */
/* Sorry: fait accompli by ARM. Revision needs preservation of function.*/
/* We could approve a FileLine field in each node - AM talk to LDS/HCM).*/
#ifndef AM_DISLIKES
static Expr *addfilelinetoexpr_i(Expr *e, FileLine *fl)
{   if (e != NULL && hasfileline_(h0_(e))) {
        FileLine *flp = (FileLine *)SynAlloc(sizeof(FileLine));
        *flp = *fl;
        /* clone the expr if it's one of our shared literals */
        if (h0_(e) == s_integer &&
            ((e == lit_zero || e == lit_one ||
              e == lit_true || e == lit_false)))
            e = mkintconst(type_(e), intval_(e), intorig_(e));
        exprfileline_(e) = flp;
    }
    return e;
}
#else
#  define addfilelinetoexpr_i(e,fl) (e)
#endif

static Expr *addfilelinetoexpr(Expr *e, FileLine *fl)
{
    return e == NULL ? e : addfilelinetoexpr_i(optimise0(e), fl);
}

static Expr *rd_exprwithfileline(int n, FileLine *fl)
{   fl->p = dbg_notefileline(*fl);
    {   Expr *e = rd_expr(n);
        e = addfilelinetoexpr_i(e, fl);
        return e;
    }
}

static void NoteCurrentFileLine(FileLine *fl) {
    *fl = curlex.fl;
    fl->p = dbg_notefileline(*fl);
}

/* note: many calls to rd_expr() are followed by a checkfor_ket(s).     */
/* It would be nice if rd_expr_ket() could check for these.             */
/* (This would give syntactic "inserted s" messages BEFORE knock-on     */
/* semantic errs.  In the past we haven't done this because of          */
/* getting wrong line numbers for semantic errors/read-ahead.           */
/* Re-think this bit of the compiler.                                   */

static SynBindList *extra_flags;
Expr *rd_expr(int n)
{   AEop op;
    Expr *a = rd_prefixexp(n);    /* see POSSLABEL */
    Expr *edtor = NULL;

    /* note that the loop does not go round if op == s_colon after a label */
    while (lprio_(op = curlex.sym) >= n)
    {   FileLine fl;
        nextsym();
        if (op == s_cond)
        {   Expr *b, *c, *bdtor, *cdtor;
            NoteCurrentFileLine(&fl);
            push_exprtemp_scope();
            b = rd_exprwithfileline(PASTCOMMA, &fl);
            bdtor = killexprtemp();
            checkfor_ket(s_colon);
            NoteCurrentFileLine(&fl);
            push_exprtemp_scope();
            c = rd_exprwithfileline(
                (LanguageIsCPlusPlus) ? rprio_(s_assign) : rprio_(s_cond), &fl);
            cdtor = killexprtemp();
            if (bdtor || cdtor)
            {   TypeExpr *t = typeofexpr(a);
                Binder *cond = gentempbinder(t);
                a = mk_exprlet(s_let, t, mkSynBindList(0, cond),
                               mkbinary(s_comma, mkbinary(s_init, (Expr *)cond, a),
                                        (Expr *)cond));
                if (!bdtor) bdtor = mkintconst(te_void, 0, 0);
                if (!cdtor) cdtor = mkintconst(te_void, 0, 0);
                add_expr_dtors(mkcond((Expr *)cond, bdtor, cdtor));
            }
            a = mkcond(a, b, c);
        } else if (op == s_comma || op == s_andand || op == s_oror) {
            Expr *sub_edtor = NULL;
            NoteCurrentFileLine(&fl);
            if (LanguageIsCPlusPlus && op != s_comma)
            {   Expr *b;
                push_exprtemp_scope();
                b = rd_exprwithfileline(rprio_(op), &fl);
                if ((sub_edtor = killexprtemp()) != NULL)
                {   Binder *flag = gentempbinder(te_int);
                    sub_edtor = mkcond((Expr *)flag, sub_edtor, mkintconst(te_void, 0, 0));
                    extra_flags = mkSynBindList(extra_flags, flag);
                    edtor = commacons(sub_edtor, edtor);
                    a = mkbinaryorop(op, a, commacons(
                            mkbinary(s_assign, (Expr *)flag, lit_one), b));
                } else
                    a = mkbinaryorop(op, a, b);
            } else
                a = mkbinaryorop(op, a, rd_exprwithfileline(rprio_(op), &fl));
        }
        else /* ANSI C */
            a = mkbinaryorop(op, a, rd_expr(rprio_(op)));
    }
    add_expr_dtors(edtor);
    return a;
}

/* The next routine is used by the preprocessor to parse #if and #elif. */
/* It relies on the caller (pp) to set pp_inhashif (see cfe/pp.h).      */
bool syn_hashif()
{    /* note that we read the largest possible expression (rather
        that the ANSI "constant expression" syntax which excludes
        (top level only!!!) '+=', ',' etc.  Then we can moan better
        at the semantic level.
     */
     Expr *e;
/* the next few lines are somewhat yukky.  Think about how to improve    */
     nextsym_for_hashif();  /* precondition for rd_expr() is that curlex.sym is valid */
     e = optimise0(rd_expr(PASTCOMMA));
     if (curlex.sym != s_eol)
     {   cc_err(curlex.sym == s_eof ? syn_err_hashif_eof : syn_err_hashif_junk);
         while (curlex.sym != s_eof && curlex.sym != s_eol) nextsym();
     }
     if (e == 0 || h0_(e) != s_integer)
     {   if (e != 0) moan_nonconst(e, syn_moan_hashif_nonconst,
                                   syn_moan_hashif_nonconst1,
                                   syn_moan_hashif_nonconst2);
         return 0;
     }
     return intval_(e) != 0;   /* != 0 essential if int != long */
}

static Expr *exprtemp_killer(Expr *orig)
{   Expr *killer;
    TypeExpr *t;
    Binder *tmp;
    if (!expr_dtors) return orig;
    if (extra_flags)
    {   SynBindList *pbl = extra_flags;
        for (; pbl != NULL; pbl = pbl->bindlistcdr)
            orig = mkbinary(s_comma, mkbinary(s_init, (Expr *)pbl->bindlistcar,
                                              lit_zero), orig);
    }
    t = typeofexpr(orig);
    tmp = gentempbinder(t);
    killer = mkbinary(s_init, (Expr *)tmp, orig);
    killer = mkbinary(s_comma, killer, expr_dtors);
    killer = mkbinary(s_comma, killer, (Expr *)tmp);
    killer = mk_exprlet(s_let, t, mkSynBindList(extra_flags, tmp), killer);
    expr_dtors = NULL;
    extra_flags = NULL;
    return optimise0(killer);
}

static Expr *rd_condition(AEop op)
{
    Expr *e;
    push_exprtemp_scope();
    if (op == s_for)
        e = rd_expr(PASTCOMMA);
    else if (curlex.sym == s_lpar)
    {   nextsym();
        e = rd_expr(PASTCOMMA);
        checkfor_ket(s_rpar);
    }
    else
    {   cc_rerr(syn_rerr_insert_parens, op);
        e = rd_expr(PASTCOMMA);
    }
    /* It is vital for s_switch that optimise0() is not called here.    */
    return op == s_switch ? mkintegral(op,e) : mktest(op,e);
}

static Expr *syn_allocexprtemps(Expr *e)
{   e = optimise0(e);
    if (e == 0) e = lit_zero;
    add_expr_dtors(killexprtemp());
    return exprtemp_killer(e);
}

/* the next routine rd_init() has a coroutine-like linkage with vargen.c */
/* it would otherwise be a nice simple recursive routine! */

static int32 syn_initdepth;  /* only used by these fns and rd_declrhslist */
static Expr *syn_initpeek;

/* these are clearly stubs of nice recursive calls! */

int32 syn_begin_agg(void)
{   if (syn_initdepth < 0) return 0;
    if (curlex.sym == s_lbrace)
    {   nextsym();
        if (!LanguageIsCPlusPlus && HasFeature(Feature_Fussy) &&
            curlex.sym == s_rbrace)
            cc_rerr(syn_rerr_empty_init);
        syn_initdepth++;
        return 1;
    }
    return 0;
}

void syn_end_agg(int32 beganbrace)
{   if (beganbrace)
    {   if (curlex.sym != s_rbrace)
        {   Expr *result;
            switch (beganbrace)
            {   case 1: cc_err(syn_err_initialisers);
                        break;
                case 2: cc_err(syn_err_initialisers1);
                        break;
            }
            /*
             * Skip the rest quitely !
             * However, beware because if a symbol like ';' if found
             * we end up in a never ending loop.
             * Thus, if an error is found bail out !!!
             */
            for
            (
                result=syn_rdinit(0,0,4);
                result && result != errornode;
                result=syn_rdinit(0,0,4)
            );
        }
        else if (beganbrace == 2)
            cc_warn(syn_warn_spurious_braces);
        nextsym();
        if (--syn_initdepth > 0 && curlex.sym != s_rbrace)
        {   checkfor_2ket(s_comma, s_rbrace);  /* @@@ improve w.r.t e.g int */
            if (curlex.sym == s_semicolon)     /* probably badly lost... */
                syn_initdepth = -1;
        }
        if (syn_initdepth == 0) syn_initdepth = -1;
    }
}

#define syn_initcast(e, whole, t) \
    (whole ? mkbinary(s_init, (Expr *)whole, e) : \
     t ? mkcast(s_assign, e, t) : \
     e)

Expr *syn_rdinit(TypeExpr *t, Binder *whole, int32 flag)
/* t is a non-aggregate type - read its initialiser.                    */
/* flag values: 0 normal, 1 peek only (for string), 4 skip silently.    */
/* if 'whole' is non-NULL then generate an assignment to it,            */
/* else if 't' is non-NULL then just generate a cast to 't'.            */
/* The case whole=0 & t=0 is used with flag=1 to test-read a RHS        */
/* for  char x[] = "abc";  and widestring variant only.                 */
/* See vargen.c for call rdinit(0,0,1) (=peek) then rdinit(0,0,0) for   */
/*  cases like   struct { char a[4]; } = { 1 }; vs. = { "abc" };        */
{   Expr *e;
    int needs_end_agg = NO;
    int static_init = flag & 8;
    flag &= ~8;
    if (syn_initpeek)
    {   e = syn_initpeek;
        if (flag != 1) syn_initpeek = 0;
    }
    else if (syn_initdepth < 0 || curlex.sym == s_rbrace)
        return 0;
    else if (curlex.sym == s_lbrace)  /* nasty ANSI optional "int x = {1}" */
    {   if (flag == 1) return 0;      /* treat x[] = {"abc"} as illegal    */
        (void) syn_begin_agg();       /* always succeeds */
        e = rd_expr(UPTOCOMMA);
        if (curlex.sym != s_rbrace)
            checkfor_2ket(s_comma, s_rbrace);  /* @@@ improve w.r.t e.g int */
        needs_end_agg = YES;
    }
    else
    {   e = rd_expr(UPTOCOMMA);
        if (flag == 1) syn_initpeek = e;
        if (syn_initdepth > 0 && curlex.sym != s_rbrace)
            checkfor_2ket(s_comma, s_rbrace);  /* @@@ improve w.r.t e.g int */
        if (syn_initdepth == 0) syn_initdepth = -1;  /* one only */
    }
#ifdef CPLUSPLUS
    if (h0_(e) == s_addrof && h0_(arg1_(e)) == s_binder &&
        (bindsym_(curlex_binder) == ctorsym ||
        bindsym_(curlex_binder) == dtorsym))
    {   cc_rerr(syn_rerr_addrof_cdtor_taken);
        e = errornode;
    }
    else
#endif
    {   e = syn_initcast(e, whole, t);
        if (!LanguageIsCPlusPlus && whole != NULL && static_init) {
            e = arg2_(skip_invisible(e));
        }
    }
    if (needs_end_agg)
        syn_end_agg(flag == 4 ? 3 : 2);         /* special flags */
    return e;
}

bool syn_canrdinit(void)
{  if (syn_initpeek) return 1;
   if (syn_initdepth < 0 ||
       curlex.sym == s_rbrace || curlex.sym == s_semicolon) return 0;
/*
 * The next test is intended to make recovery from
 *    int x[] = { int y;
 * and similar cases at least a little better.
 * This is OK in C but not C++:  int a[] = { int(1),int(2)};
 * Putting this in stops some infinite loops in error recovery, but
 * the parser still gets pretty well messed up by the example shown above.
 * AM, Sept 91: lets have another go at initialiser error recovery.
 */
    if (!LanguageIsCPlusPlus)
    {   rd_type_name();
        if (isdeclstarter2_(curlex)) return 0;
    }
    return 1;
}

/* command reading routines... */
#if 0
static SynBindList *mkSynBindList_from_Decl(DeclRhsList *d, SynBindList *r)
{   /* re-use DeclRhsList store to make a (reversed) SynBindList...     */
    while (d != 0)
    {   SynBindList *t = (SynBindList *)d;
        Binder *b = d->declbind;
        d = d->declcdr;
        t->bindlistcar = b;
        t->bindlistcdr = r;
        t->bindlistdtor = 0;
        r = t;
    }
    return r;
}
#endif
static Cmd *rd_block(enum blk_flavour f, bool real_block)
{   DeclRhsList *d,*dp;
    CmdList *c = NULL;
    SynBindList *dd;
    int scope_level = 0;
    FileLine fl;

    NoteCurrentFileLine(&fl);
    push_saved_temps(synscopeid);
    if (real_block) nextsym();        /* skip '{' if nec.     */
    if (f == blk_INNER || f == blk_SSTMT)
        scope_level = push_scope(0, Scope_Ord);
    synscope = mkSynScope(synscope, 0, ++synscopeid);
    d = rd_decllist(BLOCKHEAD);
    if (LanguageIsCPlusPlus)
    {   CmdList *cstat = 0;
        for (dp = d; dp != 0; dp = dp->declcdr)  /* add dynamic inits    */
        {   Expr *e = declinit_(dp);             /* see genstaticparts() */
            if (e != 0)
            {
                if (dp->declstg & bitofstg_(s_auto))
                {   if (cstat)
                    {   c = mkCmdList(c,
                              syn_embed_if((CmdList *)dreverse((List *)cstat)));
                        cstat = 0;
                    }
                    if (h0_(e) == s_asm)
                        c = mkCmdList (c, e);
                    else
                        c = mkCmdList(c, mk_cmd_e(s_semicolon, dp->fileline,
                                                  mkcast(s_init, e, te_void)));
                }
                else cstat = mkCmdList(cstat,
                                       mk_cmd_e(s_semicolon, dp->fileline,
                                                mkcast(s_init, e, te_void)));
            }
        }
        if (cstat)
        {   c = mkCmdList(c, syn_embed_if((CmdList *)dreverse((List *)cstat)));
            cstat = 0;
        }
    } else
        for (dp = d; dp != 0; dp = dp->declcdr)  /* add dynamic inits    */
        {   Expr *e = declinit_(dp);             /* see genstaticparts() */
            if (e != 0) {
                if (h0_(e) == s_asm)
                    c = mkCmdList (c, e);
                else
                    c = mkCmdList(c, mk_cmd_e(s_semicolon, dp->fileline,
                                              mkcast(s_init, e, te_void)));
            }
        }
/* Hmm, we would prefer genreftemp()s and DeclRhsList vars interleaved. */
/* FW: Done (in rd_decl2). Pity that no more reuse of declrhslist store. */
#if NEVER
    synscope->car = mkSynBindList_from_Decl(d, synscope->car);
#endif
    while (curlex.sym != s_rbrace && curlex.sym != s_eof)
    {   c = mkCmdList(c, rd_command(LanguageIsCPlusPlus != 0 && f != blk_SSTMT));
        if (curlex.sym == s_nothing) nextsym();
    }

    if (usrdbg(DBG_ANY) && real_block)
    {   /* If generating debug tables, terminate the block with a null   */
        /* statement to provide a place for the FileLine for the         */
        /* terminating brace to be held                                  */
        FileLine fle;
        NoteCurrentFileLine(&fle);
        c = mkCmdList(c, mk_cmd_e(s_semicolon, fle, NULL));
    }
    if (f != blk_IMPLICIT && f != blk_STMTSEQ)
      checkfor_delimiter_ket(s_rbrace, syn_err_expected1, syn_err_expected1a);
    if (f == blk_INNER || f == blk_SSTMT) pop_scope(scope_level);
    dd = synscope->car; synscope = synscope->cdr;
    if (LanguageIsCPlusPlus)
    {   Expr *edtor = mkdtor_v_list(dd);
        if (edtor)
        {   /* just what is the right FileLine for a dtor?                  */
            c = mkCmdList(c, mk_cmd_e(s_semicolon, fl, optimise0(edtor)));
        }
    }
    dd = pop_saved_temps(dd);
    return mk_cmd_block(fl, reverse_SynBindList(dd),
                            (CmdList *)dreverse((List *)c));
}

/*
   NB - many commands are terminated by a semicolon - here (rd_command())
   when I find the semicolon I set curlex.sym to s_nothing rather than reading
   ahead further. This reduces spurious read-ahead.
*/

/* Beware: the code for associating case labels with their enclosing    */
/* 'switch' which follows assumes that no such labelled command is      */
/* later thrown away by error recovery (else cg etc. will be unhappy).  */
static Cmd *adddefault(FileLine fl)
{    if (cur_switchcmd == 0)
     {   cc_err(syn_err_default); return 0; }
     if (switch_default_(cur_switchcmd))
     {   cc_err(syn_err_default1); return 0; }
     return (switch_default_(cur_switchcmd) = mk_cmd_default(fl, 0));
}

static Cmd *addcase(Expr *e, FileLine fl)
{    Cmd *p,*q; int32 n;
     if (cur_switchcmd == 0)
     {   cc_err(syn_err_case);
         return 0;
     }
     if (h0_(e) != s_integer)
     {   moan_nonconst(e, syn_moan_case_nonconst, syn_moan_case_nonconst1,
                       syn_moan_case_nonconst2);
         return 0;
     }
     n = intval_(e);
     /* the insertion sort code which follows is linear for increasing
        case expressions - it sorts into reverse (int) order (reverse later)?
        Anyway, ACN's CG code like them this way.
     */
     for (p = switch_caselist_(cur_switchcmd), q=0; p!=0; q=p, p=case_next_(p))
     {   Expr *t = cmd1e_(p);
         if (debugging(DEBUG_SYN))
             cc_msg("Comparing cases %ld %ld\n", (long)n, (long)intval_(t));
         if (n >= intval_(t))
         {   if (n > intval_(t)) break;
             cc_err(syn_err_case1, (long)n);
             return 0;
         }
     }
     {   Cmd *r = mk_cmd_case(fl, e, 0, p);
         if (q == 0)
             return switch_caselist_(cur_switchcmd) = r;
         else
             return case_next_(q) = r;
     }
}

/* rd_for_2() reads the last 2 parameters and the body of a for loop.   */
/* It is so factored for C++'s for(d;e;e)c and for(e;e;e)c styles.      */
static Cmd *rd_for_2(Expr *e1, FileLine fl)
{   Expr *e2, *e3; Cmd *c;
    if (curlex.sym == s_semicolon)
        e2 = 0;
    else {
         FileLine fl;
         NoteCurrentFileLine(&fl);
         e2 = addfilelinetoexpr(syn_allocexprtemps(rd_condition(s_for)), &fl);
    }
    checkfor_ket(s_semicolon);
    if (curlex.sym == s_rpar)
        e3 = 0;
    else {
         FileLine fl;
         NoteCurrentFileLine(&fl);
         push_exprtemp_scope();
         e3 = mkcast(s_for,rd_expr(PASTCOMMA),te_void);
         add_expr_dtors(killexprtemp());
         if (expr_dtors != 0)
         { e3 = mkbinary(s_comma, e3, expr_dtors);
           expr_dtors = NULL;
         }
         e3 = addfilelinetoexpr(e3, &fl);
    }
    checkfor_ket(s_rpar);
    {   SynScope *oldloop = cur_loopscope; AEop oldbreak = cur_break;
        c = mk_cmd_for(fl, e1,e2,e3,0);
        cur_break = s_break; cur_loopscope = synscope;
        cmd4c_(c) = rd_command(0);
        cur_loopscope = oldloop; cur_break = oldbreak;
        return c;
    }
}

#define cfront_semantics (HasFeature(Feature_CFront) && \
                !(var_cc_private_flags & 16777216L))
static Cmd *rd_command(bool declposs)
{
  rd_type_name();
  if (declposs && isdeclstarter3_(curlex))
      return rd_block(blk_IMPLICIT, NO);
  {
    AEop op;
    Cmd *c;
    Expr *e;
    bool have_exprtemp_scope = false;
    FileLine fl;
    NoteCurrentFileLine(&fl);
    expr_dtors = NULL;
    extra_flags = NULL;
    switch (op = curlex.sym)
    {
case s_default:
        nextsym();
        checkfor_ket(s_colon);
        if ((c = adddefault(fl)) == 0)
            return rd_command(declposs); /* error */
/* The next line is currently just for errors as case/default branch    */
/* can never cause destructors to happen.                               */
        if (cmd_rescope(synscope, cur_switchscope, 0) != 0)
            syserr("rescope(case)");
        cmd1c_(c) = rd_command(declposs);
        return c;
case s_case:
        nextsym();
        e = mkcast(s_case, rd_expr(PASTCOMMA), cur_switchtype);
        if (h0_(e) == s_evalerror)
        {   cc_rerr((msg_t)arg3_(e), h0_(arg2_(e)));
            e = arg1_(e);
        }
        e = optimise0(e);
        checkfor_ket(s_colon);
        if (e==0 || (c = addcase(e,fl)) == 0)
            return rd_command(declposs); /* error */
/* The next line is currently just for errors as case/default branch    */
/* can never cause destructors to happen.                               */
        if (cmd_rescope(synscope, cur_switchscope, 0) != 0)
            syserr("rescope(case)");
        cmd2c_(c) = rd_command(declposs);
        return c;
defaultcase:
default:
        if (!isexprstarter(op))
        {   cc_err(LanguageIsCPlusPlus ? syn_err_expected_stmt : syn_err_expected_cmd);
            while (curlex.sym!=s_lbrace && curlex.sym!=s_rbrace &&
                   curlex.sym!=s_semicolon && curlex.sym!=s_eof) nextsym();
            return 0;
        }
        have_exprtemp_scope = true; push_exprtemp_scope();
        e = rd_expr(POSSLABEL);
        if (h0_(e) == s_colon)
        {   Symstr *a = (Symstr *)type_(e);
            LabBind *lab = label_define(a);
            nextsym();                      /* not previously done */
            pop_exprtemp_scope();
            if (lab == 0)
                return rd_command(declposs);  /* duplicate    */
            syn_setlab(lab, synscope);
            return mk_cmd_lab(s_colon, fl, lab, rd_command(declposs));
        }
        /* @@@ perhaps we should check the ';' first */
        e = optimise0(mkcast(s_semicolon, e, te_void));
        c = (e==0) ? 0 : mk_cmd_e(s_semicolon, fl, e);
        break;
case s_semicolon:
        c = 0;
        break;
case s_lbrace:
        c = rd_block(blk_INNER, YES);
        elselast = 0;
        return c;
case s_do:
case s_while:
case s_for:
case s_if:
case s_switch:
        curlex.sym |= s_qualified;    /* FRIGORMA */
        return rd_block((!declposs) ? blk_SSTMT :
                        (cfront_semantics) ? blk_STMTSEQ : blk_INNER,
                        NO);
case s_do|s_qualified:
        nextsym();
        {   SynScope *oldloop = cur_loopscope; AEop oldbreak = cur_break;
            c = mk_cmd_do(fl, 0, 0);   /* amalgamate with for */
            cur_break = s_break; cur_loopscope = synscope;
            cmd1c_(c) = rd_command(0);
            cur_loopscope = oldloop; cur_break = oldbreak;
        }
        if (curlex.sym == s_nothing) nextsym();
        if (curlex.sym == s_while)
        {   FileLine fl;
            nextsym();
            NoteCurrentFileLine(&fl);
            e = addfilelinetoexpr(
                    syn_allocexprtemps(rd_condition(s_while)), &fl);
        }
        else
        {   cc_err(syn_err_expected_while);
            e = 0;      /* treat like "do c while;" (missing e).      */
        }
        if (e == 0) e = lit_zero; /* error => while(0). */
        cmd2e_(c) = e;
        checkfor_ket(s_semicolon);
        if (!(declposs && cfront_semantics))
        {   if (curlex.sym != s_nothing) ungetsym();
            curlex.sym = s_rbrace;
        }
        elselast = 0;
        return c;
case s_while|s_qualified:
        nextsym();
        {   FileLine fl;
            NoteCurrentFileLine(&fl);
/* Why does 'case s_while:' have a fileline but not case s_if:'?        */
            e = addfilelinetoexpr(
                    syn_allocexprtemps(rd_condition(op & ~s_qualified)), &fl);
        }
        {   SynScope *oldloop = cur_loopscope; AEop oldbreak = cur_break;
            c = mk_cmd_for(fl, 0, e, 0, 0);
            cur_break = s_break; cur_loopscope = synscope;
            cmd4c_(c) = rd_command(0);
            cur_loopscope = oldloop; cur_break = oldbreak;
            if (!(declposs && cfront_semantics))
            {   if (curlex.sym != s_nothing) ungetsym();
                curlex.sym = s_rbrace;
            }
            return c;
        }
case s_for|s_qualified:
{       Expr *edtor;
        nextsym();
        checkfor_ket(s_lpar);
        push_exprtemp_scope();
        if (LanguageIsCPlusPlus)
        {  rd_type_name();
            if (isdeclstarter2_(curlex))
            {   DeclRhsList *d = rd_decl2(BLOCKHEAD, 0), *dp;
                                        /* is BLOCKHEAD right? */
                e = 0;
                for (dp = d; dp != 0; dp = dp->declcdr)     /* add dynamic inits    */
                {   Expr *einit = declinit_(dp);            /* see genstaticparts() */
                    if (einit)
                    {   if (debugging(DEBUG_SYN)) cc_msg("[Init]");
                        e = e ? mkbinary(s_comma, e, einit) : einit;
                    }
                }
                e = e ? optimise0(mkcast(s_for, e, te_void)) : 0;
#if NEVER
                synscope->car = mkSynBindList_from_Decl(d, synscope->car);
#endif
                if (curlex.sym == s_nothing) nextsym();
                goto afterInit;
            }
        }
        e = ((curlex.sym == s_semicolon) ? 0 :
                optimise0(mkcast(s_for,rd_expr(PASTCOMMA),te_void)));
        checkfor_ket(s_semicolon);
afterInit:
        if ((edtor = killexprtemp()) != 0)
            e = mkbinary(s_comma, e, edtor);
        c = rd_for_2(e, fl);
        if (!(declposs && cfront_semantics))
        {   if (curlex.sym != s_nothing) ungetsym();
            curlex.sym = s_rbrace;
        }
        return c;
}
case s_if|s_qualified:
{       nextsym();
/* Why does 'case s_while:' have a fileline but not case s_if:'?        */
        e = syn_allocexprtemps(rd_condition(op & ~s_qualified));
        if (e == 0) e = lit_zero; /* error => if(0).    */
        c = rd_command(0);
        if (curlex.sym == s_nothing) nextsym();
        {   Cmd *c2;
            static int elseline = 0;
            if (curlex.sym == s_else)
            {   elseline = curlex.fl.l;
                nextsym();
                c2 = rd_command(0);
                elselast = 1;
            }
            else
            {   c2 = 0;
                if (elselast) /* in 'c' above */
                {   int temp = curlex.fl.l;
                    curlex.fl.l = elseline;
/* The construction applied here seems a little bit nasty - it would    */
/* certainly give trouble if diagnostics were displayed with an echo of */
/* part of the surrounding source. Still, it seems a good idea!         */
                    cc_warn(syn_warn_dangling_else);
                    curlex.fl.l = temp;
                }
            }
            if (!(declposs && cfront_semantics))
            {   if (curlex.sym != s_nothing) ungetsym();
                curlex.sym = s_rbrace;    /* FRIGORMA */
            }
            return mk_cmd_if(fl, e, c, c2);
        }
}
case s_else:
        cc_err(syn_err_else);
        nextsym();
        return rd_command(0);
case s_switch|s_qualified:
        nextsym();
/* Why does 'case s_while:' have a fileline but not case s_if:'?        */
        e = rd_condition(op & ~s_qualified);
        {   Cmd *oldswitchcmd = cur_switchcmd; AEop oldbreak = cur_break;
            SynScope *oldswitchscope = cur_switchscope;
            TypeExpr *oldswitchtype = cur_switchtype;
            Expr *ee = syn_allocexprtemps(e);
            if (ee==0) e = ee = lit_zero; /* error=>switch(0). */
            cur_switchcmd = c = mk_cmd_switch(fl, ee,0,0,0);
            cur_break = s_endcase;
            cur_switchscope = synscope;
            cur_switchtype = typeofexpr(e);     /* not optimise0(e)!    */
#ifdef TARGET_IS_ALPHA
/*
 * I make this test conditional on building code for an Alpha since it was
 * use of a host C compiler on that that bit me.  And the fact that this
 * is not unconditionally included is because introducing (yet) more
 * warnings into the compiler without full discussion is possibly
 * inconsiderate.  But I sort-of hope that this might be put into
 * general service to encourage conservative and simple-minded use of the
 * C language.
 */
#ifndef DO_NOT_WARN_ABOUT_FUNNY_SWITCHES
/*
 * This is here because one C compiler we tried hosting on (not ncc!) seemed
 * to mis-compile valid programs of the form
 *    switch (e) case c1: case c2: { ... }
 * so this generates a warning whenever the command that follows a switch is
 * not just a simple block.  I could take the view that I would like to
 * moan if the block after 'switch' had any declarations at its head.
 */
            if (curlex.sym != s_lbrace) cc_warn(syn_warn_switch_funny);
#endif
#endif
            cmd2c_(c) = rd_command(0);
            cur_switchcmd = oldswitchcmd; cur_break = oldbreak;
            cur_switchscope = oldswitchscope;
            cur_switchtype = oldswitchtype;
            if (!(declposs && cfront_semantics))
            {   if (curlex.sym != s_nothing) ungetsym();
                curlex.sym = s_rbrace;    /* FRIGORMA */
            }
            return c;
        }
case s_return:
        nextsym();
        push_exprtemp_scope();
        e = curlex.sym == s_semicolon ? 0 : rd_expr(PASTCOMMA);
        if (e)
        {   e = LanguageIsCPlusPlus && cur_structresult ?
/* The effect of this code is to disable the C struct-result            */
/* optimisation code in cg_return.  This is need significant review     */
/* for classes with constructors or virtual bases.                      */
/* The cast on the next line is a conspiracy with cg_return().          */
                  mkcast(s_return,
                         mkctor_v(mkunary(s_content, (Expr *)cur_structresult),
                                  mkExprList(0,e)),
                         te_void) :

                 mkcast(s_return, e, cur_restype);
#ifndef NO_RETURN_EXPRESSIONS
        /* Make return ALSO into an *EXPR* tree node.  Maybe this is   */
        /* dying in the advent of CPLUSPLUS changes in simplify.c.     */
            e = h0_(e) == s_error ? errornode :
                mk_expr1(s_return, cur_restype, e);
#endif
        }
        if (e != 0) implicit_return_ok = 0;
        if (e != 0 && /*equivtype(cur_restype, te_void)*/
            isprimtype_(cur_restype, s_void))
        {   if (cur_fn_is_ctor)
                cc_rerr(syn_rerr_return_expr_ctor);
            else if (cur_fn_is_dtor)
                cc_rerr(syn_rerr_return_expr_dtor);
            else
                cc_rerr(syn_rerr_return_expr_void);
        }
        if (cur_fn_is_dtor)
        {   /* forge 'goto __generated_dtor_part' instead */
            LabBind *lab = label_reference(dtorgenlabsym);
            /* the 0 in the mk_cmd_lab is never used */
            c = syn_reflab(lab, synscope, mk_cmd_lab(s_goto, fl, lab, 0));
            pop_exprtemp_scope();       /* since we won't be calling killexprtemps */
        }
        else
        {   if (e == 0 && !equivtype(cur_restype, te_void))
                /* do also the implicit return case too in cg/flowgraph.    */
            {   if (LanguageIsCPlusPlus)
                    cc_rerr(syn_warn_void_return);
                else if (!implicit_return_ok)
                    cc_warn(syn_warn_void_return);
            }
            if (cur_fn_is_ctor)
                e = (Expr*) findbinding(thissym, NULL, LOCALSCOPES);
            if (e && (h0_(e) != s_error))
            {   /* may change type (in a harmless way) and loses s_return   */
                e = optimise0(e);
                add_expr_dtors(killexprtemp());
                if (expr_dtors != NULL)
                {   if (cur_structresult != 0)
                    {   e = mkbinary(s_comma, e, mkcast(s_return, expr_dtors, te_void));
                        expr_dtors = NULL;
                        extra_flags = NULL;
                    }
                    else
                        e = exprtemp_killer(e);
                }
            }
            else
                pop_exprtemp_scope();   /* since we won't be calling killexprtemps */
            c = cmd_rescope(0, synscope, mk_cmd_e(op, fl, (e && h0_(e) != s_error) ? e : 0));
        }
        break;
#ifdef EXTENSION_VALOF
case s_resultis:
        nextsym();
        have_exprtemp_scope = true; push_exprtemp_scope();
        e = optimise0(
            mkcast(s_return,
                rd_expr(PASTCOMMA), valof_block_result_type));
        c = mk_cmd_e(op, fl, e);
        break;
#endif
case s_continue:
        if (cur_loopscope)
            c = cmd_rescope(cur_loopscope, synscope, mk_cmd_0(op, fl));
        else { c=0; cc_err(syn_err_continue); }
        nextsym();
        break;
case s_break:
        if (cur_loopscope != 0 || cur_switchcmd != 0)
            c = cmd_rescope(cur_break == s_break ? cur_loopscope :
                                                   cur_switchscope,
                            synscope,
                            mk_cmd_0(cur_break, fl));
        else { c=0; cc_err(syn_err_break); }
        nextsym();
        break;
case s_goto:
        nextsym();
        if (curlex.sym != s_identifier)
        {   cc_err(syn_err_no_label);
            return rd_command(declposs);
        }
        {   LabBind *lab = label_reference(curlex.a1.sv);
            /* the 0 in the mk_cmd_lab is never used */
            c = syn_reflab(lab, synscope, mk_cmd_lab(op, fl, lab, 0));
        }
        nextsym();
        break;
case s_throw:
        if (!LanguageIsCPlusPlus) goto defaultcase;
        nextsym();
        { Expr* e = 0;
          if (curlex.sym != s_semicolon)
            e=rd_expr(UPTOCOMMA); /* because it is an assignment-expression,
                                     not an expression */
          c = mkthrow(fl, e);
          break;
        }
case s_try:
        if (!LanguageIsCPlusPlus) goto defaultcase;
        nextsym();
        c = rd_compound_statement(s_try);
        {   Handler *h = rd_handler();
            Cmd* handler_exit;
            if (0) /* in a constructor/destructor */
              handler_exit = mkthrow(fl, 0);
            else
              handler_exit = mkexpop(fl);
            elselast = 0;
#define mk_cmd_hand(fl,a,b) mk_cmd_lab(s_catch,fl, (LabBind *)(a), (Cmd *)(b))
            return mk_cmd_try(fl, c, h, handler_exit);
        }
case s_catch:
        if (!LanguageIsCPlusPlus) goto defaultcase;
        cc_err(syn_err_catch_ignored);
        (void)rd_handler();
        return 0;
#ifdef TARGET_HAS_INLINE_ASSEMBLER
case s_asm:
        if (HasFeature(Feature_Fussy))
            cc_err(syn_err_asm_not_available);
        push_exprtemp_scope();
        c = rd_asm_block();
        if (killexprtemp() != NULL)
            syserr("exprtemp in asm block");
        elselast = 0;
        return c;
#endif
    }
    elselast = 0;
    checkfor_delimiter_ket(s_semicolon,
                           syn_err_expected1_aftercommand,
                           syn_err_expected1a_aftercommand);
    if (have_exprtemp_scope)
    {   add_expr_dtors(killexprtemp());
        if (expr_dtors != NULL)
        {   c = mk_cmd_block(curlex.fl, 0,
                     mkCmdList(mkCmdList(0, mk_cmd_e(s_semicolon, curlex.fl, expr_dtors)),
                               c));
            expr_dtors = NULL;
        }
    }
    return c;
  }
}

static Cmd *rd_body(TypeExpr *t, TypeExpr *fntype, bool is_ctor, bool is_dtor)
{   cur_switchscope = 0;
    cur_switchcmd = 0;
    cur_loopscope = 0;
    cur_break = s_error;
    cur_restype = is_ctor ? te_void : t;
    cur_fn_is_ctor = is_ctor;
    cur_fn_is_dtor = is_dtor;
    cur_switchtype = te_lint;
    cur_structresult = 0;
    if ((mcrepoftype(t) >> MCR_SORT_SHIFT) == 3 && !returnsstructinregs_t(fntype))
    {   Symstr *structresultsym = sym_insert_id("__struct_result");
        /* debugger-visible name moving to builtin.c.                   */
        cur_structresult =
            mk_binder(structresultsym, bitofstg_(s_auto), ptrtotype_(t));
    }
    currentfunction.structresult = cur_structresult;           /* for cg.c.        */
    if (curlex.sym == s_lbrace)
    {   Cmd *c = rd_block(blk_BODY, YES);  /* share scope with args...     */
        return c;
    }
    else
    {   cc_err(syn_err_no_brace);
        return 0;
    }
}


typedef struct DeclFnAux {
    FnAuxFlags flags;
    int32 val;
} DeclFnAux;

typedef struct DeclSpec {
    TypeSpec *t;
    SET_BITMAP stg;
    int32 stgval;
    DeclFnAux fnaux;
/* private flags for C/C++ for 'omitted type' for non-fn etc.           */
#define B_DECLMADE      1
#define B_TYPESEEN      2
#define B_IMPLICITINT   4
#define B_STGSEEN       8
#define B_LINKAGE       16  /* C++ extern "x" ... (incl. extern "x" { ...)  */
#define B_LINKBRACE     32  /* C++ extern "x" { ... special case            */
    int synflags;
} DeclSpec;

/* rd_declspec() reads a possibly optional list (as controlled by       */
/* 'declflag') of declaration-specifiers.  (Dec 88 ANSI draft section   */
/* 3.5).   It returns an object of TypeSpec (subtype of TypeExpr)       */
/* giving a bit map of types/storage classes read (plus Tagbinder for   */
/* struct/union or Binder for 'typedef') plus (local) B_TYPESEEN and    */
/* B_STGSEEN serve to enable 'f();' to be faulted and 'g(){}' to merely */
/* generate a warning.  We can now warn on 'static z();' (no 'int').    */
/* It also performs normalisation of 'float' to 'short double',         */
/* 'register' to 'auto register' to simplify later stages.              */
/* Note that defaulting of storage class depends not only on context,   */
/* but also on type - e.g. { int f(); ...} so it is done later.         */
/* Oct92: soon add *optional* "long long" ==> s_longlong.               */
static DeclSpec rd_declspec(int declflag,
                            ScopeSaver template_formals)

{
    SET_BITMAP illtype = 0, typesseen = 0, typedefquals = 0;
    int synflags = 0;
    Binder *b = 0;  /* typedef or struct/union/enum tag binder record */
    SET_BITMAP stgseen = 0;
    SET_BITMAP illstg = declflag & TOPLEVEL ?
                 (bitofstg_(s_register)|bitofstg_(s_auto)|
                  bitofstg_(s_virtual)|bitofstg_(s_friend)) :
        declflag & MEMBER ?
                 (bitofstg_(s_register)|bitofstg_(s_auto)|
                  bitofstg_(s_extern)|bitofstg_(s_weak)|
                  (LanguageIsCPlusPlus ? 0 : bitofstg_(s_static))) :
        declflag & BLOCKHEAD ?
                 (bitofstg_(s_virtual)|bitofstg_(s_friend)) :
        declflag & (TFORMAL|FORMAL|ARG_TYPES|CATCHER) ?
                 (STGBITS & ~bitofstg_(s_register)) : STGBITS;
    int32 stgval = 0;
    FnAuxFlags auxseen = 0;
    int32 auxval = 0; /* fnaux->val */
    bool newtag = NO;
    bool contentdefseen = NO;
    bool opaque = NO;
      /* opaque could be handled as a typebit but I don't since it's    */
      /* kept only in tag binders and the error handling is different   */

    for (;;)
    {   AEop s = curlex.sym;
        if (!isdeclstarter_(s))
        {   int scope_level = 0;
            /* A typedef may be possible, else break from loop...       */
            if (typesseen & ~CVBITS) break;
            if (template_formals)
                scope_level = push_var_scope(template_formals, Scope_TemplateArgs);
            rd_type_name();
            if (template_formals) pop_scope_no_check(scope_level);
            if ((curlex.sym & ~s_qualified) != s_identifier)
                break;
            if (curlex_typename == 0)
            {   if (((stgseen & bitofstg_(s_friend)) &&
                    peepsym() == s_semicolon &&
                     HasFeature(Feature_CFront))         /* friend X; */
                    || ((declflag & TFORMAL) && s == s_typename))
                                                        /* <typename T> same as <class T> */

                    s = s_class;                        /* != curlex.sym NB */
                else
                    break;        /* let rd_decl() handle what follows */
            }
            else
            {   b = curlex_typename;
                if (attributes_(b) & A_TEMPLATE &&
                    !(tagbindbits_(typespectagbind_(bindtype_(b))) & (TB_DEFD|TB_BEINGDEFD)))
                {   s = tagbindsort(typespectagbind_(bindtype_(b)))|s_qualified;
                } else {
                    s = s_typedefname;
                    typedefquals = qualifiersoftype(bindtype_(b)),
                    binduses_(b) |= u_referenced;
                }
            }
        }
        if (isstorageclass_(s))
        {   SET_BITMAP stgbit = bitofstg_(s);
            if (s == s_globalreg || s == s_globalfreg)
                stgbit = b_globalregvar;
            if (stgbit & illstg)
                cc_err(syn_err_stgclass, /* storage class illegal here */
                        s, ctxtofdeclflag(declflag));
            else if (stgbit & stgseen ||
                       stgbit & (PRINCSTGBITS|bitofstg_(s_register)) &&
                       stgseen & (PRINCSTGBITS|bitofstg_(s_register)))
            {   cc_err(syn_err_stgclass1, /* storage class incompatible */
                       s, stgseen);
                /* for error-recovery we keep the first stg unless the  */
                /* new one is typedef in which case we keep it          */
                if (s == s_typedef)
                    stgseen = (stgseen & ~(PRINCSTGBITS|bitofstg_(s_register))) | stgbit;
            }
            else
            {   stgseen |= stgbit;
                if (s == s_weak) stgseen |= bitofstg_(s_extern);
/* @@@ beware -- this leads to 'extern incompatible with extern'.       */
/* we should do this defaulting later, but to disallow '__weak auto'    */
/* we need a separate illstg2 bit (working like illtype).               */
            }
            nextsym();
            if (stgbit == b_globalregvar)
            {   checkfor_ket(s_lpar);
                stgval = evaluate(rd_expr(PASTCOMMA)) << 1;
                checkfor_ket(s_rpar);
                if (s == s_globalfreg) stgval |= 1;
            }
        } else if (isfnaux_(s)) {
            auxseen |= bitoffnaux_(s);
            nextsym();
            if (s == s_swi || s == s_swi_i) {
                if (s == s_swi_i)
                    auxseen |= bitoffnaux_(s_swi) | f_specialargreg;
                checkfor_ket(s_lpar);
                auxval = CheckSWIValue(evaluate(rd_expr(PASTCOMMA)));
                checkfor_ket(s_rpar);
            }
        } else if (s == s_opaque) {
            if (typesseen & ~CLASSBITS)
                cc_rerr(syn_err_typeclash, s, typesseen & ~CLASSBITS);
            else
                opaque = YES;
            nextsym();
        } else {
            SET_BITMAP typebit = bitoftype_(s & ~s_qualified);
            TagBinder *instantiatetemplate = NULL;
            int instantiatescope = 0;

            if (illtype & typebit)
            {   /* this code relies that for type symbols x,y, "x y" is
                   legal iff "y x" is. */
                cc_err(syn_err_typeclash, s,
                       typesseen & illtypecombination[shiftoftype_(s)]);
/* New error recovery: ignore previous types/stgclass and retry.        */
/* This is better for things like "class T {} int f() {...}".           */
/* Note that we aren't just inserting a ';', e.g. sizeof(struct{}int)   */
/* and also that 'struct {} typedef const int' splits AFTER the const.  */
                if (declflag & TEMPLATE) pop_scope(0);
                return rd_declspec(declflag & ~TEMPLATE, 0);
            }
            else
            {   if (opaque && (typebit & ~CLASSBITS))
                {   cc_rerr(syn_err_typeclash, s_opaque, typebit);
                    opaque = NO;
                }
                if (declflag & SIMPLETYPE && (typesseen || typebit &
                      (CVBITS|ENUMORCLASSBITS)))
                    cc_err(syn_err_illegal_simple_types, typesseen | typebit);
                if (typebit & typesseen & bitoftype_(s_long)) {
                  /* long + long => longlong (without allowing longlonglong etc) */
                    s ^= s_long ^ s_longlong;
                    typesseen &= ~bitoftype_(s_long);
                    typebit = bitoftype_(s_longlong);
                }
                typesseen |= typebit;
                illtype |= illtypecombination[shiftoftype_(s)];
            }
            if (!(typebit & ENUMORCLASSBITS && (s & s_qualified)) &&
                !(s == s_class && (curlex.sym & ~s_qualified) == s_identifier))
                nextsym();

            if (typebit & ENUMORCLASSBITS)
            {   TagBinder *b2;
                TagDefSort defining;
                bool sawid = 0;
/* Now, after "struct id" a ';' or '{' indicates a new definition at */
/* the current nesting level, but not in type names, e.g. C++        */
/*        struct T *p = new struct T;                                */

                /* The rationale is that, "class T = int" ought to be
                   interpreted as "typedef TYPE T = int" where "T" is the
                   declarator-id.
                 */
                if ((declflag & TFORMAL) && !(declflag & TEMPLATE)
                    && (typebit & CLASSBITS))
                {   DeclSpec ds;
                    ds.t = mk_typevar();
                    ds.stg = bitofstg_(s_typedef);
                    ds.stgval = stgval;
                    ds.fnaux.flags = 0;
                    ds.synflags = B_TYPESEEN;
                    return ds;
                }

                if (curlex.sym == s_identifier)
                {   Symstr *sv;
                    Binder *tvb;
/* NB: a classname (or typedefname) followed by '<' must always be a    */
/* template_postfix, not a less-than.  Hence improve error recovery.    */
                    if (LanguageIsCPlusPlus)
                        rd_template_postfix(template_formals, YES);
/* Ah: perhaps we can write "class ::t<int> ..." for a top-level        */
/* template?  Currently forbid.                                         */
                    sv = curlex.a1.sv;
                    sawid = 1;
                    nextsym();
                    defining = (curlex.sym == s_semicolon &&
                                declflag & CONC_DECLARATOR &&
                                !(stgseen & bitofstg_(s_friend))) ?
                                   TD_Decl :
/* Context TFORMAL only arises when LanguageIsCPlusPlus.                */
                               (declflag & TFORMAL &&
                                    (curlex.sym == s_comma ||
                                     curlex.sym == s_greater ||
                                     curlex.sym == s_semicolon)) ? TD_Decl :
                               (curlex.sym == s_colon && s != s_enum ||
                                curlex.sym == s_lbrace) ?
                                   TD_ContentDef : TD_NotDef;
                    if (defining == TD_ContentDef) contentdefseen = YES;

#ifdef WANT_BROKEN_SUPERFLOUS_PREFIX_WARNINGS
/* This code warns that the 'struct' is superflous in these cases:
     typedef struct T T;
     struct T* t;         // warning
     typedef struct S S;
     struct S { int s; }; // bogus warning
   but not in these cases:
     struct R;
     struct R* r;         // no warning
     struct Q;
     typedef struct Q Q2; // no warning

Additionally the warning is not seen (by sad and LDS) as being more helpful
than annoying.  Probably we don't understand the reason for it.
*/
                    if (LanguageIsCPlusPlus &&
                        !(stgseen & bitofstg_(s_typedef)))
                    {   Binder *b = findbinding(sv, 0, ALLSCOPES);
                        SET_BITMAP stgbits;
                        if (b != NULL &&
                            ((stgbits = bindstg_(b)) & bitofstg_(s_typedef)) &&
                            !(stgbits & u_implicitdef) && isclasstype_(bindtype_(b)))
                            cc_warn(syn_warn_superfluous_prefix);
                    }
#endif

                    if (syn_class_scope != NULL &&
                        (tagbindbits_(syn_class_scope) & TB_TEMPLATE))
                    {   if ((tvb = findbinding(sv, 0, ALLSCOPES)) != NULL &&
                            istypevar(bindtype_(tvb)))
                        { SET_BITMAP tbits = typebit;
                          if (tbits & bitoftype_(s_class)|bitoftype_(s_struct))
                            tbits |= bitoftype_(s_class)|bitoftype_(s_struct);
                          typespecmap_(bindtype_(tvb)) |= tbits;
                          binduses_(tvb) |= u_referenced;
                        }
                        /* Its a template because they might contain references to
                           type para in the parent.
                         */
                        bind_scope |= TEMPLATE;
                    }

                    /* transforms 'T' to whatever it's bounded to */
                    if (syn_class_scope != NULL &&
                        has_template_arg_scope())
                    {   Binder *b = findbinding(sv, 0, ALLSCOPES);
                        if (b != NULL && is_template_arg_binder((Expr *)b) &&
                            isclasstype_(princtype(bindtype_(b))))
                            sv = bindsym_(typespecbind_(bindtype_(b)));
                    }

                    /* GLOBALSTG is implicit in C++ */
                    b2 = instate_tagbinding(sv, s, defining,
                             (declflag) == (TFORMAL|TEMPLATE) ? TEMPLATE : bind_scope,
                                            &newtag);

                    if (declflag & TEMPLATE && defining == TD_ContentDef)
                            tagscope_(b2) = dup_template_scope();

                    if ((stgseen & bitofstg_(s_friend)) && defining == TD_ContentDef)
                        /*&& (curlex.sym != s_semicolon))*/
                    {   cc_rerr(syn_rerr_friend_class_not_definable, b2);
                        stgseen &= ~bitofstg_(s_friend);
                    }
/* We should share this code for "class A<1> a;" with "A<1> a;".        */
/* @@@ next test should be returned as result from rd_template_postfix. */
                    if (LanguageIsCPlusPlus)
                    { TagBinder *tb_old;

                      if (defining != TD_ContentDef &&
                          bind_global_(sv) != NULL &&
                          (attributes_(bind_global_(sv)) & A_TEMPLATE) &&
                          !(declflag & SPECIALIZE) &&
            (tb_old = tagprimary_(typespectagbind_(bindtype_(bind_global_(sv))))) != NULL)
                      { if ((tagbindbits_(tb_old) & TB_TEMPLATE) == 0)
                          syserr("primary template $c", tb_old);
                        if (tagbindbits_(tb_old) & TB_DEFD &&
                             !(tagbindbits_(b2) & (TB_DEFD|TB_BEINGDEFD)))
                        {   if (debugging(DEBUG_TEMPLATE))
                                cc_msg("template $b[%lx] -> $b[%lx]\n",
                                       tb_old, tagbindbits_(tb_old),
                                       b2, tagbindbits_(b2));
                            if (curlex.sym != s_lbrace && curlex.sym != s_times)
                            {   instantiatetemplate = class_template_reduce(tb_old,
                                                    taginstances_(tb_old), tagactuals_(b2));
                                defining = TD_ContentDef;
                            }
                            /* beware bind_scope=storage for members here! */
                            b2 = instate_tagbinding(sv, s, defining, TOPLEVEL, &newtag);
                            /* TEMPLATE OK to use 'newtag'? */
                        }
                      }
                    }

                    if (LanguageIsCPlusPlus && newtag)
/* @@@ check ansi re things like 'struct a; int a; struct a {}' etc.    */
                    {   Binder *b = instate_classname_typedef(b2, declflag);
                        if (declflag & TEMPLATE)
                        {   if (!(declflag & TFORMAL))
                                tagbindbits_(b2) |= TB_TEMPLATE;
                            attributes_(b) |= A_PRIMARY;
                        }
                    }

                    /* the 2nd condition looks unnecessary, but see t14c/_1452W12.cpp */
                    if (declflag & TEMPLATE && tagbindbits_(b2) & TB_TEMPLATE)
                    {   if (!newtag)
                        {   merge_default_template_args(template_formals, b2, NULL);
                            if (!(tagbindbits_(b2) & TB_DEFD))
                                tagformals_(b2) = template_formals;
                        } else
                        {   tagformals_(b2) = template_formals;
                            merge_default_template_args(template_formals, b2, NULL);
                        }
                    }


/* @@@ The next 6 lines should be removable now that bind.c doesn't set */
/* TB_BEINGDEFD for "struct A;".  From here ...                         */
/* Of course, since the mip/bind.c example (see TB_BEINGDEFD removal)   */
/* can't happen under C++ scope rules, TB_BEINGDEFD is a bit spurious.  */
#if 0
                    if (curlex.sym == s_semicolon &&
                            tagbindbits_(b2) & TB_BEINGDEFD)
                        syserr("rd_declspec tidyup");
                    if (curlex.sym == s_semicolon)
                        /* @@@ what about above CONC_DECLARATOR?        */
                        tagbindbits_(b2) &= ~TB_BEINGDEFD;
/* ... to here */
#endif
                    if (s == s_enum) {
                        if (defining == TD_ContentDef)
                            synflags |= B_DECLMADE;
                        else if (!(tagbindbits_(b2) & TB_DEFD))
                            cc_rerr(syn_err_undef_enum, sv);
                    } else if (defining != TD_NotDef)
                        synflags |= B_DECLMADE;  /* police 'int;' error */
                }
                else
                {   defining = TD_ContentDef;   /* anonymous class      */
                    b2 = instate_tagbinding(0, s, TD_ContentDef, bind_scope,
                                            &newtag);
                }
                if (defining == TD_ContentDef)
                {   /* assert (curlex.sym == s_lbrace                   */
                    /*         || curlex.sym == s_colon && s != s_enum) */
                    int implicit_level = 0, implicit_level2 = 0;
                    if (declflag & TEMPLATE)
                    {   if (!template_formals) syserr("funny template $c", b2);
                        implicit_level = push_var_scope(template_formals,
                                                        Scope_TemplateArgs);
                        if (template_formals != tagformals_(b2))
                            implicit_level2 = push_var_scope(tagformals_(b2),
                                                             Scope_TemplateArgs);
                    } else if (declflag & SPECIALIZE)
                        tagbindbits_(b2) |= TB_SPECIALIZED;
                    if (LanguageIsCPlusPlus && (declflag & (FORMAL|TFORMAL)) &&
                        !tagactuals_(b2))
                        cc_rerr(syn_rerr_tagdef_in_formals, b2);
                    if (instantiatetemplate)
                    {   int h = tagtext_(instantiatetemplate);
                        if (debugging(DEBUG_TEMPLATE))
                            cc_msg("instantiate $c buffer[%d]\n",
                                    instantiatetemplate, h);
                        if (h == -1) syserr("template symbol buffer lost");
                        else
                        {   instantiatescope = push_var_scope(tagscope_(b2),
                                                              Scope_TemplateDef);
                            (void) push_var_scope(tagactuals_(b2),
                                                 Scope_TemplateArgs);
                            lex_openbody(h, YES, YES,
                               bindsym_(instantiatetemplate), bindsym_(b2));
                        }
                    }
                    if (declflag & TEMPLATE) (void)lex_bodybegin();

                    /* avoid spurious (C++?) warning for enum { x,y };  */
                    if (s==s_enum)
                    {   synflags |= B_DECLMADE;
                        rd_enumdecl(b2);
                        checkfor_ket(s_rbrace);
                    }
                    else
                    {   if (stgseen & bitofstg_(s_friend))
                        {
                            cc_err(syn_err_not_friend, (bindsym_(b2)));
                            checkfor_ket(s_semicolon);
                        }
                        else
                        {   AEop old_access = access;
                            bool has_local_nested_class = (LanguageIsCPlusPlus
                                                           && (declflag & BLOCKHEAD));
                            FuncMisc func_misc;
                            PendingFnList *old_pendingfns;
                            if (has_local_nested_class)
                            {   save_pendingfns(&old_pendingfns);
                                save_curfn_misc(&func_misc);
                            }
                            /* there is a alloc_mark() in syn_note_generated_fn() */
                            rd_classdecl_(b2);
                            access = old_access;
                            checkfor_ket(s_rbrace);
                            if (has_local_nested_class
                                && (syn_pendingfns || syn_generatedfns))
                            {   Mark* mark = alloc_mark();
                                chk_for_auto = YES;
                                while (syn_pendingfns || syn_generatedfns)
                                {   TopDecl *d;
                                    cg_reinit();  /* BEFORE rd_topdecl() */
                                    /* there is a alloc_unmark() in case of
                                       syn_generatedfns */
                                    d = rd_topdecl(NO);
                                    /* careful about function template */
                                    if (h0_(d) != s_fndef) continue;
                                    /*(void)globalize_typeexpr(bindtype_(d->v_f.fn.name));*/
                                    cg_topdecl(d, curlex.fl);
                                }
                                chk_for_auto = NO;
                                alloc_unmark(mark);
                            }
                            if (has_local_nested_class)
                            {   restore_curfn_misc(&func_misc);
                                restore_pendingfns(old_pendingfns);
                            }
                        }
                    }
                    if (declflag & TEMPLATE) tagtext_(b2) = lex_bodyend();

                    if (instantiatetemplate)
                    {   lex_closebody();
                        pop_scope_no_check(instantiatescope);
                    }

                    if (declflag & TEMPLATE)
                    {   if (implicit_level2) pop_scope_no_check(implicit_level2);
                        pop_scope(implicit_level);
                    }
                }
                else if (!sawid)
                {   cc_err(syn_err_tag_brace, s);
                    /* recovers for 'struct *a' or suchlike error. */
                }
                b = (Binder *)b2;
            }
        }
    }
    if (LanguageIsCPlusPlus &&
        declflag & TOPLEVEL && isstring_(curlex.sym) &&
        typesseen == 0 && stgseen == bitofstg_(s_extern) && auxseen == 0)
    {   Expr *s = rd_ANSIstring();
        Linkage *p = syn_linkage_free;
        if (p == 0) p = (Linkage *)GlobAlloc(SU_Other, sizeof(Linkage));
        else syn_linkage_free = p->linkcdr;
        p->linkcar = linkage_of_string((String *)s);
        p->linkcdr = syn_linkage;
        syn_linkage = p;
        synflags |= B_LINKAGE;
        if (curlex.sym == s_lbrace) nextsym(), synflags |= B_LINKBRACE;
        /* else the 'extern "C" typedef int foo();' form.               */
        /* Alternative implementation: retry rd_declspec and then       */
        /* pop implicitly at terminating ';' or '}'?                    */
        {   DeclSpec ds;
            ds.t = (TypeExpr *)DUFF_ADDR;
            ds.stg = stgseen; ds.stgval = stgval;
            ds.fnaux.flags = 0;
            ds.synflags = synflags;
            return ds;
        }
    }
    if (typedefquals & typesseen)
        cc_rerr(syn_rerr_qualified_typedef(b, typedefquals & typesseen));
    /* could warn here in C (not C++) for undefined const <fntypedef>.  */
    if (typesseen) synflags |= B_TYPESEEN;
    if (stgseen) synflags |= B_STGSEEN;
    if ((declflag & TYPE_NEEDED) && typesseen == 0)
        cc_rerr(syn_rerr_missing_type), synflags |= B_TYPESEEN;

    if ((typesseen & NONQUALTYPEBITS) == 0)
    {   if ((typesseen|stgseen) != 0 || !(declflag & FORMAL))
            /* consider returning 0 for untyped formals?
               changes would be need for several routines, so pend */
        {   if ((typesseen &
                 (bitoftype_(s_long)|bitoftype_(s_short)|
                  bitoftype_(s_signed)|bitoftype_(s_unsigned))) == 0)
                synflags |= B_IMPLICITINT;
            typesseen |= bitoftype_(s_int);
            auxseen |= f_norettype;       /* in case is a function */
        }
    }

    if (typesseen & bitoftype_(s_float))    /* normalise for rest of system */
    {   typesseen ^= (bitoftype_(s_float) ^ bitoftype_(s_double));
        if (typesseen & bitoftype_(s_long))
        {   if (!(suppress & D_LONGFLOAT) && !HasFeature(Feature_PCC))
             { suppress |= D_LONGFLOAT;
               cc_rerr(syn_rerr_long_float);
             }
            typesseen &= ~bitoftype_(s_long);
        }
        else
            typesseen |= bitoftype_(s_short);  /* float => short double */
    }
    if (typesseen & bitoftype_(s_longlong)) /* normalise for rest of system */
    {   /* map type "long long" into "long short"...                    */
        /* Storing types as bit-maps must be up for review.             */
        typesseen = (typesseen & ~bitoftype_(s_longlong)) | ts_longlong;
    }

    if (typesseen & bitoftype_(s_unaligned))
    {   TagBinder *tb = NULL;
        if (typesseen & CLASSBITS)
        {   tb = (TagBinder *)b;
            if (newtag) {
                tagbindbits_(tb) |= TB_UNALIGNED;
                tb = NULL;
            }
        } else if (typesseen & bitoftype_(s_typedefname)) {
            TypeExpr *t = princtype(bindtype_(b));
            if (isclasstype_(t)) tb = typespectagbind_(t);
        }
        if (tb != NULL && !(tagbindbits_(tb) & TB_UNALIGNED))
        {   cc_rerr(syn_rerr_not_decl_qual(tb,s_unaligned));
            typesseen ^= bitoftype_(s_unaligned);
        }
    }

    if (opaque)
    {   TagBinder *tb = (TagBinder *)b;
        if (tb == NULL)
            syserr("opaque confused:  no TagBinder");
        if (contentdefseen)
        {  if (!(typesseen & CLASSBITS))
               syserr("opaque confused:  $b is not struct/class", b);
           tagbindbits_(tb) |= TB_OPAQUE;
        }
        else
        {   if ((tagbindbits_(tb) & TB_DEFD)
                && !(tagbindbits_(tb) & TB_OPAQUE))
                cc_rerr(syn_rerr_not_decl_qual(tb,s_opaque));
            else
                tagbindbits_(tb) |= TB_OPAQUE;
        }
    }

    if (stgseen & bitofstg_(s_register))   /* normalise for rest of system */
        stgseen |= bitofstg_(s_auto);
#ifndef NON_CODEMIST_MIDDLE_END
/* AM: The error recovery here is not good: this new code currently     */
/* fails unpleasantly if #pragma -r is set when a function is defined.  */
/* I think we can't do this until after function determination etc.     */
/* Also, I want to be able be able to specify physical registers not    */
/* just V1...Vn.                                                        */
    if (declflag & TOPLEVEL) {
        if (global_intreg_var > 0)
            stgseen &= ~(bitofstg_(s_static)|bitofstg_(s_extern)),
            stgseen |= b_globalregvar,
            stgval = global_intreg_var << 1;
        else if (global_floatreg_var > 0)
            stgseen &= ~(bitofstg_(s_static)|bitofstg_(s_extern)),
            stgseen |= b_globalregvar,
            stgval = (global_floatreg_var << 1) | 1;
    }
#endif
    {   DeclSpec ds;
        TypeSpec *t = primtype2_(typesseen, b);
/* AM: the next line is really the wrong place to do this code (it      */
/* should be in the loop above) since declaration specifiers may follow */
/* the struct-specification.                                            */
        if (contentdefseen && !(suppress & D_STRUCTPADDING)) {
            bool padded = NO;
            (void)sizeoftypenotepadding(t, &padded);
            if (padded) cc_warn(syn_warn_struct_padded, b);
        }
        ds.t = t;
        ds.stg = stgseen;
        ds.stgval = stgval;
        ds.fnaux.flags = auxseen,
        ds.fnaux.val = auxval,
        ds.synflags = synflags;
        return ds;
    }
}

static SET_BITMAP rd_onceonlyquals(SET_BITMAP allowed)
{   SET_BITMAP qseen = 0;
    for (;;)
    {   AEop s = curlex.sym; SET_BITMAP q;
        if (!isdeclstarter_(s)) break;
        q = bitoftype_(s);
        if (!(q & allowed)) break;
        if (q & qseen) cc_err(syn_err_typeclash, s, q);
        qseen |= q;
        nextsym();
    }
    return qseen;
}


/* the following macro checks for an arg which has not been typed */
#define is_untyped_(x) (h0_(x) == s_typespec && typespecmap_(x) == 0)

typedef TypeExpr Declarator;   /* funny inside-out Expr */
#define sub_declarator_(x) (typearg_(x))

/* Declarators: read these backwards (inside out) to yield a name
 * (omitted if abstract declarator) and a TypeExpression (a la Algol68).
 * Then the declarator AE structure is read and an in-place pointer reverse
 * is done to turn a 'basictype' (possibly typedef) and a declarator into
 * a declaree (identifier or empty) in 'declarator_name' and TypeExpr.
 * For C++ we need to allow things like "int a(3);".  This is currently
 * done by an s_cppinit Declarator node (local to rd_declarator()) and
 * declarator_init.  'inner' forbids (e.g.) "int (a(3))" etc.
 */

static Declarator *rd_formals_1(Declarator *a, const DeclFnAux *fnaux);

static Declarator *rd_declarator_postfix(Declarator *a,
            int declflag, const DeclFnAux *fnaux, bool inner)
{   for (;;) switch (curlex.sym)
    {
case s_lpar:
      { int scope_level = -1;
        if (declflag & (NEW_TYPENAME|CONVERSIONTYPE)) return a;
        nextsym();
        if (LanguageIsCPlusPlus)
        {
/* There is an ambiguity here with look-ahead for C++ initialisers and  */
/* olde-style C function definitions.  Consider:                        */
/*   int x = 3; int a(x); int f(x) int x; { return x; }.                */
/* Here we resolve this by allowing such f(x) only if x is not in scope */
/* and warning about the archaism.                                      */
/* This represents a non-upwards compatibility of C to C++.             */
/* Really we should read ahead to decide on seeing ';' (or ',' etc).    */
            if (a != 0 && h0_(a) == s_binder)
                scope_level = push_multi_scope(bindparent_((Binder *)a));
            rd_type_name();
            if (!inner && declflag & (TOPLEVEL|BLOCKHEAD) &&
                  !(curlex.sym == s_rpar || curlex.sym == s_ellipsis ||
                    isdeclstarter2_(curlex)))
            {   /* could be a C++ initialiser, but be gentle if arg is an   */
                /* unbound simple identifier.                               */
                if (!(declflag & TOPLEVEL && curlex.sym == s_identifier &&
                    findbinding(curlex.a1.sv, NULL, ALLSCOPES) == NULL))
                    /* return for caller to do rd_exprlist...               */
                    return mk_typeexpr1(s_cppinit, a, 0);
                /* warn because: not C++ and because odd 'unbound' test.    */
                cc_warn(syn_warn_archaic_fnpara);
            }
        }
        a = rd_formals_1(a, fnaux);
        if (scope_level != -1) pop_scope_no_check(scope_level);
      }
        break;
case s_lbracket:
        if (declflag & CONVERSIONTYPE) return a;
        nextsym();
        {   Expr *e = 0;
            if (curlex.sym != s_rbracket)
            {   e = mkintegral(s_subscript, rd_expr(PASTCOMMA));
/* The next line allows  new(int [n][6])  with 'n' a variable for C++.  */
                if (!(declflag & (NEW_TYPENAME|FLEX_TYPENAME) &&
                      h0_(a) == s_nothing)) e = check_arraysize(e);
            }
            a = mk_typeexpr1(t_subscript, a, e);
        }
        checkfor_ket(s_rbracket);
        break;
default:
        return a;
    }
}

/* AM: next edit the following becomes a TypeFnAux* arg to rd_formals. */
static int32 syn_minformals, syn_maxformals;
static bool syn_oldeformals;     /* @@@ use in rd_decl? */
                       /* set by rd_formals, read by rd_declarator_1() */
static Symstr *declarator_name;
                       /* set by rd_declarator: 0 or Symstr *          */
static Binder *declarator_mbinder;
                       /* set by rd_declarator: binder for A::x or 0.   */
                       /* use bindstg_(memfns/memfna) + bindparent_()   */
                       /* in fixup_fndecl/fndef.                        */
static TagBinder *declarator_qscope;
                       /* set if the declaree is qualified...           */
#define MEMFNBITS (b_memfna | b_memfns)
                       /* (declarator_name could become a Binder *.)    */
static bool declarator_init;    /* ditto */

/* rd_declarator reads a C declarator (q.v.).  We test declflag to see  */
/* whether CONC_DECLARATOR or ABS_DECLARATOR's (or both) are            */
/* acceptable, also TOPLEVEL (which allows old 'f(a,b)' non-prototype   */
/* form).  In C++ declflag is tested more.                              */
static Declarator *rd_declarator_1(int declflag, const DeclFnAux *fnaux,
        bool inner)
{
    static Declarator emptydeclarator = { s_nothing };  /* /* @@@ kill? */
    static Declarator errordeclarator = { s_error };
    Declarator *a; AEop op;
    rd_dname();
    op = curlex.sym & ~s_qualified;
    declarator_qscope = 0;
    if (declflag & CONVERSIONTYPE && !(op == s_times || op == s_and))
        /* CONVERSIONTYPE declarators include *, &, S::* types only.    */
        op = s_nothing;
    switch (op)
    {
defaultcase:
default:
        if (declflag & CONC_DECLARATOR)
        {   cc_err(syn_err_expected3);
            if (curlex.sym == s_rbrace && !(declflag & TOPLEVEL)) nextsym();
            return &errordeclarator;
        }
        a = &emptydeclarator;
        break;
case s_pseudoid:
case s_identifier:
        if (declflag & ABS_DECLARATOR)
        {   /* @@@ improve next error message                           */
            cc_err(syn_err_unneeded_id);
            a = &emptydeclarator;
        }
        else
        {   a =
                curlex.sym & s_qualified && curlex_binder ?
                    (Declarator *) curlex_binder :
                    (Declarator *) curlex.a1.sv;
            /* Symstr(s_id) is Declarator (or now s_member/s_binder).   */
            if (a == 0 ||
                  h0_(a) != s_identifier &&
                  h0_(a) != s_binder &&
                  h0_(a) != s_member) syserr("rd_member_name=0");
            if (LanguageIsCPlusPlus)
            {
/* @@@ we should fault no-fn s_pseudoid's later.                        */
                if (op == s_pseudoid && curlex_optype)
                    a = (Declarator *)syn_list3(s_convfn, a, curlex_optype);
/* We could set the access context later (at declarator_mbind), this    */
/* may even be better in that it matches scope retrieval for memfns.    */
/* Note subtleties ANSI-resolvable in:  int A::v[sizeof x], A::f(t y);  */
/* of whether x and t are looked up in A:: or just global scope.        */
                if (bind_scope & TOPLEVEL        /* @@@ nasty usage here... */
                        && curlex.sym & s_qualified)
                    (void)set_access_context(curlex_scope, 0);
            }
        }
        if (curlex.sym & s_qualified) declarator_qscope = curlex_scope;
        nextsym();
        break;
case s_lpar:
        if (declflag & NEW_TYPENAME) return &emptydeclarator;
/* Note that "int ()" means an abstract declarator (or nameless formal) */
/* of the type of "int x()", not "int (x)".                             */
/* Similarly "int (void)" or "int (typedefname)" represent fn-typenames */
/* @@@ However, the ANSI draft (Dec 88) has an ambiguity in             */
/* "typedef int t; void f(int (t));" as to whether the formal to f is   */
/* of type "int" and name "t" or nameless and of type "int (int)".      */
/* We choose to select the latter (this seems to be the ANSI ctte's     */
/* intent from the example "t f(t (t))" in section 3.5.6 (dec 88)).     */
        nextsym();
        rd_type_name();
/* @@@ for C++ a form of ungetsym() might be an idea here so that       */
/* rd_declarator_postfix can parse the '(', or maybe we need to parse   */
/* ahead as 'either'.  See other calls to rd_formals_1.                 */
        if ((declflag & (ABS_DECLARATOR|FORMAL|TFORMAL|CATCHER|MEMBER)) &&
            (curlex.sym == s_rpar || curlex.sym == s_ellipsis ||
             isdeclstarter2_(curlex)))
        {
            a = rd_formals_1(&emptydeclarator, fnaux);
        }
        else
        {   a = rd_declarator_1(declflag, fnaux, 1);
            if (h0_(a) == s_error) return a;
            checkfor_ket(s_rpar);
        }
        break;
case s_and:
        if (!LanguageIsCPlusPlus) goto defaultcase;
case s_times:
        {   AEop typeop = (curlex.sym & ~s_qualified) == s_times ?
                              t_content : t_ref;
            TagBinder *tb = curlex.sym & s_qualified ? curlex_scope : 0;
/* @@@ What is curlex_scope/mem_scope relation?                         */
            Declarator *aa;
            SET_BITMAP quals;
            nextsym();
            quals = rd_onceonlyquals(CVBITS);
            a = rd_declarator_1(declflag, fnaux, inner);
            if (h0_(a) == s_error) return a;
/* move s_cppinit to outermost level, suppress rd_declarator_postfix(). */
            if (h0_(aa = a) == s_cppinit) a = sub_declarator_(a);
            a = mk_typeexpr1(typeop, a, (Expr *)(IPtr)quals);
            if (tb) a = (Declarator *)syn_list3(t_coloncolon, a, tb);
            if (h0_(aa) == s_cppinit) { sub_declarator_(aa) = a; return aa; }
        }
        break;
    }
    return rd_declarator_postfix(a, declflag, fnaux, inner);
}

static TypeExpr *fault_incomplete_type_object(TypeExpr *tt, Symstr *name,
                                              bool member, SET_BITMAP stg)
{   /* Fault attempts to declare an object (or member) of               */
    /* 'incomplete type' or function type.  Members are constraint      */
    /* violations, objects are unclear, maybe just undefined.           */
    /* Note that "extern struct UNDEF x;" is allowed.                   */
    /* C-ONLY: Note also that member <==> (stg & PRINCSTGBITS) == 0.    */
    TypeExpr *t = princtype(tt);
    if (h0_(t) == s_typespec)
    {   SET_BITMAP m = typespecmap_(t);
        if (m & CLASSBITS)
        {   TagBinder *b = typespectagbind_(t);
            SET_BITMAP bits = tagbindbits_(b);
            /* Much of the compiler can support undefined structs until */
            /* first essential use, but ANSI ban.                       */
            if (!(member && stg & bitofstg_(s_static)
                         && bits & TB_BEINGDEFD))
            {   if (bits & TB_BEINGDEFD && (b == current_member_scope()))
                {   if (member)
                      cc_err(syn_err_selfdef_struct_member(b,name));
                    else
                      cc_err(syn_err_selfdef_struct_object(b,name));
                    goto fixup;
                }
                if (!(bits & TB_DEFD) && !(stg & bitofstg_(s_extern)) &&
                    !((stg & bitofstg_(s_static)) && member))
                {   if (member)
                    {   if (!LanguageIsCPlusPlus ||
                            !(tagbindbits_(syn_class_scope) & TB_TEMPLATE))
                            cc_err(syn_err_undef_struct_member(b,name));
                    }
                    else
                      cc_err(syn_err_undef_struct_object(b,name));
                    goto fixup;
                }
/* This is a first stab -- more work has to be to fault static members  */
/* and fn args/results at the '}' in the dark corners like              */
/*   class C:ab { friend C(); static C x; <maybe override pure fn> };   */
/* or in explicit cast                                                  */
                if (bits & TB_ABSTRACT)
                {   if (member)
                        cc_rerr(syn_rerr_abstract_class_member(b,name));
                    else
                        cc_rerr(syn_rerr_abstract_class_object(b,name));
                    /* fixup is just to allow it */
                }
                if (bits & TB_OPAQUE)
                {   if (member)
                        cc_rerr(syn_rerr_opaque_class_member(b,name));
                    else
                        cc_rerr(syn_rerr_opaque_class_object(b,name));
                    /* fixup is just to allow it */
                }
            }
        }
        if (m & bitoftype_(s_void))
        {   if (member)
              cc_err(syn_err_void_object_member(name));
            else
              cc_err(syn_err_void_object_object(name));
            goto fixup;
        }
    }
    /* @@@ pick up more [] cases (like auto, but not extern) below?     */
    if (h0_(t) == t_subscript && typesubsize_(t) == 0 && member && !(stg & bitofstg_(s_static)))
    {   if (!(suppress & D_ZEROARRAY)) {
            if (suppress & D_MPWCOMPATIBLE)
                cc_warn(syn_rerr_open_member, name);
            else
                cc_pccwarn(syn_rerr_open_member, name);
        }
        /* ANSI ban open array members, pcc treats as [0].              */
        typesubsize_(t) = globalize_int(0);
    }

    if (h0_(t) == t_fnap && LanguageIsCPlusPlus && !member)
    {   TypeExpr *tt = princtype(typearg_(t));
        TagBinder *cl;
        if (isclasstype_(tt) &&
                tagbindbits_(cl = typespectagbind_(tt)) & TB_ABSTRACT)
            cc_rerr(syn_rerr_abst_class_rtype(cl));
    }

    if (h0_(t) == t_fnap &&
        (LanguageIsCPlusPlus ? (!member && !(stg & (bitofstg_(s_extern)|bitofstg_(s_static)))) :
                               (member || !(stg & (bitofstg_(s_extern)|bitofstg_(s_static)))) ))
    {   /* Beware: next line was syn_pccwarn, but AM sees PCC error.    */
        if (member)
          cc_rerr(syn_rerr_fn_ptr_member(name));
        else
          cc_rerr(syn_rerr_fn_ptr_object(name));
        /* Check non-typedef formals have types before fixup.           */
        if (h0_(tt) == t_fnap) ensure_formals_typed(typefnargs1_(tt), 1);
        goto fixup;
    }
    return tt;
fixup:
    return ptrtotype_(tt);
}


/* @@@ AM Jan 90: The two calls to fault_incomplete_formals() make      */
/* me nervous: it is ANSI illegal to have a fn prototype DEFINITION     */
/* with an incomplete type (e.g. void or 'struct t' where tag t is not  */
/* yet defined), but in a DECLARATION this is merely ANSI undefined.    */
/* Now, to avoid syserr()s (and to be helpful) in later calls to        */
/* functions with void parameters it is necessary to fault them at the  */
/* time of declaration.  The line below has the effect of faulting      */
/*          "struct a; extern void f(struct a);" too,                   */
/* (but of course not "extern void f(struct a *);").                    */
/* In C we treat this as an error, but allow it in C++ (see below).     */
/* This only concerns FORMAL's (prototype) and so is PCC-irrelevant.    */
/* Also, don't use declstg_() for DeclRhsList/FormTypeList pun.         */
static void fault_incomplete_formals(DeclRhsList *p, bool defn)
{   for (; p != NULL; p = p->declcdr)
    {
        if (LanguageIsCPlusPlus)
        {
/* Don't moan about things like: class T { friend T f(T); ... etc.      */
/* Except that we moan for  void g(T x) {} if T undefined.              */
            TypeExpr *t = princtype(p->decltype);
            if (!defn && isclasstype_(t)) continue;
        }
        p->decltype = fault_incomplete_type_object(
                        p->decltype, p->declname, 0, bitofstg_(s_auto));
    }
}

static TypeExpr *fault_odd_fn_array(TypeExpr *t)
{   /* Precondition: t is a t_fnap or t_subscript node.                 */
    /* Return t if OK, else a fixed up version -- we are sole owners.   */
/* ANSI (Oct88) oddity: function returning fn/array is a constraint     */
/* violation, whereas array of non-object type (void/fn/undef struct)   */
/* is done by weasel words (p28).  Treat similarly.                     */
    TypeExpr *a = typearg_(t), *pa = princtype(a);  /* maybe typedef!   */

/* fault ref to void.                                                   */
    if (h0_(t) == t_ref && isprimtype_(pa, s_void))
    {   /* treat as ref to int (better ideas?)                          */
        cc_rerr(syn_rerr_ref_void);
        typearg_(t) = te_int;
        return t;
    }
/* fault array of ref, pointer to ref and ref to ref.                   */
    if (h0_(pa) == t_ref &&
         (h0_(t) == t_subscript || h0_(t) == t_content || h0_(t) == t_ref))
    {   /* just forget the ref.                                         */
        cc_rerr(syn_rerr_ill_ref, t);
        typearg_(t) = typearg_(pa);
        return t;
    }

/* fault function returning fn or array                                 */
    if (h0_(t) == t_fnap &&
         (h0_(pa) == t_subscript || h0_(pa) == t_fnap))
    {   /* fn returning array/fn => fn returning ptr to array elt/fn.   */
        cc_rerr(syn_rerr_fn_returntype, pa);
        if (h0_(pa) == t_subscript) a = typearg_(pa);
        goto addptr;
    }
/* fault arrays of fn, void, @@@???undef structs, @@@???[] arrays.      */
    if (h0_(t) == t_subscript &&
         (h0_(pa) == t_fnap || isprimtype_(pa, s_void)))
    {   /* array of fn/void => array of ptrs to fn/void.                */
        cc_rerr(syn_rerr_array_elttype, pa);
        goto addptr;
    }
    return t;
addptr:
    typearg_(t) = mk_typeexpr1(t_content, a, 0);
    return t;
}

/* rd_declarator() returns 0 in the event that it failed to find a
   declarator.  Note that this can only happen if 'CONC_DECLARATOR' is set.
   The caller is now responsible for faulting declarations of 'incomplete
   types' (see ansi).
*/
static TypeExpr *rd_declarator(int declflag, TypeExpr *basictype,
                               const DeclFnAux *fnaux, SET_BITMAP stg)
{   Declarator *x;
    bool init = 0;
    /* This is one case where CPLUSPLUS can't be removed. ctorsym et al. */
#ifdef CPLUSPLUS
    TagBinder *mem_scope = current_member_scope();
    if (LanguageIsCPlusPlus && curlex.sym == s_bitnot)
    {   rd_dtor(mem_scope);
        if ((curlex.sym & ~s_qualified) == s_pseudoid)
            curlex_binder = findbinding(dtorsym, mem_scope, INCLASSONLY);
    }
#endif
    x = rd_declarator_1(declflag, fnaux, 0);

    if (h0_(x) == s_cppinit)
    {   init = 1;
        x = sub_declarator_(x);
    }
    for (;;)
    {
        TypeExpr *convtype = NULL;
        if (h0_(x) == s_convfn)
        {   convtype = (TypeExpr *)typespecbind_(x),
            x = sub_declarator_(x);
            /* we now know x is s_identifier, s_member or s_binder.     */
        }
        switch (h0_(x))
        {
    defaultcase:
    default:
            syserr(syserr_rd_declarator, (long)h0_(x));
    case s_error:
            return 0; /* error from rd_declarator_1()         */
    case s_nothing:
            declarator_init = init;
            declarator_mbinder = 0; declarator_name = 0;
            return basictype;
#ifdef CPLUSPLUS
    case s_binder:
            if (!LanguageIsCPlusPlus) goto defaultcase;
            declarator_init = init;
            {   Binder *b = (Binder *)x;
                TypeExpr *t = bindtype_(b);
                Symstr *sv = bindsym_(b);
                if (sv == ctorsym || sv == dtorsym || convtype != NULL)
                    basictype = fixup_special_member(sv, basictype,
                                         convtype != NULL ? convtype : te_void,
                                         bindparent_(b), stg);
                if (h0_(t) == t_ovld)
                {
                    b = ovld_match_def(b, basictype, typeovldlist_(t),
                                       cur_template_formals != NULL, declflag);
                    if (cur_template_formals) (void)applicable_template_formals();
                    if (b == NULL /*|| mem_scope == NULL*/)
                        goto notmember;
                    if (!(bindstg_(b) & b_impl))
                        syserr("rd_declarator $b", b);
                    declarator_mbinder = b;     /* for fixup_fndecl/def */
                    declarator_name = bindsym_(realbinder_(b));
                    return basictype;
                }
                if (bindstg_(b) & b_undef)
                /* static data member */
                {   declarator_mbinder = b;     /* for rd_declrhs_exec  */
                    declarator_name = bindsym_(b);
                    return basictype;
                }
            }
            /* drop through */
    case s_member:
            if (!LanguageIsCPlusPlus) goto defaultcase;
            cc_err(syn_err_no_member_here, (Binder *)x);
notmember:
/* in class A {...} a ... ensure typedef A gets marked as referenced */
            if (isclasstype_(basictype)) use_classname_typedef(basictype);
            declarator_init = init;
            declarator_mbinder = 0;
            declarator_name = bindsym_((Binder *)x);
            return basictype;
#endif
    case s_identifier:
            declarator_init = init;
            declarator_mbinder = 0;
            declarator_name = (Symstr *)x;

#ifdef CPLUSPLUS
            if (LanguageIsCPlusPlus)
            {
                if ((declflag & MEMBER)
                    && (declarator_name == tagbindsym_(mem_scope) ||
                        (tagprimary_(mem_scope) != NULL &&
                         declarator_name == tagbindsym_(tagprimary_(mem_scope)))))
                    declarator_name = ctorsym;
                if (declarator_name == ctorsym || declarator_name == dtorsym
                                               || convtype != NULL)
                    basictype = fixup_special_member(declarator_name, basictype,
                                                     convtype != NULL ? convtype : te_void,
                                                     mem_scope, stg);
                else if (isclasstype_(basictype))
/* in class A {...} a ... ensure typedef A gets marked as referenced */
                    use_classname_typedef(basictype);
            }
#endif

            return basictype;
    case t_fnap:
            {   Declarator *y = sub_declarator_(x);
#ifdef CPLUSPLUS
                if (LanguageIsCPlusPlus &&
                    h0_(y) == s_nothing && (declflag & MEMBER))
                {   TypeExpr *t = princtype(basictype);
                    if (isclasstype_(t) && typespectagbind_(t) == mem_scope)
                    {   sub_declarator_(x) = y = (Declarator *)ctorsym;
                        basictype = te_int;
                        typefnaux_(x).flags |= f_norettype;
                    }
                    else
                    {   cc_err(syn_err_missing_named_mfn);
                        sub_declarator_(x) = y = (Declarator *)gensymval(1);
                    }
                }
#endif

                if (!(h0_(y) == s_identifier && (declflag & TOPLEVEL)))
                    /* all cases except outermost () of TOPLEVEL declarator */
                    ensure_formals_typed(typefnargs1_(x), 1);
            }
            /* drop through */
    case t_ref:
    case t_content:
    case t_subscript:
    case t_coloncolon:
            {   Declarator *temp = sub_declarator_(x);
                if (is_untyped_(basictype))  /* e.g. f(int a,*b) */
                {   cc_rerr(syn_rerr_missing_type1);
                    basictype = te_int;
                }
                sub_declarator_(x) = (Declarator *)basictype;
                basictype = fault_odd_fn_array((TypeExpr *)x);

                if ( h0_(x) == t_fnap &&
                     (typefnaux_(basictype).flags & bitoffnaux_(s_pure)) &&
                     (mcrepoftype(typearg_(basictype)) & MCR_SORT_MASK) == MCR_SORT_STRUCT &&
                     !(typefnaux_(basictype).flags & bitoffnaux_(s_structreg)))
                    typefnaux_(basictype).flags &= ~bitoffnaux_(s_pure);

                x = temp;
            }
            break;
        }
    }
}

static TypeExpr *rd_typename(int declflag)
{   DeclSpec ds;
    ds = rd_declspec(declflag, 0);
                                 /*  TYPE_NEEDED and ~STGCLASS_OK       */
    if (ds.synflags & B_IMPLICITINT &&
        (LanguageIsCPlusPlus || !(suppress & D_FUTURE)))
    {   if (LanguageIsCPlusPlus && !(suppress & D_IMPLICITINT))
            cc_rerr(syn_rerr_missing_type);
        else
            cc_warn(syn_rerr_missing_type);
    }
    if (!(declflag & SIMPLETYPE))
        return rd_declarator(declflag, ds.t, &ds.fnaux, ds.stg);
    else
    {   TypeExpr *t = princtype(ds.t);
        TagBinder *tb;
        if (isclasstype_(t) &&
            (tagbindbits_(tb = typespectagbind_(t)) & TB_TEMPLATE))
        {   Symstr *sv = specialized_name_of(tb);
            BindList *bl = taginstances_(tb);
            for(; bl != NULL; bl = bl->bindlistcdr)
                if (bindsym_(bl->bindlistcar) == sv)
                    return tagbindtype_((TagBinder *)bl->bindlistcar);
        }
        return ds.t;
    }
    /* Ignore the value in declarator_name as abstract declarator.      */
    /* Incomplete types are valid here (or faulted later (e.g. sizeof)) */
}

/* note that in general we cannot default storageclasses on parsing them
   due to the differing default classes in "{ int a,f();...}".
   On the other hand nonsensical combinations SHOULD be detected by
   rd_typename().
*/

static void defaultstorageclass(DeclRhsList *d, int declflag, Binder *mbind)
{
    if ((declflag & STGCLASS_OK) && (d->declstg & PRINCSTGBITS) == 0)
    {   SET_BITMAP s = d->declstg;
        TypeExpr *t = d->decltype;
        if (debugging(DEBUG_BIND))
            cc_msg("defaultstg $r[%lx]%x\n", d->declname, (long)s, declflag);
        if (declflag & (BLOCKHEAD|FORMAL|ARG_TYPES|CATCHER))
            /* of course, by now there are no arg fns (mapped to ptrs). */
            s |= isfntype(t) ? bitofstg_(s_extern) : bitofstg_(s_auto);
        else if (declflag & TOPLEVEL)
        {   if (isfntype(t))
            {   /* as of CD #2 inline no longer effects linkage */
                if (mbind == 0)
                    s |= bitofstg_(s_extern);
                else
                    s |= attributes_(bindparent_(mbind)) & A_NOLINKAGE ?
                        bitofstg_(s_static) : bitofstg_(s_extern);
            }
            else
                s |=
        LanguageIsCPlusPlus && (qualifiersoftype(t) & bitoftype_(s_const)) ?
                    bitofstg_(s_static)|b_implicitstg :
                    bitofstg_(s_extern)|b_implicitstg;
        }
        else syserr(syserr_defaultstgclass, (int)declflag);
        d->declstg = s;
    }
}

static void ensure_formals_typed(DeclRhsList *d, bool proto)
{   /* proto is here true if olde-style is not acceptable:              */
    /* e.g. non-top level.                                              */
    for (; d; d = d->declcdr)
    {   TypeExpr *t = d->decltype;
        if (is_untyped_(t))
        {   if (proto)
                /* @@@ ensure that f(,) error has not got this far */
                cc_rerr(syn_rerr_missing_type2, d->declname);
            else
              if (!HasFeature(Feature_PCC))
                  /* God knows why ANSI do not consider this an error */
                  cc_warn(syn_warn_undeclared_parm, d->declname);

            d->decltype = te_int;
        }
    }
}

/* (local to rd_formals).  merge this fn with previous?                 */
static bool is_proto_arglist(DeclRhsList *d, int map)
{   /* map is 1 if ellipsis seen, else 0.  Error if ansi/old-style mix  */
    for (; d; d = d->declcdr)
    {   TypeExpr *t = d->decltype;
        map |= (is_untyped_(t)) ? 2 : 1;
    }
    if (map == 3) cc_rerr(syn_rerr_mixed_formals);
/* The caller can indicate that () is considered empty id-list with     */
/* map=0, or empty decl-list with map=1 (e.g. for ellipsis).            */
    return (map & 1) != 0;
}

static void merge_formal_decl(DeclRhsList *d, DeclRhsList *dnew)
{
/* Here I have a formal parameter (d) which is now being given an        */
/* explicit declaration (dnew).  Merge new information in with the old.  */
    TypeExpr *t = d->decltype;
    if (!is_untyped_(t))  /* previous type info */
        cc_err(syn_err_duplicate_type, d->declname);
    d->declstg = dnew->declstg;
    d->decltype = dnew->decltype;
}

static void CheckReturnType(TypeExpr *fntype)
{
    if (!LanguageIsCPlusPlus && HasFeature(Feature_Fussy))
    {   /* dr 113: only 'void' is allowed as a function's return type   */
        /* not any void type.                                           */
        TypeExpr *resulttype = typearg_(fntype);
        if (isprimtype_(resulttype, s_void)
             ? typespecmap_(resulttype) & CVBITS
             : isprimtype_(princtype(resulttype), s_void))
            cc_rerr(syn_rerr_qualified_void);
    }
}

static void fixup_fndef(DeclRhsList *temp, Binder *mbind)
{   TypeExpr *fntype = temp->decltype;
    DeclRhsList *fnpars = typefnargs1_(fntype);
    CheckReturnType(fntype);
    if (LanguageIsCPlusPlus)
    {
/* current_member_scope is uncomfortable as a static reference.         */
/* mbind is set if the declaration had a '::', e.g. friend A::f().      */
        SET_BITMAP memflags =
            mbind ? bindstg_(realbinder_(mbind)) & MEMFNBITS : 0;
        temp->declstg |= memflags;
        if (memflags & b_memfna) memfn_typefix(temp,
            mbind ? bindparent_(mbind) : current_member_scope());
    }
    if (curlex.sym != s_lbrace && curlex.sym != s_colon)
    {   if (HasFeature(Feature_WarnOldFns))
            cc_warn(syn_warn_old_style, temp->declname);
    }
    else
    {   if (HasFeature(Feature_PCC) && HasFeature(Feature_Fussy))
            /* @@@ The next line considers f(){} ANSI only! */
            cc_warn(syn_warn_ANSI_decl, symname_(temp->declname));
    }

/* Next additional C++ could sensibly be done for C as f(...) is        */
/* illegal in C.  The ellipsis will have set oldstyle==0 anyway.        */
/* This old PCC-compatibility code could be tidied too.                 */
    if (!fntypeisvariadic(fntype))
    {   if (fnpars == 0)
        {   maxargs_(fntype) = 0;
            if (!HasFeature(Feature_PCC))
                /* treat f() {} as f(void) {} in ANSI mode... */
                typefnaux_(fntype).oldstyle = 0;
        }
    }
    temp->declstg |= b_fnconst;
}

static void fixup_fndecl(DeclRhsList *temp, Binder *mbind)
{   CheckReturnType(princtype(temp->decltype));
    if (LanguageIsCPlusPlus)
    {
/* current_member_scope is uncomfortable as a static reference.         */
/* mbind is set if the declaration had a '::', e.g. friend A::f().      */
        SET_BITMAP memflags =
            mbind ? bindstg_(realbinder_(mbind)) & MEMFNBITS : 0;
        temp->declstg |= memflags;
        if (memflags & b_memfna) memfn_typefix(temp,
            mbind ? bindparent_(mbind) : current_member_scope());
    }
    temp->declstg |= b_fnconst|b_undef;
/* really 999 can't happen in C++, but leave this in for a bit.         */
    if (maxargs_(princtype(temp->decltype)) == 999)
    {   if (warn_deprecated)
            /* The follow warning enables us to root out        */
            /* insecurities/errors of the form:                 */
            /* extern f(); g() { f(1); } f(int x,int y) {...}   */
            cc_warn(syn_warn_give_args, symname_(temp->declname));
        else xwarncount++;
    }
}

static void rd_declrhs_exec(DeclRhsList *d, int declflag,
                            bool cppinit, Binder *mbind)
{   int initflag = 0;
    bool haveinit = NO;
    int scope_level  = 0;
    Expr *dyninit = 0;
    push_exprtemp_scope();              /* this wraps up any potential mkcast not
                                           invoked under a rd_expr().
                                         */
    if (d->declstg & (bitofstg_(s_extern)|bitofstg_(s_static)|b_globalregvar))
        d->declstg |= b_undef;
    if (curlex.sym == s_assign || archaic_init(curlex.sym) ||
        (LanguageIsCPlusPlus &&
/* 'cppinit' is true when e.g. int a(3) and we have read the '('.       */
/* @@@ C++ rules should be more severe than this...                     */
         (cppinit ||
          (!(d->declstg & bitofstg_(s_extern)) || d->declstg & b_implicitstg) &&
          typehasctor(d->decltype))) )
/* Extern init only at TOPLEVEL.  Static init at AUTO scope too:        */
    {   haveinit = YES;
        if (((d->declstg & bitofstg_(s_extern)) &&
             !(declflag & TEMPLATE) &&
             (declflag & TOPLEVEL)) ||
            (d->declstg & bitofstg_(s_static)))
        {
            d->declstg &= ~b_undef;
        }
        if (d->declstg & b_fnconst)
        {   cc_rerr(syn_rerr_fn_ptr1, d->declname);
            d->decltype = ptrtotype_(d->decltype);
            d->declstg &= ~(b_fnconst | b_undef);
        }
    }

/* Fault:  template <...> class A {...} x;  etc.  A less clear case is  */
/*         template <...> typedef class A {...} B, *C;                  */
/* where C is unreasonable but arguably B is OK.                        */
/* Beware: control flow is nasty in the following (share more code).    */
/* FW: the above is not strictly true. It's OK to say,                  */
/*     template <class T> class A<T>::x;                                */
    if (declflag & TEMPLATE &&
        !(isclasstype_(d->decltype) ||
          (!(d->declstg & bitofstg_(s_typedef)) && isfntype(d->decltype))) &&
        (curlex_member == NULL || (bindstg_(curlex_member) & bitofstg_(s_static))))
    {   cc_rerr(syn_err_template_notclassorfunction);
        /* Note the above allows the function via a typedef.  OK?       */
        if (cppinit)
            (void)rd_exprlist_opt();
        else if (curlex.sym == s_assign)
        {   nextsym();
            syn_initdepth = 0, syn_initpeek = 0, (void)syn_rdinit(0,0,4);
        }
        /*        pop_scope(scope_level);        ???                    */
        /* @@@ we should probably kill gen_reftemps() here.             */
        return;
    }
    /* do the next line AFTER above type patching but before
       reading possible initialiser.  Save Binder in ->declbind.
       d->declstg now always has b_undef for statics & externs if there
       is no initialiser to read. instate_declaration removes for local
       statics not going in bss.
     */
    d->declbind = instate_declaration(d, declflag);
    if (LanguageIsCPlusPlus)
    {
        if ((declflag == (TOPLEVEL|SPECIALIZE)) && (curlex_scope != NULL))
        {   tagbindbits_(curlex_scope) |= TB_SPECIALIZED;
            if (isfntype(d->decltype))
                bindstg_(d->declbind) &= ~bitofstg_(s_inline);
        }

        scope_level = push_multi_scope(curlex_scope);
        if (declflag & ANONU)
            instate_anonu_members(declflag, d->declbind);
        if (cppinit)
        {   /* Only happens when (curlex.sym != s_rpar).               */
            ExprList *init = rd_exprlist_opt();
            /* /* overkill for 'const int k(5);' and 'const int& r(k);' */
            dyninit = mkctor_v((Expr *)d->declbind, init);
            initflag = 3;
        }
        else if (!(d->declstg & bitofstg_(s_typedef)) &&
                 (!(d->declstg & bitofstg_(s_extern)) ||
                  d->declstg & b_implicitstg ||
                  curlex.sym == s_assign))
        {   syn_initdepth = 0;
            dyninit = rd_declrhs_exec_cpp(d, &initflag);
        }
    }
    if (initflag == 0 && (curlex.sym == s_assign || archaic_init(curlex.sym)))
    {   haveinit = YES;
        if (d->declstg & (bitofstg_(s_auto)|bitofstg_(s_static)) ||
             (d->declstg & (bitofstg_(s_extern)|b_undef)) ==
                              (bitofstg_(s_extern)))
            initflag = 1;
        else
            cc_err(syn_err_cant_init, d->declstg),
            initflag = 2;

        if (archaic_init(curlex.sym))
            cc_pccwarn(syn_rerr_archaic_init);
        else
            nextsym();
    }
#ifdef CPLUSPLUS
    if (LanguageIsCPlusPlus && !haveinit &&
        !(d->declstg & (b_undef|bitofstg_(s_typedef))))
    {   TypeExpr *t = princtype(d->decltype);
        if (!(isclasstype_(t) || (isarraytype(t, &t) && isclasstype_(t))))
        {
            if (h0_(t) == t_ref)
              cc_rerr(syn_rerr_ref_not_initialised, d->declbind);
            if (qualifiersoftype(d->decltype) & bitoftype_(s_const))
              cc_rerr(syn_rerr_const_not_initialised, d->declbind);
        }
    }
#endif
    if (initflag == 2)
          syn_initdepth = 0, syn_initpeek = 0, (void)syn_rdinit(0,0,4);
    syn_initdepth = (initflag == 1) ? 0 : -1;
    syn_initpeek = 0;
    if (dyninit != NULL && declflag & TEMPLATE && declflag & TOPLEVEL &&
        d->declstg & (bitofstg_(s_extern)|b_implicitstg))
    {   /* file scope template static data member definition */
        if (h0_(dyninit) != s_init) syserr("init expr expected for dyninit");
        bindconst_(d->declbind) = globalize_expr(skip_invisible_or_cast(arg2_(dyninit)));
    }
    else
        declinit_(d) =
            genstaticparts(d, (declflag & TOPLEVEL) != 0, initflag != 1,
                           dyninit);
    add_expr_dtors(killexprtemp());
    if (declinit_(d) != NULL)
        declinit_(d) = exprtemp_killer(declinit_(d));
    /* Missing init expr & non-null edtor can never happen;
       however, genstaticparts() maps a previous error to
       a missing expr. In this case edtor can be safely ignored.
       Moreover, operations involving t_unknown will eventually
       result in errornode to prevent code generation.
     */

    if (declinit_(d)) attributes_(d->declbind) |= A_DYNINIT;
    /* The positioning of the next line is subject to some debate */
    /* -- I put it here so that the line number is exact, but     */
    /* note that (a) TOPLEVEL vars are done in vargen.c,          */
    /* (b) LOCAL vars BLOCKHEAD|FORMAL are not yet complete in    */
    /* that we have not yet decided on their eventual storage;    */
    /* this is done by dbg_scope().  See other dbg_locvar() call. */
    if (usrdbg(DBG_VAR) && (declflag & BLOCKHEAD))
        dbg_locvar(d->declbind, d->fileline);
    if (LanguageIsCPlusPlus)
    {   pop_scope(scope_level);
        if (declflag & TOPLEVEL) gen_reftemps();
    }
    IGNORE(mbind);
}

/* but for its size rd_declrhslist() would be part of rd_decl()
   maybe it will become so anyway!  It reads any of K&R's
  "(last part of undefined category)type-decl-list(see function-body)",
  "init-declarator-list" or "struct-declarator-list"
*/

static bool topfnflag;            /* extra result of rd_declrhslist()   */
static TagBinder *topfnscope;     /* ditto (temp?)                      */
static Symstr *unmangledfnname;   /* ditto, only valid if topfnflag     */
static DeclRhsList *syn_formals;  /* rd_declrhslist()+rd_fndef() only.  */
static ScopeSaver syn_formaltags;

/* A marker for deferred binding of default argument expressions...     */
static Binder deferred_default_arg_expr = {s_binder, 0, 0, 0, A_GLOBALSTORE};

static DeclRhsList *rd_declrhslist(const DeclSpec *ds, const int declflag,
                                   ScopeSaver template_formals)
{   DeclRhsList *p,*q;
    const SET_BITMAP ss = ds->stg; TypeSpec *const tt = ds->t;

    /* note - do NOT change ss, tt or declflag since used in loop below */
    for (p = q = 0; ;)                       /* 3 exits - all 'return's */
    {   DeclRhsList *temp = mkDeclRhsList(0, 0, ss);
        bool cppinit = 0;
        Binder *mbind = 0;                   /* MEMFNBITS */
        NoteCurrentFileLine(&temp->fileline);
        declstgval_(temp) = ds->stgval;
        if ((declflag & MEMBER) && curlex.sym == s_colon)
            temp->decltype = tt;        /* anon. bit field: 0 declaree  */
        /* anon unions only happen when a ';' follows -- invent a name. */
        else if (declflag & ANONU)
            temp->decltype = tt, temp->declname = gensymval(1);
        else
        {   int varlevel = -1;

            if (declflag & TEMPLATE)
                varlevel = push_var_scope(template_formals, Scope_TemplateArgs);
            temp->decltype = rd_declarator(declflag, tt, &ds->fnaux, ds->stg);
            if (declflag & TEMPLATE)
            {   if (declflag & MEMBER || curlex.sym == s_lbrace)
                    pop_scope_no_check(varlevel);
                else
                    pop_scope(varlevel);
            }

            if (temp->decltype == 0)
            {   /* error in rd_declarator already reported */
                if (declflag & TOPLEVEL) bind_scope = TOPLEVEL;
                while (curlex.sym!=s_lbrace && curlex.sym != s_rbrace &&
                       curlex.sym!=s_semicolon && curlex.sym!=s_eof)
                    nextsym();
                if ((declflag & TOPLEVEL) && curlex.sym == s_rbrace) nextsym();
                topfnflag = 0;
                return p;       /* return decls so far to recover */
            }

/* <<< dying */
if (h0_(temp->decltype) == t_coloncolon) syserr("rd_declarator(::)");

            cppinit = declarator_init;
            mbind = declarator_mbinder;
            temp->declname = declarator_name;          /* 2nd result */
            if (!(declflag & TOPLEVEL) &&
                (declarator_qscope != 0) &&
                (!(declflag & MEMBER) ||
                 !(ss & bitofstg_(s_friend)) &&
                 (declarator_qscope != current_member_scope())))
                cc_rerr(syn_rerr_declaree_out_of_scope,
                    declarator_qscope, declarator_name);
        }
        if (declflag & (FORMAL|TFORMAL|ARG_TYPES|CATCHER))
            temp->decltype = modify_formaltype(temp->decltype);
            /* transform f() -> (*f)() and a[] -> *a    */
            /* these get seen by all - even the CG.     */
        defaultstorageclass(temp,declflag, mbind);
/* AM: because f(void) is OK, but not f(void, int), checks on the       */
/* use of 'void' in parameter lists are postponed to rd_formals().      */
/* Other incomplete types (like struct t) are done there too.           */
/* However, it might be nice for early reporting to fault some cases    */
/* here (e.g. named void parameters).  See fault_incomplete_formals().  */
        if (!(declflag & (FORMAL|TFORMAL)) &&
            !(temp->declstg & bitofstg_(s_typedef)))
            temp->decltype = fault_incomplete_type_object(
                 temp->decltype, temp->declname,
                 (declflag & MEMBER) != 0, temp->declstg);
        if (h0_(temp->decltype) == t_fnap)       /* but NOT via typedef */
        {   if ((typeptrmap_(temp->decltype) & CVBITS) &&
                ((mbind != 0) ?
                     (bindstg_(mbind) & b_memfns) :
                       ((temp->declstg & bitofstg_(s_static)) ||
                      !(declflag & MEMBER))))
            {   cc_rerr(syn_rerr_no_quals_allowed);
                typeptrmap_(temp->decltype) &= ~ CVBITS;
            }

            /* see if the fn declaration is a fn definition, we have    */
            /* already (in rd_formals()) changed f(void) to f()         */
            /* Allow also in MEMBER's -- only reach here if CPLUSPLUS   */
            if (declflag & (TOPLEVEL|MEMBER) &&   /* top level or class */
                p == 0 &&                         /* first in list      */
                !(temp->declstg & bitofstg_(s_typedef)) &&
                !cppinit &&
                /* not typedef and suitable following symbol...         */
                /* (CPLUSPLUS use of s_colon.)                          */
                (curlex.sym == s_lbrace ||
                 curlex.sym == s_colon  ||

/* olde-style C "void f(x) type x; {...}":                              */
/* @@@ it would improve error recovery if we refuse extern here.        */
/* Note also that "int A::f() const;" shouldn't come here.              */
                   (declflag & TOPLEVEL &&
                      (rd_type_name(),
                          isdeclstarter2_(curlex)))))
            {   fixup_fndef(temp, mbind);               /* MEMFNBITS    */
                unmangledfnname = temp->declname;
/* move the next few lines to fixup_fndef?                              */
                if (declflag & MEMBER)
                {   Binder *b;
                    ensure_formals_typed(typefnargs1_(temp->decltype), 1);
                    temp->declstg |= bitofstg_(s_inline);
                    b = instate_member(temp, (declflag & TEMPLATE)|bind_scope);
                    temp->declbind = b;                        /* used? */
/* 'b' may either be a Binder for a member function or a realbinder_()  */
/* for a friend (or friend member) function:                            */
                    if (bindstg_(b) & b_impl) b = realbinder_(b);
                    if (h0_(b) != s_binder)
                        syserr("rd_declrhslist(inline $b)", b);
                    temp->declstg &= ~b_undef;
                    temp->declstg |= bindstg_(b) & MEMFNBITS;
                    temp->declname = bindsym_(b);
                    if (declflag & TEMPLATE)
                    {   if (bindformals_(temp->declbind))
                        {   merge_default_template_args(template_formals, NULL, temp->declbind);
                            bindformals_(temp->declbind) = template_formals;
                        } else
                        {   bindformals_(temp->declbind) = template_formals;
                            merge_default_template_args(template_formals, NULL, temp->declbind);
                        }
                    }
                }
                else
                    fault_incomplete_formals(typefnargs1_(temp->decltype), 1);
/* @@@ not yet right for friends??                                      */
                if (mbind) topfnscope = bindparent_(mbind);
                else
                    topfnscope = 0;
                topfnflag = 1;
/* @@@@@@ Why is return (instead of fn call) a good idea here????       */
                return temp;
            }
            /* ANSI C disallows 'extern f(a,b);' (types needed).:       */
            ensure_formals_typed(typefnargs1_(temp->decltype), 1);
            /* drop through into next 'if'... */
        }
#define FNSTGBITS \
            (bitofstg_(s_friend)|bitofstg_(s_inline)|bitofstg_(s_virtual))
        if (isfntype(temp->decltype))           /* possibly via typedef */
            fixup_fndecl(temp, mbind);                  /* MEMFNBITS    */
/* The following two lines anticipate __inline for ANSI C;              */
/* otherwise they would be #ifdef CPLUSPLUS.                            */
        else if (temp->declstg & FNSTGBITS)
        {   cc_rerr(syn_rerr_ignored_non_fn,
                    temp->declstg & FNSTGBITS, temp->declname);
            temp->declstg &= ~FNSTGBITS;
        }
        if (declflag & ARG_TYPES)     /* special code to save up info */
        {   DeclRhsList *p;           /* instate_decl is called later */
            Symstr *sv = temp->declname;
            for (p = syn_formals; p != 0; p = p->declcdr)
                if (sv == p->declname)
                {   merge_formal_decl(p,temp);  /* update syn_formals */
                    break;
                }
            if (p==0) cc_err(syn_err_not_a_formal, sv);
        }
        if (declflag & (TOPLEVEL|BLOCKHEAD))
        {   rd_declrhs_exec(temp, declflag, cppinit, mbind);
            if (declflag & TEMPLATE && temp->declbind)
            {   if (bindformals_(temp->declbind))
                {   merge_default_template_args(template_formals, NULL, temp->declbind);
                    bindformals_(temp->declbind) = template_formals;
                } else
                {   bindformals_(temp->declbind) = template_formals;
                    merge_default_template_args(template_formals, NULL, temp->declbind);
                }
            }
        }

        /* all the same whether type-para or not; needs a holder anyway
           in case there is default.
         */
        if (declflag == TFORMAL && temp->declname == NULL)
            temp->declname = gensymval(YES);

        if ((declflag & (TFORMAL|FORMAL)) && (temp->declname != 0))
        {
            if (declflag & TFORMAL)
            {   if (isprimtypein_(temp->decltype, bitoftype_(s_double)))
                    /* float has been transformed to short double by now? */
                    cc_err(sem_err_temp_type_float);
                /* non-type parameter has no storage */
                if (h0_(temp->decltype) != t_unknown) temp->declstg = 0;
            }
            temp->declbind = instate_declaration(temp,
                 (declflag & TFORMAL) ? declflag|GLOBALSTG : declflag);
        }
        if (LanguageIsCPlusPlus)
        {
            if (declflag & MEMBER && curlex.sym == s_assign)
            {   Expr *e;            /* parse "virtual f() = 0;"             */
                TagBinder *mem_scope = current_member_scope();
                nextsym();
/* if statement below is used rather than ?: due to Watcom C32 v9.5 problem */
                if (curlex.sym == s_lbrace)
                    e = 0;
                else
                    e = rd_expr(UPTOCOMMA);
                if (temp->declstg & bitofstg_(s_virtual) &&
                        e != 0 && ispurefnconst(e))
                {   tagbindbits_(mem_scope) |= TB_ABSTRACT;
                    temp->declstg |= b_purevirtual;
                }
                else
                  cc_err(syn_err_member_cannot_init, temp->declname);
            }

            if (declflag & (TFORMAL|FORMAL) && curlex.sym == s_assign)
            {
              nextsym();
              if (declflag & TFORMAL)
              {   ExprList *a = rd_template_actuals(NO);
                  if (a != NULL && h0_(exprcar_(a)) != s_evalerror)
                  {   Expr *e = globalize_expr(exprcar_(a));
                      if (declflag & TEMPLATE)
                      {   Binder *b;
                          if (!isclasstype_(ds->t))
                              syserr("what sort of template type is this?");
                          b = findbinding(tagbindsym_(typespectagbind_(ds->t)),
                                          NULL, LOCALSCOPES);
                          if (!b) syserr("missing template typedef");
                          bindconst_(b) = e;
                      }
                      else
                      {   if (temp->declbind == NULL) syserr("missing declbind");
                          bindconst_(temp->declbind) = e;
                      }
                  }
              } else {
                Expr *init;              /* parse "void f(int x = 42);" */
                TagBinder *tb;

                ensure_formals_typed(temp, 1);
/* Non-member function default arguments are bound at their point of    */
/* declaration. Member function default arguments are bound at the end  */
/* of the class declaration (by cpp_endstrdecl()). We treat friends as  */
/* members for this purpose... the standard is unclear...               */
                if ((tb = current_member_scope()) == 0 ||
                    !(tagbindbits_(tb) & TB_BEINGDEFD))
                {
/* AM is now of the opinion that the following code (and similar code   */
/* in mkfnap()) to widen_formaltype() is somewhat wrong-minded.         */
/* It means that "void f(char); void g() { f(257); }" is treated        */
/* differently from the similar "char x = 257".  Maybe we should defer  */
/* some of this code to cg.c.                                           */
                    SynBindList *bl = NULL;
                    TypeExpr *t;
                    push_saved_temps(synscopeid);
                    push_exprtemp_scope();
                    init = optimise0(mkcast(s_fnap, rd_expr(UPTOCOMMA),
                                            (t = widen_formaltype(temp->decltype))));
                    add_expr_dtors(killexprtemp());
                    bl = pop_saved_temps(bl);
                    if (init && bl)
                    {   init = (!expr_dtors) ? mk_exprlet(s_let, t, bl, init) :
                            mk_exprlet(s_qualified|s_let, t, bl,
                                       commacons(init, expr_dtors));
                        expr_dtors = NULL;
                        extra_flags = NULL;
                    }
/* Note that optimise0() on the next line means (1) the top-type may    */
/* be incompatible changed (so don't check it again) and moreover that  */
/* (2) optimise0() will get called on it again.  Hmm @@@.               */
/* Add a special 'optimise0'd flag node?                                */
/* optimise0() maps errornode => NULL; moved above                      */
/* LDS: 12-Jul-94 - need to globalize here or disaster can ensue...     */
                    declinit_(temp) = (init) ? globalize_expr(init) : NULL;
                }
                else
/* There are several subtle effects here: 1) we need a hook on which to */
/* to hang the lex token handle; 2) we need an (Expr *) in declinit_()  */
/* so that xbind.c::merge_default_arguments() can work correctly... and */
/* 3) we need to mark this Expr as special (with the Binder *)...       */
                    declinit_(temp) = mkintconst(te_int,
                        lex_saveexpr(), (Expr *)&deferred_default_arg_expr);
              }
            }
        }
/* @@@ the next comment is for old C implementation -- instating        */
/* formals fixes the C bug in 'void f(int a, int (*b)[sizeof a]) {...}  */
/* and instating members is invisible to C.  @@@ It is out of date.     */
        /* do not instate formals (or in casts "(int ()(int a,b))foo")
           nor structure elements. */
        if (declflag & MEMBER)
        {   if (curlex.sym == s_colon)
            {   TypeExpr *t = prunetype(temp->decltype);
/* NB. The code here is most important -- BITFIELD types have any        */
/* typedefs removed with prunetype so that later prunetype/princtype's   */
/* (e.g. isbitfield_type()) do not skip over BITFIELD.                   */
                nextsym();
                /* declbits holds bit size (= new arg to instate_mem?)   */
                declbits_(temp) = check_bitsize(
                            rd_expr(UPTOCOMMA), t, temp->declname);
                temp->decltype = check_bittype(t);
            } else
                declbits_(temp) = NULL;
            temp->declbind = instate_member(temp, (declflag & TEMPLATE)|bind_scope);
            if (declflag & TEMPLATE && isfntype(temp->decltype))
            {   if (bindformals_(temp->declbind))
                {   merge_default_template_args(template_formals, NULL, temp->declbind);
                    bindformals_(temp->declbind) = template_formals;
                }
                else
                {   bindformals_(temp->declbind) = template_formals;
                    merge_default_template_args(template_formals, NULL, temp->declbind);
                }
            }
            if (LanguageIsCPlusPlus && (declflag & ANONU))
                instate_anonu_members(declflag, temp->declbind);
        }
/* The next line loses all local vars/tags at the end of each TOPLEVEL  */
/* declarator.  This is still not quite right, but enables vars/tags    */
/* to be local to (toplevel) parameter lists.  @@@ More fixing required */
/* for parameter lists within parameter lists.                          */
        if (declflag & TOPLEVEL) bind_scope = TOPLEVEL, pop_scope(0);
        if (p == 0) p = q = temp;
        else { q->declcdr = temp; q = temp; }
        if (declflag & (FORMAL|TFORMAL|CATCHER) || curlex.sym != s_comma)
        {   topfnflag = 0;
            return p;
        }
        nextsym();
    }
}

/* AM, Sept 91: memo: too much effort is spent mapping between          */
/* DeclRhsList and FormTypeLists, and Binders.  @@@ Think.              */
/* FormTypeList is now an initial sub-struct of DeclRhsList.            */

static TopDecl *rd_fndef(DeclRhsList *d, int declflag, TagBinder *parent,
          ScopeSaver formaltags, ScopeSaver tformals)
/* d has exactly 1 item */
{   TypeExpr *fntype = d->decltype;        /* known to be fn type */
    Binder *fnbind; Cmd *body = NULL;
    DeclRhsList *fpdecllist = typefnargs1_(fntype), *fpe;
    SynBindList *lambdap = 0, *lambdaq = 0;
    SynBindList *narrowformals = 0;
    Expr *arginit = NULL, *argcopy = NULL;
    Symstr *sv;
    int varlevel = 0, scope_level = 0;
    SynScope *saved_synscope = synscope;
    synscopeid = 0;
    synscope = mkSynScope(0, 0, ++synscopeid);

    sv = currentfunction.symstr = d->declname;
    if (debugging(DEBUG_FNAMES+DEBUG_CG+DEBUG_CSE+DEBUG_REGS+DEBUG_SR))
        cc_msg("Start of function $r\n", currentfunction.symstr);

    if (LanguageIsCPlusPlus)
        scope_level = push_multi_scope(parent);
    else
        IGNORE(parent);
/* The next line re-creates the argument scope -- remember this may not */
/* be the most recently popped scope, e.g. int (*f(int a))(int b){}.    */
/* Actually it just makes a scope for instate_declaration below.        */
/* This needs weasel-word reading of C++ (no class defs in args).       */
    varlevel = push_var_scope(formaltags, Scope_Ord);
/* when ARG_TYPES is set in declflag any identifiers declared will have  */
/* been seen before (as formal parameters) and rd_decllist works by      */
/* updating these existing declaration records in a side-effect-full way */
    bind_scope = GLOBALSTG;              /* local scope for any structs! */
    {   /* syn_formals is examined by rd_declrhslist if ARG_TYPE is set */
        syn_formals = fpdecllist;
        (void) rd_decllist(ARG_TYPES);
    }
#if 0
    if (LanguageIsCPlusPlus)
    {   Symstr *s = d->declname;
        /* We could also do this for declarations...                    */
        if (symname_(s)[0] == '_' &&    /* short cut for usual case.    */
             (s == operator_name(s_assign) ||
              s == operator_name(s_comma) ||
              s == operator_name(s_addrof) &&
                                fpdecllist && !fpdecllist->declcdr))
            cc_warn(syn_warn_special_ops);
            /* See [ES, p335], AM adds last two cases (consistency).    */
    }
#endif
/* do some checking and defaulting on the arguments and types BEFORE
   instate_decl ... */
    for (fpe = fpdecllist; fpe != 0; fpe = fpe->declcdr)
    {   if (fpe->declname == 0)
        {
            if (!LanguageIsCPlusPlus)
                cc_rerr(syn_rerr_missing_formal); /* not an error in C++ */
            /* fixup so we can continue (@@@ soon alter callers)...      */
            fpe->declname = gensymval(1);
        }
        /*if (actualized) fpe->decltype = princtype(fpe->decltype);*/
    }
    ensure_formals_typed(fpdecllist, 0);
/* do the declaration of the function - this will copy the types just
 * updated in fpdecllist as part of globalize_ing the type of d.
 */
  { SET_BITMAP obinduses;
    FileLine fl;
    NoteCurrentFileLine(&fl);
    /* The following pop_scope...() ... push_var_scope() bracketing the */
    /* instate_declaration is needed BOTH for C++ and for correct       */
    /* upscoping of implicitly declared struct tags in argument lists   */
    /* (and not upscoping when the arg scope becomes the body scope).   */
    formaltags = pop_scope_no_check(varlevel);
    fnbind = instate_declaration(d, TOPLEVEL|declflag);

    /* remanant from primary ex-plunged */
    if (declflag == (TOPLEVEL|SPECIALIZE) &&
        !(d->declstg & bitofstg_(s_inline)))
        bindstg_(fnbind) &= ~bitofstg_(s_inline);
    /* @@@ bindscope_(fnbind) = dup_template_scope() */
    if (declflag & TEMPLATE)
    {   if (bindformals_(fnbind))
        {   merge_default_template_args(tformals, NULL, fnbind);
            bindformals_(fnbind) = tformals;
        }
        else
        {   bindformals_(fnbind) = tformals;
            merge_default_template_args(tformals, NULL, fnbind);
        }
        (void) push_var_scope(bindformals_(fnbind), Scope_TemplateArgs);
    }
    push_var_scope(formaltags, Scope_Ord);
    obinduses = binduses_(fnbind);
    if (LanguageIsCPlusPlus)
    {   (void)set_access_context(0, fnbind);
                              /* complete the friend access context */
        if (bindstg_(fnbind) & b_impl) fnbind = realbinder_(fnbind);
        currentfunction.symstr = bindsym_(fnbind);
    }
    if (!(declflag & TEMPLATE) && usrdbg(DBG_PROC+DBG_VAR)) {
#ifndef NEW_DBG_PROC_INTERFACE
        /* Perhaps we ought to extend the dbg_proc() interface */
        bindparent_(fnbind) = parent;
        dbg_proc(bindsym_(fnbind), bindtype_(fnbind),
                 (bindstg_(fnbind) & bitofstg_(s_extern)) != 0, fl);
        bindparent_(fnbind) = NULL;
#else
        dbg_proc(fnbind, parent,
                 (bindstg_(fnbind) & bitofstg_(s_extern)) != 0, fl);
#endif
    }

/* @@@ The following comment about re-using store is now a lie.         */
/* Now, instate_declaration above globalize_d the d->decltype field (since
 * all fns are TOPLEVEL beasties).  This leaves us free to construct a
 * BindList of instated formal parameters from the uncopied (local-store)
 * version fpdecllist above.  Start by instantiating the FORMAL's.
 * This is not so simple as it seems because we have to create new binders
 * (sharing the same name) for any narrow (char, float, short) formals
 * and a widened (int, double) binder too.
 */
    for (fpe = fpdecllist; fpe != 0; fpe = fpe->declcdr)
    {   TypeExpr *at = fpe->decltype, *wt = widen_formaltype(at), *pt;
        Binder *ab, *wb;
        bool byref = NO;
        /* lookup/instate the binder with its original type; swap to  */
        /* wide type later..                                          */
        wb  = findbinding(fpe->declname, 0, FB_LOCALS|FB_THISSCOPE);
        if (wb == 0)
            wb = instate_declaration(fpe, FORMAL);
        else
            bindtype_(wb) = at;
        ab = wb;
        pt = princtype(at);
        if (isclasstype_(pt))
        {   TagBinder *cla = typespectagbind_(pt);
            if (TB_NOTPODU_(cla, TB_NEEDSCCTOR))
            {   /* NOTPOD classes are pased by reference and callee- */
                /* copy constructed...; op= is of no concern here    */
                wt = ptrtotype_(at);
                byref = YES;
            }
        }
        if (wt != at)            /* pointer equality is fine here */
        {   Expr *e = (Expr *)wb;
            bindtype_(wb) = wt;
            if (byref) e = mkunary(s_content, e);
#ifndef NARROW_FORMALS_REUSE_ARG_BINDER
            binduses_(wb) |= u_referenced;
          {  DeclRhsList *narrowedformal = mkDeclRhsList(fpe->declname, at,
                                  fpe->declstg);
            /* do the original binder second so it gets seen first */
            ab = instate_declaration(narrowedformal, FORMAL|DUPL_OK);
            narrowformals = mkSynBindList(narrowformals, ab);
          }
#endif
            /* make a (reverse) list of copy-constructed arguments    */
            /* which need to be destroyed on scope exit...            */
            if (byref) synscope->car = mkSynBindList(synscope->car, ab);

            /* now narrow types which have been widenend and copy-    */
            /* construct class types passed by reference...           */
            /* (separately, to ensure that all narrowing comes first  */
            /* to make inlining calls to the function easier (all     */
            /* narrowing in the first block).                         */
            e = mkbinaryorop(s_init, (Expr *)ab,
                    mkcast(s_cast, e, bindtype_(ab)));
            if (byref)
                argcopy = argcopy ? mkbinary(s_comma, argcopy, e) : e;
            else
                arginit = arginit ? mkbinary(s_comma, arginit, e) : e;
        }

        if (fpe == fpdecllist && bindstg_(fnbind) & bitofstg_(s_virtual))
            /* Flag 'this' used in virtual member fn (implicit use).  */
            binduses_(ab) |= u_referenced;

        if (!LanguageIsCPlusPlus && !HasFeature(Feature_Predeclare))
            /* preclude any whinge about unused fn args */
            /* Allow whinges in C++ since formal names are omittable. */
            binduses_(ab) |= u_referenced;

        if (fpe == fpdecllist) instate_alias(first_arg_sym, wb);
        if (fpe->declcdr == 0) instate_alias(last_arg_sym, wb);
        /* The positioning of the next line is subject to some debate */
        /* note that (a) TOPLEVEL vars are done in vargen.c,          */
        /* (b) LOCAL vars BLOCKHEAD|FORMAL are not yet complete in    */
        /* that we have not yet decided on their eventual storage;    */
        /* this is done by dbg_scope().  See other dbg_locvar() call. */
        /* Further debate whether the user wishes to see the wide     */
        /* (i.e. entry) arg (wb), which is unchanging, or the narrow, */
        /* updatable arg (ab) which is not valid on entry.            */
        if (usrdbg(DBG_VAR))
        {   dbg_locvar(ab, fl);
        }
        if (lambdap == 0) lambdap = lambdaq = mkSynBindList(0,wb);
        else lambdaq = lambdaq->bindlistcdr = mkSynBindList(0,wb);
    }
    if (syn_reftemps != NULL) syserr("syn_reftemps/rd_fndef");
    if (argcopy != NULL)
        arginit = (arginit != NULL) ? mkbinary(s_comma, arginit, argcopy) :
                                      argcopy;
    {   Cmd *argstuff = arginit==0 ? 0 :
            mk_cmd_e(s_semicolon, syn_invented_fl, optimise0(arginit));
        Cmd *precmd = 0, *postcmd = 0;
        Expr *edtor = 0;
        Cmd *meminit = 0;
        SynBindList *initreftemps = 0;
        bool is_ctor = LanguageIsCPlusPlus
            && strncmp(symname_(bindsym_(fnbind)), "__ct", 4) == 0;
        bool is_dtor = LanguageIsCPlusPlus
            && strncmp(symname_(bindsym_(fnbind)), "__dt", 4) == 0;

        if (LanguageIsCPlusPlus)
/* @@@ we should pass 0 to rd_meminit if not a ctor (bit in bindstg_).  */
        {   TypeExpr *arg1t = bindstg_(fnbind) & b_memfna && lambdap ?
                                  bindtype_(lambdap->bindlistcar) : te_int;
            TypeExpr *arg1s = h0_(arg1t)==t_content ? typearg_(arg1t) : te_int;
            TagBinder *cl = isclasstype_(arg1s) ? typespectagbind_(arg1s) : 0;
            int has_core = (attributes_(fnbind) & CB_CGEN) &&
                           (cl != 0 && core_class(cl) != cl);

            synscope = mkSynScope(synscope, 0, ++synscopeid);
            meminit = rd_meminit(cl, fnbind, lambdap, &precmd, &postcmd);
            initreftemps = synscope->car;
            if (is_dtor)
            {   push_exprtemp_scope();
                edtor = syn_memdtor(cl, fnbind, lambdap, &precmd);
                add_expr_dtors(killexprtemp());
                if (expr_dtors != NULL)
                    syserr("genexprtemp() used by memdtor");
            }
            if (synscope->car != initreftemps) syserr("genreftemp() used by memdtor");
            synscope = synscope->cdr;
            synscopeid = synscope->scopeid;
            if (has_core) fnbind = realbinder_(fnbind);
        }

        bind_scope = LOCALSCOPE;
        /* @@@ Warn about templated main?? What does the std say?*/
        if (declflag == (TEMPLATE|TOPLEVEL) && bindsym_(fnbind) != mainsym)
            (void)lex_bodybegin();
        body = rd_body(typearg_(fntype), fntype, is_ctor, is_dtor);
        if (declflag == (TEMPLATE|TOPLEVEL) && bindsym_(fnbind) != mainsym)
        {   bindtext_(fnbind) = lex_bodyend();
#if 0
                /* CD2, 14.5.5, para 2 last sentence footnote explicitly
                   prohibit the implicit generation of non-template overloaded
                   function. */
                Binder *bgeneric = findbinding(sv, 0, ALLSCOPES);
                bool has_failed = NO;
                TypeExpr *t;
                BindList *bl;
                int len = length((List *)typefnargs_(bindtype_(fnbind)));
                ScopeSaver env;
                if (bgeneric == NULL || h0_(bindtype_(bgeneric)) != t_ovld)
                    syserr("No generic $r", sv);
                /* first, any b_undef ovld instance requiring instantiation */
                for (bl = typeovldlist_(bindtype_(bgeneric)); bl; bl = bl->bindlistcdr)
                {   Binder *b = bl->bindlistcar;
                    FormTypeList *ft = typefnargs_(bindtype_(b));
                    int len2 = length((List *)ft);
                    ExprList *l = NULL;

                    if (!(bindstg_(b) & b_undef) || len != len2) continue;
                    for (; ft; ft = ft->ftcdr)
                        l = mkExprList(l, gentempbinder(ft->fttype));
                    env = bindenv_(fnbind);
                    t = type_deduction(bindtype_(fnbind), dreverse(l), NULL, &env,
                                       YES, &has_failed);
                    /* For an ovld instance, make sure it's an exact match. */
                    if (!has_failed) has_failed = !equivtype(t, bindtype_(b));
                    if (!has_failed && !contains_typevars(t) &&
                        (bindstg_(b) & (b_addrof|u_referenced)) &&
                        /* check for non template function specific */
                        !is_an_instance(bindinstances_(fnbind), b))
                    {   if (debugging(DEBUG_TEMPLATE))
                            cc_msg("generating $r @ $b\n", bindsym_(fnbind), b);
                        env = globalize_env(env);
                        fixup_template_arg_type(t, env);
                        t = globalize_typeexpr(t);
                        /* @@@ unstructured */
                        bindtype_(b) = t;
                        bindenv_(b) = env;
                        parameter_names_transfer(typefnargs_(d->decltype),
                                                 typefnargs_(bindtype_(b)));
                        add_pendingfn(sv, NULL, bindtype_(b), bindstg_(b), NULL,
                                      bindenv_(b), bindtext_(fnbind), YES);
                        bindstg_(b) &= ~b_undef;
                    }
                }
#endif
                /* then, instantiates for all b_undef instances */
                if (binduses_(fnbind) & u_referenced)
                {   BindList *instances = bindinstances_(fnbind);
                    for (; instances; instances = instances->bindlistcdr)
                    {   Binder *b = instances->bindlistcar;
                        int level = push_var_scope(bindformals_(b), Scope_TemplateArgs);
                        bool has_typevar = contains_typevars(bindtype_(b));
                        pop_scope_no_check(level);
                        if (has_typevar) continue;
                        parameter_names_transfer(typefnargs_(d->decltype),
                                                 typefnargs_(bindtype_(b)));
                        add_pendingfn(sv, ovld_tmptfn_instance_name(d->declname, bindenv_(b)),
                                      bindtype_(b), bindstg_(b), NULL, NULL, bindtext_(fnbind),
                                      bindenv_(b), YES);
                        bindstg_(b) &= ~b_undef;
                        if (debugging(DEBUG_TEMPLATE))
                            cc_msg("generating $r @ $b\n", bindsym_(fnbind), b);
                    }
                }
        }
        bind_scope = TOPLEVEL;

        if (LanguageIsCPlusPlus)
        {   Expr *bdtor = mkdtor_v_list(synscope->car);
            if (bdtor)
            {   cmd2c_(body) = (Cmd *) nconc((CmdList *)cmd2c_(body),
                    mkCmdList(0, mk_cmd_e(s_semicolon, fl, optimise0(bdtor))));
            }
            if (meminit)
            {   Expr *idtor = mkdtor_v_list(initreftemps);
                CmdList *cdtor = idtor == NULL ? 0 :
                    mkCmdList(0, mk_cmd_e(s_semicolon, fl, optimise0(idtor)));
                body = mk_cmd_block(syn_invented_fl, initreftemps,
                            mkCmdList(mkCmdList(cdtor, body), meminit));
            }
            if (precmd)
                body = mk_cmd_block(fl, 0,
                   mkCmdList(mkCmdList(0, body), precmd));
            if (is_dtor)
            {   LabBind *lab = label_define(dtorgenlabsym);
                if (lab != NULL)  /* not a duplicate label */
                {   Cmd *edtorcmd;
                    syn_setlab(lab, synscope);
                    lab->labuses |= l_referenced; /* suppress warning if unused */
                    /* just what is the right FileLine for a dtor?              */
                    edtorcmd = mk_cmd_lab(s_colon, syn_invented_fl, lab,
                                               edtor != NULL ?
                                                   mk_cmd_e(s_semicolon, fl, optimise0(edtor)) :
                                                   NULL);
                    body = mk_cmd_block(syn_invented_fl, 0,
                                        mkCmdList(mkCmdList(0, edtorcmd), body));
                }
                if (!(tagbindbits_(parent) & TB_HASVBASE))
                {   /* if this class has a core we are actually building the core dtor */
                    Cmd *cdel =
                        conditionalised_delete(lambdap->bindlistcar,
                                               lambdap->bindlistcdr->bindlistcar,
                                               parent);
                    body = mk_cmd_block(fl, 0,
                                        mkCmdList(mkCmdList(0, cdel), body));
                }
            }
            if (postcmd)
                body = mk_cmd_block(fl, 0,
                               mkCmdList(mkCmdList(0, postcmd), body));
        }
        if (argstuff)
            body = mk_cmd_block(syn_invented_fl, narrowformals,
                                mkCmdList(mkCmdList(0,body), argstuff));
    }
    label_resolve();
    pop_scope(scope_level);
    if (synscope->cdr != 0) syserr("rd_fndef/synscope");
    synscope = saved_synscope;
    if (saved_synscope != 0) synscopeid = saved_synscope->scopeid;

/* Remove recursive references.  One day improve to consider the whole   */
/* of the call graph so unreferenced mutually recursion is warned of.    */
    binduses_(fnbind) &= ~(~obinduses & u_referenced);
    if (declflag & TEMPLATE)
    {   DeclRhsList *d = mkDeclRhsList(bindsym_(fnbind), bindtype_(fnbind), 0);
        d->declbind = fnbind;
        return (TopDecl *) syn_list2(s_decl, d);
    } else
/* h4_(result) is a flag to indicate the presence of an ellipsis in      */
/* the list of formal arguments for this function.                       */
        return mkTopDeclFnDef(s_fndef, fnbind, lambdap, body,
        /*
         * Beware !!!. In PCC mode all functions are considered as
         * Having a trailing '...'.  This is activated by the
         * code in cg.c which checks whether the address of ANY of the
         * args has been taken.  If so all args go to stack !!!
         */
#ifdef TARGET_HAS_SPECIAL_VARARGS
        fntypeisvariadic(fntype)
#else
        (fntypeisvariadic(fntype) || (lambdap!=0) && HasFeature(Feature_PCC))
#endif
        );
  }
}

static ScopeSaver globalize_formaltags(ScopeSaver l)
{   Binder *h = (Binder *)l;
    if (h == 0) return 0;
    bindcdr_(h) = (Binder *)globalize_formaltags((ScopeSaver)bindcdr_(h));
    if (h0_(h) == s_binder)
        h = global_mk_binder(bindcdr_(h), bindsym_(h), bindstg_(h),
                             globalize_typeexpr(bindtype_(h)));
    return (ScopeSaver)h;
}

/* rd_decl reads a possibly top-level decl, see also rd_decl2()       */
static TopDecl *rd_decl(int declflag, SET_BITMAP accbits)
/* AM: Structure decls are tantalisingly close to ordinary decls (but no
   storage class) except for length specs replacing initialisation.
   Type specs are compulsory for structure members, but not for
   vars (e.g. auto a=1;).
   Read them all them with a single parameterised routine.
   Note that 'accbits' is or-able with declstg_() (non-zero if MEMBER).
   @@@ Feb 93: It is in a different bit position from in attributes_()!!!
*/
{
    DeclRhsList *d;
    DeclSpec ds;
    int declsynflags;
    ScopeSaver template_formals = NULL;
    FileLine fl;
    NoteCurrentFileLine(&fl);

    if (curlex.sym == s_asm && peepsym() == s_lpar)
    {   Expr *e;
        if (declflag == TOPLEVEL)
            cc_err(syn_err_illegal_asm_decl);
        push_exprtemp_scope();
        e = rd_asm_decl();
        add_expr_dtors(killexprtemp());
        if (expr_dtors != NULL)
            syserr("exprtemp in asm decl");
        if (declflag == TOPLEVEL)
            return (TopDecl *)errornode;
        d = mkDeclRhsList(gensymval(0), te_int, bitofstg_(s_auto));
        declinit_(d) = e;
        d->declbind = gentempbinder(te_int);
        return (TopDecl *) syn_list2(s_decl, d);
    }
    if (LanguageIsCPlusPlus)
    {   if (declflag & (TOPLEVEL|BLOCKHEAD|MEMBER))
            cur_template_formals = NULL;
        if (curlex.sym == s_using) {
          do nextsym(); while (curlex.sym != s_semicolon);
          return (TopDecl *)errornode;
        }
        if (curlex.sym == s_export && peepsym() == s_template)
        {   cc_warn("$l ignored for template");
            nextsym();
        }
        while (curlex.sym == s_template)
        {   nextsym();
            if (curlex.sym == s_less)
            {   ScopeSaver tmp_temp_formals = NULL;
                if (declflag & INSTANTIATE)
                    cc_rerr(xsyn_rerr_instantiate_mixup);
                nextsym();
                tmp_temp_formals = rd_template_formals();
                if (template_formals == NULL)
                    template_formals = tmp_temp_formals;
                else
                {   Binder *t = template_formals;
                    while (bindcdr_(t) != NULL) t = bindcdr_(t);
                    bindcdr_(t) = tmp_temp_formals;
                }
                cur_template_formals = binder_cons2(cur_template_formals,
                                                    tmp_temp_formals);
                declflag |= (tmp_temp_formals != NULL) ? TEMPLATE : SPECIALIZE;
            }
            else
            {   if (declflag & (TEMPLATE|SPECIALIZE))
                    cc_rerr(xsyn_rerr_instantiate_mixup);
                else
                {   if (declflag & INSTANTIATE)
                        cc_rerr(xsyn_rerr_spurious_instantiate);
                    declflag |= INSTANTIATE;
                }
            }
        }
        cur_template_formals = (BindList *)dreverse((List *)cur_template_formals);
    }
    ds = rd_declspec(declflag, template_formals);
    if (fpregargs_disabled) ds.fnaux.flags |= f_nofpregargs;
    if (no_side_effects) ds.fnaux.flags |= bitoffnaux_(s_pure);
    if (no_tail_calls) ds.fnaux.flags |= f_notailcall;
    ds.stg |= accbits;          /* merge in access bits if C++ MEMBER   */
    declsynflags = ds.synflags; /* local copy of error check bits.      */

    if (declflag & TFORMAL && declsynflags & B_IMPLICITINT)
    {   declsynflags &= ~B_IMPLICITINT;
        ds.t = mk_typevar();
        declsynflags |= B_TYPESEEN;
    }

    /* extern "C" is ignored for typedefs and statics */
    if (LanguageIsCPlusPlus &&
            !(ds.stg & (bitofstg_(s_typedef)|bitofstg_(s_static))) &&
            syn_current_linkage() == LINK_C)
        ds.stg |= b_clinkage;
    if (LanguageIsCPlusPlus && declsynflags & B_LINKAGE)
    {   if (declsynflags & B_LINKBRACE)
            d = 0;              /* treat 'extern "x" {' as empty decl.  */
        else
        {   /* The 'extern "C" typedef int foo();' form. Push back an   */
            /* 'extern'.  We could just dd.stg |= bitofstg_(s_extern)   */
            /* but we need to fault things like 'extern "C" static ...'.*/
            TopDecl *dd;
            ungetsym();
            curlex.sym = s_extern;
            dd = rd_decl(TOPLEVEL, 0);
            syn_pop_linkage();
            return dd;
        }
    }
    else
  { if (curlex.sym == s_semicolon && !(declflag & (FORMAL|TFORMAL)) ||
        curlex.sym == s_rbrace    && (declflag & MEMBER))
    {   /*
         * Found an empty declaration or an empty declaration within a
         * struct or union in which the terminating ';' has been omitted.
         */
        TypeExpr *t = ds.t;         /* no 'princtype(ds.t)'         */
        if (LanguageIsCPlusPlus &&
            declflag & MEMBER && ds.stg & bitofstg_(s_friend))
        {   if (!isclasstype_(t)) t = princtype(t);
            if (isclasstype_(t))
            {   if (t != ds.t && !HasFeature(Feature_CFront))
                    cc_rerr(syn_err_friend_type);
                mk_friend_class(typespectagbind_(t), current_member_scope());
            }
            else
                cc_err(syn_err_friend_type);
                /* (and not 'enum foo' either, but let's not say this!) */
        }
        else if (LanguageIsCPlusPlus &&
                 declflag & (MEMBER|BLOCKHEAD|TOPLEVEL) &&
                 !(ds.stg & bitofstg_(s_typedef)) &&
                 isprimtype_(t, s_union) &&
                 isgensym(bindsym_(typespectagbind_(t))) &&
                 tagbindmems_(typespectagbind_(t)) != NULL)
        {   if (declflag & TOPLEVEL && !(ds.stg & bitofstg_(s_static)))
            {   cc_rerr(syn_rerr_global_anon_union);
                ds.stg = ds.stg & ~STGBITS | bitofstg_(s_static);
            }
            declflag |= ANONU;
            goto anonu;
        }
        else if ((declflag & TEMPLATE) &&
                !(isclasstype_(t) ||
                  (!(ds.stg & bitofstg_(s_typedef)) && isfntype(t))))
                cc_rerr(syn_err_template_notclassorfunction);
        else if (!(declsynflags & B_DECLMADE))
        {   if (LanguageIsCPlusPlus)
              cc_warn(syn_rerr_ineffective);
            else
              cc_pccwarn(syn_rerr_ineffective);
        }
        else
        {   if (declsynflags & B_STGSEEN)
                /* e.g. "static struct A {};".                          */
                /* harder error in C++?                                 */
                cc_warn(syn_warn_storageclass_no_declarator);
            /*
             * Here we have just got a new struct/union/enum tag
             * so let's tell the debugger about it, lest it never
             * finds out about it until its too late.
             */
            if (usrdbg(DBG_PROC)) dbg_type(gensymval(1), ds.t, fl);
        }
        d = 0;
    }
    else
anonu:      /* what a horrible place to put a label!                    */
    {   TagBinder *parent = current_member_scope();
        syn_formaltags = 0;             /* overzealous safety           */
        d = rd_declrhslist(&ds, declflag, template_formals);
        if (d != 0)
        {   d->fileline = fl;
            if (d->declstg & bitofstg_(s_friend) && !template_formals &&
                d->declbind && is_dependent_type(d->decltype) &&
                tagbindbits_(parent) & TB_TEMPLATE)
                bindformals_(d->declbind) = tagformals_(parent);
        }

        if (declflag == (TOPLEVEL|SPECIALIZE) && parent != NULL)
            tagbindbits_(parent) |= TB_SPECIALIZED;

        if (topfnflag)
        {   /* NB. it is vital that when topfnflag is set on return     */
            /* from rd_declrhslist we must soon pop_varenv/tagenv.      */
            /* This has to be done after reading the body due to ANSI   */
            /* scope joining of formals and body top block.             */
            if (d == NULL) syserr("rd_decl: no top fn");
            if (HasFeature(Feature_PCC) && !(declflag & MEMBER))
                implicit_return_ok = syn_oldeformals;
            if (!(declsynflags & (B_TYPESEEN|B_STGSEEN)) ||
                ((LanguageIsCPlusPlus || !(suppress & D_FUTURE)) &&
                 (declsynflags & B_IMPLICITINT)))
            {   if (LanguageIsCPlusPlus)
                {   if (cpp_special_member(d)) { /* nothing */ }
                    else if (suppress & D_IMPLICITINT)
                        cc_warn(syn_warn_untyped_fn, d->declname);
                    else
                        cc_rerr(syn_warn_untyped_fn, d->declname);
                }
                else if (suppress & D_IMPLICITVOID)
                {   xwarncount++;
/* The next line allows us also to suppress 'implicit return' warning   */
/* in f(){}.                                                            */
                    implicit_return_ok = 1;
                }
                else
                    cc_warn(syn_warn_untyped_fn, d->declname);
            }
            if (LanguageIsCPlusPlus && (declflag & MEMBER))
            {   if (tagprimary_(parent) != NULL && !(declflag & TEMPLATE) &&
                    !(tagbindbits_(parent) & TB_SPECIALIZED))
                {   if (d->declstg & bitofstg_(s_friend))
                    {   bool done = NO;
                        int braces = 0;
                        /* waste the inline friend defn */
                        while (!done)
                            switch (curlex.sym)
                            {   case s_lbrace: braces++;
                                default:       nextsym(); break;
                                case s_rbrace: if (--braces == 0) done = YES; else nextsym();
                                               break;
                            }
                    }
                    else {
                        /* parent is an instantiation. */
                        /* could share the body of the counterpart in the primary except */
                        /* for name substitution during an instantiation.                */
                        /* @@@ virtual fns may have to be generated immediately */
                        add_memfn_template(parent,
                                           d->declname,
                                           NULL,
                                           globalize_typeexpr_no_default_arg_vals(d->decltype),
                                           /* @@@ Suppress inlining maybe morally wrong; but
                                              ANSI permits since it is only a hint. */
                                           d->declstg & ~bitofstg_(s_inline),
                                           parent,
                                           /* @@@ the next line gets the wrong bindings in  */
                                           /*   int (*f(int a))(int b)                      */
                                           /* and probably if 'a' had a sizeof(struct defn).*/
                                           /* This only affects (C++ illegal) arg-declared  */
                                           /* classes currently.                            */
                                           globalize_formaltags(syn_formaltags),
                                           lex_savebody(),
                                           bindformals_(d->declbind));
                        /* Forgery */
                        bindstg_(d->declbind) |= b_undef;
                        d->declstg |= b_undef;
                    }
                }
                else
                {   int h = lex_savebody();
                    ScopeSaver env = NULL;
                    bool is_template = (tagbindbits_(parent) & TB_TEMPLATE) ? YES : NO;
                    if (declflag & TEMPLATE || (d->declstg & bitofstg_(s_friend) &&
                                                bindformals_(d->declbind)))
                    {
                        Binder *ftemp = (d->declstg & bitofstg_(s_friend)) ?
                                         (parent = NULL, d->declbind) :
                                         findbinding(bindsym_(d->declbind), parent,
                                                     INCLASSONLY);
                        if (ftemp == 0)
                            syserr("missing member/friend template $r", bindsym_(d->declbind));
                        bindtext_(ftemp) = h;
                        if (!(d->declstg & bitofstg_(s_friend)))
                            bindstg_(ftemp) &= ~b_undef;
                        env = bindformals_(ftemp);
                        is_template = YES;
                    }
                    add_pendingfn((d->declstg & MEMFNBITS) ? d->declname : unmangledfnname,
                                  NULL,
                                  globalize_typeexpr_no_default_arg_vals(d->decltype),
                                  d->declstg,
                                  parent,
                                  /* @@@ the next line gets the wrong bindings in  */
                                  /*   int (*f(int a))(int b)                      */
                                  /* and probably if 'a' had a sizeof(struct defn).*/
                                  /* This only affects (C++ illegal) arg-declared  */
                                  /* classes currently.                            */
                                  globalize_formaltags(syn_formaltags),
                                  h, env, is_template);
                }
                curlex.sym = s_nothing;
                /* Just pretend all is sweetness and light 'til later:  */
                return (TopDecl *) syn_list2(s_memfndef, d);
            }
            return rd_fndef(d, declflag, topfnscope,
                            syn_formaltags, template_formals); /* d != 0 by fiat */
        }

/* ANSI C requires a complaint at top level for "*x;", but not "*f(){}" */
/* This message is a little late, but cannot occur 'on time'.           */
/* C++: we might want to warn about more implicit int fns:              */
/*      e.g. friend f(); virtual g(); static h();                       */
        if ((!(declsynflags & (B_TYPESEEN|B_STGSEEN)) ||
             ((LanguageIsCPlusPlus || !(suppress & D_FUTURE)) &&
              (declsynflags & B_IMPLICITINT))) &&
            !((declflag & FORMAL) && is_untyped_(d->decltype)) &&
            !HasFeature(Feature_PCC))
        {   DeclRhsList *x = d;
/* the case d==0 has already been reported by rd_declarator/DeclRhslist */
            bool complained = false;
            bool have_needs_type = false;
            Symstr *first_no_implict_int = NULL;
            for (; x != NULL; x = x->declcdr)
            {
/* Don't moan about missing type for ctors/dtors/conversion functions   */
/* (the test for this should be handled by some form of attribute flag).*/
/* And only warn of omitted type/stgclass for member functions.         */
/* errors: 'x, *y, f(), *g();' 'struct { x, *y, f(); };'                */
/* warnings from elsewhere: 'f() {} struct { g() {} };'                 */
/* ok (silent): 'struct T { T(); ~T(); operator int(); };'              */
                bool needs_type = x->declname == NULL || !cpp_special_member(x);
                if (needs_type)
                {   have_needs_type = true;
                    if (first_no_implict_int == NULL)
                        first_no_implict_int = x->declname;
                }
                if (LanguageIsCPlusPlus && (declflag & MEMBER))
                {   if (needs_type)
                    {
#if CFRONT_MODE_WARN_LACKS_STORAGE_TYPE
                        /* Cfront allows any member function decl       */
                        /* to have implicit int return type.  But the   */
                        /* Newton sources do not need this.             */
                        if (isfntype(x->decltype) && HasFeature(Feature_CFront))
                            cc_warn(syn_warn_lacks_storage_type, x->declname);
                        else
#endif /* CFRONT_MODE_WARN_LACKS_STORAGE_TYPE */
                            if (suppress & D_IMPLICITINT)
                                cc_warn(syn_warn_lacks_storage_type, x->declname);
                            else
                                cc_rerr(syn_warn_lacks_storage_type, x->declname);
                        complained = true;
                    }
                }
                else if (!(declsynflags & (B_TYPESEEN|B_STGSEEN)))
                {   cc_rerr(syn_warn_lacks_storage_type, x->declname);
                    complained = true;
                }
            }
            if (!complained && have_needs_type && (declsynflags & B_IMPLICITINT))
            {   if (LanguageIsCPlusPlus && !(suppress & D_IMPLICITINT))
                {   if (first_no_implict_int != NULL)
                        cc_rerr(syn_rerr_missing_type_for, first_no_implict_int);
                    else
                        cc_rerr(syn_rerr_missing_type);
                }
                else if (LanguageIsCPlusPlus || !(suppress & D_FUTURE))
                {   if (first_no_implict_int != NULL)
                        cc_warn(syn_rerr_missing_type_for, first_no_implict_int);
                    else
                        cc_warn(syn_rerr_missing_type);
                }
            }
        }
    }
    if (!(declflag & (FORMAL|TFORMAL|CATCHER)))
    {
      if (!HasFeature(Feature_PCC) || curlex.sym != s_rbrace)
        checkfor_delimiter_2ket(s_semicolon, s_comma);
    }
  }
    return (TopDecl *) syn_list2(s_decl, d);
}

/* rd_decl2() reads a 'decl-specifiers-opt declarator-list;' decl.      */
/* 'declflag' is FORMAL, TFORMAL, BLOCKHEAD, ARG_TYPES or CATCHER.      */
static DeclRhsList *rd_decl2(int declflag, SET_BITMAP accbits)
{   TopDecl *d;

    if (curlex.sym == s_asm && declflag != BLOCKHEAD)
        cc_err(syn_err_illegal_asm_decl);
    d = rd_decl(declflag, accbits);
    if (declflag & BLOCKHEAD)
    {   DeclRhsList *dp = d->v_f.var;
        for (; dp; dp = dp->declcdr)
            if (dp->declbind)
                synscope->car = mkSynBindList(synscope->car, dp->declbind);
    }
    if (h0_(d) != s_decl)
        syserr(syserr_rd_decl2, d, (long)h0_(d));
    return d->v_f.var;
}

/* rd_formals_2() is only used once in rd_formals_1().  It behaves      */
/* very much like rd_decllist, but different concrete syntax.           */
/* It copes with both ANSI and olde-style formals (and now C++).        */
/* @@@ sort out the 999/1999 confusion.                                 */
static DeclRhsList *rd_formals_2(void)
{   DeclRhsList *p,*q,*temp;
    if (curlex.sym == s_rpar)
    {
       if (LanguageIsCPlusPlus)
           syn_minformals = 0, syn_maxformals = 0, syn_oldeformals = 0;
       else
           syn_minformals = 0, syn_maxformals = 999, syn_oldeformals = 1;
       return 0;
    }
    for (p = q = 0;;)
    {   if (curlex.sym == s_ellipsis)
        {
            if (!LanguageIsCPlusPlus && p == 0)
                cc_rerr(syn_rerr_ellipsis_first);
            fault_incomplete_formals(p,0);
            nextsym();
/* @@@ what about int f(int x, int y = 2, ...)?                         */
/* Answer f(1), f(1,3), f(1,3,4) all OK.                                */
            syn_minformals = length((List *)p);
            syn_maxformals = 1999;      /* @@@ remove the 999/1999 hack */
            syn_oldeformals = !is_proto_arglist(p,1);
            return p;    /* to checkfor_ket(s_rpar) */
        }
        if (LanguageIsCPlusPlus) chk_for_auto = YES;
        temp = rd_decl2(FORMAL, 0);
        if (LanguageIsCPlusPlus) chk_for_auto = NO;
        if (curlex.sym == s_nothing) nextsym();
        for (; temp != 0; temp = temp->declcdr)
        {   if (debugging(DEBUG_BIND))
                cc_msg(" Formal: $r\n", temp->declname);
            if (p == 0) p = q = temp; else q->declcdr = temp, q = temp;
        }
        if (LanguageIsCPlusPlus && curlex.sym == s_ellipsis)
            continue;    /* can omit comma  */
        else
        /* all that should legally appear here are ',' and ')', but fix    */
        /* ';' as ',' a la pascal and treat all other symbols as ')' to be */
        /* faulted by the caller (rd_declarator_1()).                      */
        if (curlex.sym == s_semicolon)   /* error recovery */
            cc_rerr(syn_rerr_semicolon_in_arglist);
        else if (curlex.sym != s_comma)
        {   /* arg list end, but first check for ANSI  "(void)" argument list
             * and remove it.  Note that "f(void) {}" is also OK by ANSI
             * if somewhat curious.
             */
            bool b = is_proto_arglist(p,0);
            if (p != 0 && p->declcdr == 0 &&                /* 1 parameter */
                p->declname == 0 &&                         /* no name     */
                isprimtype_(p->decltype, s_void))     /* void (or typedef) */
#if 0
              /* was    equivtype(p->decltype, te_void) */
#endif
                    p = 0;                            /* then clear arglist */
            fault_incomplete_formals(p,0);
            syn_maxformals = length((List *)p);
            syn_minformals = length((List *)p);
            syn_oldeformals = !b;
            return p;
        }
        nextsym();
    }
}

static Declarator *rd_formals_1(Declarator *a, const DeclFnAux *fnaux)
{   int old_bind_scope = bind_scope;
    int scope_level = push_scope(0, Scope_Args);
    SET_BITMAP quals = 0;
    DeclRhsList *f;
    TypeExprFnAux s;
    Declarator *d;
    if (bind_scope == TOPLEVEL) bind_scope = GLOBALSTG;    /* @@@ nasty */
    f = rd_formals_2();
    bind_scope = old_bind_scope;
/* @@@ beware: this gets tags from the wrong scope in things like       */
/* void (*f(struct a { } x))(struct b { } y);   Banned in C++ anyway.   */
    syn_formaltags = pop_scope_no_check(scope_level);
    checkfor_2ket(s_rpar, s_comma);
/* careful with C++ archaism: int f(x) const int *x; { ... }            */
    if (LanguageIsCPlusPlus && !syn_oldeformals) {
      quals = rd_onceonlyquals(CVBITS);
      rd_exception_spec();
    }
/* @@@ beware that ANSI disallow the use of pragma's which change         */
/* semantics -- those for printf requesting extra warnings are ok, but    */
/* not those like 'no_side_effects' which can screw code.                 */
              /* extra results for minargs_(), maxargs_()... */
    d = mkTypeExprfn(t_fnap, a, quals, (FormTypeList *)f,
                    packTypeExprFnAux1(s, (int)syn_minformals,
                                         (int)syn_maxformals,
                                         (int)special_variad,
                                         syn_oldeformals,
                                         fnaux->flags,
                                         fnaux->val));
    if (fntypeisvariadic(d)) typefnaux_(d).flags |= f_nofpregargs;
    return d;
}

static DeclRhsList *rd_decllist(int declflag)
/* reads a list of Decls and NCONC's them togther.  Used for struct/union
   elements, type specs after formal lists, rd_block().  NB:  It should not
   be used when TOPLEVEL is set as it does not look for functions.
   It should not be used either when MEMBER is set (no 'accbits' facility).
   Identical to rd_formals modulo concrete syntax - unify???
   Note the Symstr's may be 0 (abstract), or s_id.
*/
{   DeclRhsList *p,*q,*temp;
    p = q = 0;
    while (rd_type_name(),
           (declflag & BLOCKHEAD ? isdeclstarter3_(curlex) : isdeclstarter2_(curlex)))
    {   if (curlex.sym == s_typestartsym) nextsym();
        temp = rd_decl2(declflag, 0);
        if (curlex.sym == s_nothing) nextsym();
        for (; temp != 0; temp = temp->declcdr)
        {   if (p == 0) p = q = temp; else q->declcdr = temp, q = temp;
            if (debugging(DEBUG_BIND)) cc_msg(" Identifier: $r", q->declname);
        }
    }
    return p;
}

static void rd_strdecl(TagBinder *b, ClassMember *bb)
{   int nameseen = 0;
    int old_bind_scope = bind_scope;
    access = tagbindbits_(b) & bitoftype_(s_class) ? s_private : s_public;

    if (LanguageIsCPlusPlus)
    {   if (bind_scope == TOPLEVEL) bind_scope = GLOBALSTG;    /* @@@ nasty */
    /* the next line is a bit of a hack -- it enables findclassmember   */
    /* to work while reading members.  See cppfe.c.bind("p209").        */
    /* See also 'derived_from' below.                                   */
        tagbindmems_(b) = bb;
    }
  { int scope_level = push_scope(b, Scope_Ord);
    TagBinder *old_access = set_access_context(b, 0);
    for (;;)
    {
        if (isaccessspec_(curlex.sym))
        {   access = curlex.sym;
            nextsym();
            checkfor_ket(s_colon);
            continue;           /* class A { public: private: }; is OK. */
        }
        rd_type_name();
        if (LanguageIsCPlusPlus
            && (curlex.sym == s_qualified+s_identifier ||
                curlex.sym == s_qualified+s_pseudoid)
            && (peepsym()==s_semicolon || peepsym()==s_comma
                                       || peepsym()==s_rbrace))
        {
            rd_access_adjuster(b, access);
        }
        else if (isdeclstarter2_(curlex)
/* Additional C++ (odd!) ways for a member declaration to start...      */
/* ... since the 'type' info is optional (sigh):                        */
            || (curlex.sym & ~s_qualified) == s_identifier
            || (curlex.sym & ~s_qualified) == s_pseudoid
            || curlex.sym == s_lpar
            || curlex.sym == s_bitnot
            || (curlex.sym & ~s_qualified) == s_times
            || curlex.sym == s_and
            || curlex.sym == s_colon            /* e.g. class A{:32};   */
            || curlex.sym == s_semicolon
            || curlex.sym == s_template)
        {   TopDecl *td; DeclRhsList *d;
            if (curlex.sym == s_typestartsym) nextsym();
            td = rd_decl(MEMBER, stgaccof_(access));
/* using the DeclRhsList from rd_decl is now deprecated (we should      */
/* really look in tagbindmems_(b) to make nameseen).                    */
            if (td == 0 || !(h0_(td) == s_decl || h0_(td) == s_memfndef))
                syserr(syserr_rd_decl2, td, (long)(td==0 ? 0 : h0_(td)));
            for (d = td->v_f.var; d != 0; d = d->declcdr)
                nameseen |= d->declname != NULL ? 2 : 1;
            if (curlex.sym == s_nothing) nextsym();
/* Optional semicolon after member function definition:                 */
            if (h0_(td) == s_memfndef && curlex.sym == s_semicolon) nextsym();
        }
        else break;
    }
    if (LanguageIsCPlusPlus) cpp_end_strdecl(b);
    pop_scope(scope_level);
    (void)set_access_context(old_access, 0);
    if (LanguageIsCPlusPlus) bind_scope = old_bind_scope;
    switch (nameseen)
    {
case 1: cc_warn(syn_warn_no_named_member, b); break;
case 0: if (!LanguageIsCPlusPlus) cc_rerr(syn_rerr_no_members, b); break;
    }
  }
}

static void rd_classdecl_(TagBinder *b)
{   if (LanguageIsCPlusPlus)
    {   TagBinder *class_scope = syn_class_scope;
        syn_class_scope = b;
        rd_classdecl(b);
        syn_class_scope = class_scope;
    }
    else
    {   nextsym();
        rd_strdecl(b, NULL);
    }
}

/* rd_enumdecl() works very much like rd_decllist() or rd_strdecl() but the
   different surface syntax leads me to implement it separately.
   Syntax is taken from Harbison&Steele.
   ANSI draft means 'int' implementation of 'enum's.
   This doesn't yet handle C++ enums that need to be long or unsigned long
   (only happens when sizeof_int < sizeof_long).
*/

static void rd_enumdecl(TagBinder *tb)
{   TypeExpr *t = tagbindtype_(tb);
    BindList *p = 0, *q = 0;
    int32 nextenumval = 0;
    int32 minval = 0, maxval = 0;
    bool has_neg = NO, needs_unsigned = NO, is_non_neg = YES;
    nextsym();

    if (curlex.sym == s_comma && HasFeature(Feature_CFront))
    {   cc_warn(syn_warn_extra_comma);
        nextsym();
    }
    if (!LanguageIsCPlusPlus ||  /* Can't have empty enumerations in C */
        curlex.sym != s_rbrace)
    /* """""""""""""""""""""""" */ for (;;)
    {   if (curlex.sym == s_identifier)
        {   Symstr *sv = curlex.a1.sv; Expr *e = 0; Binder *b;
            DeclRhsList *temp = mkDeclRhsList(sv, t, b_enumconst);
            nextsym();
            if (curlex.sym == s_assign)
            {   nextsym();
                e = optimise0(coerceunary(rd_expr(UPTOCOMMA)));
            }
/* @@@ AM: fixup 16 bit ints here too.                                  */
            if (e != 0)
            {   bool ok = NO;
                if (h0_(e) == s_int64con) {
                    uint32 u;
                    if (!(int64map_(e) & bitoftype_(s_unsigned))) {
                        int32 n;
                        if (I64_SToI(&n, &int64val_(e).i) == i64_ok) {
                            nextenumval = n;
                            ok = YES;
                            is_non_neg = n >= 0;
                        }
                    }
                    if (!ok && I64_UToI(&u, &int64val_(e).u) == i64_ok) {
                        nextenumval = u;
                        ok = YES;
                        is_non_neg = YES;
                    }
                }
                if (!ok) {
                    nextenumval = evaluate(e);
                    is_non_neg =
                       (h0_(e) == s_integer &&
                        typespecmap_(princtype(type_(e))) & bitoftype_(s_unsigned) ||
                        nextenumval >= 0);
                }
            }
/* bind_scope is set so that all enum consts are globalized except in fns */
/* The following instate_declaration can behave like instate_member?!     */
            /* In case of an instantiation, make it global (better still at the
               same scope as the primary).
             */
            b = instate_declaration(temp, (tagparent_(tb) != NULL &&
                                           tagprimary_(tagparent_(tb)) != NULL) ?
                                    bind_scope|GLOBALSTG : bind_scope);
            binduses_(b) |= u_referenced;
            bindparent_(b) = tagparent_(tb);
            attributes_(b) |= bitofaccess_(access);
            if (nextenumval < 0)
            {   if (is_non_neg)
                {   if (LanguageIsCPlusPlus)
                    {   needs_unsigned = YES;
                        /* we need to set the container type right away in case */
                        /* of 'enum { k1 = ~0u, k2 = k1 | 1 };'                 */
                        tagbindbits_(tb) =
                            (tagbindbits_(tb) & ~TB_CONTAINER) | TB_CONTAINER_UINT;
                    }
                    else
                    {   is_non_neg = NO;        /* only one error.      */
                        cc_rerr(sem_rerr_monad_overflow(s_enum,0,0));
                    }
                }
                else
                    has_neg = YES;
            }
            if (p == 0)
                minval = maxval = nextenumval;
            else {
                if (nextenumval < minval) minval = nextenumval;
                if (nextenumval > maxval) maxval = nextenumval;
            }
            bindaddr_(b) = nextenumval++;
/* BEWARE: reuse of DeclRhsList to hold ClassMember...                  */
/* @@@ this code is most odd and probably should be discouraged.        */
/* It forges a ClassMember list of enum consts.                         */
/* Maybe we should just return a list of binders for them.              */
/* (or discourage the debugger from needing this info in this form).    */
            {   BindList *bl = bind_scope & (TOPLEVEL|GLOBALSTG) ?
                                 (BindList *)global_cons2(SU_Type, NULL, b) :
                                 mkBindList(NULL, b);
                if (p == 0) p = q = bl; else q->bindlistcdr = bl, q = bl;
            }
        }
        else
        {   cc_err(syn_err_enumdef);
            while (curlex.sym != s_rbrace && curlex.sym != s_eof) nextsym();
        }
        if (curlex.sym != s_comma) break;
        nextsym();
        if (curlex.sym == s_rbrace)
        {   if (HasFeature(Feature_CFront) || HasFeature(Feature_PCC))
                cc_warn(syn_warn_extra_comma);
            else cc_rerr(syn_warn_extra_comma);
            break;
        }
    }
    if (has_neg && needs_unsigned)
        cc_rerr(syn_rerr_neg_unsigned_enum, tb);
    tagbindbits_(tb) = (tagbindbits_(tb) & ~TB_BEINGDEFD) | TB_DEFD;
    tagbindenums_(tb) = p;

    {   SET_BITMAP container;
        if (needs_unsigned)
            container = TB_CONTAINER_UINT;
        else if (HasFeature(Feature_EnumsAlwaysInt))
            container = TB_CONTAINER_INT;
        else if (minval >= 0)
            container = maxval < (1 << 8) ?             TB_CONTAINER_UCHAR :
      /* @@@ using TB_CONTAINER_USHORT here seems worse than
         TB_CONTAINER_SHORT -- signed shorts are sometimes cheaper to extract */
               maxval < (1 << (8 * sizeof_short)) ?     TB_CONTAINER_USHORT :
      /* it doesn't seem like the choice between TB_CONTAINER_UINT and
         TB_CONTAINER_INT makes any real difference for C */
               LanguageIsCPlusPlus ?                    TB_CONTAINER_INT :
                                                        TB_CONTAINER_UINT;
        else
        {   if (-minval-1 > maxval) maxval = -minval-1;
            container = maxval < (1 << (8-1)) ?         TB_CONTAINER_CHAR :
               maxval < (1 << (8 * sizeof_short - 1)) ? TB_CONTAINER_SHORT :
                                                        TB_CONTAINER_INT;
        }
        tagbindbits_(tb) = (tagbindbits_(tb) & ~TB_CONTAINER) | container;
    }
}


static bool eof_done;

/* Exported: ONLY syn_init() and rd_topdecl().
   Calling conventions: call lex_init() first.  Then call rd_topdecl()
   until it returns { s_eof }.
*/

TopDecl *rd_topdecl(bool returneof)
{   TopDecl *d;
    TagBinder *old_access_context = set_access_context(NULL, NULL);

#ifndef NO_MLS_XDEVT_1823
/*
* move the progress from cfe/pp/pp_fillbuf() to reduce overhead
 */
    UpdateProgress();
#endif


    if (LanguageIsCPlusPlus)
    {   if (syn_reftemps != 0) syserr("syn_reftemps confused");
    }
    implicit_return_ok = 0;      /* for junky old C programs         */
#ifdef EXTENSION_VALOF
    inside_valof_block = 0;
    valof_block_result_type = (TypeExpr *) DUFF_ADDR;
    cur_restype = 0;             /* check for valof out of body      */
#endif
    if (LanguageIsCPlusPlus && syn_generatedfns)
    {   TopDecl *fd = syn_generatedfns->d;
        Mark* mark = syn_generatedfns->mark;
        if (usrdbg(DBG_PROC+DBG_VAR))
        {   Cmd *body = fd->v_f.fn.body;
            Binder *b = fd->v_f.fn.name;
            body->fileline.p = dbg_notefileline(body->fileline);
#ifndef NEW_DBG_PROC_INTERFACE
            dbg_proc(bindsym_(b), bindtype_(b), 0, body->fileline);
#else
            dbg_proc(b, NULL, 0, body->fileline);
#endif
        }
/* There is NEVER a struct result from a generated function...         */
/* Generated fns include: ctors, dtors, operator=()s and the compiler- */
/* portions of user-defined constructors/destructors.                  */
        currentfunction.structresult = 0;
        syn_generatedfns = cdr_(syn_generatedfns);
        alloc_unmark(mark);
        if (debugging(DEBUG_FNAMES+DEBUG_CG+DEBUG_CSE+DEBUG_REGS+DEBUG_SR))
          cc_msg("Generated function $b\n", fd->v_f.fn.name);
        return fd;
    }
    if (LanguageIsCPlusPlus && syn_pendingfns)
    {   TopDecl *fd;
        TagBinder *memscope = syn_pendingfns->pfscope;
        ScopeSaver formaltags = syn_pendingfns->pf_formaltags,
            tformals = syn_pendingfns->pf_templateformals;
        DeclRhsList *d;
        int instantiatescope = 0, varlevel = 0;
        int h = syn_pendingfns->pf_toklist_handle;

        /*
          Template fn:
                                                memscope        pf_templateforamls   cg
                                                --------        ------------------   --
          template class memfn                    YES &&             NO              NO
                                                    TB_TEMPLATE
          non-template class template memfn       YES                YES             NO
          template class template memfn           YES                YES             NO

          Instantiate:
          top-level                               NO                 YES             YES
          (non-)template class memfn              YES                YES             YES
         */

        bool parse_only = (memscope && (tagbindbits_(memscope) & TB_TEMPLATE)) ||
                          has_template_parameter(syn_pendingfns->pf_templateformals);

        if (memscope)
        {   if (tagbindbits_(memscope) & TB_TEMPLATE)
                varlevel = push_var_scope(tagformals_(memscope), Scope_TemplateArgs);
            else if (tagactuals_(memscope))
            {   /*if (!tagscope_(memscope)) syserr("weird template $c", memscope);*/
                instantiatescope = push_var_scope(tagscope_(memscope),
                                                  Scope_TemplateDef);
                (void) push_var_scope(tagactuals_(memscope), Scope_TemplateArgs);
            }
        }

        d = reinvent_fn_DeclRhsList(
                             syn_pendingfns->pfname,
                             syn_pendingfns->pfrealname,
                             syn_pendingfns->pftype,
                             syn_pendingfns->pfstg);
        if (syn_pendingfns->pfstg & b_memfna)
            memfn_typefix(d, memscope);
/* @@@ re-read [ES] to see if pfscope should include outermore scopes!  */
/* Perhaps we should setup access in push_multi_scope()?                */
/* The next line is OK for within-class friend DEFNS: it sets no access */
/* context, but friends are listed separately for access control.       */
        (void)set_access_context(memscope, NULL);
        lex_openbody(h, syn_pendingfns->pf_tfn, NO, NULL, NULL);
        syn_pendingfns = syn_pendingfns->pfcdr;
        fd = rd_fndef(d, (parse_only) ? TEMPLATE : TOPLEVEL, memscope, formaltags,
                      tformals);
        if (memscope)
        {   if (tagbindbits_(memscope) & TB_TEMPLATE)
                pop_scope_no_check(varlevel);
            else if (tagactuals_(memscope))
                pop_scope_no_check(instantiatescope);
            if (parse_only)
            {   if (h0_(fd) != s_decl || (fd->v_f.var)->declbind == NULL)
                    syserr("Top level template member fn $r lost",
                           (fd->v_f.var)->declname);
                bindtext_((fd->v_f.var)->declbind) = h;
            }
        }
        lex_closebody();
        (void)set_access_context(old_access_context, NULL);
        return fd;
    }

/* No pending functions, so read from input file...                     */
    if (curlex.sym == s_nothing) nextsym();
    for (;;)
    {   while (curlex.sym == s_toplevel) nextsym();
        if (LanguageIsCPlusPlus && syn_linkage != 0) switch (curlex.sym)
        {
case s_eof:     cc_err(syn_err_linkage_spec);
                /* drop through to effect insertion... */
case s_rbrace:  syn_pop_linkage(); nextsym();
                continue;
        }
        break;
    }
    if (curlex.sym == s_eof)
    {   static TopDecl eofdecl = { s_eof };
        if (LanguageIsCPlusPlus) {
            if (!returneof)
            {   (void)set_access_context(old_access_context, NULL);
                if (!eof_done) eof_done = YES, dbg_final_src_codeaddr(codebase, codep);
                if ((d = vg_dynamic_init()) != NULL)
                {
                    if (debugging(DEBUG_FNAMES+DEBUG_CG+DEBUG_CSE+DEBUG_REGS+DEBUG_SR))
                        cc_msg("Function $b\n", d->v_f.fn.name);
                    return d;
                }
            }
        } else
            dbg_final_src_codeaddr(codebase, codep);
        return &eofdecl;
    }
    if (curlex.sym == s_lbrace)  /* temp for ACN - rethink general case */
                                 /* @@@ and especially for C++ linkage! */
    {   cc_err(syn_err_misplaced_brace);
        (void)push_scope(0, Scope_Ord);    /* helps recovery */
        (void)rd_body(te_int, NULL, NO, NO);/* this will also skip initialisers */
        label_resolve();            /* tidy up in case declarations */
        pop_scope(0);
        if (LanguageIsCPlusPlus) (void)set_access_context(old_access_context, NULL);
        return (TopDecl *)errornode;
    }
    d = rd_decl(TOPLEVEL, 0);
    (void)set_access_context(old_access_context, NULL);
    curlex.fl.p = dbg_notefileline(curlex.fl);
    return d;
}

void syn_init(void)
{   bind_scope = TOPLEVEL;
    synscope = 0;
    initpriovec();
    expr_dtors = 0;
    extra_flags = 0;
    if (LanguageIsCPlusPlus)
    {   syn_reftemps = NULL;
        syn_pendingfns = 0;
        syn_generatedfns = 0;
        syn_linkage = syn_linkage_free = 0;
        (void)set_access_context(NULL, NULL);   /* no access context yet... */
        syn_class_scope = 0;
        cur_template_formals = 0;
        cur_template_actuals = 0;
        eof_done = NO;
    }
    curlex_member = NULL;
    xsyn_init();
}

/* End of cfe/syn.c */
