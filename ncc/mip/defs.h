/*
 * defs.h: front-end to cg interface.
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Codemist Ltd., 1987-1992.
 * Copyright (C) Advanced RISC Machines Limited, 1991-1992.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$ Codemist 130
 * Checkin $Date$
 * Revising $Author$
 */

/*
 * This file defines the set of data structures which constitute the
 * interface between a language-specific front-end and the code generator.
 * The set of structures is not yet minimal - some embedded comments point
 * to possible improvements.
 *
 * A similar file - cgdefs.h - defines structures which are global to the
 * code generator but hidden from front-ends. More private structures are
 * defined, perhaps opaquely, in individual module headers.
 *
 * Our intentions are good, but the execution of them is not yet perfect.
 *
 * General Convention: macros of the form foo_(x) are understood to be
 * access functions. Names with trailing underscores are used for no other
 * purpose. The names of access functions always end with an '_'.
 *
 * Some structures - e.g. Symstr and FloatCon - have trailing string fields
 * which are described as being of length [1]. These are actually allocated
 * as large as required to hold the relevant null-terminated value.
 */

#ifndef _defs_LOADED
#define _defs_LOADED 1

#include "ieeeflt.h"
#include "int64.h"

/* The following lines allow the precise details of C++ scope rules     */
/* to be ignored.  Consider  'struct A { struct B *c; }'                */
/* where B is undefined or 'struct A { struct C{} *c; };'.  IF C++      */
/* really means that structs are SCOPE's then struct B (and its typedef */
/* should not be exported from scope A.  gcc seems to export B/C!       */
/* By pre-declaring we create the struct at top level, not inside A.    */
typedef struct Binder Binder;
typedef struct LabBind LabBind;
typedef struct TagBinder TagBinder;
typedef struct ExtRef ExtRef;
typedef struct Cmd Cmd;
typedef struct SynBindList SynBindList;
typedef struct LabelNumber LabelNumber;
typedef struct BindList BindList;
typedef struct Handler Handler;
typedef struct FormTypeList FormTypeList;
typedef struct SynScope SynScope;
typedef struct SynGoto SynGoto;
typedef struct DeclRhsList DeclRhsList;

/*
 * List is a generic list type of general utility.
 */
typedef struct List { struct List *cdr; IPtr car; } List;
#define cdr_(p) ((p)->cdr)
#define car_(p) ((p)->car)

/*
 * List3 is used in some back-ends as an extended version of the existing
 * List2 datastructure but where extra informaton is needed - the only
 * case at the tim this note was written was for long-format forward
 * references where the extra field is used to cope with some ugly
 * issues about relocating 32-bit forward references where too many
 * offsets seem needed for the original structures. (ACN Feb '90)
 */
typedef struct List3 { struct List *cdr; IPtr car; IPtr csr; } List3;

/* The following two lines are IPtrs, not int32 because they are either */
/* abused (e.g. cast to pointer in aetree.c) or for storage layout      */
/* like an AEop h0_() field.                                            */
typedef IPtr       AEop;        /* An AEop is implemented as an integer */
#define SET_BITMAP IPtr         /* ... as are small sets... */

/*
 * Sometime the type VRegnum should be made into a union or some such that
 * can not accidentally be punned with an int32.
 */
typedef IPtr VRegnum;          /* a pity this has to be here, but... */

#ifndef NON_CODEMIST_MIDDLE_END
/*
 * NMAGICREGS is defined here as whatever length integer comes out
 * of the arithmetic shows.  This is intended to allow it to be a
 * preprocessor-available constant, whereas putting in a cast to (int32)
 * would mean that #if NMAGICREGS < ..  etc would be illegal.
 * NANYARGREGS is useful as an array size (e.g. per-argument register info).
 * It is (harmlessly) overlarge if TARGET_FP_ARGS_CALLSTD2.
 */
#ifdef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
#define NMAGICREGS  NINTREGS
#define NANYARGREGS NARGREGS
#else
#define NMAGICREGS  (NINTREGS+NFLTREGS)
#define NANYARGREGS (NARGREGS+NFLTARGREGS)
#endif

typedef struct RealRegSet
{
    unsigned32 map[(NMAGICREGS+31)/32];
} RealRegSet;

#endif

/*
 * A TypeExpr is the basic, generic node of a type expression tree.
 * The first field - called h0 for historical reasons - is a discriminator
 * which determines the fine structure of the node.
 * @@@ AM would like to swap typespecmap_ and typespecbind_ one day.
 */
typedef struct TypeExprFnAux
{  unsigned16 minargs, maxargs;
   unsigned8 variad, oldstyle;      /* notionally bool */
   unsigned32 flags;
   int32 inlinecode;
} TypeExprFnAux;

/* flags bits are bitoffnaux_() bits (0x3F), together with ... */
typedef int FnAuxFlags;
#define f_resultinflags   0x800
#define f_resultinintregs 0x400
#define f_notailcall      0x200
#define f_specialargreg   0x100
#define f_nofpregargs     0x080
#define f_norettype       0x040

#define fntypeisvariadic(t) (maxargs_(t)==1999) /* could do with improvement */

/*
 * packTypeExprFnAux also sets the usedregs field to describe that ALL
 * registers are clobbered.  A more refined value is set when/if the
 * function gets defined.  Codemist + LDS agree this must be re-organised.
 */

#define packTypeExprFnAux1(s,mina,maxa,var,old,fl,il) \
  (s.minargs=mina, s.maxargs=maxa, s.variad=((var)<0 ? 0:(var)), \
   s.oldstyle=old, s.flags=fl, s.inlinecode = il, \
   &s)
#define packTypeExprFnAux(s,mina,maxa,var,old,fl) \
        packTypeExprFnAux1(s,mina,maxa,var,old,fl,0)

typedef struct TypeExpr TypeExpr;
typedef struct Expr Expr;

struct TypeExpr                 /* make into a better union type */
{ AEop h0;
  union {
    TypeExpr *t;
    SET_BITMAP m;               /* for s_typespec */
  } typearg;
  union {
    Binder *b;
    TagBinder *tb;              /* for struct / union */
    BindList *bl;               /* ovldlist */
    SET_BITMAP m;               /* ptrmap */
    Expr *e;                    /* subsize */
  } typespecbind;
  IPtr dbglanginfo;            /* dbx support requires f77 type info */
#ifdef PASCAL /*ECN*/
  union {
    TypeExpr *type;
    Expr *e;
  } pun;
#endif
  union {
    FormTypeList *ftl;
    DeclRhsList *rhl;
  } fnargs;         /* only if t_fnap                */
  TypeExprFnAux fnaux;          /* only if t_fnap                */
};

/*
 * TypeExpr access functions
 */

#define typearg_(p)         ((p)->typearg.t)
#define typespecmap_(p)     ((p)->typearg.m)
#define typespecbind_(p)    ((p)->typespecbind.b)
#define typespectagbind_(p) ((p)->typespecbind.tb)
#define typefnargs_(p)      ((p)->fnargs.ftl)
#define typefnargs1_(p)     ((p)->fnargs.rhl)
#define typeovldlist_(p)    ((p)->typespecbind.bl)
#define typeptrmap_(p)      ((p)->typespecbind.m)
#define typesubsize_(p)     ((p)->typespecbind.e)
/* And the following apply only to function TypeExprs... */
#define typefnaux_(p)       ((p)->fnaux)
#define typedbginfo_(p)     ((p)->dbglanginfo)
#define minargs_(p)         ((p)->fnaux.minargs)
#define maxargs_(p)         ((p)->fnaux.maxargs)
#define typefnauxflags_(p)  ((p)->fnaux.flags)
#define TypeSpec TypeExpr   /* used when known to be a s_typespec TypeExpr */

/*
 * A Symstr is a symbol table entry. Symstr's can be overloaded - i.e. can
 * have several definitions - e.g. as a variable name, as a structure field,
 * as a label. The 3 'overloading classes' (pointing to Binders of one kind
 * or another) are explicitly represented.
 */
typedef struct Symstr Symstr;
struct Symstr {
  AEop h0;             /* keyword or s_identifier. Must be first field */
  Symstr *symchain;             /* linear list of hash bucket members  */
  /* The 4 overloading classes... */
  Binder  *symbind;             /* variable name, function name etc.   */
  LabBind *symlab;              /* definition as a label               */
  TagBinder *symtag;            /* structure, union, enumeration tag   */
  ExtRef *symext;               /* Data about use as an external sym   */
  Symstr *symfold;              /* for 6 char monocase extern check    */
             /* may one day allocate within *symext to save space here */
  char  symname[1];             /* Text name... allocated as needed    */
};
/*
 * Symstr access functions
 */
#define symchain_(sym)      ((sym)->symchain)
#define symtype_(sym)       ((sym)->h0)
#define sympp_(sym)         ((sym)->sympp)
#define symlab_(sym)        ((sym)->symlab)
/* #define symtag_(sym)        ((sym)->symtag)        @@@ under threat */
#define symext_(sym)        ((sym)->symext)
#define symfold_(sym)       ((sym)->symfold)
/* #define symdata_(sym)       ((sym)->bindglobal)    @@@ under threat */
#ifdef CALLABLE_COMPILER
#define symname_(sym)       ((sym)->symname + 1)
#else
#define symname_(sym)       ((sym)->symname)
#endif
#define bind_global_(sym)   ((sym)->symbind)
#define tag_global_(sym)    ((sym)->symtag)

#if defined(CALLABLE_COMPILER)
#define dbgbinder_(sym)     (*(Binder **)&((sym)->symext))
#endif
/*
 * String literals in ANSI-C are naturally segmented, so the code
 * generator is prepared to handle segmented string values.
 */
typedef struct StringSegList StringSegList;
struct StringSegList
{ StringSegList *strsegcdr;
  char *strsegbase;
  IPtr strseglen;
};

typedef struct String
{ AEop h0;
  StringSegList *strseg;
} String;

typedef struct FloatCon {
  AEop h0;                      /* the type discriminator for the union */
  SET_BITMAP floatlen;
  union {
    int32 irep[2];              /* so asemblers can print hex patterns */
    DbleBin db;
    FloatBin fb;
  } floatbin;
  char floatstr[1];             /* the source representation - if there  */
} FloatCon;                     /* is one (consider x = 1.0 + 2.0, which */
                                /* has none) - allocated as needed.      */
typedef struct {
  AEop h0;
  SET_BITMAP typespec;
  union {
    int64 i;
    uint64 u;
  } bin;
} Int64Con;

/* MiniFileLine structures are used to describe source file positions in
 * support of detailed assembler output, and potentially debugger table
 * generation. They are stored inside an Icode so want it to be smaller.
 * Could become an anonymous member of FileLine, in C11...
 */
typedef struct {
    const char *f;
    unsigned16 l;
    unsigned16 column;
} MiniFileLine;

/*
 * FileLine structures are used to describe source file positions and
 * in support of debugger table generation. Essentially, a FileLine can
 * associate a file name and position with any object.
 * Notionally, p should be of type struct dbg_... *.
 */
typedef struct FileLine {
  char const *f;                /* The source file name */
  unsigned16 l;                 /* Source file line number */
  unsigned16 column;            /* position within line */
  int32 filepos;                /* source file byte offset */
  VoidStar p;
} FileLine;

typedef List ExprList;          /* a list of Exprs is a List... */
/*
 * exprcar: ExprList -> Expr    -- extract an Expr from an Expr list element
 * mkExprList: ExprList x Expr -> ExprList -- add an Expr to an ExprList
 */
#define exprcar_(l)            (*(Expr **)&(l)->car)
#define mkExprList(a,b)        ((ExprList *)syn_cons2(a,b))
#define mkExprList1(x)         (mkExprList(0,x))
#define mkExprList2(x,y)       (mkExprList(mkExprList(0,y),x))
#define mkExprList3(x,y,z)     (mkExprList(mkExprList(mkExprList(0,z),y),x))
#define mkExprList4(x,y,z,a)   (mkExprList(mkExprList3(y,z,a),x))
#define mkExprList5(x,y,z,a,b) (mkExprList(mkExprList4(y,z,a,b),x))

typedef List CmdList;           /* a list of commands is a List... */
/*
 * cmdcar: CmdList -> Cmd       -- extract a Cmd from a Cmd list element
 * mkCmdList: CmdList x Cmd -> CmdList -- add a Cmdr to a CmdList
 */
#define mkCmdList(a,b)      ((CmdList *)syn_cons2(a,b))
#define cmdcar_(l)          (*(Cmd **)&(l)->car)

/*
 * A node of an expression tree is an Expr...
 * (or a FloatCon or Int64Con or String or Binder)
 */
struct Expr {
  AEop h0;                      /* node type, discriminates unions */
  TypeExpr *etype;
  FileLine *fileline;           /* only a small subset of Exprs want this */
  union {
      Expr *e;                  /* as in expr :: unop exprr...   */
      Cmd *c;                   /* for valof expressions...      */
      SynBindList *bl;          /* for expr :: (let t; f(t,...)) */
      IPtr i;                   /* h0==s_integer; expr = intval  */
  } arg1;
  /* Fields from here on are optional any may not even be allocated.      */
  union {
      Expr *e;                  /* e.g. expr :: expr binop expr, */
                                /* & const expr yielding arg1.i  */
      ExprList *l;              /* as in expr :: f(expr,expr...) */
      IPtr i;                   /* as in expr :: expr dot intval */
  } arg2;
  union {
      Expr *e;                  /* eg ?-expr :: expr expr expr...*/
                                /*   (as in (e1 ? e2 : e3))      */
      IPtr i;                   /* for bitfields, intval bitsize */
  } arg3;
  IPtr msboff;                  /* for bitfields, ms bit offset  */
};
/*
 * And the Expr access functions...
 */
#define type_(p)            ((p)->etype)
#define arg1_(p)            ((p)->arg1.e)
#define arg2_(p)            ((p)->arg2.e)
#define arg2i_(p)           ((p)->arg2.i)
#define arg3_(p)            ((p)->arg3.e)
#define arg3i_(p)           ((p)->arg3.i)
#define exprletbind_(p)     ((p)->arg1.bl)
#define exprfnargs_(p)      ((p)->arg2.l)
#define exprdotoff_(p)      ((p)->arg2.i)
#define exprbsize_(p)       ((p)->arg3.i)
#define exprmsboff_(p)      ((p)->msboff)
#define expr1c_(p)          ((p)->arg1.c)
#define exprfileline_(p)    ((p)->fileline)
/* for integer constants */
#define intval_(p)          ((p)->arg1.i)
#define intorig_(p)         arg2_(p)

#define exb_(e)             ((Binder *)(e))
#define exs_(e)             ((String *)(e))
#define exi64_(e)           ((Int64Con *)(e))
#define exf_(e)             ((FloatCon *)(e))

#define int64map_(e)        (exi64_(e)->typespec)
#define int64val_(e)        (exi64_(e)->bin)

#ifdef TARGET_HAS_INLINE_ASSEMBLER

typedef struct AsmInstr {
    struct AsmInstr *cdr;
    FileLine fl;
    IPtr opcode;
    Expr *opnd1, *opnd2, *opnd3, *opnd4;
} AsmInstr;

#define asmopcode_(p)       ((p)->opcode)
#define asmfl_(p)           ((p)->fl)
#define asmopnd1_(p)        ((p)->opnd1)
#define asmopnd2_(p)        ((p)->opnd2)
#define asmopnd3_(p)        ((p)->opnd3)
#define asmopnd4_(p)        ((p)->opnd4)

#endif

#define handcdr cdr
struct Handler {
  Handler *handcdr;
  SynBindList *handbl;
  Cmd *handbody;
  TypeExpr *caught_type;
};
#define mkHandler(a,b,c,d)  ((Handler *)syn_list4(a,b,c,d))

/*
 * The other essential object the code generator recognises is a Cmd,
 * which represents a command or statement. The structure is very flexible
 * and is designed to represent any C abstract syntax command.
 */
struct Cmd {
  AEop h0;                      /* The node type and union discriminator */
  FileLine fileline;            /* File, line, and code address hook...  */
  union {                       /* Then up to four component Cmd/Exprs...*/
      Cmd *c;                   /* Consider, for example, the C 'for':-  */
      Expr *e;                  /* for-cmd :: expr expr expr cmd         */
  } cmd1, cmd2, cmd3, cmd4;     /* (for (e1; e2; e3) stmnt;)             */
};
/*
 * Cmd structure access functions...
 */
#define cmd1c_(x)           ((x)->cmd1.c)
#define cmd2c_(x)           ((x)->cmd2.c)
#define cmd3c_(x)           ((x)->cmd3.c)
#define cmd4c_(x)           ((x)->cmd4.c)
#define cmd1e_(x)           ((x)->cmd1.e)
#define cmd2e_(x)           ((x)->cmd2.e)
#define cmd3e_(x)           ((x)->cmd3.e)
#define cmd4e_(x)           ((x)->cmd4.e)
#define cmdfileline_(x)     ((x)->fileline)

/*
 * And some more convenient syntactic sugaring, which hints how other
 * structures such as case labels, labels, and blocks.
 */
#define cmd1lab_(c)         ((LabBind *)cmd1c_(c))
#define switch_caselist_(c) cmd3c_(c)
#define switch_default_(c)  cmd4c_(c)
#define case_next_(c)       cmd3c_(c)
#define case_lab_(c)        ((LabelNumber *)cmd4c_(c))
#define cmdblk_bl_(c)       ((SynBindList *)cmd1c_(c))
#define cmdblk_cl_(c)       ((CmdList *)cmd2c_(c))
#define cmdhand_(c)         ((Handler *)cmd2c_(c))

/*
 * LabBinds describe source-level labels (e.g. 'out' in goto out;... out:...)
 * and addres the corresponding internal LabelNumber.
 */
#define labcdr cdr
struct LabBind {
  LabBind *labcdr;              /* rev. list of binders at this scope level */
  Symstr *labsym;               /* the label's name */
  LabelNumber *labinternlab;    /* and its internal representation, */
                                /* (opaque to back end).            */
  IPtr labuses;                 /* flags, further elucidated below. */
  union {
    SynGoto *ref;
    SynScope *def;
  } labu;                       /* opaque to all but C/C++ syn.c        */
#ifdef PASCAL /*ECN*/
  union {
    Binder *jbuf;
    Binder *proc;
  } lun;
  unsigned8 bindlevel;
#endif
};

/*
 * Flags for labuses in LabBind
 */
#define l_referenced        1L
#define l_defined           2L

/*
 * In C++, Binders, TagBinders and ClassMembers can all occur in name scopes,
 * on the same list of named entities, discriminated by their h0 fields.
 * Pro tem, and prior to more radical rationalisation, we ensure that each
 * structure has the same common head:
 *    AEop h0;
 *    SelfType *cdr;
 *    Symstr *name;
 *    TypeExpr *type;
 *    SET_BITMAP attributes;
 * Attributes sweeps up C++ access specifiers (via bitofaccess_(), base
 * class flags and other miscellaneous flag values. Eventually, we could
 * unify attributes with h0.
 * AM, Jun-93: merge Binder and ClassMember.
 */

#define  attributes_(p)  ((p)->attributes)

/* Fields of attributes...        */
/* bitofaccess_(s_private, s_protected, s_public) = 0x700 */
#define A_DYNINIT      0x0100   /* Binder has dynamic init.             */
#define A_NOLINKAGE    0x0400   /* [Tag]Binder has no linkage...        */
#define A_INTERN       0x0800   /* Binder has internal linkage...       */
#define A_EXTERN       0x1000   /* [Tag]Binder has external linkage...  */
#define A_PRIMARY      0x2000   /* Binder is a primary template name    */
#define A_TEMPLATE     0x4000   /* Binder is a template name.           */
#define A_REALUSE      0x8000

#define CB_VBASE      0x10000   /* virtual base class */
#define CB_BASE       0x20000   /* base class         */
#define CB_CORE       0x40000   /* base class core member */
#define CB_HASCOREFN  CB_CORE   /* real Binder has attached core Binder */
#define CB_VBPTR      0x80000   /* ptr to VBASE       */
#define CB_VTAB      0x100000   /* vtable pointer...  */
#define CB_ANON      0x200000   /* anon union binder  */
#define CB_MASK      0x3f0000   /* non-aggregate fields */
#define CB_TCONV     0x400000   /* type conversion fn */
#define CB_CGEN      0x800000   /* (member) fn has compiler-generated */
                                /* components: ctor, dtor, operator=  */
#define NON_CONFORMING 0x1000000
                                /* attribute but really to indicate a t_unknown
                                   type is conforming only to itself.
                                 */
#define DEDUCED      0x2000000  /* attribute but really to indicate the non-t_unknown
                                   type is deduced rather than by other means.
                                 */
#define A_LOCALSTORE  (~0x7fffffff)
#define A_GLOBALSTORE 0x40000000

/*
 * Binders describe variables and functions (named objects).
 * The code generator also introduces Binders for some anonymous abjects.
 * In C++ (CPLUSPLUS) they are also used for member bindings.
 * The intent is that this should only be exploited in code guarded by
 * CPLUSPLUS so that in C the two structs can differ.
 */
typedef struct SuperBinder SuperBinder; /* opaque here */

#define ClassMember Binder
typedef ClassMember *ScopeSaver;

struct Binder {
  AEop h0;                      /* needed as Binder is a subtype of Expr */
  Binder *bindcdr;              /* reverse chain of binders at this level */
  Symstr *bindsym;              /* pointer to Symstr (for name and restore) */
  TypeExpr *bindtype;           /* the object's type... but disappears */
                                /* for auto objects - cached in bindmcrep */
  SET_BITMAP attributes;        /* this scope entity's attributes... */

  SET_BITMAP bindstg;           /* flags describing sort of object - also */
                                /* used to discriminate unions and opts */
  union {                       /* discriminated by bindstg & b_bindaddrlist */
     /* BindVar choices: */
     IPtr i;                    /* offset in stack/dataseg etc. or enumval */
     BindList *bl;              /* stack offset as BindList (auto only) */
     Binder *realbinder;        /* for instate_alias()... */
     SuperBinder *super;        /* for sub binders made by splitting */
                                /* live ranges.                      */
     /* enumvals are represented as 'i' above.                          */
  } bindaddr;

  struct TagBinder *bindparent; /* name of scope or NULL                */

  union {
     struct {
        Expr *bindconst;        /* allows C++ "const x=8, A[x], *y=&x;" */
        void *inlineinfo;
#ifdef PASCAL /*ECN*/
        unsigned8 bindlevel;
        unsigned16 synflags;
#endif
     } bindvar;
     struct {
#ifdef PASCAL /*ECN*/
        int32 offset;
        struct VariantList *vlist;
#else
        int32 offset;           /* Sadly, not in bindaddr (anonus need  */
                                /* a realbinder)                        */
        unsigned8 bitfieldbits,
                  bitfieldpos;
#endif
     } bindmem;
  } var_or_mem;

/* The following fields support the debugger toolbox */
#ifdef CALLABLE_COMPILER
  void *namedef, *dbgdata;
#define namedef_(b)     (*(Dbg_NameDef **)&((b)->namedef))
#define dbgdata_(b,t)   (*(t **)&((b)->dbgdata))
#else
  IPtr binddbg;
#endif

  ScopeSaver bindscope;         /* set only if A_PRIMARY */
  ExprList *bindactuals;        /* set only in generic binder and temporarily */
  ScopeSaver bindformals;       /* set only if A_PRIMARY and in specialized binder */
  BindList *bindinstances;      /* set only if A_PRIMARY */
  int bindtext;                 /* set only if A_PRIMARY */
  BindList *fntmptlist;         /* set only in generic binder */

/* Athough the following fields are logically part of BindVar, the code */
/* requires less changes by leaving them here.                          */
#define SIZEOF_NONAUTO_BINDER offsetof(Binder,bindxx)
#define SIZEOF_CLASSMEMBER    offsetof(Binder,bindxx)
  union {
    VRegnum i;
    void *p;
  } bindxx;            /* this and following fields in s_auto Binders only */
  int32 bindmcrep;              /* in flux */
#define NOMCREPCACHE (-1L)
};

/* If s_member (or b_member soon) then memtype_() can be ACCESSADJ...   */
#define ACCESSADJ te_void       /* flag for [ES, p245]                  */
#ifdef CPLUSPLUS
#define is_datamember_(/*(ClassMember *)*/l) \
    (h0_(l) == s_member && !(attributes_(l) & CB_ANON) \
                        && memtype_(l) != ACCESSADJ)
#define is_datamemberoranon_(/*(ClassMember *)*/l) \
    (h0_(l) == s_member && memtype_(l) != ACCESSADJ)
#else
#define is_datamember_(l) 1
#define is_datamemberoranon_(l) 1
#endif

#define memcdr_(p)   ((p)->bindcdr)
#define memsv_(p)    ((p)->bindsym)
#define memtype_(p)  ((p)->bindtype)
#define membits_(p)  ((p)->var_or_mem.bindmem.bitfieldbits)
#define memwoff_(p)  ((p)->var_or_mem.bindmem.offset)
#define memboff_(p)  ((p)->var_or_mem.bindmem.bitfieldpos)
#define memvtablesize_(p) ((p)->bindaddr.i)

#define OFFSET_UNSET (~0x7fffffffL)

/*
 * Useful access functions...
 */
#define bindcdr_(p)         ((p)->bindcdr)
#define bindsym_(p)         ((p)->bindsym)
#define bindstg_(p)         ((p)->bindstg)
#define bindtype_(p)        ((p)->bindtype)
#define binduses_(p)        ((p)->bindstg)    /* n.b. */
#define bindaddr_(p)        ((p)->bindaddr.i)
#define bindenumval_(p)     ((p)->bindaddr.i)
#define bindbl_(p)          ((p)->bindaddr.bl)
#define realbinder_(p)      ((p)->bindaddr.realbinder)
#define bindconst_(p)       ((p)->var_or_mem.bindvar.bindconst)
#define bindinline_(p)      ((p)->var_or_mem.bindvar.inlineinfo)
#define bindparent_(p)      ((p)->bindparent)
#define bindsuper_(p)       ((p)->bindaddr.super)
#define bindxx_(p)          ((p)->bindxx.i)
#define bindxxp_(b)         ((b)->bindxx.p)
#define bindmcrep_(p)       ((p)->bindmcrep)
#define binddbg_(p)         ((p)->binddbg)
#define bindscope_(p)       ((p)->bindscope)
#define bindactuals_(p)     ((p)->bindactuals)
#define bindformals_(p)     ((p)->bindformals)
#define bindenv_(p)         ((p)->bindformals)
#define bindinstances_(p)   ((p)->bindinstances)
#define bindtext_(p)        ((p)->bindtext)
#define bindftlist_(p)      ((p)->fntmptlist)

/*
 * Flag bits in bindaddr
 */
#define BINDADDR_MASK       (~0x0fffffffL)
/* Use top-bit-set values to provide a little free union checking.      */
/* The lower 28 bits give offset within class for local_address()       */
/* (q.v.) which should only get to see BINDADDR_ARG or BINDADDR_LOC.    */
#define BINDADDR_ARG        (~0x7fffffffL) /* a formal parameter        */
#define BINDADDR_LOC        (~0x3fffffffL) /* a local variable          */
/* The next case is currently only used if TARGET_STACK_MOVES_ONCE and  */
/* is converted to BINDADDR_LOC by flowgraf.c  (in flux Nov89).         */
#define BINDADDR_NEWARG     (~0x2fffffffL) /* an actual parameter       */
#define BINDADDR_UNSET      (~0x1fffffffL)

/* aeops.h reserves the (lsb) bits satisfying isdeclstarter_() for      */
/* bit maps of types and storage classes (C allows their intermixing).  */
/* These now (Apr 93) never occupy the same word, so need not be        */
/* disjoint.  Sep 93: there are 17 type bits (occupying 0x1ffff) and    */
/* 10 STGBITS (occupying 0x03ff0000) so the top 6 bits plus the lower   */
/* STGBITS are available for the uses listed below                      */
/* After parsing, the type has the additional value 'BITFIELD'. The     */
/* storage part is held in bindstg_ and shares with the binduses_ field */
/* of a Binder. The stg part can (and does) re-use the type part of the */
/* map below.                                                           */

#ifdef PASCAL
/* No longer used in C/C++:                                             */
#define b_synbit1           (~0x7fffffffL) /* reserved to parser */
#define b_synbit2           0x40000000L    /* reserved to parser */
#define b_synbits           (b_synbit1+b_synbit2)
#endif

#define b_generated         (~0x7fffffffL) /* generated ctor/assignment.*/
#define b_impl              0x40000000L /* real_binder_() implements.   */
#define b_pseudonym         0x20000000L /* for instate_alias            */
#define b_dbgbit            0x10000000L /* reserved to debugger support */
/* N.B. none of the above 4 bits were used by instate_decl/member.      */
/* (they are only tested via bindstg_(b) & b_xxx).                      */

/* So, pending rework, we have used the 0x70000000 bits for access      */
/* specs (so to remove an arg to instate_member to allow instate_decl   */
/* to be merged).  Beware.  AM Feb 93.                                  */
/* @@@ HIGHLY DEPENDENT ON aeops.h!   Rework soon.                      */
#define killstgacc_(m)      ((m) & ~0x70000000)
#define attribofstgacc_(m)  \
              ((((m) >> 28) & 7) << shiftoftype_(s_union+1))
#define stgaccof_(s)        (1L << (s)-s_private+28)

#define b_memfna            0x08000000L /* memfn (non-static)           */
#define b_memfns            0x04000000L /* memfn (static)               */

/*
 * bit selectors within binduses_ (now in bindstg_) additional to STGBITS
 * The bits in lowbit(STGBITS)-1 are available (Sep 93: this is 0xffff,
 * i.e. 16 bits.
 */
#define u_implicitdef     0x0001L
#define u_referenced      0x0002L
#define b_purevirtual     0x0004L
#define u_bss             0x0008L
#define u_constdata       0x0010L
#define u_loctype          (u_bss+u_constdata)
#define u_superceded      0x0020L

/* bit selectors logically within the sharing bindstg_:                 */
#define b_spilt           0x0040L /* not allocatable to registers, but  */
                                  /* not address taken (i.e. unaliased) */
#define b_addrof          0x0080L
#define b_maybeinline     0x0100L /* for class member fns until definite */
#define b_enumconst       0x0200L
#define b_implicitstg     0x0400L
#define b_undef           0x0800L /* 'forward ref' static or extern */
#define b_fnconst         0x1000L
#define b_bindaddrlist    0x2000L /* discriminator for bindstg */
#define b_noalias         0x4000L /* variable p is a pointer: *(p+x)
                                     (any x) is guaranteed to have no
                                      aliases not involving p */
#define b_clinkage       0x08000L /* c linkage */
#define b_globalregvar    bitofstg_(s_globalreg)
/*      STGBITS       0x03ff0000L */

#define isenumconst_(b)     (bindstg_(b) & b_enumconst)

/* b_enumconst isn't wanted by the back-end (no binder in the jopcode   */
/* stream can have it: any that did has been transformed to the         */
/* appropriate constant). So we can share it for a property wanted only */
/* in the backend.                                                      */
#define b_unbound         b_enumconst

/* Bits additional to TYPEBITS, sharing with STGBITS:                   */
#define BITFIELD  bitoftype_(s_lasttype+1) /* beware: a type not a stg bit */

typedef struct Friend Friend;
#define friendcdr cdr
struct Friend {
  Friend *friendcdr;
  union {
    TagBinder *friendclass;            /* h0_() == s_tagbind */
    Binder *friendfn;                  /* h0_() == s_binder  */
  } u;
};

typedef BindList TagBindList;

/*
 * The type TagBinder is used for struct name bindings and is similar
 * to Binder. BEWARE: the relationship with Binder may be depended upon.
 */
struct TagBinder
{
  AEop h0;                      /* Must be the first field... */
  TagBinder *bindcdr;           /* reverse chain of binders at this level */
  Symstr *bindsym;              /* pointer to Symstr (for name and restore) */
  TypeExpr *tagbindtype;        /* pointer to parent type... */
  SET_BITMAP attributes;        /* common binder attributes */

  SET_BITMAP tagbindbits;       /* TagBinder-specific flags: */
                                /* discriminates struct, union, (enum?)... */
                                /* ...TB_UNDEFMSG, TB_BEINGDEFD, TB_DEFD. */

  union {
      ClassMember *tagbindmems; /* list of struct/union members */
      BindList *tagbindenums;   /* list of enum members */
  } m;
  Friend *friends;              /* list of friends of the class... */
  TagBinder *tagparent;         /* parent class of class or 0.          */
  int32 cachedsize;
/* Rearrange next 2-3 lines to end so need not always be allocated?     */
  TagBindList *taginstances;       /* used if TB_TEMPLATE                  */
  ScopeSaver tagscope;          /* used if TB_TEMPLATE                  */
  ScopeSaver tagformals;        /* used if TB_TEMPLATE                  */
  ScopeSaver tagactuals;        /* used if TB_TEMPLATE                  */
  int tagtext;                  /* used if TB_TEMPLATE                  */
  TagBinder *tagprimary;
  IPtr *tagmemfns;              /* used if TB_TEMPLATE                  */
#ifdef TARGET_HAS_DEBUGGER
  IPtr tagbinddbg;             /* space reserved to debug-table writer */
#endif
  Symstr *typedefname;
};

#define tagbindcdr_(p)      ((p)->bindcdr)
#define tagbindsym_(p)      ((p)->bindsym)
#define tagbindtype_(p)     ((p)->tagbindtype)
#define tagbindbits_(p)     ((p)->tagbindbits)
#define tagbindmems_(p)     ((p)->m.tagbindmems)
#define tagbindenums_(p)    ((p)->m.tagbindenums)
#define tagbindparent_(p)   ((p)->tagparent)
#define tagbinddbg_(p)      ((p)->tagbinddbg)
#define tagscope_(p)        ((p)->tagscope)
#define tagformals_(p)      ((p)->tagformals)
#define tagactuals_(p)      ((p)->tagactuals)
#define tagtext_(p)         ((p)->tagtext)
#define taginstances_(p)    ((p)->taginstances)
#define tagprimary_(p)      ((p)->tagprimary)
#define tagmemfns_(p)       (*(IPtr **)&(p)->tagmemfns)

/* Fields of tagbindbits...                                             */
/* beware: bitoftype_(s_enum, s_struct, s_class, s_union) = 0x1c8       */
#define TB_UNALIGNED        1
#define TB_TEMPLATE         2   /* tagbinder is just a template.        */
#define TB_TPARAM           4   /* tagbinder is just a template param.  */
#define TB_SPECIALIZED 0x0010   /* tagbinder is an explicitly specialized template instance */
#define TB_ABSTRACT    0x0800   /* has >=1 pure virtual fn.             */
#define TB_BEINGDEFD   0x1000   /* police "struct d { struct d { ..."   */
#define TB_UNDEFMSG    0x2000   /* so 'size needed' msg appears once.   */
#define TB_DEFD        0x4000   /* in C++ struct a;/struct a{} differ.  */
#define TB_HASVTABLE   0x8000   /* has a virtual function table member. */

#define TB_CONTAINER        0x70000   /* enums only */
#define TB_CONTAINER_SHIFT  16
#define TB_CONTAINER_CHAR   0x00000
#define TB_CONTAINER_SHORT  0x10000
#define TB_CONTAINER_INT    0x20000
#define TB_CONTAINER_LONG   0x30000
#define TB_CONTAINER_UCHAR  0x40000
#define TB_CONTAINER_USHORT 0x50000
#define TB_CONTAINER_UINT   0x60000
#define TB_CONTAINER_ULONG  0x70000

#define TB_HASDTOR         0x00080000   /* has a dtor in its derivation... */
#define TB_HASCONSTCCTOR   0x00100000   /* generate T(T*, const T&) */
#define TB_HASCONSTOPEQ    0x00200000   /* generate op=(T*, const T&) */
#define TB_NEEDSCTOR       0x00400000   /* has a ctor in class */
#define TB_HASVBASE        0x00800000   /* has a vbase member */
#define TB_CORE            0x01000000   /* tagparent points to derivation */
#define TB_HASCMEM         0x02000000   /* has a const data member or its derivation*/
#define TB_SIZECACHED      0x04000000
#define TB_OPAQUE          0x08000000   /* data member access and sizeof not allowed*/
#define TB_NEEDSCCTOR      0x00000200   /* has a user-defined copy ctor in class
                                           or in its derivation
                                         */
#define TB_NEEDSOPEQ       0x00000400   /* has a user_defined op= in class or
                                           in its derivation
                                         */

/* POD def for pass by value purpose: no vfns, no user cctor, no vbases and
   all base/mems are bitwise cctor/op= OK.
 */

#define TB_NOTPODC_(tb)    (tagbindbits_(tb) & (TB_NEEDSCCTOR|TB_NEEDSOPEQ))
#define TB_NOTPODU_(tb, a) (tagbindbits_(tb) & (TB_HASVTABLE|TB_HASVBASE|a))
#define TB_NOTPOD_(tb)     (tagbindbits_(tb) & (TB_NEEDSOPEQ|TB_NEEDSCTOR|TB_NEEDSCCTOR))

#define isclasstagbinder_(tb) (tagbindbits_(tb) & \
            (bitoftype_(s_struct)|bitoftype_(s_class)|bitoftype_(s_union)))
#define isenumtagbinder_(tb) (tagbindbits_(tb) & bitoftype_(s_enum))

/*
 * FormTypeList is used in globalised types, and is a subtype of
 * DeclRhsList for both minimality and space reasons.
 */


typedef struct TentativeDefn TentativeDefn;
#define declcdr cdr
struct DeclRhsList {
  DeclRhsList *declcdr;
  Symstr *declname;
  TypeExpr *decltype;
  union {
      Expr *init;               /* temp. for init (shares with declbits). */
      Expr *bits;               /* (members never have inits).            */
      IPtr stgval;              /* for global register number             */
  } u;
#ifdef PASCAL /*ECN*/
  unsigned16 synflags;
  unsigned8 section;
#endif
  SET_BITMAP declstg;
  FileLine fileline;            /* added by RCC 25-Mar-88 */
  Binder *declbind;             /* temp. working space to help ->declinit */
  Symstr *declrealname;         /* declrealname set only for specialized template
                                   function name
                                */
  TentativeDefn *tentative;
};

#define declbits_(d) ((d)->u.bits)
#define declinit_(d) ((d)->u.init)
#define declstgval_(d) ((d)->u.stgval)

#define ftcdr cdr
struct FormTypeList {
  FormTypeList *ftcdr;
  Symstr *ftname;
  TypeExpr *fttype;
#ifdef PASCAL /*ECN*/
  unsigned16 synflags;
  unsigned8 section;
#endif
  Expr *ftdefault;              /* C++ default args.                    */
};

/*
 * SynBindList and BindList are notionally identical, but AM wants
 * to separate concerns while re-arranging allocators.
 */
#define bindlistcdr cdr
struct SynBindList {
  SynBindList *bindlistcdr;
  Binder *bindlistcar;
/* AM: this code in flux: I want to moan about 'private' destructors    */
/* at scope start, not scope end.  Thus I make the destructor Expr      */
/* when the Binder and ctor) is made.  Dunno if this will persist.      */
  Expr *bindlistdtor;           /* CPLUSPLUS only (else 0) */
};

#define mkSynBindList(a,b)  ((SynBindList *)syn_list3(a,b,0))
#define freeSynBindList(p)  ((SynBindList *)discard3((List *)p))

struct BindList {
  BindList *bindlistcdr;
  Binder *bindlistcar;
};

#define mkBindList(a,b)     ((BindList *)binder_cons2(a,b))

typedef struct BindListList BindListList;
struct BindListList {
  BindListList *bllcdr;
  SynBindList *bllcar;
};

typedef struct VfnList VfnList;
#define vfcdr cdr
struct VfnList {
  VfnList *vfcdr;
  Binder *vfmem;
  IPtr vfdelta;
};

#define mkVfnList(a,b,c)  ((VfnList *)syn_list3(a,b,c))

typedef struct TopDecl {        /* a top-level decalration */
    AEop h0;                    /* discriminator for union v_f... */
    union {
        DeclRhsList *var;       /* h0 == s_decl => variable  */
        struct {
          Binder *name;         /* the function's name */
          SynBindList *formals; /* its formal argument list... */
          Cmd  *body;           /* its body... */
          bool ellipsis;        /* and whether the argument list ends '...' */
        } fn;                   /* h0 = s_fndef => fn definition */
    } v_f;
} TopDecl;

/*
 * ****** TEMPORARY HACK ******
 * This structure should be private to the back-end. Making it so
 * requires splitting vargen into machine-specific and language-specific
 * parts. Also used by xxxobj.c and xxxasm.c
 * @@@ LDS: also used by bind.c for tentative definition stuff... but that
 * be improved by moving save/restore_vargen_state to vargen...
 */
typedef struct DataInit DataInit;
#define datacdr cdr
struct DataInit {
    DataInit *datacdr;
    IPtr rpt, sort, len, val;
};

/*
 * To be used sparingly...
 */
#define h0_(p) ((p)->h0)

typedef struct {
    /* Return values from structfield ... */
    int32 woffset,   /* offset (bytes) of current field (for bitfields, */
                     /* offset of word containing current field.        */
          boffset,   /* bit offset of start of bitfield in word; or 0.  */
          bsize,     /* bit size of field - 0 if not a bitfield.        */
          typesize;  /* Byte size of field - 0 for bitfields.           */
    bool nopadding,
         padded;     /* If padding occurred.                            */
    /* Internal fields for structfield's use - caller of structfield should
       set them to zero before the first call for a structure.
     */
    int32 n, bitoff;
    int32 sizeofcontainer,
          endofcontainer;
} StructPos;

#endif

/* end of defs.h */
