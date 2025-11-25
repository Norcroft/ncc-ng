/*
 * cgdefs.h - structures used by the back-end
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Codemist Ltd., 1987-1992.
 * Copyright 1991-1997 Advanced Risc Machines Limited. All rights reserved
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$ Codemist 4
 * Checkin $Date$
 * Revising $Author$
 */

#ifndef _cgdefs_LOADED
#define _cgdefs_LOADED

/* see mip/defs.h for explanation of this...                            */
typedef struct BlockHead BlockHead;
typedef struct Icode Icode;
typedef struct VRegSet *VRegSetP;
typedef struct BlockList BlockList;
typedef struct CSEBlockHead CSEBlockHead;
typedef struct SRBlockHead SRBlockHead;

/*
 * LabelNumbers describe compiler-generated labels (e.g. arising from if-else
 * and looping constructs). The structure of the forward references list is
 * defined and managed by target-specific local code generators. The defn field
 * is also multiply used as a jopcode location (by the code generator) and as
 * a machine-code location (by the local code generator). Source-level labels
 * also have associated LabelNumbers addressed via label binders.
 */
struct LabelNumber {            /* compiler-generated-label descriptor */
  BlockHead *block;             /* block containing label */
  union {
      List *frefs;              /* forwd ref list, managed by local cg */
      int32 defn;               /* jopcode location or code location   */
  } u;
  IPtr name;                    /* 'name' (internal label number) -  */
};                              /* top bit indicates 'label defined' */
/*
 * Useful access and constructor functions...
 */
#define addfref_(l,v)       ((l)->u.frefs = \
                             (List *)binder_icons2((l)->u.frefs,(v)))
#define addlongfref_(l,v,i) ((l)->u.frefs = \
                             (List *)binder_icons3((l)->u.frefs,(v),(IPtr)(i)))
#define lab_isset_(l)       ((l)->name < 0)
#define lab_setloc_(l,v)    ((l)->name |= ~0x7fffffff, (l)->u.defn = (v))
#define lab_name_(l)        ((l)->name)
#define lab_xname_(l)       (is_exit_label(l) ? (int32)(IPtr)(l) : \
                             lab_name_(l) & 0x7fffffff)
#define lab_block_(l)       ((l)->block)

/*
 * A list of labels numbrs is a generic List... used by local code generators
 * and by disassemblers. The mk function has the obvious sort:
 * mkLabList: LabList x LabelNumber -> LabList
 */
typedef struct LabList LabList;
#ifndef labcdr
#  define labcdr cdr
#endif
struct LabList {
    LabList *labcdr;
    LabelNumber *labcar;
};
#define mkLabList(a,b) ((LabList *)binder_cons2((LabList *)a,(LabelNumber *)b))


typedef struct HandlerList HandlerList;
struct HandlerList
{  HandlerList* cdr;
  int /*TypeId*/ type;
  LabelNumber *handler;};

typedef enum { ex_destructor, ex_handlerblock } ex_enum;
/*
 * Structure describing an exception environment (one per basic block)
 */
typedef struct ExceptionEnv ExceptionEnv;
struct ExceptionEnv
{
  ExceptionEnv *cdr;
  ex_enum type;
  union {
    Binder *destructee;
    struct HandlerEnv {
      int handlercount;
      LabelNumber *handlerblock;
      HandlerList *handlerlist;
    } henv;
  } handlers;
};
extern ExceptionEnv *currentExceptionEnv;

/*
 * Structure describing a basic block.
 */
struct BlockHead
{
  struct Icode *code;               /* start of 3-address code           */
  int32 length;                     /* length of ditto                   */
  int32 flags;                      /* misc flag bits (incl. exit cond)  */
  union { LabelNumber *next;            /* successor block               */
          LabelNumber **table;          /* or block table for switch     */
          BlockHead *backp;             /* for branch_chain() only       */
        } succ1;
  union { LabelNumber *next1;           /* alternative successor         */
          /* int32 */ IPtr tabsize;     /* or size of switch table       */
          BlockHead *backp1;            /* for branch_chain() only       */
        } succ2;
  BlockHead *down;                  /* forward chaining                  */
  BlockHead *up;                    /* backward chaining                 */
  LabelNumber *lab;                 /* label for this block              */
  VRegSetP use;                     /* registers needed at block head    */
                                    /* (private to regalloc)             */
                                    /* and also dominators of this block */
                                    /* (during cse & live range splitting*/
  union { BindList *l;              /* binders active at head of block   */
          /* int32 */ IPtr i;
        } stack;
  BindListList *debenv;             /* @@@ temp/rationalise - see flowgraph */
  BlockList *usedfrom;              /* list of blocks that ref. this one */
  union {
    CSEBlockHead *cse;
    SRBlockHead *sr;
  } extra;
  int32  loopnest;                  /* depth of loop nesting in this blk */
  ExceptionEnv* exenv;              /* exception environment             */
};

#define blklstcdr cdr


#define blkcode_(x)     (x->code)            /* start of 3-address code  */
#define blklength_(x)   (x->length)          /* length of ditto          */
#define blkflags_(x)    (x->flags)           /* misc flag bits           */
#define blknext_(x)     (x->succ1.next)      /* successor block          */
#define blknext1_(x)    (x->succ2.next1)     /* alternative successor    */
#define blktable_(x)    (x->succ1.table)     /* table of successors      */
#define blktabsize_(x)  (x->succ2.tabsize)   /* size of aforesaid table  */
#define blkbackp_(x)    (x->succ1.backp)     /* for branch_chain() only  */
#define blkbackp1_(x)   (x->succ2.backp1)    /* for branch_chain() only  */
#define blkdown_(x)     (x->down)            /* forward chaining         */
#define blkup_(x)       (x->up)              /* backward chaining        */
#define blklab_(x)      (x->lab)             /* label for this block     */
#define blkuse_(x)      (x->use)      /* registers needed at block head  */
#define blk_dominators_(x) (x->use)
#define blkstack_(x)    (x->stack.l)  /* binders active at head of block */
#define blkstacki_(x)   (x->stack.i)
#define blkdebenv_(x)   (x->debenv)   /* for debugger                    */
#define blkusedfrom_(x) (x->usedfrom) /* used in cross-jump optimization */
#define blknest_(x)     (x->loopnest) /* # loops enclosing this block.   */
#define blkexenv_(x)    (x->exenv)    /* exception environment           */
#define blkcse_(x)      (x->extra.cse)
#define blksr_(x)       (x->extra.sr)

/* bits for use in blkflags_(x)                                          */

/* #define BLKREFMASK          3L  DEFUNCT    refcount 0,1,2,many        */
#define BLKALIVE               4L   /* used when flattening graph        */
#define BLKSWITCH              8L   /* contains 'switch' multi-exit      */
#define BLK2EXIT            0x10L   /* contains conditional exit         */
#define BLKBUSY             0x20L   /* used when flattening graph        */
#define BLKCODED            0x40L   /* ditto                             */
#define BLKEMPTY            0x80L   /* SET IF BLOCK EMPTY                */
#define BLKLOOP            0x100L   /* block is a loop head              */
#define BLKCCLIVE          0x200L   /* condition code set on entry to    */
                                    /* block (block is second part of    */
                                    /* 3-way branch)                     */
/*#define BLKINNER         0x200L*/ /* loop has no other loops inside    */
                                    /* Nowhere used ?                    */
#define BLKOUTER           0x400L   /* set in function header block      */
#define BLK0EXIT           0x800L   /* no exit (tail procedure call)     */
#define BLKP2             0x1000L   /* bits used to control backpointer  */
#define BLKP3             0x2000L   /* bits used to control backpointer  */
#define BLKCALL           0x4000L   /* block contains a proc call        */
#define BLK2CALL          0x8000L   /* block contains 2 proc calls       */
#define BLKSETJMP        0x10000L   /* block may call setjmp (groan).    */
#define BLKSTACKI       0x100000L   /* blkstack is a number not a bindlist*/
#define BLKREXPORTED2   0x200000L
#define BLKCCEXPORTED   0x400000L
#define BLKREXPORTED    0x800000L
/* N.B. Q_MASK values above also used when BLK2EXIT is set (condition)   */
/* Also, the following bits are are disjoint from the above but are only */
/* used in 'procflags'.  Some of them may later be BLK oriented.         */
#define PROC_ARGADDR      0x20000L  /* arg address taken                 */
#define PROC_ARGPUSH      0x40000L  /* treat args carefully (see cg.c)   */
#define PROC_BIGSTACK     0x80000L  /* stack bigger than 256             */
#define PROC_USESADCONS  0x200000L
#define PROC_HASMOVC    0x1000000L
#define PROC_CASEBRANCH 0x2000000L
#define PROC_FPTEMP     0x4000000L  /* hack for SPARC.  Generalise?      */
#define PROC_INLNASM    0x8000000L  /* Fn contains inline assembler      */
/* Special values to go in blknext_(), getting to be too many...         */

#define RetIntLab       ((LabelNumber *)-256L)
#define RetFloatLab     ((LabelNumber *)-252L)
#define RetDbleLab      ((LabelNumber *)-248L)
#define RetVoidLab      ((LabelNumber *)-244L)
#define RetImplLab      ((LabelNumber *)-240L)
/* and for use in flowgraph.c - change soon? */
#define RETLAB          ((LabelNumber *)-236L)
#define NOTALAB         ((LabelNumber *)-232L)

struct BlockList
{ BlockList *blklstcdr;
  BlockHead *blklstcar;
};

#define mkBlockList(a,b) ((BlockList *)binder_cons2(a,b))

/* The following is used when a real machine register is required.       */

typedef IPtr RealRegister;

#define RegSort int32    /* the following 3 values ... */

#define INTREG      0x10000000L
#define FLTREG      0x20000000L
#define DBLREG      0x28000000L
#define SENTINELREG 0x30000000L   /* for clarity in regalloc */

/* The following mask is used so that cse and regalloc can pack a       */
/* RegSort value and a small integer into an int32.                     */
/* Maybe neither of these are very essential anymore.                   */
#define REGSORTMASK (~0x07ffffff) /* for pack/unpack of RegSort & int   */

#ifdef ADDRESS_REG_STUFF
#define ADDRREG     0x18000000L
#define isintregtype_(rsort) ((rsort) == INTREG || (rsort) == ADDRREG)
#else
#define ADDRREG INTREG
#define isintregtype_(rsort) ((rsort) == INTREG)
#endif

#define regbit(n) (((unsigned32)1L)<<(n))
#define reglist(first,nregs) (regbit((first)+(nregs))-regbit(first))

/* the next lines are horrid, but less so that the previous magic numbers */
/*   - they test for virtual regs having become real - see flowgraph.c   */
/* Their uses ought to be examined and rationalised.                     */
#define isany_realreg_(r)  ((unsigned32)((r)) < (unsigned32)NMAGICREGS)
#ifdef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
# if sizeof_double == 4
#   define is_physical_double_reg_(r) 0
#else
#   define is_physical_double_reg_(r) \
      (xxregtype_(r)==DBLREG && isany_realreg_(r))
# endif
#endif

#define V_resultreg(rsort) (isintregtype_(rsort) ? R_A1result : R_FA1result)
/* The following line allows for the possibility of the function result   */
/* register being different in caller and callee (e.g. register windows). */
#define V_Presultreg(rsort) (isintregtype_(rsort) ? R_P1result : R_FP1result)

/* 'GAP' is a non-value of type VRegnum.  The bit pattern is chosen so  */
/* that it invalidates any packing with REGSORTMASK above, and often    */
/* causes a memory trap if used as an index (hence better than -1).     */
/* It is also specified in a way that is 64-bit-long friendly.          */
#define GAP ((VRegnum)(~0x000fffffL))

typedef struct RegList {
    struct RegList *rlcdr;
    /* VRegnum */ IPtr rlcar;
} RegList;

#define mkRegList(a,b) ((RegList *)binder_icons2(a,b))
#define RegList_Member(a,l) (generic_member((IPtr)(a), (List *)(l)))
#define RegList_DiscardOne(p) ((RegList *)discard2(p))
#define RegList_NDelete(a,p) ((RegList *)generic_ndelete((IPtr)(a), (List *)(p)))

/* Structure for an abstract instruction (3-address code)                */

typedef union VRegInt
{
    /* VRegnum */ IPtr r;
    /* RealRegister */ IPtr rr;
    /* int32 */ IPtr i;
    char const *str;
    StringSegList *s;
    LabelNumber *l;
    LabelNumber **lnn;
    Binder *b;
    Expr *ex;             /* Binder, when we want to view it as an Expr */
    FloatCon *f;
    BindList *bl;
    Symstr *sym;
    Int64Con *i64;
    void *p;            /* should only be used for debugger support */
} VRegInt;

struct Icode
{
/*
 * The jopcode field here really contains a J_OPCODE plus contition bits
 * (Q_MASK), see jopcode.h.   Maybe there should be packed in using bitfields
 * rather than the unchecked arithmetic coding currently used?  This is not
 * the highest priority clean-up for me to worry about
 */
  UPtr op;
  VRegInt r1, r2, r3, r4;
#if RECORD_SOURCE_LOCATION
  char const *f;     /* The source file name */
  unsigned16 l;      /* Source file line number */
  unsigned16 column; /* position within line */
#endif
  uint32 flags; // moved for tight packing, avoiding alloc limit on 64-bit host.
};

#if RECORD_SOURCE_LOCATION
#define INIT_FL(ic) (ic).f=0; (ic).l=0; (ic).column=0;
#else
#define INIT_FL(ic)
#endif

#define INIT_IC(ic,o) {(ic).op=(o);(ic).flags=0;(ic).r1.r=(ic).r2.r=(ic).r3.r=GAP;(ic).r4.r=0;INIT_FL(ic)}
#define INIT_IC3(ic,o,R1,R2,R3) {(ic).op=(o);(ic).flags=0;(ic).r1=(R1);(ic).r2=(R2);(ic).r3=(R3);(ic).r4.r=0;INIT_FL(ic)}
#define INIT_IC4(ic,o,R1,R2,R3,R4) {(ic).op=(o);(ic).flags=0;(ic).r1=(R1);(ic).r2=(R2);(ic).r3=(R3);(ic).r4.r=(R4);INIT_FL(ic)}

#endif

/* end of mip/cgdefs.h */
