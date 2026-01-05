/*
 * mip/csescan.c: CSE available expression analysis
 * Copyright (C) Acorn Computers Ltd., 1988.
 * Copyright 1991-1997 Advanced Risc Machines Limited, All rights reserved
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$ Codemist 125
 * Checkin $Date$
 * Revising $Author$
 */

#ifdef __STDC__
#  include <string.h>
#  include <time.h>
#  include <stddef.h>
#else
#  include <strings.h>
#  include "time.h"
#  include "stddef.h"
#endif

#include "globals.h"
#include "cse.h"
#include "aeops.h"
#include "jopcode.h"
#include "store.h"
#include "cgdefs.h"
#include "builtin.h"   /* for sim */
#include "mcdep.h"     /* immed_cmp */
#include "flowgraf.h"  /* is_exit_label */
#include "regalloc.h"  /* vregister */
#include "errors.h"
#include "cg.h"
#include "codebuf.h"
#include "cseguts.h"
#include "ieeeflt2.h"

#define HASHSIZE 1024
#define hash(op,a,b) \
  ( ((op) + ((((IPtr)(a))/4) * 7)) & (HASHSIZE-1) )

#define LOCHASHSIZE 512
#define lochash(type,base,k,id) \
  ( ((type) + ((type) == LOC_VAR ? (IPtr)(id) : (k))) & (LOCHASHSIZE-1) )

Exprn **exprnindex[EXPRNINDEXSIZE];

#define LOCSEGSIZE 512
#define LOCINDEXSIZE 64
#define LOCSEGBITS 9

static Location **locindex[LOCINDEXSIZE];
#define loc_(id) (locindex[(id)>>LOCSEGBITS])[(id)&(LOCSEGSIZE-1)]

#define addtoreglist(r, l) l = (RegList *) syn_cons2(l, r)

static Location **locations; /* list of Locations used */
static Exprn **cse_tab;      /* hash table of Exprns */
static Exprn *heapptr;

#define CSEIDSEGSIZE 128     /* This must be a multiple of the VRegSet chunk
                                size (or its intended space-saving fails)
                              */
int32 cse_debugcount;

static int32 cseidsegment;
static int32 csealiasid, csealiaslimit;
static int32 csenonaliasid, csenonaliaslimit;

static VRegSetP availableexprns,
                liveexprns,
                wantedexprns,
                killedlocations;

static VRegSetP loadrs;

#define CALLLOC (-1) /* a fake locid to say 'has calls' */
#define isrealloc(p) ((p) > CALLLOC)

#ifdef TARGET_ALLOWS_COMPARE_CSES
#  define CCLOC   (-2) /* fake locid meaning 'alters condition codes */
static VRegSetP compares;

#endif

#ifndef CSE_COMPARE_MASK
#  define CSE_COMPARE_MASK Q_MASK  /* just one op for all compares */
#endif

#define MOVCLOC (-2)

#define J_NEK J_INIT     /* really, we should have a different jopcode for this */
#define J_HEAPPTR J_NOOP /* and for this */

#define IsLive(x) (vregset_member(exid_(x), liveexprns))
#define LocKills(x, p) (vregset_member(x, (p)->aliasusers))

static int32 locationid;

typedef struct FloatConList FloatConList;
struct FloatConList {
    FloatConList *cdr;
    FloatCon *f;
};
#define mkFloatConList(a,b) (FloatConList *)syn_cons2(a,b)

static FloatConList *floatconlist;

typedef struct Int64ConList Int64ConList;
struct Int64ConList {
    Int64ConList *cdr;
    Int64Con *i;
};
#define mkInt64ConList(a,b) (Int64ConList *)syn_cons2(a,b)

static Int64ConList *int64conlist;

struct LocList {
    LocList *cdr;
    Location *loc;
};
#define ll_loc_(p) ((p)->loc)

static LocList *LocList_New(LocList *next, Location *loc) {
  return (LocList *)CSEList2(next, loc);
}

static LocList *LocList_DiscardOne(LocList *locs) {
  return (LocList *)discard2((VoidStar)locs);
}

typedef struct RegValue {
    struct RegValue *cdr;
    /* VRegnum */ IPtr reg;
    ExSet *value;
} RegValue;

#define rv_reg_(r) ((r)->reg)
#define rv_val_(r) ((r)->value)

static RegValue *knownregs;

static RegValue *RegValue_DiscardOne(RegValue *rv) {
  return (RegValue *)discard3((VoidStar)rv);
}

static RegValue *RegValue_New(RegValue *next, VRegnum reg, ExSet *val) {
  return (RegValue *)CSEList3(next, reg, val);
}

static RegValue const *RegValue_RegMember(VRegnum r, RegValue const *list) {
  for (; list != NULL; list = cdr_(list))
    if (r == list->reg)
      return list;
  return NULL;
}

typedef struct LocSet LocSet;
struct LocSet {
    LocSet *cdr;
    Location *loc;
    ExSet *oldval;
};
#define ls_loc_(p) ((p)->loc)
#define ls_oldval_(p) ((p)->oldval)

#define LocSet_Member(x, s) generic_member((IPtr)x, (List const *)s)

static LocSet *LocSet_New(LocSet *next, Location *loc) {
  return (LocSet *)CSEList3(next, loc, NULL);
}

static LocSet *LocSet_DiscardOne(LocSet *locs) {
  return (LocSet *)discard3((VoidStar)locs);
}

static LocSet *LocSet_Copy(LocSet const *locs) {
  LocSet *res = NULL, **resp = &res;
  for (; locs != NULL; locs = cdr_(locs)) {
    LocSet *p = LocSet_New(NULL, ls_loc_(locs));
    *resp = p; resp = &cdr_(p);
  }
  return res;
}

static void LocSet_Discard(LocSet *locs) {
  for (; locs != NULL; locs = LocSet_DiscardOne(locs))
    continue;
}

static bool LocSet_Subset(LocSet const *sub, LocSet const *super) {
  for (; sub != NULL; sub = cdr_(sub))
    if (!LocSet_Member(ls_loc_(sub), super))
      return NO;
  return YES;
}

typedef struct StoreAccessList {
    struct StoreAccessList *cdr;
    LocSet *locs;
    bool needed;
    Icode *ic;
} StoreAccessList;
#define sa_locs_(p) ((p)->locs)
#define sa_needed_(p) ((p)->needed)
#define sa_ic_(p) ((p)->ic)

static StoreAccessList *storeaccesses;

static StoreAccessList *StoreAccessList_New(
    StoreAccessList *next, LocSet *locs, bool needed, Icode *ic) {
  return (StoreAccessList *)CSEList4(next, locs, needed, ic);
}

static StoreAccessList *StoreAccessList_DiscardOne(StoreAccessList const *sa) {
  return cdr_(sa);
}

static StoreAccessList *StoreAccessList_Copy(StoreAccessList const *sa) {
  StoreAccessList *res = NULL, **resp = &res;
  for (; sa != NULL; sa = cdr_(sa)) {
    StoreAccessList *p = StoreAccessList_New(NULL, LocSet_Copy(sa_locs_(sa)), sa_needed_(sa), sa_ic_(sa));
    *resp = p; resp = &cdr_(p);
  }
  return res;
}

static void StoreAccessList_Discard(StoreAccessList *sa) {
  for (; sa != NULL; sa = StoreAccessList_DiscardOne(sa))
    LocSet_Discard(sa_locs_(sa));
}

#ifdef ENABLE_CSE

/*
 * Debugging stuff.
 */

void cse_print_loc(Location const *x)
{
    switch (loctype_(x)) {
    default:
        cc_msg("<odd-loc %ld>", (long)loctype_(x)); break;
    case LOC_VAR:
        cc_msg("'%s'", symname_(bindsym_(locbind_(x))));
        break;
    case LOC_PVAR:
        cc_msg("'%s'P", symname_(bindsym_(locbind_(x))));
        break;
    case LOC_(MEM_B):
    case LOC_(MEM_W):
    case LOC_(MEM_I):
    case LOC_(MEM_LL):
    case LOC_(MEM_F):
    case LOC_(MEM_D):
        cc_msg("[(%ld), #%ld]", (long)exid_(locbase_(x)), (long)locoff_(x));
        break;
    }
}

void cse_print_node(Exprn const *p)
{
    J_OPCODE op;
    if (p == NULL) { cc_msg("null\n"); return; }
    op = exop_(p);
    cc_msg("node %ld: ", (long)exid_(p));
    if (op == J_NEK) {
      /* Re-using J_INIT for this turns out not to be such a great idea ... */
      cc_msg("NEK%13s%ld\n", "", (long)e1k_(p));
      return;
    } else if (op == J_HEAPPTR) {
      cc_msg("HEAPPTR\n");
      return;
    }
    jopprint_opname(op);
    switch (extype_(p)) {
    case E_UNARYK:
        { VRegInt r2, r3;
          r2.r = GAP; r3.b = e1b_(p);
          jopprint_op3(op, r2, r3);
        }
        break;
    case E_UNARY:
        cc_msg("(%ld)", (long)exid_(e1_(p)));
        break;
    case E_BINARYK:
        cc_msg("(%ld), #%ld", (long)exid_(e1_(p)), (long)e2k_(p));
        break;
    case E_BINARY:
        cc_msg("(%ld), (%ld)", (long)exid_(e1_(p)), (long)exid_(e2_(p)));
        break;
    case E_TERNARY:
        cc_msg("(%ld) %s  ? (%ld) : (%ld)",
               (long)exid_(e1_(p)), condition_name(exmask_(p)),
               (long)exid_(e2_(p)), (long)exid_(e3_(p)));
        break;
    case E_LOAD:
        cse_print_loc(exloc_(p));
        break;
    case E_LOADR:
        cc_msg(" r%ld", (long)e1_(p));
        break;
    case E_MISC:
        cc_msg("**");
        break;
    case E_CALL:
        {   int32 i;
            cc_msg("%s(", symname_(bindsym_(exfn_(p))));
            for (i = 0 ; i < exnargs_(p) ; i++) {
                if (i != 0) cc_msg(", ");
                cc_msg("(%ld)", (long)exid_(exarg_(p, i)));
            }
            cc_msg(")");
            if (exnres_(p) > 1) cc_msg("=>%ld", exnres_(p));
        }
        break;
    }
    cc_msg("\n");
}

void cse_printexits(int32 flags, LabelNumber *exit, LabelNumber *exit1)
{
    Icode ic;
    if (flags & BLKSWITCH)
        return;
    INIT_IC(ic, J_NOOP);
    if (flags & BLK2EXIT) {
        ic.op = J_B + (flags & Q_MASK);
        ic.r3.l = exit1;
        print_jopcode(&ic);
    }
    if (!(flags & BLK0EXIT)) {
        ic.op = J_B;
        ic.r3.l = exit;
        print_jopcode(&ic);
    }
}

static void ExSet_Print(ExSet const *set, char const *s) {
  char c = '{';
  for (; set != NULL; set = cdr_(set)) {
    cc_msg("%c%ld", c, (long)exid_(exs_ex_(set)));
    c = ' ';
  }
  if (c != '{') cc_msg("}%s", s);
}

static void StoreAccessList_Print(StoreAccessList const *p, char const *s) {
  char *s1 = "store accesses: ";
  for (; p != NULL; p = cdr_(p)) {
    LocSet *locs = sa_locs_(p);
    char *s2 = " <";
    cc_msg("%s%s", s1, loads_r1(sa_ic_(p)->op) ? "LD": "ST");
    for (; locs != NULL; locs = cdr_(locs)) {
      cc_msg(s2); cse_print_loc(ls_loc_(locs));
      cc_msg(" {%ld}", exid_(ls_loc_(locs)->load));
      s2 = ", ";
    }
    cc_msg(">");
    s1 = ", ";
  }
  cc_msg("%s", s);
}

static void RegValue_Print(RegValue const *p, char const *s) {
  for (; p != NULL; p = cdr_(p)) {
    cc_msg("r%ld = ", rv_reg_(p));
    ExSet_Print(p->value, cdr_(p) == NULL ? s : " ");
  }
}

#else

void cse_print_loc(Location const *x)
{
    IGNORE(x);
}

void cse_print_node(Exprn const *p)
{
    IGNORE(p);
}

void cse_printexits(int32 flags, LabelNumber *exit, LabelNumber *exit1)
{
    IGNORE(flags); IGNORE(exit); IGNORE(exit1);
}

static void ExSet_Print(ExSet const *set, char const *s) {
  IGNORE(set);
}

static void StoreAccessList_Print(StoreAccessList const *p, char const *s) {
    IGNORE(p); IGNORE(s);
}

static void RegValue_Print(RegValue const *p, char const *s) {
    IGNORE(p); IGNORE(s);
}

#endif /* ENABLE_CSE */

#define J_SIGNbits (J_SIGNED|J_UNSIGNED)

#define CantBeSubExprn(x) ((x) == NULL || (x) == heapptr || exop_(x) == J_NEK)

#define ExprnToSet(e) ExSet_Insert(e, NULL)
#define ExSet_Copy(e) ExSet_Append(e, NULL)
#define ExSet_DiscardOne(e) ((ExSet *)discard2(e))

bool ExSet_Member(Exprn const *e, ExSet const *set) {
  ExSet const *p = set;
  for (; p != NULL; p = cdr_(p))
    if (exs_ex_(p) == e) return YES;
  return NO;
}

static ExSet *ExSet_Insert(Exprn *e, ExSet *set) {
  return (ExSet_Member(e, set)) ? set : (ExSet *) CSEList2(set, e);
}

static ExSet *ExSet_NDelete(Exprn *e, ExSet *set) {
  ExSet *p, **prev = &set;
  for (; (p = *prev) != NULL; prev = &cdr_(p))
    if (exs_ex_(p) == e) {
      *prev = ExSet_DiscardOne(p);
      break;
    }
  return set;
}

static ExSet *ExSet_Union(ExSet *e1, ExSet const *e2) {
  for (; e2 != NULL; e2 = cdr_(e2))
    e1 = ExSet_Insert(exs_ex_(e2), e1);
  return e1;
}

static void ExSet_Discard(ExSet *set) {
  for (; set != NULL; )
    set = ExSet_DiscardOne(set);
}

static ExSet *LiveExSet(ExSet *set) {
  /* Destructively modify <set>, removing from it those Exprns which    */
  /* aren't live.                                                       */
  ExSet *p, **prev = &set;
  while ((p = *prev) != NULL)
    if (!IsLive(exs_ex_(p)))
      *prev = ExSet_DiscardOne(p);
    else
      prev = &cdr_(p);

  return set;
}

static ExSet *ExSet_Intersection(ExSet *s, ExSet const *s1) {
  ExSet *p, **prev = &s;
  while ((p = *prev) != NULL)
    if (ExSet_Member(exs_ex_(p), s1))
      prev = &cdr_(p);
    else
      *prev = ExSet_DiscardOne(p);
  return s;
}

static bool AlreadyNarrowed(Exprn const *e, J_OPCODE op);

static ExSet *NarrowedSet(ExSet *set, J_OPCODE op) {
  ExSet *p, *res = NULL;
  for (p = set; p != NULL; p = cdr_(p))
    if (AlreadyNarrowed(exs_ex_(p), op))
      res = ExSet_Insert(exs_ex_(p), res);
  return res;
}

typedef bool ExSetMapFn(Exprn *, void *);

static bool ExSet_Map(ExSet const *p, ExSetMapFn *f, void *a) {
  for (; p != NULL; p = cdr_(p))
    if (!f(exs_ex_(p), a)) return NO;
  return YES;
}

static Exprn *ExSet_Some(ExSet const *p, ExSetMapFn *f, void *a) {
  for (; p != NULL; p = cdr_(p))
    if (f(exs_ex_(p), a)) return exs_ex_(p);
    return NULL;
}

static ExSet *ExSet_Append(ExSet const *a, ExSet *b) {
  ExSet *res = b;
  for (; a != NULL; a = cdr_(a))
    res = ExSet_Insert(exs_ex_(a), res);
  return res;
}

bool ExSetsOverlap(ExSet const *a, ExSet const *b) {
  ExSet const *p;
  for (p = a; p != NULL; p = cdr_(p))
    if (!CantBeSubExprn(exs_ex_(p)) && ExSet_Member(exs_ex_(p), b))
      return YES;
  return NO;
}

ExSet *ExSet_OpMember(ExSet *set, J_OPCODE op, int32 ignorebits) {
  for (; set != 0; set = cdr_(set))
    if ((exop_(exs_ex_(set)) & ~ignorebits) == op)
      return set;
  return NULL;
}

typedef bool OpInSet_Aux(Exprn const *);
static ExSet *OpInSetFn(ExSet *set, OpInSet_Aux *p) {
  for (; set != 0; set = cdr_(set))
    if (p(exs_ex_(set)))
      return set;
  return NULL;
}

#ifdef TARGET_HAS_ROTATE
static ExSet *OpInSetWithE1(ExSet *set, J_OPCODE op, int32 ignorebits, Exprn *e1) {
  for (; set != 0; set = cdr_(set))
    if ((exop_(exs_ex_(set)) & ~ignorebits) == op &&
        e1_(exs_ex_(set)) == e1)
      return set;
  return NULL;
}
#endif

static ExSet *ExprnInSet(ExSet *set, Exprn *e) {
  for (; set != 0; set = cdr_(set))
    if (exs_ex_(set) == e) return set;
  return NULL;
}

void ExSet_TransferExprnsInSet(VRegSetP *s1, VRegSetP *s2, ExSet const *set) {
  bool ins1;
  for (; set != 0; set = cdr_(set)) {
    int32 exid = exid_(exs_ex_(set));
    cseset_delete(exid, *s1, &ins1);
    if (ins1) cseset_insert(exid, *s2, &ins1);
  }
}

static int32 cse_optype(int32 op)
{
/* The order of these tests is significant, as remarked below .. */
  if (op == CSE_LOADR) return E_LOADR;
  if ((op & ~Q_MASK) == CSE_COND) return E_TERNARY;
  if (isproccall_(op)) return E_CALL;
  if (j_is_adcon(op)) return E_UNARYK;
  if (j_is_ldr_or_str(op)) return E_LOAD;
  if (j_is_diadr(op)) return E_BINARY;
  if (j_is_diadk(op)) return E_BINARYK;
  if (reads_r3(op)) return E_UNARY;  /* must be after j_is_diadr(op) */
  if (loads_r1(op)) return E_UNARYK; /* must be at end */

  /* WD: TODO - broken for loads_r2, etc */
  /* But only if such things are made CSEs, which they currently aren't */
  return E_MISC;
}

static int32 locsize(LocType type)
{
  switch (type) {
  case LOC_(MEM_B): return 1;
  case LOC_(MEM_W): return 2;
  case LOC_(MEM_I): return 4;
  case LOC_(MEM_LL): return 8;
/* we should really get these values from sizeof_short &c?              */
  case LOC_(MEM_F): return 4;
  case LOC_(MEM_D): return 8;
/* /* the next line is dubious -- what about LOC_VAR/LOC_PVAR?          */
/* Harry Meekings and AM just (13/4/92) agreed to put MEM_xxx parts in  */
/* LOC_VAR and LOC_PVAR fields.  Soon to be done!                       */
  default:       return 4;
  }
}

static LocType loctype(J_OPCODE op)
{ int32 mem = j_memsize(op);
  switch (mem) {
  case MEM_D:
  case MEM_F:
  case MEM_I:
  case MEM_B:
  case MEM_W:
  case MEM_LL: return LOC_(mem);
  default:    syserr(syserr_loctype); return LOC_(MEM_I);
  }
}

static bool overlap(LocType typea, int32 a,
                    LocType typeb, int32 b)
{
    return ((a >= b && a < (b+locsize(typeb))) ||
            (b >= a && b < (a+locsize(typea))));
}

Exprn *cse_AdconBase(Exprn *ex, bool allowvaroffsets)
{   if (ex == NULL) syserr(syserr_adconbase);
    if (ex == heapptr) return ex;
    switch (exop_(ex) & J_TABLE_BITS)
    {
case J_ADCON: case J_ADCONV: case J_ADCONF: case J_ADCOND: case J_ADCONLL:
        return ex;
case J_LDRK:        /* J_LDRLK on TARGET_IS_ALPHA? */
        {   Location *loc = exloc_(ex);
            return (loctype_(loc) == LOC_VAR &&
                     (bindstg_(locbind_(loc)) & b_noalias)) ? ex : NULL;
        }
case J_ADDR:
        if (!allowvaroffsets) break;
        {
            Exprn *r = cse_AdconBase(e1_(ex), YES);
            if (r != NULL) return r;
            if (!OpIsShifted(exop_(ex)))
              return cse_AdconBase(e2_(ex), YES);
        }
        break;
case J_SUBR:
        if (!allowvaroffsets) break;
        /* drop through */
case J_SUBK:
case J_ADDK:
        return cse_AdconBase(e1_(ex), allowvaroffsets);
    }
    return NULL;
}

static Exprn *AdconBaseK(Exprn *ex, int32 *p)
{   if (ex == NULL) syserr(syserr_adconbase);
    if (ex == heapptr) return ex;
    switch (exop_(ex) & J_TABLE_BITS)
    {
case J_ADCON: case J_ADCONV: case J_ADCONF: case J_ADCOND: case J_ADCONLL:
        return ex;
case J_SUBK:
        *p -= e2k_(ex);
        return AdconBaseK(e1_(ex), p);
case J_ADDK:
        *p += e2k_(ex);
        return AdconBaseK(e1_(ex), p);
    }
    return NULL;
}

typedef enum {
    NotAlias,   /* Definitely unrelated */
    MaybeAlias, /* Possible aliases (address-taken var vs pointer dereference)
                   or definitely overlapping but not identical.
                 */
    IsSynonym   /* The same location accessed identically (LDRV x vs LDRVK 0,x)
                 */
} AliasType;

static AliasType possiblealias(Location const *loc, Location const *loc1)
{
    /* Determine whether loc may be an alias of loc1. Both loc and    */
    /* loc1 may have any type.                                        */
    /* NB required to return NO if loc is the same as loc1            */
    /* Simple variables are an oddity here: x may be aliased by       */
    /* something like ((ADCONV x) . n), but by nothing else (or else  */
    /* it would be marked as address-taken, and be a LOC_PVAR instead)*/

    LocType t = loctype_(loc);
    LocType t1 = loctype_(loc1);

    if ((t & LOC_REG) || (t1 & LOC_REG))
    {   if ((t|t1) & LOC_REALBASE) syserr("possiblealias(REG+REALBASE)");
        return NotAlias;
    }

    if ((t & LOC_anyVAR) && (t1 & LOC_anyVAR)) {
      if (locbind_(loc) != locbind_(loc1)) return NotAlias;
      if (locvartype_(loc) != locvartype_(loc1)) return MaybeAlias;
        /* Same variable, different access */
      return NotAlias;
    }

    if (t1 & LOC_anyVAR) {
      LocType x = t; Location const *xl = loc;
      t = t1, loc = loc1;
      t1 = x, loc1 = xl;
    }

    if (t & LOC_anyVAR) {
      /* hence by above t1 = LOC_(MEM_xx)+maybe(REALBASE) */
      int32 k = locoff_(loc1);
      Exprn *base1 = locbase_(loc1);
      Exprn *b1 = AdconBaseK(base1, &k);
      Binder *v = locbind_(loc);
      if (b1 != NULL) {
        t = locvartype_(loc);
        if (exop_(b1) == J_ADCONV && e1b_(b1) == v)
          return k == 0 && t == t1 ? IsSynonym :
                    k < locsize(t) ? MaybeAlias :
                                     NotAlias;
        return NotAlias;
      }
      b1 = cse_AdconBase(base1, YES);
      return b1 == NULL ? ((t == LOC_PVAR) ? MaybeAlias : NotAlias) :
                 (exop_(b1) == J_ADCONV && e1b_(b1) == v) ? MaybeAlias :
                                                            NotAlias;
    }
    /* By above both t and t1 are LOC_(MEM_xx)+maybe(REALBASE) */
    { Exprn *b = locbase_(loc), *b1 = locbase_(loc1);
      int32 off = locoff_(loc), off1 = locoff_(loc1);
      if (b != b1) {
        Exprn *ba = cse_AdconBase(b, YES),
              *b1a = cse_AdconBase(b1, YES);
        if (ba == NULL || b1a == NULL)
          return MaybeAlias;
        else if (ba == b1a)
          return MaybeAlias;
        else if (exop_(ba) == J_ADCON && exop_(b1a) == J_ADCON &&
                 (bindstg_(e1b_(b1a)) & bitofstg_(s_static)) &&
                 (bindstg_(e1b_(ba)) & bitofstg_(s_static))) {
          if (AdconBaseK(b, &off) == ba && AdconBaseK(b1, &off1) == b1a) {
            return overlap(t1, off1 + bindaddr_(e1b_(b1a)), t, off + bindaddr_(e1b_(ba))) ?
                 MaybeAlias : NotAlias;
          }
        }
        return NotAlias;
      }
      return (t == t1 && off == off1)  ? NotAlias :
             overlap(t1, off1, t, off) ? MaybeAlias :
                                         NotAlias;
    }
}

static void updateusers_cb(IPtr n, void *arg) {
    int32 id = *(int32 *)arg;
    Location *loc = loc_(n);
    int32 i;
    for (i = 0 ; i < LOCINDEXSIZE ; i++) {
        Location **index = locindex[i];
        int32 j;
        if (index == 0) break;
        for (j = 0 ; j < LOCSEGSIZE ; j++) {
            Location *q = index[j];
            if (q == 0) break;
            if (possiblealias(q, loc))
                cseset_insert(id, q->aliasusers, NULL);
        }
    }
    cseset_insert(id, loc->users, NULL);
    cseset_insert(id, loc->aliasusers, NULL);
}

static void updateusers(int32 id, Exprn *p)
{ /*
   * Update the 'users' field for all locations which are leaves of the
   * expression p to include the expression node id.
   * On the assumption that expressions are small, no attempt is made to be
   * clever about getting at the leaves.
   */
    if (p != NULL) cseset_map(exleaves_(p), updateusers_cb, &id);
}

static void maybealias_cb(IPtr n, void *arg) {
    if (ispublic(loc_(n))) *(bool *)arg = YES;
}

static bool maybealias(Exprn *p)
{ /*
   * Returns true if p or some part of it may have aliases.
   * (Used to give things which do and don't distinct sets of ids,
   *  to reduce the space usage of killed sets).
   */
    bool res = NO;
    if (p != NULL) cseset_map(exleaves_(p), maybealias_cb, &res);
    return res;
}

FloatCon *CSE_CanonicalFPConst(FloatCon *old)
{
    FloatConList *p;
    for ( p = floatconlist ; p != NULL ; p = cdr_(p) )
        if (p->f->floatlen == old->floatlen &&
            p->f->floatbin.irep[0] == old->floatbin.irep[0] &&
            ((p->f->floatlen & bitoftype_(s_short)) ||
             p->f->floatbin.irep[1] == old->floatbin.irep[1]))
            return p->f;
    floatconlist = mkFloatConList(floatconlist, old);
    return old;
}

Int64Con *CSE_CanonicalLLConst(Int64Con *old)
{
    Int64ConList *p;
    for ( p = int64conlist ; p != NULL ; p = cdr_(p) )
        if (p->i->bin.i.hi == old->bin.i.hi
            && p->i->bin.i.lo == old->bin.i.lo)
            return p->i;
    int64conlist = mkInt64ConList(int64conlist, old);
    return old;
}

typedef struct {
    int32 expid;
    bool killed;
} ULWRec;

static void ulw_cb(IPtr id, void *arg)
{
    ULWRec *ulw = (ULWRec *) arg;
    if (isrealloc(id) && !ulw->killed) {
        ulw->killed = LocKills(ulw->expid, loc_(id));
    }
}

bool cse_KilledInBlock(int32 expid)
{
    /* (For use only from within cse_scanblock).
       Determine whether the Exprn with id expid could reach the current
       icode position from the block head (whether it has been killed yet
       in the block).
     */
    ULWRec ulw; ulw.expid = expid; ulw.killed = NO;
    cseset_map(killedlocations, ulw_cb, (VoidStar) &ulw);
    return ulw.killed;
}

#define OldLive 1
#define OldAvail 2

static int updateliveandwanted(Exprn *exp, int flags)
{
  /* Update the set of live expressions to include expid (the return value
   * indicates whether it was already in the set).
   * If the expression has not been killed, add it also to the set of wanted
   * expressions
   */
    int oldlive;
    bool old;
    int32 expid = exid_(exp);
    cseset_insert(expid, liveexprns, &old);
    oldlive = old ? OldLive : 0;
    if (!(flags & U_NOTDEF2)) {
        cseset_insert(expid, availableexprns, &old);
        if (old) oldlive |= OldAvail;
        if (!(flags & U_NOTREF)) {
            if (cseset_member(CALLLOC, killedlocations)) {
                int32 i;
                for (i = 0 ; i < LOCINDEXSIZE ; i++) {
                    Location **index = locindex[i];
                    int32 j;
                    if (index == 0) break;
                    for (j = 0 ; j < LOCSEGSIZE ; j++) {
                        Location *loc = index[j];
                        if (loc == 0) break;
                        if (ispublic(loc) && LocKills(expid, loc))
                            return oldlive;
                    }
                }
            }
#ifdef TARGET_ALLOWS_COMPARE_CSES
            if (cseset_member(CCLOC, killedlocations) &&
                is_compare(exop_(exp)))
                return oldlive;
#endif
            if (!cse_KilledInBlock(expid))
                cseset_insert(expid, wantedexprns, NULL);
        }
    }
    return oldlive;
}

BlockHead *cse_currentblock;
static Icode *currenticode;

ExprnUse *ExprnUse_New(ExprnUse *old, int flags, int valno)
{
    return (ExprnUse *)CSEList3(old, cse_currentblock,
               vfi_(valno, flags, currenticode - blkcode_(cse_currentblock)));
}

static bool HasSameArgList(
  int is_commutative, int32 n, Exprn * const a[], Exprn * const b[])
{
    int32 i;
    if (is_commutative
        && (  (n == 2
               && a[0] != NULL && a[0] == b[1]
               && a[1] != NULL && a[1] == b[0])
           || (n == 4
               && a[0] != NULL && a[0] == b[2]
               && a[1] != NULL && a[1] == b[3]
               && a[2] != NULL && a[2] == b[0]
               && a[3] != NULL && a[3] == b[1])))
        return YES;
    for (i = 0 ; i < n ; i++)
        if (a[i] == NULL || a[i] != b[i]) return NO;
    return YES;
}

static bool SubExprn(Exprn const *sub, Exprn const *p)
{   if (p == NULL) return NO;
    if (p == sub) return YES;
    switch (extype_(p)) {
    case E_BINARY:
        if (SubExprn(sub, e2_(p))) return YES;
    case E_BINARYK:
    case E_UNARY:
        return SubExprn(sub, e1_(p));
    case E_LOAD:
        {   Location *loc = exloc_(p);
            if (loctype_(loc) & LOC_anyVAR) return NO;
            return SubExprn(sub, locbase_(loc));
        }
    case E_CALL:
        {   int32 i;
            for (i = 0 ; i < exnargs_(p) ; i++)
                if (SubExprn(sub, exarg_(p, i))) return YES;
        }
    }
    return NO;
}

static void useoldexprn(Exprn *p, int flags) {
  /* if the expression is already live in this block, then local cse
   * will kill this occurrence, so I don't want to remember its position.
   */
  if (!(flags & U_NOTDEF)) {
    int oldlive = updateliveandwanted(p, flags);
    if (!(oldlive & OldLive) || (flags & U_STORE)) {
    /* If it has become alive, having previously been alive, there may
     * still be some locations whose value I think it is.  (Up to now,
     * I would have known they weren't because it wasn't alive).  Their
     * values must be killed here.
     */
      LocList *q = exlocs_(p);
      for (; q != NULL; q = LocList_DiscardOne(q)) {
        Location *loc = ll_loc_(q);
        locvalue_(loc) = ExSet_NDelete(p, locvalue_(loc));
      }
      exlocs_(p) = NULL;
      { RegValue *r, **prevp = &knownregs;
        for (; (r = *prevp) != NULL ; ) {
          rv_val_(r) = ExSet_NDelete(p, rv_val_(r));
          if (rv_val_(r) == NULL)
            *prevp = RegValue_DiscardOne(r);
          else
            prevp = &cdr_(r);
        }
      }
      if (!(oldlive & OldLive)) {
        StoreAccessList **sap = &storeaccesses;
        StoreAccessList *sa;
        while ((sa = *sap) != NULL) {
          LocSet **locsp = &sa->locs;
          LocSet *locs;
          while ((locs = *locsp) != NULL)
            if (SubExprn(p, locs->loc->load))
              *locsp = LocSet_DiscardOne(locs);
            else
              locsp = &cdr_(locs);
          if (sa->locs == NULL)
            *sap = StoreAccessList_DiscardOne(sa);
          else
            sap = &cdr_(sa);
        }
      }
    }
    if (!(oldlive & OldAvail) || (flags & U_STORE)) {
      if (!(flags & U_NOTDEF2))
        exuses_(p) = ExprnUse_New(exuses_(p), flags & ~U_STORE, 0);
      exwaslive_(p) = NO;
    }
  }
}

#define find_varloc(id, load, flags) find_loc(LOC_VAR, NULL, 0, id, load, flags)
#define find_regloc(reg, load, flags) find_loc(LOC_REG, NULL, reg, NULL, load, flags)
#define find_memloc(type, base, offset, load, flags) find_loc(type, base, offset, NULL, load, flags)

static Location *find_loc(LocType type, Exprn *base, int32 k, Binder *id, J_OPCODE load,
                          int32 loctypeflags);

static Exprn *find_exprn(J_OPCODE op, Exprn *a, Exprn *b, Exprn *arg[], int flags)
{
    Exprn *p, *prev;
    Exprn **list;
    int32 type;
    VRegSetP leaves = NULL;
    if (op == J_ADDK || op == J_SUBK) {
      if (a == heapptr)
        return heapptr;
      else if (exop_(a) == J_NEK) {
        int32 k = (int32)(IPtr)b;
        if (op == J_SUBK) k = -k;
        op = J_NEK;
        a = (Exprn *)(IPtr)(e1k_(a) + k);
        b = NULL;
        flags = U_NOTDEF2+U_NOTREF;
      }
    } else if (op == J_ADDR && a == heapptr)
        return heapptr;

    list = &cse_tab[hash(op, a, b)];
    type = cse_optype(op);

    switch (type) {
    case E_TERNARY:
        if (CantBeSubExprn(arg[0]) || CantBeSubExprn(b) || CantBeSubExprn(a))
            return NULL;
        for (prev = NULL, p = *list; p != NULL; prev = p, p = cdr_(p)) {
            if (exop_(p) == (op & ~Q_MASK)
                && a == e1_(p) && b == e2_(p) && arg[0] == e3_(p)
                && (op & Q_MASK) == exmask_(p)) {
                if (prev != NULL) {
                    cdr_(prev) = cdr_(p); cdr_(p) = *list; *list = p;
                }
                if (!(flags & U_PEEK)) useoldexprn(p, flags);
                return p;
            }
        }
        if (flags & U_PEEK) return NULL;  /* just checking */
        p = (Exprn *) CSEAlloc(
                       (int) (offsetof(Exprn, u.ternary.mask) + sizeof(int32)));
        e2_(p) = b;
        e3_(p) = arg[0];
        exmask_(p) = op & Q_MASK;
        op &= ~Q_MASK;
        leaves = cseset_copy(exleaves_(a));
        cseset_union(leaves, exleaves_(b));
        cseset_union(leaves, exleaves_(arg[0]));
        break;
    case E_BINARY:
        if (CantBeSubExprn(b) || CantBeSubExprn(a)) return NULL;
        for (prev = NULL, p = *list; p != NULL; prev = p, p = cdr_(p)) {
            if (exop_(p) == op && a == e1_(p) && b == e2_(p)) { /* eureka! */
                if (prev != NULL) {
                    cdr_(prev) = cdr_(p); cdr_(p) = *list; *list = p;
                }
                if (!(flags & U_PEEK)) useoldexprn(p, flags);
                return p;
            }
        }
        if (j_is_commutative(op)) {
            Exprn **list2 = &cse_tab[hash(op, b, a)];
            for (prev = NULL, p = *list2; p != NULL; prev = p, p = cdr_(p)) {
                if (exop_(p) == op && b == e1_(p) && a == e2_(p)) { /* eureka! */
                    if (prev != NULL) {
                        cdr_(prev) = cdr_(p); cdr_(p) = *list2; *list2 = p;
                    }
                    if (!(flags & U_PEEK)) useoldexprn(p, flags);
                    return p;
                }
            }
        }
        if (flags & U_PEEK) return NULL;  /* just checking */
        p = (Exprn *) CSEAlloc(
                       (int) (offsetof(Exprn, u.binary.e2) + sizeof(Exprn *)));
        e2_(p)   = b;
        leaves = cseset_copy(exleaves_(a));
        cseset_union(leaves, exleaves_(b));
        break;
    case E_BINARYK:
        if (CantBeSubExprn(a)) return NULL;
        for (prev = NULL, p = *list; p != NULL; prev = p, p = cdr_(p)) {
            if (exop_(p) == op && a == e1_(p) && b == e2_(p)) { /* eureka! */
                if (prev != NULL) {
                    cdr_(prev) = cdr_(p); cdr_(p) = *list; *list = p;
                }
                if (!(flags & U_PEEK)) useoldexprn(p, flags);
                return p;
            }
        }
        if (flags & U_PEEK) return NULL;  /* just checking */
        p = (Exprn *) CSEAlloc(
                       (int) (offsetof(Exprn, u.binary.e2) + sizeof(Exprn *)));
        e2_(p)   = b;
        leaves = cseset_copy(exleaves_(a));
        break;
    case E_UNARY:
        if (CantBeSubExprn(a)) return NULL;
    case E_LOAD:
    case E_UNARYK:
    case E_LOADR:
        for (prev = NULL, p = *list; p != NULL; prev = p, p = cdr_(p)) {
            if (exop_(p) == op && a == e1_(p)) {
                if (prev != NULL) {
                    cdr_(prev) = cdr_(p); cdr_(p) = *list; *list = p;
                }
                if (!(flags & U_PEEK)) useoldexprn(p, flags);
                return p;
            }
        }
        if (flags & U_PEEK) return NULL;  /* just checking */
        switch (type) {
        case E_UNARY:
            leaves = cseset_copy(exleaves_(a));
            break;
        case E_LOAD:
            {   Location *loc = (Location *)a;
                if (!(loctype_(loc) & LOC_anyVAR))
                    cseset_union(leaves, exleaves_(locbase_(loc)));
                cseset_insert(locid_(loc), leaves, NULL);
            }
            break;
        case E_LOADR:
            {   VRegnum r = (VRegnum)(IPtr)a;
                Location *loc = isany_realreg_(r) ? find_regloc(r, CSE_LOADR, 0): NULL;
                if (loc != NULL) {
                    cseset_insert(locid_(loc), leaves, NULL);
                }
                p = (Exprn *) CSEAlloc(
                            (int)(offsetof(Exprn, u.unary.e1) + sizeof(Exprn *) + sizeof(Location *)));
                exloadrloc_(p) = loc;
                break;
            }
        }
        if (p == NULL)
            p = (Exprn *) CSEAlloc(
                        (int)(offsetof(Exprn, u.unary.e1) + sizeof(Exprn *)));
        break;
    case E_CALL:
        {   int32 i, n = k_argregs_((IPtr)b);
            int iscommutative = flags & U_COMMUTATIVEFN;
            flags &= ~U_COMMUTATIVEFN;
            for (i = 0 ; i < n ; i++)
                if (CantBeSubExprn(arg[i])) return NULL;
            for (prev = NULL, p = *list; p != NULL; prev = p, p = cdr_(p)) {
                if (exop_(p) == op && a == e1_(p) && b == e2_(p) &&
                    HasSameArgList(iscommutative, n, &exarg_(p, 0), arg)) {
                    if (prev != NULL) {
                        cdr_(prev) = cdr_(p); cdr_(p) = *list; *list = p;
                    }
                    if (!(flags & U_PEEK)) useoldexprn(p, flags);
                    return p;
                }
            }
            if (flags & U_PEEK) return NULL;  /* just checking */
            p = (Exprn *) CSEAlloc(
                 (int) (offsetof(Exprn, u.call.arg[0]) + n * sizeof(Exprn *)));
            for (i = 0 ; i < n ; i++) {
                exarg_(p, i) = arg[i];
                cseset_union(leaves, exleaves_(arg[i]));
            }
            e2_(p)   = b; /* @@@ this updates call.nargs hence exfntype_()! */
        }
        break;
    default:
        p = NULL;   /* to keep dataflow happy */
        syserr(syserr_find_exprn, (long)type);
    }
    cdr_(p)   = *list;
    exop_(p)  = op;
    p->nodeid = type;  /* id 0 (type is needed for maybealias) */
    exwaslive_(p) = NO;
    exleaves_(p) = leaves;
    {   int32 id; int32 alias;
        exuses_(p) = (flags & (U_NOTDEF+U_NOTDEF2)) ? NULL : ExprnUse_New(NULL, flags, 0);
        e1_(p)   = a;
        *list = p;
        exlocs_(p) = NULL;
        if (maybealias(p)) {
            if (++csealiasid >= csealiaslimit) {
                csealiasid = cseidsegment;
                csealiaslimit = (cseidsegment += CSEIDSEGSIZE);
            }
            id = csealiasid;
            alias = EX_ALIAS;
        } else {
            if (++csenonaliasid >= csenonaliaslimit) {
                csenonaliasid = cseidsegment;
                csenonaliaslimit = (cseidsegment += CSEIDSEGSIZE);
            }
            id = csenonaliasid;
            alias = 0;
        }
        p->nodeid = mknodeid_(id, alias|type);  /* rewrite with correct id */
        updateusers(id, p);
        if (!(flags & U_NOTDEF)) updateliveandwanted(p, flags);

        if (id >= EXPRNSEGSIZE * EXPRNINDEXSIZE)
            syserr("CSE exprn table overflow");
        {   Exprn **index = exprnindex[id>>EXPRNSEGBITS];
            if (index == NULL) {
                index = CSENewN(Exprn *, EXPRNSEGSIZE);
                *(cseallocrec.statsbytes) += EXPRNSEGSIZE * sizeof(Exprn **);
                exprnindex[id>>EXPRNSEGBITS] = index;
                memclr(index, EXPRNSEGSIZE * sizeof(Exprn **));
            }
            index[id & (EXPRNSEGSIZE-1)] = p;
        }
    }
    if (debugging(DEBUG_CSE)) cse_print_node(p);
    return p;
}


static Exprn *find_binaryk(J_OPCODE op, Exprn *e, int32 n, int flags) {
    return find_exprn(op, e, (Exprn *)(IPtr)n, NULL, flags);
}

#define find_movk(n, flags) find_unaryk(J_MOVK, n, flags)

static Exprn *find_unaryk(J_OPCODE op, int32 n, int flags) {
    return find_exprn(op, (Exprn *)(IPtr)n, NULL, NULL, flags);
}

static Exprn *find_loadr(VRegnum r, int flags) {
    return find_exprn(CSE_LOADR, (Exprn *)(IPtr)r, NULL, NULL, flags);
}

static Exprn *find_unaryb(int32 op, Binder *b, int flags) {
    return find_exprn(op, (Exprn *)b, NULL, NULL, flags);
}

static Exprn *find_loadexprn(int32 op, Location *loc, int flags) {
    return find_exprn(op, (Exprn *)loc, NULL, NULL, flags);
}

/*
 * Stuff about reading/writing/corrupting Locations.
 */

static Location *find_loc(LocType type, Exprn *base, int32 k, Binder *id,
                          J_OPCODE load, int32 loctypeflags)
{
    Location *p, *prev;
    Location **list = &locations[lochash(type, base, k, id)];
    if (base != NULL && exop_(base) == J_NEK)
        return NULL;
    for (prev = NULL, p = *list; p != NULL; prev = p, p = cdr_(p)) {
        LocType ltype = loctype_(p);
        if (ltype == LOC_REG) {
            if (type != LOC_REG || locreg_(p) != k)
                continue;

        } else if ((ltype & LOC_anyVAR) && type == LOC_VAR) {
        /* ltype is either LOC_VAR or LOC_PVAR (LOC_REG filtered out above) */
        /* type can't be LOC_PVAR: that gets invented below */
            if (locbind_(p) != id ||
                locvartype_(p) != LOC_(j_memsize(load)))
            /* The same variable accessed differently is a different (aliased)
               location. Maybe can't happen as generated by cg, but I have
               intentions to turn LDRVK 0,x into LDRV x.
             */
                continue;

        } else {
            if (ltype != type || locbase_(p) != base || locoff_(p) != k)
                continue;
        }
        if (prev != NULL) {
            cdr_(prev) = cdr_(p); cdr_(p) = *list; *list = p;
        }
        return p;
    }
    if (loctypeflags & LOC_PEEK)
        return NULL;

    {   Location **index = locindex[locationid>>LOCSEGBITS];
        p = CSENew(Location);
        if (locationid >= LOCSEGSIZE * LOCINDEXSIZE)
            syserr("CSE location table overflow");
        if (index == NULL) {
            index = CSENewN(Location *, LOCSEGSIZE);
            *(cseallocrec.statsbytes) += LOCSEGSIZE * sizeof(Location **);
            locindex[locationid>>LOCSEGBITS] = index;
            memclr(index, LOCSEGSIZE * sizeof(Location **));
        }
        index[locationid & (LOCSEGSIZE-1)] = p;
    }
    cdr_(p)     = *list;
    locvalue_(p)= NULL;
    p->users    = NULL;
    p->aliasusers = NULL;
    locsynonym_(p) = NULL;
    if (type == LOC_VAR) {
        SET_BITMAP stg = bindstg_(id);
        if (stg & (b_addrof | b_globalregvar |
                   bitofstg_(s_static) | bitofstg_(s_extern))) {
            type = LOC_PVAR;
        }
        locbind_(p) = id;
        locvartype_(p) = LOC_(j_memsize(load));
    } else if (type == LOC_REG) {
        locreg_(p) = k;
    } else {
        int32 n;
        Exprn *b = AdconBaseK(base, &n);
        if (b != NULL) {
            J_OPCODE op = exop_(b) & J_TABLE_BITS;
            if (op == J_ADCONF || op == J_ADCOND || op == J_ADCONLL)
                loctypeflags |= LOC_CONST;
            else if (op == J_ADCONV && !(bindstg_(e1b_(b)) & b_addrof))
                loctypeflags |= LOC_LOCAL;
        }
        locbase_(p) = base;
        locoff_(p) = k;
    }
    p->idandtype = mkidandtype_(locationid++, type | loctypeflags);
    {   int32 i;
        for (i = 0 ; i < LOCINDEXSIZE ; i++) {
            Location **index = locindex[i];
            int32 j;
            if (index == 0) break;
            for (j = 0 ; j < LOCSEGSIZE ; j++) {
                Location *q = index[j];
                AliasType a;
                if (q == 0) break;
                a = possiblealias(q, p);
                if (a != NotAlias) cseset_union(p->aliasusers, q->users);
                if (a == IsSynonym) locsynonym_(p) = q, locsynonym_(q) = p;
            }
        }
    }
    p->load = (type == LOC_REG) ? NULL :
      find_loadexprn(load, p, U_NOTDEF+U_NOTREF);
    return (*list = p);
}

static J_OPCODE cse_J_LDRK_w[] = MEM_to_J_LDRxK_table;
static J_OPCODE j_to_ldrk(J_OPCODE a) {
    return (cse_J_LDRK_w[j_memsize(a)] & ~J_ALIGNMENT) | (a & J_ALIGNMENT);
}

static bool is_narrow(Location const *loc)
{
    int32 type = loctype_(loc);
    return (type == LOC_(MEM_B) || type == LOC_(MEM_W));
}

static bool is_flavoured(J_OPCODE op, Location const *loc)
{
    return (op & J_SIGNbits) ? is_narrow(loc) : NO;
}

static Exprn *flavoured_load(J_OPCODE op, Location *loc, int flags)
{
    return find_loadexprn(j_to_ldrk(op) | (op & J_SIGNbits), loc, flags);
}

static bool SignBitClear(Exprn const *e)
{   /* Can be improved to match AlreadyNarrowed()                       */
    J_OPCODE op = exop_(e);
    switch (op & J_TABLE_BITS)
    {
case J_LDRBK: case J_LDRBR: case J_LDRBVK:      /* j_memsize(op)==MEM_B */
case J_LDRWK: case J_LDRWR: case J_LDRWVK:      /* j_memsize(op)==MEM_W */
         if (op & J_UNSIGNED) return YES;
         break;
case J_MOVK:
         if (e1k_(e) >= 0) return YES;
         break;
case J_ANDK:
         if (e2k_(e) >= 0) return YES;
         break;
    }
    return NO;
}

static bool AlreadyNarrowed(Exprn const *e, J_OPCODE op)
{
   /* The intent here is to catch values which have been explicitly narrowed.
      But while we're at it, it's no great effort to notice some expressions
      whose results are already narrow.
    */
   /* op is known to be flavoured, so its size is either MEM_B or MEM_W */
   int32 shift = 24, limit = 256;
   J_OPCODE eop = exop_(e);
   if (j_memsize(op) != MEM_B) shift = 16, limit = 0x10000;
   if (op & J_UNSIGNED)
       return (eop == J_ANDK && e2k_(e) >= 0 && e2k_(e) < limit) ||
              (eop == J_MOVK && e1k_(e) >= 0 && e1k_(e) < limit);
   else {
       limit = limit >> 1;
       return (( eop == J_ANDK && e2k_(e) >= 0 && e2k_(e) < limit) ||
               ( eop == (J_SHRK | J_SIGNED) && e2k_(e) >= shift &&
                 (exop_(e1_(e)) & ~J_SIGNbits) == J_SHRK &&
                 e2k_(e1_(e)) == e2k_(e)) ||
               ( eop == J_MOVK && e1k_(e) >= -limit && e1k_(e) < limit));
   }
}

static ExSet *loc_read(Location *p, int exprnflags, J_OPCODE op)
{
  /* op is to tell us about sign/zero-extension if the location is
     a narrow one. */
  ExSet *e = LiveExSet(locvalue_(p));
  if (!IsLive(p->load)) e = NULL;
  locvalue_(p) = e;  /* Otherwise, if an exprn in locvalue_(p) subsequently
                        becomes live we are in trouble
                      */
  if (!(loctype_(p) & LOC_anyVAR) && locbase_(p) == heapptr) return NULL;
  e = ExSet_Copy(e);
  { Exprn *load;
    if (is_flavoured(op, p)) {
      load = flavoured_load(op, p, exprnflags);
    } else {
      load = p->load;
      if ( !IsLive(load) && is_narrow(p) && !(op & J_SIGNbits)) {
          /* If we have a plain load of a narrow location, the value
             from a previous flavoured load will do.  (This works only
             locally, of course - a way to do it non-locally would
             supersede this code
           */
        Exprn *e1 = flavoured_load(op | J_SIGNED, p, U_NOTREF+U_NOTDEF+U_PEEK);
        if (e1 != NULL && IsLive(e1)) {
          load = e1;
        } else {
          e1 = flavoured_load(op | J_UNSIGNED, p, U_NOTREF+U_NOTDEF+U_PEEK);
          if (e1 != NULL && IsLive(e1))
            load = e1;
        }
      }
      useoldexprn(load, exprnflags);
    }
    if (load != p->load) useoldexprn(p->load, U_NOTREF+U_NOTDEF2);
    if (is_flavoured(op, p))
    /* we must discard all but a correctly extended values for the flavour
       of load wanted.
     */
      e = NarrowedSet(e, op);
    return ExSet_Insert(load, e);
  }
}

static ExSet *locs_read(LocSet *p, int exprnflags, J_OPCODE op) {
  ExSet *e = NULL;
  for (; p != NULL; p = cdr_(p)) {
    Location *loc = p->loc;
    ExSet *locval = loc_read(loc, exprnflags, op);
    e = e == NULL ? locval : ExSet_Union(e, locval);
    if (locsynonym_(loc) != NULL)
      e = ExSet_Union(e, loc_read(locsynonym_(loc), exprnflags, op));
  }
  return e;
}

static bool AddToLocs(Exprn *e, void *loc) {
    exlocs_(e) = LocList_New(exlocs_(e), (Location *)loc);
    return YES;
}

static void setlocvalue(Location *p, ExSet *val, VRegSetP localiases)
{
    if (locbase_(p) == heapptr) return;
    locvalue_(p) = ExSet_Copy(val);
    ExSet_Map(val, AddToLocs, p);
    if (localiases == NULL) {
      cseset_difference(availableexprns, p->aliasusers);
      cseset_difference(liveexprns, p->aliasusers);
    } else {
      VRegSetP es = cseset_copy(p->aliasusers);
      cseset_difference(availableexprns, es);
      cseset_difference(es, localiases);
      cseset_difference(liveexprns, es);
      cseset_discard(es);
    }
    cseset_insert(locid_(p), killedlocations, NULL);
    /* Now for any locations whose known values depended on p, we don't know
     * their values anymore.  It's horribly expensive to go through them here,
     * though - instead, we check for liveness when we look at the value.  In
     * addition, we need to ensure that the value doesn't become live again in
     * between - so every time an expression becomes live, we destroy the value
     * of all locations with that value.
     */
}

static bool SetExWasLive(Exprn *e, void *ignore) {
    IGNORE(ignore);
    exwaslive_(e) = YES;
    if (exop_(e) == J_RESULT2) exwaslive_(e1_(e)) = YES;
    return YES;
}

static void setreg(VRegnum reg, ExSet *val, bool newvalue)
{
    RegValue **prevp = &knownregs, *r;
    if (isany_realreg_(reg)) {
      Exprn *ex = find_loadr(reg, U_NOTDEF+U_NOTREF);
      Location *loc = exloadrloc_(ex);
      cseset_difference(availableexprns, loc->users);
      cseset_difference(liveexprns, loc->users);
      cseset_insert(locid_(loc), killedlocations, NULL);
    }
    /* LOADRs are never available */
    for (; (r = *prevp) != NULL ; prevp = &cdr_(r)) {
        if (rv_reg_(r) == reg) {
            if (newvalue && val != rv_val_(r)) {
            /* the second condition covers the case of a register being */
            /* copied to itself, as a result of optimisation of one of  */
            /* the few cases where register reuse is permitted          */
                ExSet_Discard(rv_val_(r));
                rv_val_(r) = NULL;
            }
            if (val == NULL) {
                *prevp = RegValue_DiscardOne(r);
                return;
            }
            break;
        }
    }
    if (r == NULL ) {
        if (val== NULL) return;
        knownregs = RegValue_New(knownregs, reg, NULL);
        r = knownregs;
    }
    rv_val_(r) = ExSet_Append(val, rv_val_(r));
    ExSet_Map(val, SetExWasLive, NULL);
}

static ExSet *valueinreg(VRegnum reg)
{  /* Returns the value held in the argument register if it is known,
    * otherwise NULL.
    */
    RegValue **prevp = &knownregs, *r;
    for (; (r = *prevp) != NULL ; prevp = &cdr_(r))
        if (rv_reg_(r) == reg) {
            ExSet *e = LiveExSet(rv_val_(r));
            if (e == NULL)
                *prevp = RegValue_DiscardOne(r);
            else
                rv_val_(r) = e;
            return e;
        }
    return NULL;
}

static ExSet *readreg(VRegnum reg)
{  /* Returns the value held in the argument register if it is known,
    * otherwise an Exprn describing the register (used only for base/
    * index registers of store accesses).
    */
    ExSet *res = valueinreg(reg);
    if (res != NULL) return res;
    {   Exprn *r = find_loadr(reg, U_NOTDEF+U_NOTREF);
        cseset_insert(exid_(r), loadrs, NULL);
        cseset_insert(exid_(r), liveexprns, NULL);
        res = ExprnToSet(r);
        setreg(reg, res, YES);
        return res;
    }
}

static void setmem(Location *p, ExSet *val, VRegSetP localiases)
{
    setlocvalue(p, val, localiases);
}

static void setvar(Location *p, ExSet *val, VRegSetP localiases)
{
    int32 i;
    setlocvalue(p, val, localiases);
    /* Now if p may be an alias for anything, we must discard
       the known value of that thing. */
    for (i = 0 ; i < LOCINDEXSIZE ; i++) {
        Location **index = locindex[i];
        int32 j;
        if (index == 0) break;
        for (j = 0 ; j < LOCSEGSIZE ; j++) {
            Location *q = index[j];
            if (q == 0) break;
            if (possiblealias(p, q) != NotAlias) setlocvalue(q, NULL, localiases);
        }
    }
}

static void corruptmem(void)
{   int32 i;
    for (i = 0 ; i < LOCINDEXSIZE ; i++) {
        Location **index = locindex[i];
        int32 j;
        if (index == 0) break;
        for (j = 0 ; j < LOCSEGSIZE ; j++) {
            Location *q = index[j];
            if (q == 0) break;
            if (ispublic(q) && !locconst_(q)) setlocvalue(q, NULL, NULL); /* value of p may be changed */
        }
    }
    /* Also, all future public expressions must be killed.  We record this
     * as location CALLLOC (real locations start at 0).
     */
    cseset_insert(CALLLOC, killedlocations, NULL);
}

static int32 movcbaseid;
typedef struct MOVCTarget MOVCTarget;
struct MOVCTarget {
    MOVCTarget *cdr;
    Exprn *base;
    int32 id;
    VRegSetP locswithbase;
};
static MOVCTarget *movctargets;

static int32 BaseId(Exprn *base)
{   MOVCTarget *p = movctargets;
    for (; p != NULL; p = cdr_(p))
        if (p->base == base) return p->id;
    p = CSENew(MOVCTarget);
    cdr_(p) = movctargets;
    p->base = base; p->id = --movcbaseid; p->locswithbase = NULL;
    movctargets = p;
    return p->id;
}

static void corruptlocswithbase(Exprn *base, int32 limit)
{   int32 i;
    int32 ldop = alignof_struct < 4 ? J_LDRBK|J_ALIGN1 : J_LDRK|J_ALIGN4;
    int32 mem = alignof_struct < 4 ? MEM_B : MEM_I;
    find_memloc(LOC_(mem), base, 0, ldop, LOC_REALBASE);
    for (i = 0 ; i < LOCINDEXSIZE ; i++) {
        Location **index = locindex[i];
        int32 j;
        if (index == 0) break;
        for (j = 0 ; j < LOCSEGSIZE ; j++) {
            Location *q = index[j];
            if (q == 0) break;
            if (!(loctype_(q) & LOC_anyVAR) &&
                 locbase_(q) == base && locoff_(q) < limit)
                setlocvalue(q, NULL, NULL);
        }
    }
    cseset_insert(BaseId(base), killedlocations, NULL);
}

/*
 * End of stuff about Locations.
 */

static void blocksetup(void)
{
    int32 i;
    for (i = 0 ; i != HASHSIZE ; i++) {
        Exprn *p = cse_tab[i];
        for ( ; p != NULL ; p = cdr_(p)) {
            exwaslive_(p) = NO;
            while (exlocs_(p) != NULL)
                exlocs_(p) = LocList_DiscardOne(exlocs_(p));
        }
    }
    availableexprns = NULL;
    liveexprns = NULL;
    cseset_insert(0, liveexprns, NULL);
    wantedexprns = NULL;
    killedlocations = NULL;
}

static void cse_corrupt_register(VRegnum r)
{
    setreg(r, NULL, YES);
}

static bool ExprIsExprPlusK(ExSet *es1, ExSet *es2, int32 *p1, int32 *p2)
{
    int32 n1 = 0, n2 = 0;
    Exprn *ex1 = NULL, *ex2 = NULL;
    ExSet *e2, *e1 = ExSet_OpMember(es1, J_ADDK, 0);
    if (e1 != NULL)
        n1 = e2k_(e1->exprn);
    else {
        e1 = ExSet_OpMember(es1, J_SUBK, 0);
        if (e1 != NULL)
            n1 = -e2k_(e1->exprn);
    }
    if (e1 != NULL) ex1 = e1_(e1->exprn);
    e2 = ExSet_OpMember(es2, J_ADDK, 0);
    if (e2 != NULL)
        n2 = e2k_(e2->exprn);
    else {
        e2 = ExSet_OpMember(es2, J_SUBK, 0);
        if (e2 != NULL) n2 = -e2k_(e2->exprn);
    }
    if (e2 != NULL) ex2 = e1_(e2->exprn);
    if (ex2 != NULL) {
       if (ex2 == ex1) {
           *p1 = n1; *p2 = n2; return YES;
        }
        if (ExprnInSet(es1, ex2)) {
            *p1 = 0; *p2 = n2; return YES;
        }
    }
    if (ex1 != NULL && ExprnInSet(es2, ex1)) {
        *p1 = n1; *p2 = 0; return YES;
    }
    return NO;
}

static void KillArc(BlockHead *block, LabelNumber *lab) {
    if (!is_exit_label(lab)) {
        BlockHead *b = lab->block;
        if (blk_pred_(b) == NULL) return;
        cse_RemovePredecessor(lab, block);
        if (blk_pred_(b) != NULL || (blkflags_(b) & BLKSWITCH)) return;
        if (blkflags_(b) & BLK2EXIT) KillArc(b, blknext1_(b));
        KillArc(b, blknext_(b));
    }
}

static void RemoveComparison_i(LabelNumber *dest, BlockHead *block) {
    LabelNumber *conddest = blknext1_(block);
    if (debugging(DEBUG_CSE))
        cc_msg("Comparison removed: %sbranch always taken\n",
               dest == conddest ? "" : "other ");
    { LabelNumber *other = dest != conddest ? conddest : blknext_(block);
      blknext_(block) = dest;
      blkflags_(block) &= ~(Q_MASK | BLK2EXIT);
      currenticode->op = J_NOOP;
      /* To give non-local value propagation a better chance, remove this block
         from the predecessors of the block which is the target of the untakeable
         branch (recursively, if that block then becomes unreachable).
       */
      KillArc(block, other);
    }
}

static void RemoveComparison1(bool taken, BlockHead *block) {
    RemoveComparison_i(taken ? blknext1_(block) : blknext_(block), block);
}

static LabelNumber *ComparisonDest(int32 a, int32 b, BlockHead const *block) {
    bool taken;
    unsigned32 ua = just32bits_(a),
               ub = just32bits_(b);
    if (!(blkflags_(block) & BLK2EXIT)) return NULL;
    switch (blkflags_(block) & Q_MASK) {
    case Q_UEQ:
    case Q_EQ:  taken = (a == b); break;
    case Q_UNE:
    case Q_NE:  taken = (a != b); break;
    case Q_HS:  taken = (ua >= ub); break;
    case Q_LO:  taken = (ua < ub); break;
    case Q_HI:  taken = (ua > ub); break;
    case Q_LS:  taken = (ua <= ub); break;
    case Q_GE:  taken = (a >= b); break;
    case Q_LT:  taken = (a < b); break;
    case Q_GT:  taken = (a > b); break;
    case Q_LE:  taken = (a <= b); break;
    case Q_AL:  taken = YES; break;
    default:    syserr(syserr_removecomparison, (long)blkflags_(block));
                taken = NO;
    }
    return taken ? blknext1_(block) : blknext_(block);
}

static void RemoveComparison(int32 a, int32 b, BlockHead *block) {
    LabelNumber *dest = ComparisonDest(a, b, block);
    if (dest == NULL) return;
    RemoveComparison_i(dest, block);
}

static ExSet *newexprnpart(int32 part, ExSet *set)
{
    ExSet *res = NULL;
    for (; set != NULL; set = cdr_(set)) {
      Exprn *e = set->exprn;
      Exprn *e1 = find_exprn(part, e, NULL, NULL, U_NOTREF+U_NOTDEF);
      if (IsLive(e)) {
        cseset_insert(exid_(e1), liveexprns, NULL);
        cseset_insert(exid_(e1), availableexprns, NULL);
      }
      res = ExSet_Insert(e1, res);
    }
    return res;
}

static void add_store_access(LocSet *x) {
    bool needed = NO;
    if (!stores_r1(currenticode->op)) {
      StoreAccessList *a, **ap = &storeaccesses;
      while ((a = *ap) != NULL)
        if (a->ic->op != J_NOOP && !stores_r1(a->ic->op) && LocSet_Subset(a->locs, x)) {
          LocSet_Discard(a->locs);
          *ap = StoreAccessList_DiscardOne(a);
        } else
          ap = &cdr_(a);
    }
    /* Ensure that stores to function arguments on the stack don't get */
    /* removed as redundant.                                           */
    { LocSet *p = x;
      for (; p != NULL; p = cdr_(p)) {
        Location *loc = p->loc;
        if (loctype_(loc) < LOC_VAR) {
          int32 n;
          Exprn *adcon = AdconBaseK(locbase_(loc), &n);
          if (adcon != NULL && exop_(adcon) == J_ADCONV) {
            needed = (bindstg_(e1b_(adcon)) & b_unbound) != 0;
            break;
          }
        }
      }
    }
    storeaccesses = StoreAccessList_New(storeaccesses, x, needed, currenticode);
    if (debugging(DEBUG_CSE) && CSEDebugLevel(4))
      StoreAccessList_Print(storeaccesses, "\n");
}

#define LocInSet(a, s) generic_member((IPtr)a, (List const *)s)

static LocType MaxLocType(LocSet *locs, Location **locp) {
    Location *loc = locs->loc;
    LocType type = loctype_(loc);
    while ((locs = cdr_(locs)) != NULL)
        if (loctype_(locs->loc) > type) {
            loc = locs->loc;
            type = loctype_(loc);
        }
    *locp = loc;
    return type;
}

static void KillOldUnusedStore(Location *loc, int ignorealiascount)
{ /* If the last reference to loc was in a store instruction, discard it.
     We can ignore stores to something which may be an alias of loc,
     but not loads from a possible alias.
   */
  StoreAccessList *a = storeaccesses;
  for (; a != NULL; a = cdr_(a), --ignorealiascount) {
    Icode *ic = sa_ic_(a);
    J_OPCODE op = ic->op;
    if (locbase_(loc) != heapptr && LocInSet(loc, sa_locs_(a))) {
      if (stores_r1(op) && !sa_needed_(a)) {
        if (debugging(DEBUG_CSE)) {
          cc_msg("-- killed unused");
          print_jopcode(ic);
        }
        ic->op = J_NOOP;
      }
      return;
    } else if (op != J_NOOP && !stores_r1(op) && ignorealiascount <= 0) {
      bool notalias = YES;
      LocSet *s = sa_locs_(a);
      for (; s != NULL; s = cdr_(s))
        if (possiblealias(loc, ls_loc_(s)))
          notalias = NO;
        else {
          notalias = YES; break;
        }
      if (!notalias) return;
    }
  }
}

static void EnsureOldStore(Location *loc, int ignorealiascount)
{ /* If the last reference to loc was in a store instruction, ensure it
     can't subsequently be discarded.
     We can ignore stores to something which may be an alias of loc,
     but not loads from a possible alias.
   */
  StoreAccessList *a = storeaccesses;
  for (; a != NULL; a = cdr_(a), --ignorealiascount) {
    Icode *ic = sa_ic_(a);
    J_OPCODE op = ic->op;
    if (locbase_(loc) != heapptr && LocInSet(loc, sa_locs_(a))) {
      if (stores_r1(op)) a->needed = YES;
      return;
    } else if (op != J_NOOP && !stores_r1(op) && ignorealiascount <= 0) {
      bool notalias = YES;
      LocSet *s = sa_locs_(a);
      for (; s != NULL; s = cdr_(s))
        if (possiblealias(loc, ls_loc_(s)))
          notalias = NO;
        else {
          notalias = YES; break;
        }
      if (!notalias) return;
    }
  }
}

static bool CanAmalgamateStoreBytes(LocSet *locs) {
  Location *baseloc = ls_loc_(locs);
  Exprn *base = locbase_(baseloc);
  int32 basek = locoff_(baseloc) & ~3;
  StoreAccessList *a = storeaccesses;
  int32 k, n = 0;
  for (; a != NULL; a = cdr_(a)) {
    LocSet *locs = sa_locs_(a);
    if (loads_r1(sa_ic_(a)->op)) {
      if (ls_loc_(locs)->load != base)
        return NO;
    } else {
      Location *loc = NULL;
      for (; locs != NULL; locs = cdr_(locs)) {
        loc = ls_loc_(locs);
        if (loctype_(loc) != LOC_(MEM_B))
          return NO;
        if (locbase_(loc) == base) break;
      }
      if (locs == NULL || (locoff_(loc) & ~3) != basek)
        return NO;
      k = locoff_(loc) & 3;
      if (n & regbit(k))
        return NO;

      { ExSet *locval = loc_read(loc, U_NOTREF+U_NOTDEF, j_to_ldrk(sa_ic_(a)->op));
        int32 kval;
        locval = MOVKinSet(locval);
        if (locval == NULL)
          return NO;
        kval = e1k_(exs_ex_(locval));
        if (kval != 0
            && (n != 0
                || (kval & 255) != kval
                || k != (target_lsbytefirst ? 0 : 3)))
          return NO;
      }
      n |= regbit(k);
      if (n == 15) {
        StoreAccessList **prevp = &storeaccesses;
        for (n = 0; n < 4;) {
          StoreAccessList *a = *prevp;
          Icode *ic = sa_ic_(a);
          if (stores_r1(ic->op)) {
            if (n > 0) {
              if (debugging(DEBUG_CSE)) {
                cc_msg("-- killed (amalgamated)");
                print_jopcode(ic);
              }
              ic->op = J_NOOP;
            }
            n++;
            *prevp = cdr_(a);
          } else
            prevp = &cdr_(a);
        }
        return YES;
      }
    }
  }
  return NO;
}

static Exprn *LocSetBase(LocSet *locs) {
  Exprn *base = NULL;
  for (; locs != NULL; locs = cdr_(locs))
    if (!(loctype_(ls_loc_(locs)) & LOC_anyVAR)) {
      if ((base = cse_AdconBase(locbase_(ls_loc_(locs)), YES)) != NULL)
        break;
    }
  return base;
}

static int NonAliasLoadCount(LocSet *locs) {
  Location *maxloc;
  LocType maxtype = MaxLocType(locs, &maxloc);
  StoreAccessList *a = storeaccesses;
  int i = 0;
  Exprn *base = (maxtype & LOC_anyVAR) ? NULL : LocSetBase(locs);

  for (; a != 0; a = cdr_(a), i++)
    if (a->ic->op != J_NOOP && !stores_r1(a->ic->op)) {
      LocType type1; Location *loc1;
      switch (type1 = MaxLocType(a->locs, &loc1)) {
      case LOC_VAR:
      case LOC_PVAR:
        if (maxtype == type1) {
          if (locbind_(loc1) == locbind_(maxloc))
            goto DoReturn;
        } else if (base == NULL ||
                   (exop_(base) == J_ADCONV && e1b_(base) == locbind_(loc1)))
          goto DoReturn;
        break;

      default:
        if (maxtype == LOC_VAR) break;
        { Exprn *base1 = LocSetBase(a->locs);
          if (base == NULL || base1 == NULL || base1 == base)
            goto DoReturn;
        }
      }
    }
DoReturn:
  return i;
}

static void KillRedundantStore(void) {
  if (debugging(DEBUG_CSE)) {
    cc_msg("-- redundant "); jopprint_opname(currenticode->op);
    cc_msg("\n");
  }
  currenticode->op = J_NOOP;
}

static bool storein_i(VRegnum r1, ExSet *val, LocSet *locs, bool isvolatile) {
  LocSet *p; ExSet *loadexs = NULL;
  VRegSetP loads = NULL;
  VRegSetP waslive = NULL;
  int32 i;
  bool old;
  if (val != NULL && exop_(val->exprn) == CSE_LOADR)
    val = cdr_(val);
  for (i = 0, p = locs; p != NULL; i++, p = cdr_(p)) {
    if (IsLive(ls_loc_(p)->load))
      cseset_insert(i, waslive, &old);
    ls_oldval_(p) = loc_read(ls_loc_(p), U_NOTREF, exop_(ls_loc_(p)->load));
  }
  if (!isvolatile)
    for (p = locs; p != NULL; p = cdr_(p)) {
      if (ExSetsOverlap(ls_oldval_(p), val)) {
        for (p = locs; p != NULL; p = cdr_(p))
          locvalue_(ls_loc_(p)) = ExSet_Append(val, ls_oldval_(p));
        return YES;
      }
    }
  { int n = NonAliasLoadCount(locs);
    for (i = 0, p = locs; p != NULL; i++, p = cdr_(p)) {
      loadexs = ExSet_Insert(ls_loc_(p)->load, loadexs);
      cseset_insert(exid_(ls_loc_(p)->load), loads, NULL);
      if (cseset_member(i, waslive)) {
      /* There is a load or store of this location within this block which
       * is still valid.  If a store, we may be able to eradicate it (if
       * there is no intervening load from a possible alias).
       */
        KillOldUnusedStore(ls_loc_(p), n);
      }
    }
  }
  { int uflags = U_NOTREF+U_STORE;
    if (r1 == GAP) uflags |= U_NOTDEF2;
    for (p = locs; p != NULL; p = cdr_(p)) {
      ExSet_Discard(ls_oldval_(p));
      if (loctype_(ls_loc_(p)) & LOC_anyVAR)
        setvar(ls_loc_(p), val, loads);
      else
        setmem(ls_loc_(p), val, loads);
      useoldexprn(ls_loc_(p)->load, uflags);
      exwaslive_(ls_loc_(p)->load) = YES;
    }
  }
  cseset_discard(loads);
  cseset_discard(waslive);
  if (r1 != GAP) {
    add_store_access(locs);
    setreg(r1, loadexs, NO);
  }
  return NO;
}

static bool storein(VRegnum r1, Location *loc, ExSet *val, bool isvolatile) {
  LocSet *locs = LocSet_New(NULL, loc);
  if (locsynonym_(loc) != NULL) locs = LocSet_New(locs, locsynonym_(loc));
  return storein_i(r1, val, locs, isvolatile);
}

static bool storeink(VRegnum r1, ExSet *val, LocType type, int32 m,
                     J_OPCODE load, ExSet *bases, bool isvolatile, LocSet **locp) {
  LocSet *locs = NULL;
  for (; bases != NULL; bases = cdr_(bases)) {
    Location *loc = find_memloc(type, bases->exprn, m, load, LOC_REALBASE);
    if (loc != NULL) {
      locs = LocSet_New(locs, loc);
      if (locsynonym_(loc) != NULL) locs = LocSet_New(locs, locsynonym_(loc));
    }
  }
  if (locs == NULL) return NO;
  *locp = locs;
  return storein_i(r1, val, locs, isvolatile);
}

static VRegSetP deleteloadvariant(Location *loc, int32 variant, VRegSetP set)
{
    Exprn *e = find_loadexprn(exop_(loc->load) | variant, loc,
                              U_NOTREF+U_NOTDEF+U_PEEK);
    if (e != NULL)
        return cseset_delete(exid_(e), set, NULL);
    else
        return set;
}

static VRegSetP deleteloads(Location *loc, VRegSetP set)
{
     if (loc == NULL) return set;
     cseset_delete(exid_(loc->load), set, NULL);
     if (is_narrow(loc)) {
     /* must remove all flavours of load */
          set = deleteloadvariant(loc, J_SIGNED, set);
          set = deleteloadvariant(loc, J_UNSIGNED, set);
     }
     return set;
}

static bool validdisplacement(J_OPCODE op, int32 n) {
    return    n >= MinMemOffset(op)
           && n <= MaxMemOffset(op)
           && (n & -MemQuantum(op)) == n;
}

static bool OpIs32MinusEx(Exprn const *e, Exprn const *ex) {
  if (exop_(e) == J_SUBR) {
    Exprn const *e1 = e1_(e);
    return (exop_(e1) == J_MOVK && e1k_(e1) == 32 &&
            e2_(e) == ex);
  }
  return NO;
}

static Exprn *SHRR_IsLogical(ExSet *e1, ExSet *e2) {
  ExSet *e = NULL;
  if ((e = ExSet_OpMember(e1, J_SHRR, J_SIGNbits)) == NULL) {  /* @@@ J_TABLE_BITS */
    if ((e = ExSet_OpMember(e2, J_SHRR, J_SIGNbits)) == NULL) {
      return NULL;
    } else {
      ExSet *t = e1; e1 = e2; e2 = t;
    }
  }
  { Exprn *ee = e->exprn;
    Exprn *shift = e2_(ee);
    Exprn *ex;
    e = ExSet_OpMember(e2, J_SUBK, 0);
    if (e != NULL && e2k_(e->exprn) == 1) {
      ex = e->exprn;
      ex = e1_(ex);
      if ((exop_(ex) & ~J_SIGNbits) == J_SHLR &&
          exop_(e1_(ex)) == J_MOVK && e1k_(e1_(ex)) == 1 &&
            OpIs32MinusEx(e2_(ex), shift))
          return ee;
    } else {
      e = ExSet_OpMember(e2, J_NOTR, 0);
      if (e != NULL) {
        ex = e1_(e->exprn);
        if ((exop_(ex) & ~J_SIGNbits) == J_SHLR &&
            exop_(e1_(ex)) == J_MOVK && e1k_(e1_(ex)) == -1 &&
            OpIs32MinusEx(e2_(ex), shift))
          return ee;
      }
    }
  }
  return NULL;
}

#ifdef TARGET_HAS_ROTATE
static bool FindShiftPair(ExSet *e1, ExSet *e2, ExSet **shl, ExSet **shr) {
  ExSet *e;
  for (;  (e1 = ExSet_OpMember(e1, J_SHLR, J_SIGNbits)) != NULL;  e1 = cdr_(e1))
    if ((e = OpInSetWithE1(e2, J_SHRR|J_UNSIGNED, 0, e1_(e1->exprn))) != NULL)
      {
      *shl = e1; *shr = e; return YES;
    }
  return NO;
}

static Exprn *ORRR_IsRORR(ExSet *e1, ExSet *e2) {
  ExSet *ex1, *ex2;

  if (!FindShiftPair(e1, e2, &ex1, &ex2) &&
      !FindShiftPair(e2, e1, &ex1, &ex2))
    return NULL;

  { Exprn *s1 = e2_(ex1->exprn),
          *s2 = e2_(ex2->exprn);
    if (OpIs32MinusEx(s2, s1) || OpIs32MinusEx(s1, s2))
      if (IsLive(ex2->exprn))
        return ex2->exprn;
  }
  return NULL;
}
#endif

static bool BottomBitsKnownZero(ExSet *e, int32 n) {
  ExSet *ex = ExSet_OpMember(e, J_ANDK, 0);
  if (ex != NULL && (e2k_(ex->exprn) & ((1L << n) - 1L)) == 0)
    return YES;
  ex = ExSet_OpMember(e, J_SHLK, J_SIGNbits);
  if (ex != NULL && e2k_(ex->exprn) >= n)
    return YES;
  return NO;
}

static bool TopBitsKnownZero_e(Exprn *e, int32 n) {
  if (exop_(e) == J_ANDK) {
    if ((e2k_(e) & (0xffffffffL << (32-n))) == 0)
      return YES;
  } else if (exop_(e) == J_SHRK+J_UNSIGNED) {
    int32 shift = e2k_(e);
    if (shift >= n)
      return YES;
    else
      return TopBitsKnownZero_e(e1_(e), n - shift);
  }
#ifdef TARGET_HAS_SCALED_OPS
  else if ((exop_(e) & ~(SHIFT_MASK<<J_SHIFTPOS)) == J_ANDR+(SHIFT_RIGHT<<J_SHIFTPOS)) {
    int32 shift = (exop_(e) >> J_SHIFTPOS) & SHIFT_MASK;
    if (shift >= n)
      return YES;
    else
      return TopBitsKnownZero_e(e2_(e), n - shift);
  }
#endif
  return NO;
}

static bool TopBitsKnownZero(ExSet *e, int32 n) {
  ExSet *ex = ExSet_OpMember(e, J_ANDK, 0);
  if (ex != NULL)
    return TopBitsKnownZero_e(ex->exprn, n);
  ex = ExSet_OpMember(e, J_SHRK+J_UNSIGNED, 0);
  if (ex != NULL)
    return TopBitsKnownZero_e(ex->exprn, n);
#ifdef TARGET_HAS_SCALED_OPS
  ex = ExSet_OpMember(e, J_ANDR+(SHIFT_RIGHT<<J_SHIFTPOS), SHIFT_MASK<<J_SHIFTPOS);
  if (ex != NULL)
    return TopBitsKnownZero_e(ex->exprn, n);
#endif
  return NO;
}

#if defined TARGET_HAS_SCALED_ADDRESSING || defined TARGET_HAS_SCALED_OPS || \
    defined TARGET_HAS_SCALED_ADD
static bool ShiftedOutBitsKnownZero(J_OPCODE op, ExSet *e) {
  int32 shift = (op & J_SHIFTMASK) >> J_SHIFTPOS;
  int32 shiftby = shift & SHIFT_MASK;
  if (shiftby == 0)
      return YES;
  else if (shift & SHIFT_RIGHT)
      return BottomBitsKnownZero(e, shiftby);
  else
      return TopBitsKnownZero(e, shiftby);
  return NO;
}
#endif

#ifdef TARGET_ALLOWS_COMPARE_CSES
static bool AddCompare(Exprn *node, void *ignore) {
  IGNORE(ignore);
  cseset_insert(exid_(node), compares, NULL);
  return YES;
}
#endif

static bool AddUse(Exprn *e, void *ignore) {
  IGNORE(ignore);
  if (!cseset_member(exid_(e), liveexprns))
    exuses_(e) = ExprnUse_New(exuses_(e), 0, 0);
  return YES;
}

#ifdef RANGECHECK_SUPPORTED
static bool ExprnWasntLive(Exprn *e, void *c) {
  if (exwaslive_(e)) {
    *(Exprn **)c = e;
    return NO;
  } else {
    return YES;
  }
}
#endif

static ExSet *FindRRSet(int32 op, ExSet *a, ExSet *b, int flags) {
  ExSet *res = NULL;
  int acount = 0, ocount = 0;
  for (; a != NULL && (++acount <= 4 || ocount < 16); a = cdr_(a)) {
    int bcount = 0;
    ExSet *p = b;
    for (; p != NULL && (++bcount <= 4 || ocount < acount * 4); p = cdr_(p)) {
      Exprn *e = find_exprn(op, a->exprn, p->exprn, NULL, flags);
      if (e != NULL) {
        res = ExSet_Insert(e, res);
        ocount++;
      }
    }
  }
  return res;
}

static ExSet *FindRKSet(int32 op, ExSet *a, IPtr m, int flags) {
  /* m is union {int32,pointer} */
  ExSet *res = NULL;
  for (; a != NULL; a = cdr_(a)) {
    Exprn *e = find_exprn(op, a->exprn, (Exprn *)m, NULL, flags);
    if (e != NULL)
      res = ExSet_Insert(e, res);
  }
  return res;
}

/* @@@ pure OPSYSK */
static struct {
  Binder *f;
  int32 argres;
  int commutative;
} fcsrec;

static ExSet *FindCallSet_aux(
    ExSet *arg[], Exprn *argex[], int32 argno, int32 maxarg, ExSet *res) {
  if (argno > maxarg) {
    Exprn *e = find_exprn(J_CALLK, (Exprn *)fcsrec.f,
                                   (Exprn *)(IPtr)fcsrec.argres, argex, fcsrec.commutative);
    if (e != NULL) res = ExSet_Insert(e, res);
  } else {
    ExSet *p = arg[argno];
    int32 n;
    for (n = 0; p != NULL && n <= 4; p = cdr_(p), n++) {
      argex[argno] = p->exprn;
      res = FindCallSet_aux(arg, argex, argno+1, maxarg, res);
    }
  }
  return res;
}

static ExSet *FindCallSet(
    Binder *f, int32 restype, int32 argdesc, ExSet *arg[]) {
  Exprn *argex[NANYARGREGS==0 ? 1 : NANYARGREGS];
/* /* AM: the use of k_setflags_() to add a VREGSORT to replace a K_FLAGS  */
/* field looks jolly dubious here...                                       */
  if (debugging(DEBUG_CSE))
    cc_msg("FindCallset $b %lx %lx\n", f, restype, argdesc);
  fcsrec.commutative = k_iscommutative_(argdesc) ? U_COMMUTATIVEFN : 0;
  fcsrec.f = f; fcsrec.argres = k_setflags_(argdesc, restype);
  return FindCallSet_aux(arg, argex, 0, k_argregs_(argdesc)-1, NULL);
}

static ExSet *FindRes2CallSet(
    Binder *f, int32 restype, int32 argdesc, ExSet *arg[], Icode *c) {
  ExSet *res = FindCallSet(f, restype, argdesc, arg);
  ExSet *p;
  for (p = res; p != NULL; p = cdr_(p)) {
    Exprn *e = p->exprn;
     /* care needs to be exercised here - the call of find_exprn
        will have made e live, so its use in the RESULT2 exprn below
        will always set exwaslive_.
      */
    bool live = exwaslive_(e);
    Exprn *e2 = find_exprn(J_RESULT2, e, NULL, NULL, U_NOTREF+U_NOTDEF2);
    if (!live) {
      exwaslive_(e) = NO;
      exwaslive_(e2) = NO;
    }
    if (&useicode_(exuses_(e)) == c)
      setvalno_(exuses_(e), 1);
    p->exprn = e2;
  }
  return res;
}

static ExSet *Find2ResCallSet(
    ExSet **res2, Binder *f, int32 restype, int32 argdesc, ExSet *arg[], Icode *c) {
  ExSet *res = FindCallSet(f, restype, argdesc, arg);
  ExSet *r2 = NULL;
  ExSet *p;
  for (p = res; p != NULL; p = cdr_(p)) {
    Exprn *e = p->exprn;
    bool live = exwaslive_(e);
    Exprn *e2 = find_exprn(J_RESULT2, e, NULL, NULL, U_NOTREF+U_NOTDEF2);
    if (!live) {
      exwaslive_(e) = NO;
      exwaslive_(e2) = NO;
    }
    if (&useicode_(exuses_(e)) == c)
      setnvals_(exuses_(e), 1);
    r2 = ExSet_Insert(e2, r2);
  }
  *res2 = r2;
  return res;
}

static LocSet *rr_locs(J_OPCODE op, ExSet *e1, ExSet *e2) {
/* Note here that if scaled addressing is not supported the SUB option  */
/* here will never get activated. The apparent test on the NEGINDEX bit */
/* is redundant but harmless.                                           */
  J_OPCODE op1 = OpWithShift(((op & NEGINDEX) ? J_SUBR : J_ADDR), op);
  ExSet *rrset = FindRRSet(op1, e1, e2, U_NOTREF+U_NOTDEF);
  LocSet *locs = NULL;
  for (; rrset != NULL; rrset = cdr_(rrset))
    locs = LocSet_New(locs,
                find_memloc(loctype(op), rrset->exprn, 0, j_to_ldrk(op), 0));
  return locs;
}

typedef struct {
  J_OPCODE op;
  LocSet *locs;
  VRegnum r1;
  bool isload;
} WTLRec;

static bool WorthTryingLocalCSE(Exprn *e, void *w) {
  WTLRec *wp = (WTLRec *)w;
  bool answ;
  if (debugging(DEBUG_CSE) && CSEDebugLevel(5)) {
    cc_msg("WorthTrying %ld(", (long)exid_(e));
    jopprint_opname(wp->op);
    cc_msg("%ld) %d ", (long)wp->r1, exwaslive_(e));
  }
  answ =
#if 0
         ( wp->isload &&
           ( extype_(e) != E_LOAD ||
             !LocSet_Member(exloc_(e), wp->locs)
           )
         ) /* That is, e is a propagated value */
           ? NO :
#endif
           ( ( exwaslive_(e) ||
               ( exop_(e) == J_RESULT2 &&
                 exwaslive_(e1_(e))
               )
             ) &&

          /* Surprisingly, it seems to be necessary here to make loads
             of a non-known value into CSEs.  That is,
              ( isload ? node != ... : (exwaslive_(node) || ...) )
             produces a non-working compiler.  What's going on here ?
           */
          /* isany_realreg_(r1) means that the cost of making this a CSE
             reference is likely to be larger by one MOVR.  So if it is
             anyway marginal, we don't make it a CSE.  Something less
             ad-hoc would be an improvement.
           */
            !( isany_realreg_(wp->r1) &&
                 (wp->op == J_MOVK || wp->op == J_ADCON || wp->op == J_ADCONV)
             )
           );

  if (debugging(DEBUG_CSE) && CSEDebugLevel(5))
    cc_msg("=> %d\n", answ);
  return answ;
}

/* Semi-global value propagation.
   Handles forward propagation only (no loops in path)
*/

typedef struct LocValList LocValList;
typedef struct CompVals CompVals;
typedef struct CondList CondList;

struct CondList {
  CondList *cdr;
  int32 cond;
};
#define cl_cond_(p) ((p)->cond)

struct CompVals {
  CompVals *cdr;
  Exprn *ex;
  CondList *cond;
};
#define cv_ex_(p) ((p)->ex)
#define cv_cond_(p) ((p)->cond)

struct LocValList {
  LocValList *cdr;
  Location *loc;
  ExSet *vals;
};
#define lv_loc_(p) ((p)->loc)
#define lv_vals_(p) ((p)->vals)

struct SavedLocVals {
  SavedLocVals *cdr;
  BlockHead *exporter;
  LocValList *locvals;
  StoreAccessList *storeaccesses;
  RegValue *exportedregs;
  CompVals *comp;
};
#define sl_exporter_(p) ((p)->exporter)
#define sl_locvals_(p) ((p)->locvals)
#define sl_storeaccesses_(p) ((p)->storeaccesses)
#define sl_exportedregs_(p) ((p)->exportedregs)
#define sl_comp_(p) ((p)->comp)
#define mkSavedLocVals(a,b,c,d,e,f) (SavedLocVals *)syn_list6(a,b,c,d,e,f)

typedef struct {
  int32 mask;
  VRegnum r2;
  ExSet *r2vals;
  int32 m;
  ExSet *cmpex;
} CmpRec;

#define cmp_mask_(p) ((p)->mask)
#define cmp_r2_(p) ((p)->r2)
#define cmp_r2vals_(p) ((p)->r2vals)
#define cmp_m_(p) ((p)->m)
#define cmp_ex_(p) ((p)->cmpex)

static CompVals *comparevalues;

#ifdef ENABLE_CSE

static void SavedLocVals_Print(LocValList const *p, char const *s1, char const *s2) {
  cc_msg("%s{", s1);
  for (; p != NULL; p = cdr_(p)) {
    cc_msg(" {"); cse_print_loc(p->loc); cc_msg(" = "); ExSet_Print(p->vals, "}");
  }
  cc_msg("}%s", s2);
}

static void CompVals_Print(CompVals const *cv) {
  for (; cv != NULL; cv = cdr_(cv)) {
    CondList *cl = cv->cond;
    cc_msg(" {%ld", (long)exid_(cv->ex));
    for (; cl != NULL; cl = cdr_(cl))
      cc_msg(" %s", condition_name(cl->cond));
    cc_msg("}");
  }
}

#else

static void SavedLocVals_Print(LocValList const *p, char const *s1, char const *s2) {
  IGNORE(p); IGNORE(s1); IGNORE(s2);
}

static void CompVals_Print(CompVals const *cv, char const *s) {
  IGNORE(cv); IGNORE(s);
}

#endif

static int32 Cond_Or(int32 a, int32 b) {
  if (Q_implies(a, b)) return b;
  if (Q_implies(b, a)) return a;
  switch (Q_CondPair(a, b)) {
  case Q_CondPair(Q_LT, Q_EQ):
  case Q_CondPair(Q_LT, Q_UEQ): return Q_LE;
  case Q_CondPair(Q_GT, Q_EQ):
  case Q_CondPair(Q_GT, Q_UEQ): return Q_GE;
  case Q_CondPair(Q_LO, Q_EQ):
  case Q_CondPair(Q_LO, Q_UEQ): return Q_LS;
  case Q_CondPair(Q_HI, Q_EQ):
  case Q_CondPair(Q_HI, Q_UEQ): return Q_HS;
  case Q_CondPair(Q_LT, Q_GT):  return Q_NE;
  case Q_CondPair(Q_LO, Q_HI):  return Q_NE;
  }
  return Q_AL;
}

static int32 Cond_And(int32 a, int32 b) {
  if (Q_implies(a, b)) return a;
  if (Q_implies(b, a)) return b;
  switch (Q_CondPair(a, b)) {
  case Q_CondPair(Q_LE, Q_GE):  return Q_EQ;
  case Q_CondPair(Q_LS, Q_HS):  return Q_EQ;
  case Q_CondPair(Q_LE, Q_NE):
  case Q_CondPair(Q_LE, Q_UNE): return Q_LT;
  case Q_CondPair(Q_GE, Q_NE):
  case Q_CondPair(Q_GE, Q_UNE): return Q_GT;
  case Q_CondPair(Q_LS, Q_NE):
  case Q_CondPair(Q_LS, Q_UNE): return Q_LO;
  case Q_CondPair(Q_HS, Q_NE):
  case Q_CondPair(Q_HS, Q_UNE): return Q_HI;
  }
  return Q_AL;
}

#define CondList_New(cl, cond) ((CondList *)CSEList2(cl, cond))

static CondList *CondList_Copy(CondList const *cl) {
  CondList *p = NULL;
  for (; cl != NULL; cl = cdr_(cl))
    p = CondList_New(p, cl->cond);
  return p;
}

static CondList *CondList_Insert(int32 cond, CondList *cl) {
  CondList *p = NULL;
  for (; cl != NULL; cl = cdr_(cl))
    if (Q_implies(cond, cl->cond)) {
      /* The condition to be inserted is narrower than an existing one: */
      /* drop the existing one (and add the new one later)              */
    } else {
      int32 newcond = Cond_And(cond, cl->cond);
      if (newcond == Q_AL)
        newcond = cl->cond;
      else
        cond = Q_AL;
      p = CondList_New(p, newcond);
    }
  if (cond != Q_AL) p = CondList_New(p, cond);
  return p;
}

#define CompVals_New(next, ex, conds)  ((CompVals *)CSEList3(next, ex, conds))

static CompVals *CompVals_Copy(CompVals const *cv) {
  CompVals *p = NULL;
  for (; cv != NULL; cv = cdr_(cv))
    p = CompVals_New(p, cv->ex, CondList_Copy(cv->cond));
  return p;
}

static CompVals *CompVals_Delete(CompVals const *del, CompVals const *cv) {
  CompVals *p = NULL;
  for (; cv != NULL; cv = cdr_(cv))
    if (cv != del)
      p = CompVals_New(p, cv->ex, CondList_Copy(cv->cond));
  return p;
}

static CompVals const *CompVals_ExprnMember(Exprn const *ex, CompVals const *cv) {
  for (; cv != NULL; cv = cdr_(cv))
    if (ex == cv->ex)
      return cv;
  return NULL;
}

static CompVals *CompVals_AddOne(CompVals *cv, Exprn *ex, int32 cond) {
  CompVals const *p = CompVals_ExprnMember(ex, cv);
  if (p != NULL) {
    CondList *cl = p->cond;
    for (; cl != NULL; cl = cdr_(cl))
      if (Q_implies(cl->cond, cond))
        return cv;
    return CompVals_New(CompVals_Delete(p, cv), ex, CondList_Insert(cond, CondList_Copy(p->cond)));
  }
  return CompVals_New(cv, ex, CondList_Insert(cond, NULL));
}

static CompVals *CompVals_Add(CompVals *cv, ExSet const *ex, int32 cond) {
  if (cond != Q_AL && cond != Q_NOT)
    for (; ex != NULL; ex = cdr_(ex))
      cv = CompVals_AddOne(cv, ex->exprn, cond);
  return cv;
}

static CompVals *CompVals_Intersect(CompVals *a, CompVals const *b) {
  CompVals *p, **pp = &a;
  for (; (p = *pp) != NULL;) {
    CompVals const *bp = CompVals_ExprnMember(p->ex, b);
    if (bp == NULL
        || cdr_(p->cond) != NULL || cdr_(bp->cond) != NULL)
      *pp = cdr_(p);
    else {
      int32 cond = Cond_Or(p->cond->cond, bp->cond->cond);
      if (cond == Q_AL)
        *pp = cdr_(p);
      else {
        p->cond->cond = cond;
        pp = &cdr_(p);
      }
    }
  }
  return a;
}

static LocValList *LocValList_New(LocValList *next, Location *loc, ExSet *vals) {
  return (LocValList *)CSEList3(next, loc, vals);
}

static LocValList *LocValList_DiscardOne(LocValList *vals) {
  return (LocValList *)discard3((VoidStar)vals);
}

static LocValList *LocValList_FindLoc(LocValList *vals, Location const *loc) {
  for (; vals != NULL; vals = cdr_(vals))
    if (vals->loc == loc) return vals;
  return NULL;
}

static LocValList *LocValList_Copy(LocValList const *v) {
  LocValList *res = NULL, **resp = &res;
  for (; v != NULL; v = cdr_(v)) {
    LocValList *p = LocValList_New(NULL, v->loc, ExSet_Copy(v->vals));
    *resp = p; resp = &cdr_(p);
  }
  return res;
}

static LocValList *LocValList_Intersect(LocValList *a, LocValList *b) {
 /* Destructively modifies a, removing everything not also present in b */
  LocValList *v, **vp = &a;
  for (; (v = *vp) != NULL;) {
    LocValList *t = LocValList_FindLoc(b, v->loc);
    if (t == NULL) {
      ExSet_Discard(v->vals);
      *vp = LocValList_DiscardOne(v);
    } else {
      v->vals = ExSet_Intersection(v->vals, t->vals);
      if (v->vals == NULL)
        *vp = LocValList_DiscardOne(v);
      else
        vp = &cdr_(v);
    }
  }
  return a;
}

static RegValue *MergeRegValues(RegValue *rv1, RegValue *rv2) {
  RegValue *res = NULL;
  for (; rv2 != NULL; rv2 = cdr_(rv2)) {
    VRegnum r = rv_reg_(rv2);
    RegValue *p = rv1;
    for (; p != NULL; p = cdr_(p))
      if (rv_reg_(p) == r) {
        ExSet *ex = ExSet_Copy(rv_val_(p));
        ex = ExSet_Intersection(ex, rv_val_(rv2));
        if (ex != NULL) res = RegValue_New(res, r, ex);
        break;
      }
  }
  return res;
}

static VRegnum CheckForTernaryExprn(SavedLocVals const *sv, Exprn **tep) {
  SavedLocVals *sv1 = cdr_(sv);
  if (cdr_(sv1) == NULL) {
    CompVals *cv = sl_comp_(sv);
    for (; cv != NULL; cv = cdr_(cv)) {
      CompVals const *cv1 = CompVals_ExprnMember(cv_ex_(cv), sl_comp_(sv1));
      if (cv1 != NULL) {
        CondList *cl = cv_cond_(cv);
        for (; cl != NULL; cl = cdr_(cl)) {
          CondList *cl1 = cv_cond_(cv1);
          for (; cl1 != NULL; cl1 = cdr_(cl1))
            if (cl_cond_(cl) == Q_NEGATE(cl_cond_(cl1))) {
              RegValue *rv = sl_exportedregs_(sv);
              for (; rv != NULL; rv = cdr_(rv)) {
                RegValue const *rv1 = RegValue_RegMember(rv_reg_(rv), sl_exportedregs_(sv1));
                if (rv1 != NULL && !ExSetsOverlap(rv_val_(rv), rv_val_(rv1))) {
                  Exprn *e2 = exs_ex_(rv_val_(rv));
                  Exprn *e3 = exs_ex_(rv_val_(rv1));
                  if (extype_(e2) != E_LOADR && extype_(e3) != E_LOADR) {
                    *tep = find_exprn(CSE_COND|cl->cond, cv_ex_(cv), e2, &e3, 0);
                    return rv_reg_(rv);
                  }
                }
              }
            }
        }
        break;
      }
    }
  }
  return GAP;
}

static VRegSetP setnotused;

static void ImportLocVals(BlockHead *block) {
  comparevalues = NULL;
  if (blk_pred_(block) != NULL && !(var_cc_private_flags & 64L)) {
    if (debugging(DEBUG_CSE) && CSEDebugLevel(2)) {
      SavedLocVals *p = blk_locvals_(block);
      BlockList *pred = blk_pred_(block);
      char *s = "\n  ";
      cc_msg("  predecessors");
      for (; pred != NULL; pred = pred->blklstcdr)
        cc_msg(" %ld", blklabname_(pred->blklstcar));
      for (; p != NULL; p = cdr_(p)) {
        cc_msg("  %s [%ld] ", s, blklabname_(sl_exporter_(p)));
        SavedLocVals_Print(sl_locvals_(p), "", "  ");
        if (sl_storeaccesses_(p) != NULL) StoreAccessList_Print(sl_storeaccesses_(p), "  ");
        if (sl_exportedregs_(p) != NULL) RegValue_Print(sl_exportedregs_(p), "");
        if (sl_comp_(p) != NULL) CompVals_Print(sl_comp_(p));
        cc_msg("\n");
        s = "+ ";
      }
    }
    if (length((List *)blk_pred_(block)) == length((List *)blk_locvals_(block))) {
      SavedLocVals *sv = blk_locvals_(block);
      /* LocValLists are now no longer shared, but we still need to make a copy
         since the original LocValLists may be wanted later */
      LocValList *vals = LocValList_Copy(sv->locvals);
      Exprn *ternaryex = NULL;
      if (cdr_(sv) == NULL)
        storeaccesses = StoreAccessList_Copy(sl_storeaccesses_(sv));
      else
        blk_ternaryr_(block) = CheckForTernaryExprn(sv, &ternaryex);

      knownregs = sl_exportedregs_(sv);
      comparevalues = CompVals_Copy(sl_comp_(sv));
      for (; (sv = cdr_(sv)) != NULL; ) {
        vals = LocValList_Intersect(vals, sl_locvals_(sv));
        knownregs = MergeRegValues(knownregs, sl_exportedregs_(sv));
        comparevalues = CompVals_Intersect(comparevalues, sl_comp_(sv));
      }
      if (ternaryex != NULL) {
        VRegnum r = blk_ternaryr_(block);
        knownregs = RegValue_New(knownregs, r, ExprnToSet(ternaryex));
        cseset_insert(r, setnotused, NULL);
      }
      if (debugging(DEBUG_CSE) && CSEDebugLevel(2))
        if (cdr_(blk_pred_(block)) != NULL) {
          SavedLocVals_Print(vals, " => ", " ");
          if (knownregs != NULL) RegValue_Print(knownregs, "");
          if (comparevalues != NULL) CompVals_Print(comparevalues);
          cc_msg("\n");
        }
      for (; vals != NULL; vals = LocValList_DiscardOne(vals)) {
        ExSet *s;
        bool old;
        locvalue_(lv_loc_(vals)) = lv_vals_(vals);
        ExSet_Map(lv_vals_(vals), AddToLocs, lv_loc_(vals));
        for (s = lv_vals_(vals); s != NULL; s = cdr_(s))
          cseset_insert(exid_(s->exprn), liveexprns, &old);
        cseset_insert(exid_(lv_loc_(vals)->load), liveexprns, &old);
      }
      { StoreAccessList *sa;
        RegValue *rv;
        CompVals *cv;
        bool old;
        for (sa = storeaccesses; sa != NULL; sa = cdr_(sa)) {
          LocSet *locs = sa_locs_(sa);
          for (; locs != NULL; locs = cdr_(locs))
            cseset_insert(exid_(ls_loc_(locs)->load), liveexprns, &old);
        }
        for (rv = knownregs; rv != NULL; rv = cdr_(rv)) {
          ExSet *vals = rv_val_(rv);
          cseset_insert(rv_reg_(rv), setnotused, NULL);
          for (; vals != NULL; vals = cdr_(vals))
            cseset_insert(exid_(vals->exprn), liveexprns, &old);
        }
        for (cv = comparevalues; cv != NULL; cv = cdr_(cv))
          cseset_insert(exid_(cv_ex_(cv)), liveexprns, &old);
      }
    }
  }
}

static void SavedLocVals_Add(BlockHead *block, BlockHead *b, LocValList *lv,
                             StoreAccessList *sa, RegValue *rv, CompVals *comp) {
  blk_locvals_(block) = mkSavedLocVals(blk_locvals_(block), b, lv, sa, rv, comp);
}

static void SaveLocVals(
    BlockHead *block, LabelNumber *lab, LocValList *locvals,
    J_OPCODE op, ExSet *r2vals, int32 n,
    StoreAccessList *sl, RegValue *rv, CompVals *comp) {

  if (!is_exit_label(lab) && !blk_scanned_(lab->block)) {
    LocValList *lv = LocValList_Copy(locvals);
    if (op != J_NOOP) {
      for (; r2vals != NULL; r2vals = cdr_(r2vals)) {
        int32 n1 = n;
        Location *loc = NULL;
        Exprn *r2ex = r2vals->exprn;
        if (extype_(r2ex) == E_LOAD)
          loc = exloc_(r2ex);
        else if ((exop_(r2ex) == J_ADDK || exop_(r2ex) == J_SUBK) &&
                 extype_(e1_(r2ex)) == E_LOAD) {
          loc = exloc_(e1_(r2ex));
          if (exop_(r2ex) == J_ADDK)
            n1 -= e2k_(r2ex);
          else
            n1 += e2k_(r2ex);
        }
        if (loc != NULL) {
          Exprn *ex = find_unaryk(op, n1, U_NOTDEF2+U_NOTREF);
          LocValList *p = LocValList_FindLoc(lv, loc);
          if (p == NULL)
            lv = LocValList_New(lv, loc, ExprnToSet(ex));
          else
            p->vals = ExSet_Insert(ex, p->vals);
        }
      }
    }
    SavedLocVals_Add(lab->block, block, lv, StoreAccessList_Copy(sl), rv, comp);
  }
}

static RegValue *RegValue_CopyList(RegValue const *rv) {
  RegValue *p = NULL;
  for (; rv != NULL; rv = cdr_(rv))
    p = RegValue_New(p, rv_reg_(rv), ExSet_Copy(rv_val_(rv)));
  return p;
}

static RegValue *RegValueForReg(VRegnum r) {
  ExSet *rvals = valueinreg(r);
  return (rvals == NULL) ? NULL :
                           RegValue_New(NULL, r, ExSet_Copy(rvals));
}

static RegValue *ExportedR2Val(RegValue *exportedr, BlockHead *bfrom, CmpRec *cmpk, LabelNumber *lab) {
  if (!is_exit_label(lab) && !blk_scanned_(lab->block)) {
    BlockHead *bto = lab->block;
    if (exportedr != NULL)
      exportedr = RegValue_CopyList(exportedr);
    if (((blkflags_(bto) & BLK2EXIT) && blklength_(bto) <= 1)
        || (cmp_mask_(cmpk) != Q_AL && (blkflags_(bfrom) & BLKREXPORTED))) {
      RegValue *p = RegValueForReg(cmp_r2_(cmpk));
      if (p == NULL)
        return exportedr;
      else {
        if (exportedr != NULL)
          cdr_(p) = exportedr;
        return p;
      }

    } else if (blklength_(bfrom) == 0) {
      RegValue *rv = knownregs;
      for (; rv != NULL; rv = cdr_(rv)) {
        RegValue *q = RegValueForReg(rv->reg);
        if (q != NULL) { cdr_(q) = exportedr; exportedr = q; }
      }
    }
    return exportedr;
  }
  return NULL;
}

static void RewriteNext(BlockHead *b, LabelNumber *oldlab, LabelNumber *newlab,
                        SavedLocVals *sv) {
  bool ok = NO;
  if (blkflags_(b) & BLKSWITCH) {
    int32 n = blktabsize_(b);
    LabelNumber **table = blktable_(b);
    for (; --n >= 0; )
      if (table[n] == oldlab)
        ok = YES, table[n] = newlab;
  } else {
    if ((blkflags_(b) & BLK2EXIT) && blknext1_(b) == oldlab)
      ok = YES, blknext1_(b) = newlab;
    if (blknext_(b) == oldlab)
      ok = YES, blknext_(b) = newlab;
  }
  if (!ok) syserr(cse_rewritenext, blklabname_(b), lab_name_(oldlab));
  if (!is_exit_label(newlab)) {
    BlockHead *newdest = newlab->block;
    if (cse_AddPredecessor(newlab, b) && !blk_scanned_(newlab->block)) {
      RegValue *rv =  sv->exportedregs;
      RegValue *newrv = rv == NULL ? NULL :
          RegValue_New(NULL, rv_reg_(rv), ExSet_Copy(rv_val_(rv)));
      SavedLocVals_Add(newdest, sv->exporter, LocValList_Copy(sv->locvals),
                                StoreAccessList_Copy(sv->storeaccesses),
                                newrv,
                                CompVals_Copy(sv->comp));
    } else {
      SavedLocVals *newsv = blk_locvals_(newdest);
      for (; newsv != NULL; newsv = cdr_(newsv))
        if (newsv->exporter == b) {
          sl_locvals_(newsv) = LocValList_Intersect(sl_locvals_(newsv), sl_locvals_(sv));
          sl_exportedregs_(newsv) = MergeRegValues(sl_exportedregs_(newsv), sl_exportedregs_(sv));
          sl_comp_(newsv) = CompVals_Intersect(sl_comp_(newsv), sl_comp_(sv));
          break;
        }
    }
  }
}

static void ELV_cb(IPtr n, void *arg) {
  RegValue **pp = (RegValue **)arg;
  RegValue *rv = RegValueForReg(n);
  if (rv != NULL) {
    cdr_(rv) = *pp;
    *pp = rv;
  }
}

static void ExportLocVals(BlockHead *block, CmpRec *cmpk,
                          bool sideeffectfree, VRegSetP exportedregs) {
  /* Also, as a side effect, clear the known value of all Locations */
  int32 i;
  SavedLocVals *sv = blk_locvals_(block);
  LocValList *locvals = NULL;
  CompVals *cv, *compvals = NULL;
  RegValue *exportedr = NULL;
  if (sideeffectfree &&
      !(blkflags_(block) & (BLKLOOP|BLK2EXIT|BLKSWITCH|BLKREXPORTED)) &&
      !is_exit_label(blknext_(block)) && !blk_scanned_(blknext_(block)->block)) {
    LabelNumber *lab = blklab_(block);
    if (lab != blknext_(block))
      for (; sv != NULL; sv = cdr_(sv)) {
        BlockHead *prev = sl_exporter_(sv);
        if (debugging(DEBUG_CSE) && CSEDebugLevel(2))
          cc_msg("Block %ld successor rewritten from %ld to %ld\n",
                 blklabname_(prev), lab_name_(lab), lab_name_(blknext_(block)));
        RewriteNext(prev, lab, blknext_(block), sv);
        KillArc(prev, lab);
      }
  }
  if (blklength_(block) != 0) {
    VRegSetP rs = cseset_copy(exportedregs);
    bool old;
    for (i = R_A1; i < R_A1 + NARGREGS; i++)
      rs = cseset_insert(i, rs, &old);
    cseset_map(rs, ELV_cb, &exportedr);
  }
  for (sv = blk_locvals_(block); sv != NULL; sv = cdr_(sv)) {
    LocValList *lv = sl_locvals_(sv);
    for (; lv != 0; lv = LocValList_DiscardOne(lv))
      ExSet_Discard(lv->vals);
    sl_locvals_(sv) = NULL;
    StoreAccessList_Discard(sl_storeaccesses_(sv));
  }
  for (cv = comparevalues; cv != NULL; cv = cdr_(cv)) {
    if (!cse_KilledInBlock(exid_(cv->ex)))
      compvals = CompVals_New(compvals, cv->ex, CondList_Copy(cv->cond));
  }
  for (i = 0 ; i < LOCINDEXSIZE ; i++) {
    Location **index = locindex[i];
    int32 j;
    if (index == 0) break;
    for (j = 0 ; j < LOCSEGSIZE ; j++) {
      Location *q = index[j];
      ExSet *vals;
      if (q == NULL) break;
      vals = locvalue_(q);
      locvalue_(q) = NULL;
      if (q->load != NULL && IsLive(q->load)) {
        vals = LiveExSet(vals);
        if (vals != NULL) locvals = LocValList_New(locvals, q, vals);
      } else
        ExSet_Discard(vals);
    }
  }
  if (blk_pred_(block) != NULL || block == top_block) {
    if (!(var_cc_private_flags & 64L)) {
      if (blkflags_(block) & BLKSWITCH) {
        int32 n = blktabsize_(block);
        LabelNumber **table = CSENewN(LabelNumber *, n);
        memcpy(table, blktable_(block), (size_t)n * sizeof(LabelNumber *));
        while (--n > 0) {
          LabelNumber *lab = table[n];
          if (lab != NULL) {
            int32 j;
            J_OPCODE op = J_MOVK;
            for (j = n; --j >= 0; )
              if (table[j] == lab) op = J_NOOP, table[j] = 0;

            SaveLocVals(block, lab, locvals, op, cmp_r2vals_(cmpk), n-1, NULL,
                        RegValue_CopyList(exportedr), compvals);
          }
        }
        if (table[0] != NULL)
          SaveLocVals(block, table[0], locvals, J_NOOP, NULL, 0, NULL,
                      RegValue_CopyList(exportedr), compvals);

      } else if (blkflags_(block) & BLK2EXIT) {
        J_OPCODE op, op1;
        if (cmp_mask_(cmpk) == Q_EQ)
          op = J_NEK, op1 = J_MOVK;
        else if (cmp_mask_(cmpk) == Q_NE)
          op = J_MOVK, op1 = J_NEK;
        else
          op = op1 = J_NOOP;
        SaveLocVals(block, blknext1_(block), locvals, op1, cmp_r2vals_(cmpk), cmp_m_(cmpk),
                    NULL, ExportedR2Val(exportedr, block, cmpk, blknext1_(block)),
                    CompVals_Add(compvals, cmp_ex_(cmpk), cmp_mask_(cmpk)));
        SaveLocVals(block, blknext_(block), locvals, op, cmp_r2vals_(cmpk), cmp_m_(cmpk),
                    NULL, ExportedR2Val(exportedr, block, cmpk, blknext_(block)),
                    CompVals_Add(compvals, cmp_ex_(cmpk), Q_NEGATE(cmp_mask_(cmpk))));

      } else {
      /* Remove from storeaccesses everything that isn't live, since
         liveness info isn't a thing that gets exported.
       */
        StoreAccessList **slp = &storeaccesses, *sl;
        for (; (sl = *slp) != NULL;) {
          LocSet **locsp = &sa_locs_(sl), *locs;
          for (; (locs = *locsp) != NULL;) {
            Location *loc = locs->loc;
            if (!IsLive(loc->load)) {
              *locsp = cdr_(locs);
              if (!stores_r1(sa_ic_(sl)->op)) {
              /* This is a load : all possibly aliasing earlier stores */
              /* must be removed (or they may later be discarded as    */
              /* unwanted                                              */
                StoreAccessList **slp2 = &cdr_(sl), *sl2;
                for (; (sl2 = *slp2) != NULL;) {
                  LocSet **locsp2 = &sa_locs_(sl2), *locs2;
                  for (; (locs2 = *locsp2) != NULL;) {
                    Location *loc2 = locs2->loc;
                    if (loc == loc2 || possiblealias(loc, loc2))
                      *locsp2 = cdr_(locs2);
                    else
                      locsp2 = &cdr_(locs2);
                  }
                  if (sa_locs_(sl2) == NULL)
                    *slp2 = cdr_(sl2);
                  else
                    slp2 = &cdr_(sl2);
                }
              }
            } else
              locsp = &cdr_(locs);
          }
          if (sl->locs == NULL)
            *slp = cdr_(sl);
          else
            slp = &cdr_(sl);
        }
        if (cmpk->mask != Q_AL)
          exportedr = ExportedR2Val(exportedr, block, cmpk, blknext_(block));
        SaveLocVals(block, blknext_(block), locvals, J_NOOP, NULL, 0,
                    storeaccesses, exportedr, compvals);
      }
    }
  }
  for (; locvals != NULL; locvals = LocValList_DiscardOne(locvals))
    ExSet_Discard(locvals->vals);
}

#define SetTaken(val) (*taken = (val), YES)

static bool ComparisonValueKnown(bool *taken, CmpRec const *cmpk, CompVals const *cv) {
  for (; cv != NULL; cv = cdr_(cv)) {
    Exprn *ex = cv_ex_(cv);
    if (!cse_KilledInBlock(exid_(ex))) {
      if (ExSet_Member(ex, cmp_ex_(cmpk))) {
        CondList *cl = cv_cond_(cv);
        for (; cl != NULL; cl = cdr_(cl))
          if (Q_implies(cl_cond_(cl), cmp_mask_(cmpk)))
            return SetTaken(YES);
          else if (Q_implies(cl_cond_(cl), Q_NEGATE(cmp_mask_(cmpk))))
            return SetTaken(NO);

        return NO;

      } else if (exop_(ex) == J_CMPK
                 && cmp_ex_(cmpk) != NULL
                 && exop_(exs_ex_(cmp_ex_(cmpk))) == J_CMPK) {
        ExSet *es = cmp_ex_(cmpk);
        Exprn *e1 = e1_(ex);
        for (; es != NULL; es = cdr_(es)) {
          if (e1 == e1_(exs_ex_(es))) {
            int32 k1 = e2k_(ex),
                  k2 = e2k_(exs_ex_(es));
            CondList *cl = cv_cond_(cv);
            for (; cl != NULL; cl = cdr_(cl)) {
              switch (cl_cond_(cl)) {
              case Q_GE:
              case Q_GT: if (k1 > k2)
                           switch (cmp_mask_(cmpk)) {
                           case Q_GT: case Q_GE: case Q_NE:
                             return SetTaken(YES);
                           case Q_LT: case Q_LE: case Q_EQ:
                             return SetTaken(NO);
                           }
                         break;

              case Q_LE:
              case Q_LT: if (k1 < k2)
                           switch (cmp_mask_(cmpk)) {
                           case Q_LT: case Q_LE: case Q_NE:
                             return SetTaken(YES);
                           case Q_GT: case Q_GE: case Q_EQ:
                             return SetTaken(NO);
                           }
                         break;

              case Q_HS:
              case Q_HI: if ((uint32)k1 > (uint32)k2)
                           switch (cmp_mask_(cmpk)) {
                           case Q_HI: case Q_HS: case Q_NE:
                             return SetTaken(YES);
                           case Q_LO: case Q_LS: case Q_EQ:
                             return SetTaken(NO);
                           }
                         break;

              case Q_LS:
              case Q_LO: if ((uint32)k1 < (uint32)k2)
                           switch (cmp_mask_(cmpk)) {
                           case Q_LS: case Q_LO: case Q_NE:
                             return SetTaken(YES);
                           case Q_HI: case Q_HS: case Q_EQ:
                             return SetTaken(NO);
                           }
                         break;
              }
            }
          }
        }
      }
    }
  }
  return NO;
}
#undef SetTaken

static void MaybeKillBranchToBlock(BlockHead *block, CmpRec *cmpk) {
/* <block> ends with a CMPK, and is known to be otherwise side-effect  */
/* free. For any predecessors for which the result of the comparison   */
/* is known, we may change the successor <block> to the appropraite    */
/* successor of <block>.                                               */
  SavedLocVals *sv = blk_locvals_(block),
               *nextsv;
  LabelNumber *lab = blklab_(block);
  for (; sv != NULL; sv = nextsv) {
    /* We must take a copy here, because if the arc from sv->exporter  */
    /* to block is killed, sv is removed from block and attached to    */
    /* the arc's new destination.                                      */
    nextsv = cdr_(sv);
    if (!(blkflags_(sl_exporter_(sv)) & BLKSWITCH)) {
      ExSet *p;
      BlockHead *prev = sl_exporter_(sv);
      LabelNumber *nextlab = NULL;
      /* First try for the value of the comparison being known because */
      /* a variable with known value is its subject                    */
      if (cmpk->r2vals == NULL) {
        RegValue const *rv = RegValue_RegMember(cmp_r2_(cmpk), sl_exportedregs_(sv));
        if (rv != NULL) {
          ExSet *c1 = MOVKinSet(rv_val_(rv));
          if (c1 != NULL)
            nextlab = ComparisonDest(e1k_(exs_ex_(c1)), cmp_m_(cmpk), block);
        }
      } else for (p = cmp_r2vals_(cmpk); p != NULL; p = cdr_(p))
        if (extype_(exs_ex_(p)) == E_LOAD) {
          LocValList *vals = LocValList_FindLoc(sl_locvals_(sv), exloc_(exs_ex_(p)));
          if (vals != NULL) {
            ExSet *c1 = MOVKinSet(lv_vals_(vals));
            if (c1 != NULL) {
              nextlab = ComparisonDest(e1k_(exs_ex_(c1)), cmp_m_(cmpk), block);
              break;
            } else {
              /* Otherwise, see whether the subject of the comparison  */
              /* is known not to have the value compared against. This */
              /* is not the same as the case below, because knowledge  */
              /* that it doesn't have a particular value need not come */
              /* from there having been a comparison. For example,     */
              /* &global is known non-zero if global isn't weak.       */
              c1 = ExSet_OpMember(lv_vals_(vals), J_NEK, 0);
              if (c1 != NULL && e1k_(exs_ex_(c1)) == cmp_m_(cmpk)) {
                if (cmp_mask_(cmpk) == Q_EQ) {
                  nextlab = blknext_(block);
                  break;
                } else if (cmp_mask_(cmpk) == Q_NE) {
                  nextlab = blknext1_(block);
                  break;
                }
              }
            }
          }
        }
      if (nextlab == NULL) {
        /* Finally, see whether the result of the comparison can be    */
        /* inferred from one whose result is known                     */
        bool taken;
        if (cmp_ex_(cmpk) == NULL)
          for (p = cmpk->r2vals; p != NULL; p = cdr_(p)) {
            Exprn *e = find_binaryk(J_CMPK, exs_ex_(p), cmp_m_(cmpk), U_PEEK);
            if (e != NULL)
              cmp_ex_(cmpk) = ExSet_Insert(e, cmp_ex_(cmpk));
          }
        if (ComparisonValueKnown(&taken, cmpk, sl_comp_(sv)))
          nextlab = taken ? blknext1_(block) : blknext_(block);
      }
      if (nextlab != NULL && lab != nextlab) {
        if (debugging(DEBUG_CSE) && CSEDebugLevel(2))
          cc_msg("Block %ld successor rewritten from %ld to %ld\n",
                 blklabname_(prev), lab_name_(lab), lab_name_(nextlab));

        RewriteNext(prev, lab, nextlab, sv);
        KillArc(prev, lab);
      }
    }
  }
}

typedef struct {
  Binder *base;
  int32 k;
} AdconRec;

static J_OPCODE AdconInSet(ExSet *e, AdconRec *ad) {
  ExSet *c;
  J_OPCODE op;
  if ((c = ExSet_OpMember(e, J_ADDK, 0)) != NULL) {
    Exprn *e = c->exprn;
    J_OPCODE opa = exop_(e1_(e));
    op = opa & ~J_BASEALIGN4;
    if (op == J_ADCONV || op == J_ADCON) {
      ad->k = e2k_(e);
      ad->base = e1b_(e1_(e));
      return opa;
    }
  }
  if ((c = ExSet_OpMember(e, J_ADCONV, J_BASEALIGN4)) != NULL ||
      (c = ExSet_OpMember(e, J_ADCON, J_BASEALIGN4)) != NULL) {
    Exprn *e = c->exprn;
    ad->k = 0;
    ad->base = e1b_(e);
    return exop_(e);
  }
  return 0;
}

static void OpRewritten(Icode const *c) {
    if (debugging(DEBUG_CSE) && CSEDebugLevel(1)) {
      cc_msg("rewritten: ");
      print_jopcode(c);
    }
}

static void KillExpr(ExSet *s, Icode *p) {
  ptrdiff_t icoden = p - blkcode_(cse_currentblock);
  bool wasLocalCSE = cse_KillExprRef(s, p);
  for (; s != NULL; s = cdr_(s)) {
    Exprn *ex = s->exprn;
    ExprnUse *use, **usep;

    for (usep = &exuses_(ex); (use = *usep) != NULL; usep = &cdr_(use))
      if (use->block == cse_currentblock && icoden_(use) == icoden) {
        *usep = cdr_(use);
        if (!wasLocalCSE) {
          cseset_delete(exid_(ex), availableexprns, NULL);
          cseset_delete(exid_(ex), wantedexprns, NULL);
        }
        break;
      }
  }
}

#define setnotused_insert(x, s) \
  if (x >= NMAGICREGS) { cseset_insert(x, s, NULL); } else sideeffectfree = NO
#define setnotused_delete(x, s) cseset_delete(x, s, NULL)

/* These are now functions in preparation for use of J_VOLATILE.        */
static bool load_isvolatile(Icode const *c, Icode const *limit)
{   Icode const *nextic = c + 1;
    return nextic < limit &&
        (nextic->op== J_USE || nextic->op == J_USEF || nextic->op == J_USED);
}
static bool store_isvolatile(Icode const *c, Icode const *limit)
{   Icode const *nextic = c + 1;
    return nextic < limit && nextic->op == J_VSTORE;
}

static void corrupt_f(RealRegister r, RealRegSet_MapArg *a)
{   IGNORE(a);
    cse_corrupt_register(r);
}

static void cse_scanblock(BlockHead *block)
{
  Icode *c, *limit;
  CmpRec cmpk;
  LocSet *locs = NULL;
  int32 flags = blkflags_(block);        /* remember these now, because they may */
  LabelNumber *exit = blknext_(block);   /* get altered (by value propagation to */
#ifdef ENABLE_CSE
  LabelNumber *exit1 = blknext1_(block); /* a compare) before we reach the end.  */
#endif
  bool sideeffectfree = YES;
  int callcount = 0;
  bool istop = block == top_block;
  cmpk.mask = Q_AL;
  setnotused = NULL;
  storeaccesses = NULL;
  cse_currentblock = block;
  currenticode = blkcode_(block)-1;
  blocksetup();
  ImportLocVals(block);
  for (c = blkcode_(block), limit = c + blklength_(block); c < limit; ++c) {
#ifdef TARGET_IS_ARM_OR_THUMB
    RealRegUse reg;
#endif
    ExSet *values = NULL;
    ExSet *values2 = NULL;
    ExSet *valuesToStore;
    ExSet *e1, *e2;
    Exprn *node = NULL;
    int32 op = c->op;
    VRegInt r1 = c->r1, r2 = c->r2, r3 = c->r3, r4 = c->r4;
    int32 atmp;
    bool isload = NO,
         isvolatile = NO,
         maybelocalcse = YES,
         sideeffectfree_prev = sideeffectfree;
    int32 nvals = 0, valno = 0;
    currenticode = c;

    if (debugging(DEBUG_CSE) && CSEDebugLevel(1)) {
        cc_msg("%6d:", c - blkcode_(block));
        print_jopcode(c);
    }
    e1 = NULL; e2 = NULL; node = NULL;
    /*
     * Convert all instructions to nodes of the DAG.
     * Do copy propagation on the fly.
     */

/*
 * Setnotused records information about register which have been written but not
 * yet read. This is used in order to find basic blocks which don't
 * do anything useful and to find exported registers. If a virtual register is
 * written and read in the same basic block, all other reads are assumed to be local.
 * This may not be the case for physical registers (eg inline assembler), but we're
 * only interested in the set of rexported virtual registers...
 * Physical registers are considered global, so any instruction which sets these
 * is considered to have side effects (setnotused_insert).
 */

    if (reads_r1(op)) { e1 = valueinreg(r1.r); setnotused_delete(r1.r, setnotused); }
    if (reads_r2(op)) { e1 = valueinreg(r2.r); setnotused_delete(r2.r, setnotused); }
    if (reads_r3(op)) { e2 = valueinreg(r3.r); setnotused_delete(r3.r, setnotused); }
    if (reads_r4(op)) {                        setnotused_delete(r4.r, setnotused); }

    if (has_side_effects(c)) {
        sideeffectfree = NO;
    }
    if (loads_r1(op)) {
        if (op != J_INIT && op != J_INITF && op != J_INITD) {
            setnotused_insert(r1.r, setnotused);
        }
    }
    if (loads_r2(op)) {
        setnotused_insert(r2.r, setnotused);
    }
    if (sets_psr(c)) {
        sideeffectfree = NO;
    }
    switch (op & J_TABLE_BITS) {
    case J_SHRK:
    case J_SHRR:
      if (op & J_SIGNED && !OpIsShifted(op) && OpInSetFn(e1, SignBitClear)) {
        c->op = op = op ^ (J_SIGNED | J_UNSIGNED);
        OpRewritten(c);
      }
      break;

#ifdef TARGET_HAS_ROTATE
/* It is probably best to treat ROTATEs like SHIFT.  There are hence    */
/* 4 of them RO{LR}{RK}, but if TARGET_LACKS_ROL then ROL's are done    */
/* with a ROR of 32-n, thus improving current code (for n non-const).   */
/* ARM should probably have: TARGET_HAS_ROTATE, TARGET_LACKS_ROL        */
/* By the way, unless TARGET_HAS_SCALED_OPS then this code catches      */
/* rotates by variables, but not by constants!                          */
    case J_ADDR:
    case J_ORRR:
#ifdef TARGET_HAS_SCALED_ADDRESSING
      if (OpIsShifted(op)) {
        int32 shift = (op & J_SHIFTMASK) >> J_SHIFTPOS;
        ExSet *ex;
        if ( ( ( !(shift & SHIFT_RIGHT) &&
                 (ex = ExSet_OpMember(e1, J_SHRK | J_UNSIGNED, 0)) != NULL) ||
               ( (shift & (SHIFT_RIGHT+SHIFT_ARITH)) == SHIFT_RIGHT &&
                 (ex = ExSet_OpMember(e1, J_SHLK, J_SIGNbits)) != NULL) ) &&
             ExSet_Member(e1_(ex->exprn), e2) &&
             (shift & SHIFT_MASK) == (32 - e2k_(ex->exprn)) &&
             IsLive(ex->exprn)) {
          Icode *ip = &useicode_(exuses_(ex->exprn));
          c->op = op = J_RORK;
          c->r2 = r2 = ip->r2;
          c->r3.i = r3.i = (shift & SHIFT_RIGHT) ? 32 - e2k_(ex->exprn) : e2k_(ex->exprn);
          OpRewritten(c);
          e1 = e2;
          e2 = (ExSet *)DUFF_ADDR;
        }
      } else
#endif
        {
        Exprn *shex = ORRR_IsRORR(e1, e2);
        if (shex != NULL && IsLive(shex)) {
          Icode *ip = &useicode_(exuses_(shex));
          e1 = ExprnToSet(e1_(shex));
          e2 = ExprnToSet(e2_(shex));
          c->op = op = J_RORR;
          c->r2 = r2 = ip->r2;
          c->r3 = r3 = ip->r3;
          OpRewritten(c);
        }
      }
      break;
#endif

    case J_ANDR:
      {
#ifdef TARGET_HAS_SCALED_ADDRESSING
        int32 shift = (op & J_SHIFTMASK) >> J_SHIFTPOS;
        if (shift & SHIFT_RIGHT) {
          ExSet *c1 = MOVKinSet(e1);
          if (c1 != NULL) {
            shift &= SHIFT_MASK;
            if (just32bits_(e1k_(c1->exprn)) ==
                (1L << (32 - shift)) - 1L) {
              c->op = op = J_SHRK | J_UNSIGNED;
              c->r2 = r3;
              c->r3.i = r3.i = shift;
              OpRewritten(c);
              e1 = e2;
              e2 = (ExSet *) DUFF_ADDR;
            }
          }
        } else if (shift == 0)
#endif
          {
          Exprn *shex = SHRR_IsLogical(e1, e2);
          if (shex != NULL && IsLive(shex)) {
            Icode *ip = &useicode_(exuses_(shex));
            e1 = ExprnToSet(e1_(shex));
            e2 = ExprnToSet(e2_(shex));
            c->op = op = J_SHRR | J_UNSIGNED;
            c->r2 = r2 = ip->r2;
            c->r3 = r3 = ip->r3;
            OpRewritten(c);
          }
        }
      }
      break;

    case J_ANDK:
      if (r3.i != -1)
      { int32 k = ~r3.i;
        int32 lowones = logbase2(k & -k);
        if (TopBitsKnownZero(e1, 32 - lowones)) {
          c->op = op = J_MOVR;
          c->r3 = r3 = r2;
          c->r2.r = r2.r = GAP;
          OpRewritten(c);
          e2 = e1; e1 = NULL;
        }
      }
      break;
    }
    switch (op & J_TABLE_BITS) {
    case J_CALLK:
#ifdef TARGET_HAS_DIVREM_FUNCTION
      if (   (Expr *)r3.b == arg1_(sim.divfn)
          || (Expr *)r3.b == arg1_(sim.udivfn))
        c->r2.i = r2.i = k_setresultregs_(r2.i, 2);
      if (   (Expr *)r3.b == sim.llsdiv || (Expr *)r3.b == sim.llsrdv
          || (Expr *)r3.b == sim.lludiv || (Expr *)r3.b == sim.llurdv)
        c->r2.i = r2.i = k_setresultregs_(r2.i, 4);
#endif
    case J_CALLR:
      if (e2 != NULL) {
      /* (won't be if op is J_CALLK) */
        ExSet *e = ExSet_OpMember(e2, J_ADCON, 0);
        if (e != NULL) {
          c->op = op = J_CALLK;
          c->r3.b = r3.b = e1b_(e->exprn);
          OpRewritten(c);
          e2 = NULL;
        }
      }
    case J_OPSYSK:  /* @@@ pure OPSYSK */
      { int32 i;
        sideeffectfree = NO;
        if (op == J_CALLK) {
          ExSet *arg[NANYARGREGS==0 ? 1 : NANYARGREGS];
          int32 val;
          int32 nargs = k_argregs_(r2.i);
          DRes dres;
          for (i = 0 ; i < nargs; i++) {
            VRegnum r = k_argisfp_(r2.i,i) ? R_FA1+i : R_A1+i-k_fltregs_(r2.i);
            setnotused_delete(r, setnotused);
            arg[i] = valueinreg(r);
          }
          if (CSE_EvaluableIntValuedCall(r3.ex, r1.r, r2.i, arg, &val)) {
            r3.i  = val;
            r1 = c->r1;
            goto ForgeMOVK;
          }
#ifdef TARGET_HAS_DIV_10_FUNCTION
          if (
#ifndef TARGET_HAS_DIVREM_FUNCTION
              r3.ex == arg1_(sim.remfn) ||
              r3.ex == arg1_(sim.uremfn) ||
#endif
              r3.ex == arg1_(sim.divfn) ||
              r3.ex == arg1_(sim.udivfn) ) {

            ExSet *v1 = MOVKinSet(arg[0]);
            if (v1 != NULL && e1k_(v1->exprn) == 10) {
              Icode *a1p = NULL, *a2p = NULL;
              Icode *p = c, *base = blkcode_(block);
              for (; --p >= base; ) {
                if (loads_r1(p->op)) {
                  if (a1p == NULL && p->r1.r == R_A1) {
                    a1p = p;
                    if (a2p != NULL) break;
                  } else if (a2p == NULL && p->r1.r == R_A1+1) {
                    a2p = p;
                    if (a1p != NULL) break;
                  }
                }
              }
              if (a1p != NULL && a2p != NULL) {
                arg[0] = arg[1];
                a2p->r1.r = R_A1;
                a1p->r1.r = vregister(INTREG);
                r2.i = c->r2.i = k_argdesc_(1, 0, 1, 0, 2, r2.i & K_FLAGS);
                r3.ex = c->r3.ex =
#ifndef TARGET_HAS_DIVREM_FUNCTION
                    r3.ex == arg1_(sim.remfn)  ? arg1_(sim.rem10fn) :
                    r3.ex == arg1_(sim.uremfn) ? arg1_(sim.urem10fn) :
#endif
                    r3.ex == arg1_(sim.divfn)  ? arg1_(sim.div10fn) :
                                                 arg1_(sim.udiv10fn);
                OpRewritten(c);
              }
            }
          }
#endif
          if (CSE_EvaluableDoubleValuedCall(r3.ex, r1.r, r2.i, arg, &dres)) {
            if (r1.r != R_F0) {
              /* The call returns two integer registers. To replace it  */
              /* it, there must be two preceding instructions which we  */
              /* can overwrite (as yet, we're not extending the block): */
              /* the replacement is ADCONx + two loads.                 */
              Icode *blockstart = blkcode_(block);
              Icode *prev1 = c-1,
                    *prev2;
              for (; prev1 > blockstart && prev1->op == J_SETSPENV; prev1--) continue;
              prev2 = prev1 - 1;
              if (prev2 > blkcode_(block)
                  && loads_r1(prev1->op) && prev1->r1.r < nargs
                  && ( (loads_r1(prev2->op) && prev2->r1.r < nargs)
                      || (prev1->op == J_MOVR
                          && loads_r1(prev2->op) && prev2->r1.r == prev1->r3.r))) {
                VRegnum res1, res2, r = vregister(ADDRREG);
                /* Kill any CSE definitions OR references of the 2 LDRKs */
                KillExpr(arg[prev1->r1.r], prev1);
                if (prev2->r1.r < nargs)
                  KillExpr(arg[prev2->r1.r], prev2);
                else
                  KillExpr(arg[prev1->r1.r], prev2);
                if (dres.isdouble) {
                  INIT_IC(*prev2, J_ADCOND);
                  prev2->r3.f = CSE_NewDCon(&dres.val.d);
                } else {
                  INIT_IC(*prev2, J_ADCONLL);
                  prev2->r3.i64 = CSE_NewLLCon(&dres.val.i);
                }
                /* Unfortunately, we can't do the following (though in  */
                /* principle we should) because a load will have killed */
                /* an earlier instance of the same load in the list     */
                /* (for performance reasons). The only effect is that   */
                /* we won't be able to optimise away a redundant store. */
#if 0
                while (storeaccesses != NULL
                       && (sa_ic_(storeaccesses) == prev1
                           || sa_ic_(storeaccesses) == prev2))
                    storeaccesses = StoreAccessList_DiscardOne(storeaccesses);
#endif
                prev2->r1.r = r;
                if (c+2 < limit
                    && reads_r1(c[1].op) && c[1].r1.r == r1.r
                    && reads_r1(c[2].op) && c[2].r1.r == r1.r+1) {
                  res1 = vregister(INTREG); res2 = vregister(INTREG);
                  c[1].r1.r = res1;
                  c[2].r1.r = res2;
                } else {
                  res1 = r1.r; res2 = r1.r+1;
                }
                INIT_IC(*prev1, J_LDRK+J_ALIGN4);
                prev1->r1.r = res1;
                prev1->r2.r = r;
                prev1->r3.i = 0;
                INIT_IC(*c, J_LDRK+J_ALIGN4);
                c->r1.r = res2;
                c->r2.r = r;
                c->r3.i = 4;
                /* Now rescan the 3 inserted instructions */
                c -= 3;
                continue;
              } else {
                /* We can't replace the call by its value, but we do    */
                /* know what that value is, and must remember it in     */
                /* order to be able to fold it as an operand of further */
                /* expressions.                                         */
                Exprn *base = (dres.isdouble)
                  ? find_exprn(J_ADCOND, (Exprn *)CSE_NewDCon(&dres.val.d), 0, NULL, U_NOTREF+U_NOTDEF2)
                  : find_exprn(J_ADCONLL, (Exprn *)CSE_NewLLCon(&dres.val.i), 0, NULL, U_NOTREF+U_NOTDEF2);
                Exprn *r0ex = locload_(find_memloc(loctype(J_LDRK), base, 0, J_LDRK+J_ALIGN4, 0));
                Exprn *r1ex = locload_(find_memloc(loctype(J_LDRK), base, 4, J_LDRK+J_ALIGN4, 0));
                cseset_insert(exid_(r0ex), liveexprns, NULL);
                cseset_insert(exid_(r1ex), liveexprns, NULL);
                values = ExprnToSet(r0ex);
                values2 = ExprnToSet(r1ex);
                maybelocalcse = NO;
              }
              break;

            } else {
              r3.f = CSE_NewDCon(&dres.val.d);
              goto ForgeMOVDK;
            }
          }
          if ((r2.i & K_PURE) &&
#ifdef TARGET_FP_ARGS_IN_FP_REGS
            /* @@@ the 2 here is a bit dubious                          */
              k_intregs_(r2.i)+2*k_fltregs_(r2.i) == k_argwords_(r2.i)
#else
              k_argregs_(r2.i) == k_argwords_(r2.i)
#endif
             ) {
/* It is not clear to AM that we need vregsort below, the reg suffices! */
            { int32 nres = k_resultregs_(r2.i);
            /* We need a better way of handling the divide + remainder functions */
              if (nres > 1) {
                if (r1.r == R_A1+1 && nres == 2) {
                  /* Call is of a function returning two distinct results */
                  /* - only the second is used here. (div+rem fn, this    */
                  /* is use of rem)                                       */
                  values = FindRes2CallSet(r3.b, vregsort(r1.r), r2.i, arg, c);
                  valno = r1.r-R_A1;
                } else
                  /* either the div case of the above, or a function      */
                  /* returning a single result in multiple registers.     */
                  /* k_resultregs can't distinguish.                      */
                if (r3.ex == arg1_(sim.div10fn) || r3.ex == arg1_(sim.udiv10fn)
                    || r3.ex == arg1_(sim.divfn) || r3.ex == arg1_(sim.udivfn))
                  values = FindCallSet(r3.b, vregsort(r1.r), r2.i, arg);
                else {
                  values = Find2ResCallSet(&values2, r3.b, vregsort(r1.r), r2.i, arg, c);
                  nvals = 1;
                  valno = r1.r-R_A1;
                }
              } else {
                values = FindCallSet(r3.b, vregsort(r1.r), r2.i, arg);
              }
            }
          } else {
            corruptmem();
          }
        } else {
          corruptmem();
        }
        callcount++;
      }
      if (op == J_CALLK &&
          !(var_cc_private_flags & 32L) &&
          returnsheapptr(bindsym_(r3.b)))
        node = heapptr;
      break;

    case J_ADCON:
      node = find_unaryb(op, r3.b, 0);
      if (r3.b != datasegment
          && ((bindstg_(r3.b) & (bitofstg_(s_static)+u_loctype+b_undef+b_fnconst)) == bitofstg_(s_static))
          && bindaddr_(r3.b) == 0) {
        values = ExprnToSet(node);
        node = find_unaryb(op, datasegment, 0);
        values = ExSet_Insert(node, values);
      }
      break;

    case J_FNCON:
    case J_ADCONV:
      node = find_unaryb(op, r3.b, 0);
      break;

    case J_PUSHR:
    case J_PUSHF:
    case J_PUSHL:
    case J_PUSHD:
      sideeffectfree = NO;
      break;

    case J_LDRVK:  case J_LDRLVK:
    case J_LDRFVK: case J_LDRDVK:
    case J_LDRBVK: case J_LDRWVK:
TransformedToLDRVK:
      { Exprn *base = find_unaryb(J_ADCONV, r3.b, U_NOTDEF+U_NOTREF);
        isvolatile = load_isvolatile(c,limit);
        locs = LocSet_New(NULL,
                    find_memloc(loctype(op), base, r2.i, j_to_ldrk(op), 0));
        values = locs_read(locs, 0, op);
if (debugging(DEBUG_CSE) && CSEDebugLevel(1))
      ExSet_Print(values, " LDRVK values\n");

        if (op == J_LDRVK) {
          StoreAccessList *a = storeaccesses;
          for (; a != NULL; a = cdr_(a))
            if (a->ic->op != J_NOOP && stores_r1(a->ic->op)) {
              if (IsLive(locs->loc->load) && LocSet_Member(locs->loc, a->locs)) {
                c->op = op = J_MOVR;
                c->r2.r = r2.r = GAP;
                c->r3 = r3 = a->ic->r1;
                OpRewritten(c);
              } else
                a = NULL;
              break;
            }
          if (a != NULL) break;
        }
      }
      isload = YES;
      break;

    case J_STRVK:  case J_STRLVK:
    case J_STRFVK: case J_STRDVK:
    case J_STRBVK: case J_STRWVK:
TransformedToSTRVK:
      { Exprn *base = find_unaryb(J_ADCONV, r3.b, U_NOTDEF+U_NOTREF);
        ExSet *val = valueinreg(r1.r);
        isvolatile = store_isvolatile(c,limit);
        sideeffectfree = NO;
        locs = LocSet_New(NULL,
                    find_memloc(loctype(op), base, r2.i, j_to_ldrk(op), 0));
        if (storein_i(r1.r, val, locs, isvolatile)) KillRedundantStore();
        if ((op & J_TABLE_BITS) == J_STRBVK && alignof_toplevel_auto >= 4)
          if (CanAmalgamateStoreBytes(locs)) {
            c->op = op = J_STRVK+J_ALIGN4;
            c->r2.i = r2.i = r2.i & ~3;
            OpRewritten(c);
            goto TransformedToSTRVK;
          }
      }
      break;

    case J_LDRR:  case J_LDRLR:
    case J_LDRFR: case J_LDRDR:
    case J_LDRBR: case J_LDRWR:
      { ExSet *c2;
        e1 = readreg(r2.r);
        e2 = readreg(r3.r);
        c2 = MOVKinSet(e2);
        if (c2 != NULL) {
          int32 a2 = ShiftedVal(op, e1k_(c2->exprn));
          if (validdisplacement(op, a2)) {
            c->op = op = j_to_ldrk(op) | (op & J_SIGNbits);
            c->r3.i = r3.i = a2;
            OpRewritten(c);
            goto TransformedToLDRK;
          }
        }
        isvolatile = load_isvolatile(c,limit);
        locs = rr_locs(op, e1, e2);
        if (locs != NULL) values = locs_read(locs, 0, op);
      }
      isload = YES;
      break;

    case J_LDRBK:
      { ExSet *p = ExSet_OpMember(e1, J_STRING, 0);
        if (p != NULL) {
          int32 n = r3.i;
          StringSegList *s = e1s_(p->exprn);
          for (; s != NULL; n -= s->strseglen, s = s->strsegcdr)
            if (n < s->strseglen) {
              r3.i = (op & J_SIGNED) ? ((signed char *)s->strsegbase)[n] :
                                      s->strsegbase[n];
              goto ForgeMOVK;
            }
          if (n == 0) {
            r3.i = 0;
            goto ForgeMOVK;
          }
        }
      }
    case J_LDRK:  case J_LDRLK:
    case J_LDRFK: case J_LDRDK:
    case J_LDRWK:
      e1 = readreg(r2.r);
TransformedToLDRK:
      { ExSet *p = e1;
        AdconRec ad;
        J_OPCODE adcon = AdconInSet(p, &ad);
        if (adcon == J_ADCONV) {
          c->op = op = J_addvk(op);
          c->r2.i = r2.i = r3.i + ad.k;
          c->r3.b = r3.b = ad.base;
          OpRewritten(c);
          goto TransformedToLDRVK;
        } else if (adcon == J_ADCON+J_BASEALIGN4 && (ad.k & 3) == 0)
          c->op = op |= J_BASEALIGN4;
        isvolatile = load_isvolatile(c,limit);
        locs = NULL;
        for (; p != NULL; p = cdr_(p)) {
          Location *loc =
            find_memloc(loctype(op), p->exprn, r3.i, j_to_ldrk(op), LOC_REALBASE);
          if (loc != NULL) locs = LocSet_New(locs, loc);
        }
      }
      if (locs != NULL) values = locs_read(locs, 0, op);
      isload = YES;
      break;

    case J_STRR:  case J_STRLR:
    case J_STRFR: case J_STRDR:
    case J_STRBR: case J_STRWR:
      { ExSet *c2;
        sideeffectfree = NO;
        valuesToStore = valueinreg(r1.r);
        e1 = readreg(r2.r);
        e2 = readreg(r3.r);
        c2 = MOVKinSet(e2);
        if (c2 != NULL) {
          int32 a2 = ShiftedVal(op, e1k_(c2->exprn));
          if (validdisplacement(op, a2)) {
            c->op = op = J_LDtoST(j_to_ldrk(op));
            c->r3.i = r3.i = a2;
            OpRewritten(c);
            goto TransformedToSTRK;
          }
        }
        isvolatile = store_isvolatile(c,limit);
        locs = rr_locs(op, e1, e2);
        if (locs != NULL && storein_i(r1.r, valuesToStore, locs, isvolatile))
          KillRedundantStore();
      }
      break;

    case J_STRK:  case J_STRLK:
    case J_STRFK: case J_STRDK:
    case J_STRBK: case J_STRWK:
      sideeffectfree = NO;
      valuesToStore = valueinreg(r1.r);
      e1 = readreg(r2.r);
TransformedToSTRK:
      { AdconRec ad;
        J_OPCODE adcon = AdconInSet(e1, &ad);
        if (adcon == J_ADCONV) {
          op = c->op = J_addvk(op);
          r2.r = c->r2.r = r3.i + ad.k;
          r3.b = c->r3.b = ad.base;
          OpRewritten(c);
          e1 = valuesToStore;
          goto TransformedToSTRVK;
        } else if (adcon == J_ADCON+J_BASEALIGN4 && (ad.k & 3) == 0)
          c->op = op |= J_BASEALIGN4;
        isvolatile = store_isvolatile(c,limit);
        { LocSet *locs = NULL;
          if (storeink(r1.r, valuesToStore, loctype(op), r3.i, j_to_ldrk(op), e1, isvolatile, &locs))
            KillRedundantStore();
          if ((op & J_TABLE_BITS) == J_STRBK && (op & J_BASEALIGN4))
            if (CanAmalgamateStoreBytes(locs)) {
              c->op = op = J_STRK+J_ALIGN4+J_BASEALIGN4;
              c->r3.i = r3.i = r3.i & ~3;
              OpRewritten(c);
              goto TransformedToSTRK;
            }
        }
      }
      break;

    case J_LDRV1: case J_LDRLV1: case J_LDRFV1: case J_LDRDV1:
      break;
    case J_LDRV: case J_LDRLV: case J_LDRFV: case J_LDRDV:
      isvolatile = load_isvolatile(c,limit);
      locs = LocSet_New(NULL, find_varloc(r3.b, j_to_ldrk(op), 0));
      values = locs_read(locs, 0, op);
      isload = YES;
      break;

    case J_STRV: case J_STRLV: case J_STRFV: case J_STRDV:
      isvolatile = store_isvolatile(c,limit);
      sideeffectfree = NO;
      locs = LocSet_New(NULL, find_varloc(r3.b, j_to_ldrk(op), 0));
      if (storein_i(r1.r, e1, locs, isvolatile))
        KillRedundantStore();
      break;

    ForgeMOVR:
      e2 = ExSet_Copy(e1); e1 = NULL;
      c->op = op = J_MOVR;
      c->r3.r = r3.r = r2.r;
      c->r2.r = r2.r = GAP;
      OpRewritten(c);

    case J_MOVR:
#ifdef never
>>      if (EvalUnary(op, &atmp, e2))
>>      {   r3.i = atmp;
>>          goto ForgeMOVK;
>>      }
#endif
      if (isany_realreg_(r3.r) && e2 == NULL) {
        node = find_loadr(r3.r, U_NOTDEF2+U_NOTREF);
        if (istop) {
        /* handle the MOVR virtreg, realreg jopcodes present at function entry
           to initialise argument binders (really, these ought to be STRVs)
         */
          BindList *bl = argument_bindlist;
          Binder *thisarg = NULL;
          if (currentfunction.structresult != NULL
              && r1.r == bindxx_(currentfunction.structresult)) {
            /* A structure result pointer is guaranteed non-NULL        */
            /* (this is important in C++ if there's an inlined copy     */
            /* constructor: we avoid a test and allocation call)        */
            thisarg = currentfunction.structresult;
            node = find_unaryk(J_NEK, 0, U_NOTDEF2+U_NOTREF);
          } else
            for (; bl != NULL; bl = cdr_(bl))
              if (r1.r == bindxx_(bl->bindlistcar)) {
                thisarg = bl->bindlistcar;
                break;
              }

          if (thisarg != NULL) {      /* j_to_ldrk(J_LDRK) */
            Location *loc = find_varloc(thisarg, J_LDRK|J_ALIGN4, 0);
            if (storein(GAP, loc, ExprnToSet(node), NO))
              KillRedundantStore();
          }
        }
        break;
      } else if (isany_realreg_(r1.r)) {
        ExSet *e = ExSet_OpMember(e2, CSE_LOADR, 0);
        if (e != NULL && exloadr_(e->exprn) == r1.r) {
          r3.r = c->r3.r = r1.r;
          OpRewritten(c);
          values = e2;
          break;
        }
      }
    case J_MOVFR: case J_MOVDR:
      if (e2 != NULL) {
        values = e2;
        ExSet_Map(e2, AddUse, NULL);
      }
      break;

#ifdef TARGET_HAS_BLOCKMOVE
/* AM: In the following 'n' is a multiple of alignof_struct.  However,  */
/* it may be desirable to know whether the front-end can guarantee      */
/* that a MOVC of (say) 12 can is word-aligned if alignof_struct=1.     */
/* Future direction: use J_SHIFTMASK for this?                          */
    case J_CLRC:   /* CLRC dest, -, n      */
      e1 = NULL;
    case J_MOVC:   /* MOVC dest, source, n */
      /* These have implications for value propagation, and for
         elimination of unwanted stores.
         Also, they may (depending on target) destroy some registers.
         Because this is in flux, there are no written rules.
       */
      e2 = valueinreg(r1.r);
      { ExSet *e;
        int32 offset = 0;
        int32 load = J_LDRK | (op & J_ALIGNMENT);
        sideeffectfree = NO;
        for (e = e2; e != NULL; e = cdr_(e))
          if (AdconBaseK(e->exprn, &offset) != NULL)
            break;
        if (e == NULL) {
          corruptmem();
        } else {
          if (r3.i <= 32 && (r3.i & 3) == 0) {
            ExSet *vals[8];
            int32 i;
            for (i = r3.i>>2; --i >= 0; ) {
              LocSet *locs = NULL;
              ExSet *p;
              vals[i] = NULL;
              for (p = e1; p != NULL; p = cdr_(p)) {
                Location *loc =
                  find_memloc(LOC_(MEM_I), p->exprn, 4*i, load, LOC_REALBASE);
                if (loc != NULL) {
                  locs = LocSet_New(locs, loc);
                  EnsureOldStore(loc, 0);
                }
              }
              if (locs != NULL) vals[i] = locs_read(locs, U_NOTREF+U_NOTDEF2, load);
              for (; locs != NULL; locs = cdr_(locs)) {
                StoreAccessList *a = storeaccesses;
                for (; a != NULL; a = cdr_(a)) {
                  LocSet *slocs = a->locs;
                  for (; slocs != NULL; slocs = cdr_(slocs))
                    if (possiblealias(locs->loc, slocs->loc)) {
                      a->needed = YES;
                      break;
                    }
                }
              }
            }
            { bool redundant = YES;
              for (i = r3.i>>2; --i >= 0; )
                if (!storeink(GAP, vals[i], LOC_(MEM_I), 4*i, load, e2, NO, &locs))
                  redundant = NO;
              if (redundant) KillRedundantStore();
            }
          } else {
            corruptlocswithbase(e->exprn, r3.i);
          }
        }
        { StoreAccessList *a = storeaccesses;
          for (; a != NULL; a = cdr_(a)) {
            LocSet *locs = a->locs;
            for (; locs != NULL; locs = cdr_(locs)) {
              Location *loc = locs->loc;
              if (!(loctype_(loc) & LOC_anyVAR)) {
                int32 off = locoff_(loc);
                if (ExSet_Member(locbase_(loc), e1) &&
                    0 <= off && off < r3.i) {
                  a->needed = YES;
                  break;
                }
              }
            }
          }
        }
      }
      node = NULL;
      break;
#endif

    case J_SETSPENV:
#ifdef NOT_YET
      /* Not yet convinced by the worth of this */
      { int32 nb = length((List *)r3.bl) - length((List *)r2.bl);
        if (nb < 0) {
        /* Leaving a scope: all stores to stack objects going out of    */
        /* scope (which haven't been used) can be killed. This is       */
        /* mainly useful for address-taken things (others regalloc can  */
        /* kill, maybe after structure splitting). Structure arguments  */
        /* for evaluated functions are the prime case to catch.         */
          BindList *bl = r2.bl;
          LocSet *kills = NULL;
          for (; ++nb <= 0; bl = cdr_(bl)) {
            Location *loc = find_varloc(bl->bindlistcar, j_to_ldrk(J_LDRV), LOC_PEEK);
            StoreAccessList *sa;
            Exprn *base;
            if (loc != NULL && IsLive(locload_(loc)))
              kills = LocSet_New(kills, loc);

            base = find_unaryb(J_ADCONV, bl->bindlistcar, U_PEEK);
            if (base != NULL)
              for (sa = storeaccesses; sa != NULL; sa = cdr_(sa)) {
                LocSet *locs = sa_locs_(sa);
                for (; locs != NULL; locs = cdr_(locs)) {
                  loc = ls_loc_(locs);
                  if (!(loctype_(loc) & LOC_anyVAR)
                      && locbase_(loc) == base
                      && IsLive(locload_(loc))
                      && !LocSet_Member(loc, kills))
                    kills = LocSet_New(kills, loc);
                }
              }
          }
          for (; kills != NULL; kills = LocSet_DiscardOne(kills))
            KillOldUnusedStore(ls_loc_(kills), 0);
        }
      }
#endif
    case J_SETSPGOTO:
      setsplist = (SetSPList*)CSEList3((IPtr)setsplist,
                                       (IPtr)cse_currentblock,
                                       (IPtr)currenticode);
    case J_ENTER:
    case J_INIT: case J_INITF: case J_INITD:
    case J_INFOLINE: case J_INFOSCOPE: case J_INFOBODY:
    case J_COUNT:
    case J_WORD:
    case J_ORG:
      sideeffectfree = NO;
      node = NULL;
      break;

    case J_THUNKTABLE:
    case J_CASEBRANCH:
      sideeffectfree = NO;
      node = NULL;
      cmp_r2vals_(&cmpk) = e1;
      break;

    case J_CMPFK:
      { ExSet *c1 = MOVFKinSet(e1);
        int r;
        if (c1 != NULL && CSE_Compare_F(&r, &e1f_(c1->exprn)->floatbin.fb, &r3.f->floatbin.fb)) {
          RemoveComparison(r, 0, block);
          break;
        }
      }
      e2 = ExprnToSet((Exprn *)CSE_CanonicalFPConst(r3.f));
      goto CmpF;

    case J_CMPDK:
      { ExSet *c1 = MOVDKinSet(e1);
        int r;
        if (c1 != NULL && CSE_Compare_D(&r, e1f_(c1->exprn), r3.f)) {
          RemoveComparison(r, 0, block);
          break;
        }
      }
      e2 = ExprnToSet((Exprn *)CSE_CanonicalFPConst(r3.f));
      goto CmpF;

    case J_CMPFR:
      { ExSet *c1 = MOVFKinSet(e1);
        ExSet *c2 = MOVFKinSet(e2);
        int r;
        if (c1 != NULL && c2 != NULL &&
            CSE_Compare_F(&r, &e1f_(c1->exprn)->floatbin.fb, &e1f_(c2->exprn)->floatbin.fb)) {
          RemoveComparison(r, 0, block);
          break;
        }
      }
      goto CmpF;

    case J_CMPDR:
      { ExSet *c1 = MOVDKinSet(e1);
        ExSet *c2 = MOVDKinSet(e2);
        int r;
        if (c1 != NULL && c2 != NULL &&
            CSE_Compare_D(&r, e1f_(c1->exprn), e1f_(c2->exprn))) {
          RemoveComparison(r, 0, block);
          break;
        }
      }

CmpF: if (e1 != NULL && e2 != NULL) {
        bool taken;
        cmp_mask_(&cmpk) = op & CSE_COMPARE_MASK;
        cmp_ex_(&cmpk) = FindRRSet(op & ~CSE_COMPARE_MASK, e1, e2, U_NOTDEF+U_NOTREF);
        cmp_r2vals_(&cmpk) = NULL;
        if (ComparisonValueKnown(&taken, &cmpk, comparevalues)) {
          RemoveComparison1(taken, block);
          break;
        }
#ifdef TARGET_ALLOWS_COMPARE_CSES
        values = FindRRSet(op & ~CSE_COMPARE_MASK, e1, e2, 0);
        ExSet_Map(values, AddCompare, NULL);
        blk_cmp_(block) = ExSet_Copy(values);
#endif
      }
      break;

#ifdef RANGECHECK_SUPPORTED
    case J_CHKLR: case J_CHKUR:
      { ExSet *c2 = MOVKinSet(e2);
        if (c2 == NULL) {
          values = FindRRSet(op, e1, e2, 0);
          break;
        }
        r3.i = ShiftedVal(op, e1k_(c2->exprn));
      }
      /* and fall through */
    case J_CHKLK: case J_CHKUK:
      { ExSet *c1 = MOVKinSet(e1);
        if (c1 != NULL) {
          int32 index = e1k_(c1->exprn);
          int32 baseop = op & J_TABLE_BITS;
          if ((baseop == J_CHKLK || baseop == J_CHKLR) ? (index >= r3.i) :
                                                         (index <= r3.i))
            goto KillOp;
        }
      }
      values = FindRKSet(op, e1, r3.i, 0);
      break;

    case J_CHKNEK:
      { ExSet *c1 = MOVKinSet(e1);
        if (c1 != NULL && e1k_(c1->exprn) != r3.i)
          goto KillOp;
      }
      values = FindRKSet(op, e1, r3.i, 0);
      break;

    KillOp:
      op = c->op = J_NOOP;
      OpRewritten(c);
      node = NULL;
      break;

    case J_CHKNEFR:
    case J_CHKNEDR:
      break;

#endif
    case J_CMPR:
      if (e1 == NULL || e2 == NULL)
        break;

      { ExSet *c2 = MOVKinSet(e2);
        int32 cond = op & (Q_MASK & ~Q_UBIT);
        int32 n1 = 0, n2 = 0;
        bool taken;
        if (c2 == NULL) {
          if ((c2 = MOVKinSet(e1)) != NULL) {
#ifdef TARGET_HAS_SCALED_ADDRESSING
            if ((cond == Q_EQ || cond == Q_NE) &&
                ShiftedOutBitsKnownZero(op, e2)) {
              n1 = e1k_(c2->exprn);
              n2 = ShiftedVal(op ^ (SHIFT_RIGHT << J_SHIFTPOS), n1);
              if (ShiftedVal(op, n2) != n1) {
                RemoveComparison(0, 1, block);
                break;
              } else {
                e1 = e2;
                r2.r = c->r2.r = r3.r;
                goto ConvertToCMPK;
              }
            }
#endif
            if (!OpIsShifted(op) && (cond & ~Q_UBIT) != Q_UKN && cond != Q_UNDEF) {
              op = Q_swap(op);
              blkflags_(block) = flags = Q_swap(flags);
              n2 = e1k_(c2->exprn);
              e1 = e2;
              r2.r = c->r2.r = r3.r;
              goto ConvertToCMPK;
            }
          } else if (!OpIsShifted(op) && ExSetsOverlap(e1, e2)) {
            RemoveComparison(0, 0, block);
            break;
          } else if (!OpIsShifted(op) && (cond == Q_EQ || cond == Q_NE || !(op & Q_UBIT)) &
                     ExprIsExprPlusK(e1, e2, &n1, &n2)) {
          /* Comparison for equality are completely safe.
             Signed comparisons for order are arguably OK because of the
             undefinedness of signed overflow.
           */
            RemoveComparison(n1, n2, block);
            break;
          }
          cmp_mask_(&cmpk) = op & CSE_COMPARE_MASK;
          cmp_ex_(&cmpk) = FindRRSet(op & ~CSE_COMPARE_MASK, e1, e2, U_NOTDEF+U_NOTREF);
          cmp_r2vals_(&cmpk) = NULL;
          if (ComparisonValueKnown(&taken, &cmpk, comparevalues)) {
            RemoveComparison1(taken, block);
            break;
          }
#ifdef TARGET_ALLOWS_COMPARE_CSES
          values = FindRRSet(op & ~CSE_COMPARE_MASK, e1, e2, 0);
          ExSet_Map(values, AddCompare, NULL);
          blk_cmp_(block) = ExSet_Copy(values);
#endif
          break;

        } else {
          ExSet *c1 = MOVKinSet(e1);
          n2 = ShiftedVal(op, e1k_(c2->exprn));
          if (c1 != NULL) {
            RemoveComparison(e1k_(c1->exprn), n2, block);
            break;
          }
        }
ConvertToCMPK:
        op = c->op = J_RTOK(UnshiftedOp(op));
        r3.i = c->r3.i = n2;
        OpRewritten(c);
      }
      /* and the second arg. constant, first not case falls through */
    case J_CMPK:
      { ExSet *c1 = MOVKinSet(e1);
        int32 mask = op & (Q_MASK & ~Q_UBIT);
        AdconRec ad;
        cmp_mask_(&cmpk) = op & CSE_COMPARE_MASK;
        cmp_r2_(&cmpk) = r2.r;
        cmp_r2vals_(&cmpk) = e1;
        cmp_m_(&cmpk) = r3.i;
        cmp_ex_(&cmpk) = NULL;
        if (c1 != NULL) {
          RemoveComparison(e1k_(c1->exprn), r3.i, block);
        } else if ( (mask == Q_EQ || mask == Q_NE)
                    &&
                    ( /* Special for CFront's demented constructor invocation */
                     (r3.i == 0 && AdconInSet(e1, &ad) != 0 && !(bindstg_(ad.base) & bitofstg_(s_weak)))
                     || ( (c1 = ExSet_OpMember(e1, J_NEK, 0)) != NULL && e1k_(c1->exprn) == r3.i) ) )

          RemoveComparison(1, 0, block);
        else if ((mask == Q_LT || mask == Q_GE) &&
                 r3.i == 0 && TopBitsKnownZero(e1, 1))
          RemoveComparison(1, 0, block);
        else {
          bool taken;
          if (sideeffectfree_prev && Q_RealMask(op & Q_MASK)
              && setnotused == NULL && !(flags & BLKREXPORTED))
            MaybeKillBranchToBlock(block, &cmpk);
          cmp_ex_(&cmpk) = FindRKSet(op & ~CSE_COMPARE_MASK, e1, r3.i, U_NOTDEF+U_NOTREF);
          if (ComparisonValueKnown(&taken, &cmpk, comparevalues)) {
            RemoveComparison1(taken, block);
            break;
          }
          if (!immed_cmp(r3.i)) {
            op = J_MOVK;
            node = find_movk(r3.i, 0);
            break;
          }
#ifdef TARGET_ALLOWS_COMPARE_CSES
          if (e1 != NULL) {
            values = FindRKSet(op & ~CSE_COMPARE_MASK, e1, r3.i, 0);
            ExSet_Map(values, AddCompare, NULL);
            blk_cmp_(block) = ExSet_Copy(values);
          }
#endif
        }
      }
      break;

    case J_USE: case J_USEF: case J_USED:
    case J_VSTORE:
      /* I think I have to assume that this directly follows a load
       * or store.  I can't get from the register to the store location
       * in the case of stores, if the value being stored was known.
       */
      sideeffectfree = NO;
      if (storeaccesses->ic == c-1) {
        LocSet *locs = storeaccesses->locs;
        for (; locs != NULL; locs = cdr_(locs)) {
          Location *loc = locs->loc;
          wantedexprns = deleteloads(loc, wantedexprns);
          availableexprns = deleteloads(loc, availableexprns);
          liveexprns = deleteloads(loc, liveexprns);
          /* All of which is a bit over-enthusiastic. wanted need not be
             changed if there's an earlier non-volatile load of the same
             location; live and available need not really change at all (the
             volatile load/store provides a perfectly good value to a later
             non-volatile load). Still, this is only relevant if volatile
             and non-volatile accesses to the same location are mixed, and
             doing it requires more care to be taken elsewhere.
           */
        }
      }
      node = NULL;
      break;

    case J_MOVIFR: case J_MOVIDR: case J_MOVFIR:
      cse_corrupt_register(r1.r);
      node = NULL;
      break;

    case J_MOVDIR:
      if (e2 != NULL)
      {   /* General code (at the end of the switch) will deal with setting
             r1 & r2.
           */
          values2 = newexprnpart(CSE_WORD2, e2);
          values = newexprnpart(CSE_WORD1, e2);
          break;
      }
      /* drop through */
    case J_MOVLIR:
      cse_corrupt_register(r1.r);
      cse_corrupt_register(r2.r);
      node = NULL;
      break;

    case J_MOVDFR:
      { ExSet *c1 = MOVDKinSet(e2);
        if (c1 != NULL) {
          FloatCon *fc = e1f_(c1->exprn);
          FloatBin f;
          if (fltrep_narrow(&fc->floatbin.db, &f) <= flt_ok) {
            r3.f = real_of_string(fc->floatstr ? fc->floatstr : "<expr>", 0);
            r3.f->floatlen = ts_float;
            r3.f->floatbin.fb = f;
            goto ForgeMOVFK;
          }
        }
      }
      if (e2 != NULL)
        values = FindRKSet(op, e2, 0, 0);
      break;

    case J_ADDDK: case J_MULDK: case J_SUBDK: case J_DIVDK:
      if (e1 != NULL) {
        FloatCon *a = CSE_EvalBinary_D(op, e1, r3.f);
        if (a != NULL) {
          r3.f = a;
          goto ForgeMOVDK;
        }
        values = FindRKSet(op, e1, (IPtr)CSE_CanonicalFPConst(r3.f), 0);
      }
      break;

    case J_ADDDR: case J_MULDR: case J_SUBDR: case J_DIVDR:
      if (e1 != NULL && e2 != NULL) {
        ExSet *c2 = MOVDKinSet(e2);
        if (c2 != NULL) {
          FloatCon *a = CSE_EvalBinary_D(J_RTOK(op), e1, e1f_(c2->exprn));
          if (a != NULL) {
            r3.f = a;
            goto ForgeMOVDK;
          }
#ifdef TARGET_HAS_FP_LITERALS
          /* Maybe rewrite as xxxDK */
#endif
        }
        values = FindRRSet(op, e1, e2, 0);
      }
      break;

    ForgeMOVDK:
      op = c->op = J_MOVDK;
      c->r3 = r3;
      c->r2.r = GAP;
      OpRewritten(c);
    case J_ADCOND:
    case J_MOVDK:
      node = find_exprn(op, (Exprn *)CSE_CanonicalFPConst(r3.f), 0, NULL, 0);
      break;

    case J_ADCONLL:
      node = find_exprn(op, (Exprn *)CSE_CanonicalLLConst(r3.i64), 0, NULL, 0);
      break;

    case J_MOVFDR:
      { ExSet *c1 = MOVFKinSet(e2);
        if (c1 != NULL) {
          FloatCon *fc = e1f_(c1->exprn);
          r3.f = real_of_string(fc->floatstr ? fc->floatstr : "<expr>", 0);
          r3.f->floatlen = ts_double;
          fltrep_widen(&fc->floatbin.fb, &r3.f->floatbin.db);
          goto ForgeMOVDK;
        }
      }
      if (e2 != NULL)
        values = FindRKSet(op, e2, 0, 0);
      break;

    case J_ADDFK: case J_MULFK: case J_SUBFK: case J_DIVFK:
      if (e1 != NULL) {
        FloatCon *a = CSE_EvalBinary_F(op, e1, r3.f);
        if (a != NULL) {
          r3.f = a;
          goto ForgeMOVFK;
        }
        values = FindRKSet(op, e1, (IPtr)CSE_CanonicalFPConst(r3.f), 0);
      }
      break;

    case J_ADDFR: case J_MULFR: case J_SUBFR: case J_DIVFR:
      if (e1 != NULL && e2 != NULL) {
        ExSet *c2 = MOVFKinSet(e2);
        if (c2 != NULL) {
          FloatCon *a = CSE_EvalBinary_F(J_RTOK(op), e1, e1f_(c2->exprn));
          if (a != NULL) {
            r3.f = a;
            goto ForgeMOVFK;
          }
#ifdef TARGET_HAS_FP_LITERALS
          /* Maybe rewrite as xxxFK */
#endif
        }
        values = FindRRSet(op, e1, e2, 0);
      }
      break;

    ForgeMOVFK:
      op = c->op = J_MOVFK;
      c->r3 = r3;
      c->r2.r = GAP;
      OpRewritten(c);
    case J_ADCONF:
    case J_MOVFK:
      node = find_exprn(op, (Exprn *)CSE_CanonicalFPConst(r3.f), 0, NULL, 0);
      break;

    case J_STRING:
      node = find_exprn(op, (Exprn *)r3.s, 0, NULL, 0);
      break;

    case J_NEGR:
    case J_NOTR:
    case J_FIXFR: case J_FIXDR:
    case J_FIXFRM: case J_FIXDRM:
      if (CSE_EvalUnary_I(op, &atmp, e2)) {
        r3.i = atmp;
        goto ForgeMOVK;
      }
      goto UnaryR;

    case J_NEGFR:
    case J_FLTFR:
      if (e2 != NULL) {
        FloatCon *f = CSE_EvalUnary_F(op, e2);
        if (f != NULL) {
          r3.f = f;
          goto ForgeMOVFK;
        }
      }
      goto UnaryR;

    case J_NEGDR:
    case J_FLTDR:
      if (e2 != NULL) {
        FloatCon *f = CSE_EvalUnary_D(op, e2);
        if (f != NULL) {
          r3.f = f;
          goto ForgeMOVDK;
        }
      }
    UnaryR:
      if (e2 != NULL)
        values = FindRKSet(op, e2, 0, 0);
      break;

    case J_INLINE1: case J_INLINE1F: case J_INLINE1D:
      if (e1 != NULL)
        values = FindRKSet(op, e1, r3.i, 0);
      break;

    case J_EORR:
    case J_SUBR:
    case J_RSBR:
      if (!OpIsShifted(op) && ExSetsOverlap(e1, e2)) {
        r3.i = 0;
        goto ForgeMOVK;
      }
      goto BinaryR;

    case J_ANDR: case J_ORRR:
      if (!OpIsShifted(op) && ExSetsOverlap(e1, e2))
        goto ForgeMOVR;
      goto BinaryR;

    case J_ADDR: case J_MULR:
    case J_DIVR: case J_REMR:
    case J_SHLR: case J_SHRR: case J_RORR:
BinaryR:
      if (e1 != NULL && e2 != NULL) {
        ExSet *c2 = MOVKinSet(e2);
        if (c2 != NULL) {
          int32 a2 = ShiftedVal(op, e1k_(c2->exprn));
          ExSet *c1 = MOVKinSet(e1);
          if (c1 != NULL &&
              CSE_EvalBinary_I(J_RTOK(UnshiftedOp(op)), &atmp, c1->exprn, a2)) {
            r3.i = atmp;
            goto ForgeMOVK;
          } else if (jop_canRTOK(UnshiftedOp(op))) {
            op = UnshiftedOp(op);
            r3.i = a2;
            goto ForgeIOpK;
          }
        }
        if (!OpIsShifted(op) && j_is_commutative(op)) {
          ExSet *c1 = MOVKinSet(e1);
          if (c1 != NULL && jop_canRTOK(op)) {
            e1 = e2;
            c->r2.r = r2.r = r3.r;
            r3.i = e1k_(c1->exprn);
            goto ForgeIOpK;
          }
        }
        values = FindRRSet(op, e1, e2, 0);
      }
      break;

    ForgeIOpK:
      c->op = op = J_RTOK(op);
      c->r3.i = r3.i;
      e2 = NULL;
      OpRewritten(c);
      /* fall through to handle rewrite as OpK */

    case J_ADDK: case J_MULK: case J_ANDK: case J_ORRK: case J_EORK:
    case J_SUBK: case J_DIVK: case J_RSBK: case J_REMK:
    case J_SHLK: case J_SHRK: case J_RORK:
    case J_EXTEND:
      if (e1 != NULL) {
        ExSet *c1 = MOVKinSet(e1);
        if (c1 != NULL && CSE_EvalBinary_I(op, &atmp, c1->exprn, r3.i) ) {
          r3.i = atmp;
          goto ForgeMOVK;
        } else {
          switch (op & ~Q_MASK) {
          case J_ORRK:
            if (r3.i == -1) goto ForgeMOVK;
          case J_ADDK: case J_SUBK: case J_EORK:
            if (r3.i == 0) goto ForgeMOVR;
            break;
          case J_MULK: case J_DIVK:
            if (r3.i == 1) goto ForgeMOVR;
            break;
          case J_ANDK:
            if (r3.i == 0) goto ForgeMOVK;
            if (r3.i == -1) goto ForgeMOVR;
            { int32 x = r3.i + 1;
              if ((x & (-x)) == x) {
                int32 bits = logbase2(x);
                if (BottomBitsKnownZero(e1, bits)) {
                  r3.i = 0;
                  goto ForgeMOVK;
                } else if (TopBitsKnownZero(e1, 32-bits))
                  goto ForgeMOVR;
              }
              x = ~r3.i + 1;
              if ((x & (-x)) == x) {
                int32 bits = logbase2(x);
                if (TopBitsKnownZero(e1, 32-bits)) {
                  r3.i = 0;
                  goto ForgeMOVK;
                } else if (BottomBitsKnownZero(e1, bits))
                  goto ForgeMOVR;
              }
            }
            break;
          case J_EXTEND:
            /* Kill extend applied to an already extended value. Regalloc will
             * also handle this (though maybe not if the value has passed
             * through a variable), but by turning the load into a plain one.
             * Killing the extend is sometimes better, never worse.
             */
            if (r3.i == 2) {
              if (ExSet_OpMember(e1, J_LDRWK+J_SIGNED, J_ALIGNMENT)
                  || ExSet_OpMember(e1, J_LDRWVK+J_SIGNED, J_ALIGNMENT)
                  || ExSet_OpMember(e1, J_LDRWR+J_SIGNED, J_ALIGNMENT))
                goto ForgeMOVR;
            } else if (r3.i == 1) {
              if (ExSet_OpMember(e1, J_LDRBK+J_SIGNED, J_ALIGNMENT)
                  || ExSet_OpMember(e1, J_LDRBVK+J_SIGNED, J_ALIGNMENT)
                  || ExSet_OpMember(e1, J_LDRBR+J_SIGNED, J_ALIGNMENT))
                goto ForgeMOVR;
            }
          }
          values = FindRKSet(op, e1, r3.i, 0);
        }
      }
      break;

    ForgeMOVK:
      op = c->op = J_MOVK;
      c->r2.r = GAP;
      c->r3.i = r3.i;
      OpRewritten(c);
    case J_MOVK:
      /* J_STRV and TARGET_IS_ALPHA? */
      node = find_movk(c->r3.i, immed_op(r3.i, op) &&
                               ( c+1 == limit ||
                                 (c+1)->op == (J_STRV|J_ALIGN4) ||
                                 isany_realreg_(r1.r) ) ? U_NOTDEF2+U_NOTREF
                                                        : 0);
      break;

#ifdef ARM_INLINE_ASSEMBLER

    case J_BL:
        corruptmem();
        callcount++;
        break;
#endif

    default:
      /* syserr(syserr_scanblock, (long)op); */
      node = NULL;
      break;

    } /* switch */

    /* Now update the CSE state */

#ifndef TARGET_IS_INTERPRETER
    if (corrupts_psr(c))
        cse_corrupt_register(R_PSR);
#endif
    if (corrupts_r1(c))
        cse_corrupt_register(r1.r);
    if (corrupts_r2(c))
        cse_corrupt_register(r2.r);

#ifdef TARGET_IS_ARM_OR_THUMB
    {
        /* Mark all registers which are either written or corrupted as 'corrupted'.
         * This is because CSE marks all registers with an unknown value as corrupted.
         * If defined registers are not included CSE thinks the value didn't change...
         * Later the value may be set to a known value using setreg.
         */
        RealRegisterUse(c, &reg);
        map_RealRegSet(&reg.c_in, corrupt_f, NULL);
        map_RealRegSet(&reg.c_out, corrupt_f, NULL);
        map_RealRegSet(&reg.def, corrupt_f, NULL);
    }
#endif

    if (values == NULL && node != NULL)
      values = ExprnToSet(node);

    if (debugging(DEBUG_CSE) && CSEDebugLevel(1))
      ExSet_Print(values, "\n");

#ifdef RANGECHECK_SUPPORTED
    if (j_is_check(op) && values != NULL) {
      if (!ExSet_Map(values, ExprnWasntLive, &node)) {
        c->op = J_NOOP;
        if (debugging(DEBUG_CSE) && CSEDebugLevel(1))
          cc_msg("-- local CSE reference [%ld] -> NOOP\n", exid_(node));
      } else {
        ExSet_Map(values, SetExWasLive, NULL);
      }
    } else
#endif
/* J_MOVDIR sets r1 (and this causes setreg(r1,NULL,YES) below), but    */
/* the previous PUSHD/POP/POP sequence didn't.  Hence next line's hack. */
/* Without the hack K_PURE fn calls don't get CSE'd.                    */
    if (loads_r1(op)) {
    /* what I really want to say here is try for a local cse only if nothing
       in values suggests it's not sensible
     */
      WTLRec wtlrec;
      wtlrec.op = op; wtlrec.locs = locs;
      wtlrec.r1 = r1.r; wtlrec.isload = isload;
      if ( !isvolatile &&
           maybelocalcse &&
           values != NULL &&
           !register_movep(op) &&
           (node = ExSet_Some(values, WorthTryingLocalCSE, &wtlrec)) != NULL ) {

        if (exop_(node) == J_RESULT2) {
          Exprn *e1 = e1_(node);
          if (cseset_member(exid_(e1), availableexprns))
            isload = isload & !cse_AddLocalCSE(e1, 1, 0, block);
        } else if (exop_(node) != CSE_WORD1 && exop_(node) != CSE_WORD2) {
          if (cseset_member(exid_(node), availableexprns))
            isload = isload & !cse_AddLocalCSE(node, valno, nvals, block);
        }
        /* If addlocalcse returned NO, maybe we should think about
           patching the load (if isload).  Or maybe we should do it
           anyway, since the CSE might later be discarded.  If we don't,
           the CSE had better not be discarded! (or a believed to be
           redundant store of the value used here may be killed).
         */
      }
      if (isload && locs != NULL)
        add_store_access(locs);
      setreg(r1.r, values, YES);
    }
    if (loads_r2(op))
        setreg(r2.r, values2, YES);
    else if (values2 != NULL) {
        if (op == J_CALLK)
            setreg(r1.r+1, values2, YES);
        else
            syserr("cse_scanblock values2");
    }

#ifdef TARGET_ALLOWS_COMPARE_CSES
    if (alterscc(c))
      cseset_insert(CCLOC, killedlocations, NULL);
#endif
  }

  if (!(flags & BLK2EXIT) && is_exit_label(exit)) {
    /* We may kill all unused stores to local objects.  regalloc will do
       better with non-address-taken binders, but not with address-taken
       ones or local structs.
     */
    StoreAccessList *a;
    for (a = storeaccesses; a != NULL; a = cdr_(a)) {
      Icode *ic = a->ic;
      if (stores_r1(ic->op)) {
        Location *loc;
        LocType type = MaxLocType(a->locs, &loc);
        if (type & LOC_anyVAR) {
          if (IsLive(loc->load) &&
              (bindstg_(locbind_(loc)) &
               (bitofstg_(s_auto) | b_globalregvar))
                  == bitofstg_(s_auto))
            KillOldUnusedStore(loc, 0);
        } else {
          LocSet *locs = a->locs;
          for (; locs != NULL; locs = cdr_(locs))
            if (exop_(locbase_(loc)) == J_ADCONV) {
              if (IsLive(loc->load))
                KillOldUnusedStore(loc, 0);
              break;
            }
        }
      }
    }
  }
  if (blklength_(block) > 0 && c[-1].op == J_MOVK
      && !is_exit_label(exit) && !(blkflags_(block) & BLK2EXIT)) {
    BlockHead *bdest = exit->block;
    if (blkflags_(bdest) & BLK2EXIT) {
      int32 destlen = blklength_(bdest);
      Icode const *const destic = blkcode_(bdest);
      if (0 < destlen && (destic[destlen - 1].op & ~Q_MASK) == J_CMPK) {
        Icode const *ic = destic;
        VRegnum prevr1 = c[-1].r1.r;
        int32 i = 0;
        bool matches = YES;
        --destlen; /* look at all but last */
        for (; i < destlen; ++i, ++ic) {
          if (ic->op == J_SETSPENV)
            continue;
          if (!(ic->op == J_MOVR && ic->r3.r == prevr1)
              && !((ic->op == J_ANDK || ic->op == J_EXTEND)
                   && ic->r2.r == prevr1)) {
            matches = NO;
            break;
          }
          prevr1 = ic->r1.r;
        }
        if (matches && ic->r2.r == prevr1) {
          LabelNumber *newl = nextlabel();
          BlockHead *newb = (BlockHead *)BindAlloc(sizeof(BlockHead));
          if (debugging(DEBUG_CSE))
            cc_msg("Cloning block %ld as successor of block %ld\n",
                   (long)lab_name_(exit), (long)blklabname_(block));
          newl->block = newb;
          *newb = *bdest;
          blklab_(newb) = newl;
          blkdown_(newb) = blkdown_(block);
          blkup_(newb) = block;
          blkup_(blkdown_(block)) = newb; blkdown_(block) = newb;
          blkcse_(newb) = CSEBlockHead_New();
          blk_dominators_(newb) = cseset_copy(blk_dominators_(bdest));
          blk_pred_(newb) = NULL;
          cse_AddPredecessor(newl, block);
          cse_AddPredecessor(blknext_(newb), newb);
          cse_AddPredecessor(blknext1_(newb), newb);
          KillArc(block, exit);
          blknext_(block) = exit = newl;
          { int32 n = blklength_(bdest);
            Icode *ic_old = blkcode_(bdest);
            Icode *ic_new = (Icode *)BindAlloc(n * sizeof(Icode));
            memcpy(ic_new, ic_old, (size_t)n * sizeof(Icode));
            blkcode_(newb) = ic_new;
          }
        }
      }
    }
  }
  ExportLocVals(block, &cmpk, sideeffectfree && setnotused == NULL, setnotused);
  blk_scanned_(block) = YES;
  for (; knownregs != NULL; knownregs = RegValue_DiscardOne(knownregs))
    ExSet_Discard(rv_val_(knownregs));
  StoreAccessList_Discard(storeaccesses);
  storeaccesses = NULL;
#ifdef ENABLE_CSE
  if (debugging(DEBUG_CSE) && CSEDebugLevel(1))
    cse_printexits(flags, exit, exit1);
#endif
  /* Take account of evaluated function calls. Since no calls have been
     introduced, we need merely to clear the BLKxCALL bits if appropriate
   */
  if (callcount < 1)
    blkflags_(block) &= ~(BLKCALL+BLK2CALL);
  else if (callcount == 1)
    blkflags_(block) &= ~BLK2CALL;
  if (setnotused != NULL && !is_exit_label(exit)) {
    blkflags_(block) |= BLKREXPORTED;
    if (debugging(DEBUG_CSE) || debugging(DEBUG_CG)) {
      cc_msg("Block %ld marked RExported: ", (long)blklabname_(block));
      cse_printset(setnotused);
      cc_msg("\n");
    }
  }
  blk_available_(block) = availableexprns;
  blk_wanted_(block) = wantedexprns;
  blk_killed_(block) = killedlocations;
}

static void csescan_setup(void)
{
    memclr(exprnindex, EXPRNINDEXSIZE * sizeof(Exprn **));
    cse_tab = CSENewN(Exprn *, HASHSIZE);
    memclr(cse_tab, HASHSIZE * sizeof(Exprn **));
    memclr(locindex, LOCINDEXSIZE * sizeof(Location **));
    locations = CSENewN(Location *, LOCHASHSIZE);
    memclr(locations, LOCHASHSIZE * sizeof(Location **));
    cseidsegment = CSEIDSEGSIZE;
    heapptr = CSENew(Exprn);
    exop_(heapptr) = J_HEAPPTR;
    heapptr->nodeid = mknodeid_(0, EX_ALIAS|E_UNARYK);
    exuses_(heapptr) = NULL;
    exwaslive_(heapptr) = YES;
    exleaves_(heapptr) = NULL;
    csealiasid = csealiaslimit = 1;
    csenonaliasid = 0; csenonaliaslimit = CSEIDSEGSIZE;
    locationid = 0;
    floatconlist = NULL;
    int64conlist = 0;
    knownregs = NULL;
    loadrs = NULL;
    movcbaseid = MOVCLOC; movctargets = NULL;
#ifdef TARGET_ALLOWS_COMPARE_CSES
    compares = NULL;
#endif
}

#ifdef EXPERIMENT_PRUNEEXPRNS
/* Temporarily disabled, because it was pruning too much (see comment below) */

static void renumber_cb(int32 id, VoidStar arg)
{
    VRegSetP *newp = (VRegSetP *)arg;
    int32 newid = exnewid_(exprn_(id));
    if (newid != 0) {
        bool oldp;
        cseset_insert(newid, *newp, &oldp);
    }
}

static VRegSetP renumber(VRegSetP set)
{
    VRegSetP newset = NULL;
    vregset_map(set, renumber_cb, (VoidStar)&newset);
    vregset_discard(set);
    return newset;
}

static void pruneandrenumberexprns(BlockHead *top)
{
    int32 i, j, count = 0;
    Exprn *left = NULL;
    cseidsegment = CSEIDSEGSIZE;
    csealiasid = csealiaslimit = 0;
    csenonaliasid = 0; csenonaliaslimit = CSEIDSEGSIZE;
    if (debugging(DEBUG_CSE)) cc_msg("\nDiscarding exprns");

    for (i = 0; i < EXPRNINDEXSIZE; i++) {
        Exprn **p = exprnindex[i];
        if (p == NULL) break;
        for (j = 0; j < EXPRNSEGSIZE; j++) {
            Exprn *ex = p[j];
            if (ex != NULL) {
                ExprnUse *use = exuses_(ex);
                /* if this is activated, only-once subexpressions of more-than-once
                   expressions will not be considered for lifting out of the whole
                   function "loop", and so will get loaded twice if the larger
                   expression is lifted.
                 */
                if (use == NULL) syserr(syserr_prune);
                if (cdr_(use) == NULL && !(flags_(use) & U_LOCALCSE) &&
                    blknest_(use->block) <= 1) {
                    if (debugging(DEBUG_CSE)) {
                        cc_msg(" %ld", exid_(ex));
                        if ((++count) % 20 == 0) cc_msg("\n");
                    }
                    exnewid_(ex) = 0;
                } else {
                    if (exalias_(ex)) {
                        if (++csealiasid >= csealiaslimit) {
                            csealiasid = cseidsegment;
                            csealiaslimit = (cseidsegment += CSEIDSEGSIZE);
                        }
                        exnewid_(ex) = csealiasid;
                    } else {
                        if (++csenonaliasid >= csenonaliaslimit) {
                            csenonaliasid = cseidsegment;
                            csenonaliaslimit = (cseidsegment += CSEIDSEGSIZE);
                        }
                        exnewid_(ex) = csenonaliasid;
                    }
                    cdr_(ex) = left;
                    left = ex;
                }
            }
        }
    }
    if (debugging(DEBUG_CSE)) cc_msg(" [%ld]\n", count);
    {   BlockHead *bp;
        for (bp = top; bp != NULL; bp = blkdown_(bp)) {
            blk_available_(bp) = renumber(blk_available_(bp));
            blk_wanted_(bp) = renumber(blk_wanted_(bp));
        }
    }
    for (i = 0 ; i < LOCINDEXSIZE ; i++) {
        Location **index = locindex[i];
        if (index == 0) break;
        for (j = 0 ; j < LOCSEGSIZE ; j++) {
            Location *q = index[j];
            if (q == 0) break;
            q->users = renumber(q->users);
            q->aliasusers = renumber(q->aliasusers);
        }
    }
    for (i = 0; i < EXPRNINDEXSIZE; i++) {
        Exprn **p = exprnindex[i];
        if (p == NULL) break;
        for (j = 0; j < EXPRNSEGSIZE; j++) {
            p[j] = NULL;
        }
    }
    for (; left != NULL; left = cdr_(left)) {
        int32 newid = exnewid_(left);
        left->nodeid = mknodeid_(newid, left->nodeid & EX_ALIASandTYPE);
        exprn_(newid) = left;
    }
}
#endif

static void addkilledexprns(IPtr locno, VoidStar arg)
{
    Location *loc = loc_(locno);
    VRegSetP *s = (VRegSetP *) arg;
    cseset_union(*s, loc->aliasusers);
}

void cse_scanblocks(BlockHead *top)
{   /* For each block, record the set of expressions evaluated within it.
     * Multiple occurrences of the same expression (with the same value) get
     * flattened at this stage.
     * Output:
     *   available   the set of expressions evaluated within and reaching the
     *               end of the block
     *   wanted      the set of expressions evaluated within the block and not
     *               killed within it (so could be evaluated earlier).
     *   killed      the set of LOCATIONS killed in the block
     */
    BlockHead *p;
    clock_t t0 = clock();
    csescan_setup();
    if (debugging(DEBUG_CSE | DEBUG_STORE)) {
        cc_msg("CSE available expression scan\n");
    }
    for (p = top; p != NULL; p = blkdown_(p)) {
        if (debugging(DEBUG_CSE) && CSEDebugLevel(1))
            cc_msg("L%li\n", (long)blklabname_(p));
        cse_scanblock(p);
        cseset_discard(liveexprns);
    }
    {   clock_t now = clock();
        if (debugging(DEBUG_CSE | DEBUG_STORE))
            cc_msg("%ld Exprns, %ld Locations - %d csecs\n",
                   (long)(cseidsegment-1), (long)(locationid), now-t0);
        t0 = now;
    }
#ifdef EXPERIMENT_PRUNEEXPRNS
    pruneandrenumberexprns(top);
#endif

    {   MOVCTarget *mt;
        VRegSetP universe = NULL, callkills = NULL;
        int32 ul;
        {   int32 i;
            for (i = 1 ; i < cseidsegment ; i++)
                cseset_insert(i, universe, NULL);
            for (i = csealiasid+1 ; i < csealiaslimit ; i++)
                cseset_delete(i, universe, NULL);
            for (i = csenonaliasid+1 ; i < csenonaliaslimit ; i++)
                cseset_delete(i, universe, NULL);

            for (i = 0 ; i < LOCINDEXSIZE ; i++) {
                Location **index = locindex[i];
                int32 j;
                if (index == 0) break;
                for (j = 0 ; j < LOCSEGSIZE ; j++) {
                    Location *q = index[j];
                    if (q == 0) break;
                    if (ispublic(q))
                        cseset_union(callkills, q->users);
                    if (!(loctype_(q) & LOC_anyVAR)) {
                        Exprn *base = locbase_(q);
                        for (mt = movctargets; mt != NULL; mt = cdr_(mt))
                            if (mt->base == base) {
                                cseset_insert(locid_(q), mt->locswithbase, NULL);
                                break;
                            }
                    }
                }
            }
        }
        ul = cseset_size(universe);
        for (p = top; p != NULL; p = blkdown_(p)) {
        /* Turn the set of killed locations now recorded with each block into a
         * set of killed expressions.  We couldn't do this earlier, because the
         * full set of expressions which have a given location as leaf is available
         * only after the first pass.
         */
            VRegSetP s = NULL;
            bool present;
            VRegSetP locs = cseset_delete(CALLLOC, blk_killed_(p), &present);
            if (present) s = cseset_copy(callkills);
#ifdef TARGET_ALLOWS_COMPARE_CSES
            locs = cseset_delete(CCLOC, blk_killed_(p), &present);
            if (present) cseset_union(s, compares);
#endif
            for (mt = movctargets; mt != NULL; mt = cdr_(mt)) {
                locs = cseset_delete(mt->id, blk_killed_(p), &present);
                if (present) cseset_union(locs, mt->locswithbase);
            }
            cseset_map(locs, addkilledexprns, (VoidStar) &s);
            cseset_discard(locs);
            if (s != NULL) cseset_union(s, loadrs);
            {   int32 n = cseset_size(s);
                if (n >= ul/2) {
                    VRegSetP s1 = cseset_copy(universe);
                    cseset_difference(s1, s);
                    if (cseset_size(s1) >= n) {
                        cseset_discard(s1);
                    } else {
                        cseset_discard(s);
                        s = s1;
                        blk_killedinverted_(p) = YES;
                    }
                }
                blk_killed_(p) = s;
            }
        }
        cseset_discard(universe);
        cseset_discard(callkills);
        cseset_discard(loadrs);
#ifdef TARGET_ALLOWS_COMPARE_CSES
        cseset_discard(compares);
#endif
        for (mt = movctargets; mt != NULL; mt = cdr_(mt))
            cseset_discard(mt->locswithbase);
    }
    {   int32 i;
        for (i = 0 ; i < LOCINDEXSIZE ; i++) {
            Location **index = locindex[i];
            int32 j;
            if (index == 0) break;
            for (j = 0 ; j < LOCSEGSIZE ; j++) {
                Location *q = index[j];
                if (q == 0) break;
                cseset_discard(q->users);
                cseset_discard(q->aliasusers);
            }
        }
    }
    if (debugging(DEBUG_CSE | DEBUG_STORE)) {
        cc_msg("constructed killed(blocks) - %d csecs\n", clock()-t0);
    }
}

/* end of mip/csescan.c */
