/*
 * sr.c: Live range splitting
 * Copyright 1993-1997 Advanced Risc Machines Limited. All rights reserved
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$ Codemist 2
 * Checkin $Date$
 * Revising $Author$
 */

#include <stdio.h>
#ifdef __STDC__
#  include <string.h>
#else
#  include <strings.h>
#endif

#include "globals.h"
#include "aeops.h"
#include "cgdefs.h"
#include "jopcode.h"
#include "regsets.h"
#include "sr.h"
#include "store.h"
#include "flowgraf.h"
#include "builtin.h"
#include "cg.h"
#include "regalloc.h"
#include "bind.h"
#include "mcdep.h"
#include "simplify.h"
#include "errors.h"

typedef struct VKUse VKUse;
typedef struct VKLoc VKLoc;
typedef struct VKList VKList;
typedef struct MOVCList MOVCList;
typedef struct AdconvList AdconvList;

struct MOVCList {
  MOVCList *cdr;
  BlockHead *block;
  Icode *ic;
  Binder *b1, *b2;
};
#define mkMOVCList(a,b,c,d,e) (MOVCList *)syn_list5(a,b,c,d,e)

struct VKUse {
  VKUse *cdr;
  Icode *use;
};
#define mkVKUse(a,b) (VKUse *)syn_list2(a,b)

struct VKLoc {
  VKLoc *cdr;
  unsigned32 offset;
  int type;
  VRegnum ruse;
  VKUse *uses;
  Binder *bind;
};

struct VKList {
  VKList *cdr;
  VRegnum bindxx;
  bool splittable;
  VKLoc *locs;
  Binder *b;
};

struct AdconvList {
  AdconvList *cdr;
  IPtr /* VRegnum */ r;
  Binder *b;
};
#define mkAdconvList(a,b,c) (AdconvList *)syn_list3(a,b,c)
#define AdconvList_DiscardOne(p) ((AdconvList *)discard3(p))

static VKList *vklist;
static VKUse *setsplist;
static MOVCList *movclist, **movctail;

static int const memsize[] = {
  1,
  2,
  4,
  sizeof_float,
  sizeof_double,
  8
};

#define BinderIsArg(b) \
  (!(bindstg_(b) & b_bindaddrlist) && /* (implies BINDADDR_LOC) */ \
   (bindaddr_(b) & BINDADDR_MASK) == BINDADDR_ARG)

static VRegnum ArgumentRegister(Binder *b) {
  return (bindaddr_(b) & ~BINDADDR_MASK) / alignof_toplevel_auto -
         currentfunction.fltargwords;
}

static BindList *bindlist_member(Binder *b, BindList *bl) {
  for (; bl != NULL; bl = cdr_(bl))
    if (bl->bindlistcar == b) return bl;
  return NULL;
}

static void SpliceInBL(BindList *bl, VKLoc *locs, bool setbindaddr) {
  if (bl != NULL) {
    BindList *newbl, *q = cdr_(bl);
    Binder *b = locs->bind;
    bl->bindlistcar = b;
    if (setbindaddr) bindbl_(b) = bl;
    for (; (locs = cdr_(locs)) != NULL; bl = newbl) {
      b = locs->bind;
      newbl = mkBindList(NULL, b);
      cdr_(bl) = newbl;
      if (setbindaddr) bindbl_(b) = newbl;
    }
    cdr_(bl) = q;
  }
}

static bool Overlap(int typea, int32 offseta, int typeb, int32 offsetb) {
  return (offseta >= offsetb && offseta < offsetb + memsize[typeb]) ||
         (offsetb >= offseta && offsetb < offseta + memsize[typea]);
}

static VKLoc *VKLoc_New(VKLoc *next, int32 offset, int type, VRegnum ruse) {
  VKLoc *p = NewSyn(VKLoc);
  cdr_(p) = next;
  p->type = type;
  p->offset = offset;
  p->ruse = ruse;
  p->uses = NULL;
  p->bind = NULL;
  return p;
}

static VKLoc *VKLoc_ReverseCopy(VKLoc *locs) {
  VKLoc *res = NULL;
  for (; locs != NULL; locs = cdr_(locs)) {
    VKLoc *p = NewSyn(VKLoc);
    *p = *locs;
    cdr_(p) = res;
    res = p;
  }
  return res;
}

#define bindvklist_(b) ((VKList *)bindxxp_(b))

static VKList *GetVKList(Binder *b) {
  if ((bindstg_(b) & (bitofstg_(s_auto)|b_addrof|b_spilt)) != bitofstg_(s_auto))
    return NULL;
  if (BinderIsArg(b)) {
    /* Only attempt to split argument structures passed entirely in registers */
    VRegnum argreg = ArgumentRegister(b);
    int32 size = bindmcrep_(b) & MCR_SIZE_MASK;
    if (argreg + size / sizeof_int > NARGREGS) return NULL;
  }
  if (!(bindstg_(b) & u_loctype)) {
     VKList *vk = NewSyn(VKList);
     cdr_(vk) = vklist;
     vklist = vk;
     vk->bindxx = bindxx_(b);
     vk->splittable = YES;
     vk->b = b;
     vk->locs = NULL;
     bindxxp_(b) = vk;
     bindstg_(b) |= u_loctype;
     return vk;
   } else
     return bindvklist_(b);
}

static void MarkAdconvUnsplittable(VRegnum r, AdconvList *p) {
  for (; p != NULL; p = cdr_(p))
    if (r == p->r) {
      if (debugging(DEBUG_SR))
        cc_msg("Mark adconv unsplittable $b\n", p->b);
      bindvklist_(p->b)->splittable = NO;
      break;
    }
}

static void MarkBinderUnsplittable(Binder *b) {
  VKList *vk = GetVKList(b);
  if (vk != NULL) {
    if (debugging(DEBUG_SR))
      cc_msg("Mark binder unsplittable $b\n", b);
    vk->splittable = NO;
  }
}

static AdconvList *adconv_unused;
static RegList *movc_unknown;

static void AddStructsInBL(BindList const *bl) {
  for (; bl != NULL; bl = cdr_(bl)) {
    Binder *b = bl->bindlistcar;
    if ((bindmcrep_(b) & MCR_SORT_MASK) == MCR_SORT_STRUCT)
      GetVKList(b);
  }
}

static void OpRewritten(Icode const *c) {
  if (debugging(DEBUG_SR)) {
    cc_msg("rewritten: ");
    print_jopcode(c);
  }
}

static void SplitStructs_ScanBlock(BlockHead const *block) {
  Icode *c, *limit;
  AdconvList *adconvs = NULL;
  if (debugging(DEBUG_SR))
    cc_msg("L%li:\n", (long)lab_name_(blklab_(block)));
  AddStructsInBL(blkstack_(block));
  for (c = blkcode_(block), limit = c + blklength_(block); c < limit; ++c) {
    VKList *vk;
    if (debugging(DEBUG_SR))
        print_jopcode(c);

    switch (c->op & J_TABLE_BITS) {
    case J_LDRK: case J_STRK:
      { AdconvList *p = adconvs;
        for (; p != NULL; p = cdr_(p)) {
          if (p->r == c->r2.r) {
            c->op = J_addvk(c->op);
            c->r2 = c->r3;
            c->r3.b = p->b;
            OpRewritten(c);
            break;
          }
        }
        if (p == NULL) break;
      }
      /* Fall through */
    case J_LDRVK:  case J_LDRLVK:
    case J_LDRFVK: case J_LDRDVK:
    case J_STRVK:  case J_STRLVK:
    case J_STRFVK: case J_STRDVK:
      vk = GetVKList(c->r3.b);
      if (vk != NULL && vk->splittable) {
        uint32 offset = c->r2.i;
        int type = (int)j_memsize(c->op);
        VKLoc *locs, **locp = &vk->locs;
        bool add = YES;
        for (; (locs = *locp) != NULL; locp = &cdr_(locs))
          if (type == locs->type && offset == locs->offset) {
            add = NO;
            break;
          } else if (Overlap(type, offset, locs->type, locs->offset)) {
            if (debugging(DEBUG_SR))
              cc_msg("Mark binder unsplittable $b\n", c->r3.b);
            vk->splittable = NO;
            goto ExitSwitch;
          } else if (offset < locs->offset)
            break;

        if (add) *locp = locs = VKLoc_New(locs, offset, type, c->r1.r);

        locs->uses = mkVKUse(locs->uses, c);
      }
ExitSwitch:
      continue;

    case J_LDRBVK: case J_LDRWVK:
    case J_STRBVK: case J_STRWVK:
      MarkBinderUnsplittable(c->r3.b);
      continue;

    case J_ADCONV:
      vk = GetVKList(c->r3.b);
      if (vk != NULL && vk->splittable)
        adconvs = mkAdconvList(adconvs, c->r1.r, c->r3.b);
      continue;

    case J_MOVC:
      { AdconvList *p, *q = adconvs, **pp = &q;
        Binder *b1 = NULL, *b2 = NULL;
        for (; (p = *pp) != NULL; ) {
          VRegnum r = p->r;
          if (r == c->r1.r)
            b1 = p->b;
          else if (r == c->r2.r)
            b2 = p->b;
          else {
            pp = &cdr_(p);
            continue;
          }
          *pp = AdconvList_DiscardOne(p);
        }
        if (b1 == NULL) movc_unknown = (RegList *)syn_list2(movc_unknown, c->r1.r);
        if (b2 == NULL) movc_unknown = (RegList *)syn_list2(movc_unknown, c->r2.r);
        adconvs = q;
        if (c->r3.i <= NARGREGS * sizeof_int) {
          if (b1 != NULL || b2 != NULL) {
            MOVCList *p = mkMOVCList(NULL, block, c, b1, b2);
            *movctail = p;
            movctail = &cdr_(p);
          }
        } else {
          if (b1 != NULL) MarkBinderUnsplittable(b1);
          if (b2 != NULL) MarkBinderUnsplittable(b2);
        }
      }
      continue;

    case J_SETSPENV:
      AddStructsInBL(c->r3.bl);
    case J_SETSPGOTO:
      AddStructsInBL(c->r2.bl);
      setsplist = mkVKUse(setsplist, c);
      continue;

    case J_MOVR:
      if (!isany_realreg_(c->r1.r)) {
      /* Move to a real register means function argument, so splitting mustn't
         happen (and we drop into the default case to prevent it).
       */
        AdconvList *p;
        for (p = adconvs; p != NULL; p = cdr_(p))
          if (p->r == c->r3.r) {
            adconvs = mkAdconvList(adconvs, c->r1.r, p->b);
            break;
          }
        for (p = adconv_unused; p != NULL; p = cdr_(p))
          if (p->r == c->r3.r) {
            adconvs = mkAdconvList(adconvs, c->r1.r, p->b);
            break;
          }
        continue;
      }
      break;

    case J_LDRDV: case J_STRDV:
    case J_LDRLV: case J_STRLV:
    case J_LDRFV: case J_STRFV:
    case J_LDRV: case J_STRV:
      MarkBinderUnsplittable(c->r3.b);
      break;
    }
    if (adconvs != NULL) {
      if (reads_r1(c->op)) MarkAdconvUnsplittable(c->r1.r, adconvs);
      if (reads_r2(c->op)) MarkAdconvUnsplittable(c->r2.r, adconvs);
      if (reads_r3(c->op)) MarkAdconvUnsplittable(c->r3.r, adconvs);
      if (reads_r4(c->op)) MarkAdconvUnsplittable(c->r4.r, adconvs);
    }
  }
  if (debugging(DEBUG_SR) && !(blkflags_(block) & BLKSWITCH)) {
    Icode ic;
    INIT_IC(ic, J_NOOP);
    if (blkflags_(block) & BLK2EXIT) {
      ic.op = J_B + (blkflags_(block) & Q_MASK);
      ic.r3.l = blknext1_(block);
      print_jopcode(&ic);
    }
    if (!(blkflags_(block) & BLK0EXIT)) {
      ic.op = J_B;
      ic.r3.l = blknext_(block);
      print_jopcode(&ic);
    }
  }
  if (blkflags_(block) & BLKREXPORTED) {
    VRegnum exportedr = GAP;
    if (blkflags_(block) & BLKREXPORTED2) {
      c--;
      if (loads_r1(c->op) && !isany_realreg_(c->r1.r))
        exportedr = c->r1.r;
    }
    for (; adconvs != NULL; adconvs = AdconvList_DiscardOne(adconvs))
      if (exportedr == GAP || exportedr == adconvs->r) {
        if (debugging(DEBUG_SR))
          cc_msg("Binder $b unsplittable (exportedr)\n", adconvs->b);
        bindvklist_(adconvs->b)->splittable = NO;
      }
  } else if (adconvs != NULL) {
    AdconvList **pp = &adconvs;
    for (; *pp != NULL; pp = &cdr_(*pp)) continue;
    *pp = adconv_unused;
    adconv_unused = adconvs;
  }
}

static void FillInFields(Binder *b, unsigned32 n) {
  VKList *v = bindvklist_(b);
  VKLoc **locsp = &v->locs;
  VKLoc *locs;
  unsigned32 offset = 0;
  if (v->splittable) {
      /* Even a structure referenced only as a whole (*locsp == NULL    */
      /* here) is worth splitting: it's the only way that unwanted      */
      /* writes to it can be discarded.                                 */
    for (; offset < n; locsp = &cdr_(locs)) {
      locs = *locsp;
      if (locs != NULL && offset == locs->offset)
        offset += memsize[locs->type];

      else {
        unsigned32 isize = memsize[MEM_I];
        unsigned32 size = n - offset;
        if (locs != NULL && size > locs->offset - offset)
          size = locs->offset - offset;
        if (size % isize != 0) {
          offset = 0;
          break;
        }
        for (; size != 0; offset += isize, size -= isize) {
          VKLoc *p = VKLoc_New(locs, offset, (int)MEM_I, GAP);
          *locsp = p; locsp = &cdr_(p);
        }
      }
    }
    if (offset != n) v->splittable = NO;
  }
}

static bool CheckSameStructure(Binder *b1, Binder *b2, unsigned32 n) {
  /* There is a structure assignment from b2 to b1. Check that b1 and b2 have
     the same structure, as far as it's known, and fill in the unknown bits
     from the other. If there's a mismatch, mark both b1 and b2 as
     unsplittable (really, only one need be marked, but which?).
   */
  VKList *v1 = bindvklist_(b1),
         *v2 = bindvklist_(b2);
  VKLoc **locs1p = &v1->locs,
        **locs2p = &v2->locs;
  unsigned32 offset = 0;
  unsigned32 size;
  for (; offset < n; offset += size) {
    VKLoc *locs1 = *locs1p,
          *locs2 = *locs2p;
    if (locs1 != NULL && offset == locs1->offset) {
      size = memsize[locs1->type];
      if (locs2 != NULL && offset == locs2->offset) {
        if (locs1->type != locs2->type) {
          offset = 0;
          break;
        }
      } else if (locs2 != NULL && offset+size > locs2->offset) {
        offset = 0;
        break;
      } else
        *locs2p = locs2 = VKLoc_New(locs2, offset, locs1->type, locs1->ruse);

      locs1p = &cdr_(locs1); locs2p = &cdr_(locs2);

    } else if (locs2 != NULL && offset == locs2->offset) {
      size = memsize[locs2->type];
      if (locs1 != NULL && offset+size > locs1->offset) {
        offset = 0;
        break;
      } else
        *locs1p = locs1 = VKLoc_New(locs1, offset, locs2->type, locs2->ruse);
      locs1p = &cdr_(locs1); locs2p = &cdr_(locs2);

    } else {
      unsigned32 isize = memsize[MEM_I];
      size = n - offset;
      if (locs1 != NULL && size > locs1->offset - offset)
        size = locs1->offset - offset;
      if (locs2 != NULL && size > locs2->offset - offset)
        size = locs2->offset - offset;
      if (size % isize != 0) {
        offset = 0;
        break;
      }
      for (; size != 0; offset += isize, size -= isize) {
        VKLoc *p = VKLoc_New(locs1, offset, (int)MEM_I, GAP);
        *locs1p = p; locs1p = &cdr_(p);
        p = VKLoc_New(locs2, offset, (int)MEM_I, GAP);
        *locs2p = p; locs2p = &cdr_(p);
      }
    }
  }
  if (offset != n) {
    v1->splittable = v2->splittable = NO;
    return NO;
  } else
    return YES;
}

static RegSort SortOfReg(VRegnum r) {
  if (r != GAP) switch (vregsort(r)) {
  case FLTREG:  return FLTREG;
  case DBLREG:  return DBLREG;
#ifdef ADDRESS_REG_STUFF
  case ADDRREG: return ADDRREG;
#endif
  }
  return INTREG;
}

static J_OPCODE LDRV_Op(int32 memtype) {
  switch (memtype) {
  case MEM_F:  return J_LDRFV | J_ALIGN4;
  case MEM_D:  return J_LDRDV | J_ALIGN8;
  case MEM_LL: return J_LDRLV | J_ALIGN8;
  default:     return J_LDRV  | J_ALIGN4;
  }
}

static Binder *SR_NewBinder(char *name, VRegnum oldr) {
  /* @@@ The following code should share with with addcsebinder(),      */
  /* particularly beware te_int for 64-bit machines.                    */
  RegSort regsort = SortOfReg(oldr);
  return gentempvarofsortwithname(regsort, name);
}

static void SplitStructs(BindList *local_binders, BindList *regvar_binders) {
  /* Here we turn non address taken local structures into a set of      */
  /* binders, one per field. Fields must be disjoint, and accessed only */
  /* in one way (unions of machine-level distinct types not allowed).   */
  /* For structures accessed only by loads and stores, ({LD/ST}RxVK)    */
  /* this transformation is regardless of size: those assigned to and   */
  /* from (MOVC) are transformed only if they are sufficiently small.   */
  BlockHead *b;
  int32 argwords = 0;
  vklist = NULL;
  setsplist = NULL;
  movclist = NULL, movctail = &movclist;
  adconv_unused = NULL;
  movc_unknown = NULL;
  if (debugging(DEBUG_SR))
    cc_msg("Splitting structures\n\n");
  for (b = top_block; b != NULL; b = blkdown_(b))
    SplitStructs_ScanBlock(b);

  { RegList *rl = movc_unknown;
    for (; rl != NULL; rl = rl->rlcdr) {
      AdconvList *a = adconv_unused;
      VRegnum r = rl->rlcar;
      for (; a != NULL; a = cdr_(a))
        if (a->r == r) {
          if (debugging(DEBUG_SR))
            cc_msg("$b unsplittable (adconv_unused)\n", a->b);
          MarkBinderUnsplittable(a->b);
          break;
        }
    }
  }
  { MOVCList *p = movclist;
    for (; p != NULL; p = cdr_(p))
      if (p->b1 == NULL)
        FillInFields(p->b2, p->ic->r3.i);
      else if (p->b2 == NULL)
        FillInFields(p->b1, p->ic->r3.i);
      else
        CheckSameStructure(p->b1, p->b2, p->ic->r3.i);
  }
  { VKList *p; VKLoc *loc;
    /* Argument structures some of whose fields aren't integers can't   */
    /* be split                                                         */
    for (p = vklist; p != NULL; p = cdr_(p))
      if (BinderIsArg(p->b))
        for (loc = p->locs; loc != NULL; loc = cdr_(loc))
          if (loc->type != MEM_I) {
            if (debugging(DEBUG_SR))
              cc_msg("$b unsplittable (argument with non-int field)\n", p->b);
            p->splittable = NO;
            break;
          }
    for (p = vklist; p != NULL; p = cdr_(p))
      if (p->splittable) {
        Binder *oldb = p->b;
        bool isarg = BinderIsArg(oldb);
        /* p->locs == NULL and p->splittable means completely unused.   */
        /* (Probably CSE discarded uses). Splitting the struct is the   */
        /* easy way to discard it.                                      */
        if (p->locs == NULL) {
          if ((bindmcrep_(oldb) & MCR_SIZE_MASK) >= sizeof_int)
            FillInFields(oldb, sizeof_int);
          else {
            if (debugging(DEBUG_SR))
              cc_msg("$b unsplittable (referenced argument)\n", p->b);
            p->splittable = NO;
          }
          if (!p->splittable) continue;
        }
        if (debugging(DEBUG_SR | DEBUG_CG))
          cc_msg("split $b\n", oldb);

        for (loc = p->locs; loc != NULL; loc = cdr_(loc)) {
          char name[128];
          VKUse *use;
          Binder *newb;
          sprintf(name, "<%s.%ld>", symname_(bindsym_(oldb)), loc->offset);
          newb = SR_NewBinder(name, loc->ruse);
          if (isarg) {
            argwords++;
            bindaddr_(newb) = bindaddr_(oldb) + loc->offset;
          } else
            bindstg_(newb) |= b_bindaddrlist;

          for (use = loc->uses; use != NULL; use = cdr_(use)) {
            Icode *c = use->use;
            c->op = J_XtoY(c->op, J_LDRVK, J_LDRV);
            c->r2.r = GAP;
            c->r3.b = newb;
          }
          loc->bind = newb;
        }
        { BindList *bl = NULL;
          for (b = top_block; b != NULL; b = blkdown_(b)) {
            bl = bindlist_member(p->b, blkstack_(b));
            if (bl != NULL) break;
          }
          if (bl == NULL) {
            VKUse *sp;
            for (sp = setsplist; sp != NULL; sp = cdr_(sp)) {
              bl = bindlist_member(p->b, sp->use->r2.bl);
              if (bl == NULL && sp->use->op == J_SETSPENV)
                bl = bindlist_member(p->b, sp->use->r3.bl);
              if (bl != NULL) break;
            }
          }
          SpliceInBL(bl, p->locs, YES);
          SpliceInBL(bindlist_member(p->b, local_binders), p->locs, NO);
          SpliceInBL(bindlist_member(p->b, regvar_binders), p->locs, NO);
          SpliceInBL(bindlist_member(p->b, argument_bindlist), p->locs, NO);
        }
      }
  }
  { MOVCList *p, **pp = &movclist;
    for (; (p = *pp) != NULL; ) {
      if (p->b1 != NULL && !bindvklist_(p->b1)->splittable) p->b1 = NULL;
      if (p->b2 != NULL && !bindvklist_(p->b2)->splittable) p->b2 = NULL;
      if (p->b1 == NULL && p->b2 == NULL)
        *pp = cdr_(p);
      else
        pp = &cdr_(p);
    }
    if (argwords != 0) {
      BlockHead *b = top_block;
      int32 oldl = blklength_(b);
      Icode *newic = newicodeblock(oldl+argwords);
      Icode *oldic = blkcode_(b);
      VKList *vk;
      int32 n;

      blkcode_(b) = newic;
      /* Copy everything up to J_ENTER */
      n = 0;
      do { *newic++ = *oldic++; n++; } while (((newic-1)->op & J_TABLE_BITS) != J_ENTER);
      blklength_(b) += argwords;
      for (vk = vklist; vk != NULL; vk = cdr_(vk)) {
        VKLoc *loc;
        if (vk->splittable && BinderIsArg(vk->b))
          for (loc = vk->locs; loc != NULL; loc = cdr_(loc), newic++) {
            VRegnum ir = ArgumentRegister(loc->bind);
            INIT_IC(*newic, J_MOVR);
            newic->r1.r = bindxx_(loc->bind);
            newic->r3.r = R_P1+ir;
          }
      }
      memcpy(newic, oldic, (size_t)(oldl-n) * sizeof(Icode));
    }
    for (p = movclist; p != NULL; ) {
      BlockHead *b = p->block;
      MOVCList *q;
      int32 n = 0;
      for (q = p; q != NULL && q->block == b; q = cdr_(q)) {
        unsigned32 size = q->ic->r3.i;
        Binder *b = q->b1 == NULL ? q->b2 : q->b1;
        VKLoc *loc = bindvklist_(b)->locs;
        for (; loc != NULL; loc = cdr_(loc))
          if (loc->offset < size) n += 2;
        n--;
      }
      { int32 oldl = blklength_(b);
        Icode *newic = newicodeblock(oldl+n);
        Icode *oldic = blkcode_(b);
        int32 i;
        blkcode_(b) = newic;
        blklength_(b) += n;
        for ( i = 0 ; i != oldl ; i++ ) {
          if (p == q || &oldic[i] != p->ic)
            *newic++ = oldic[i];
          else {
            unsigned32 size = p->ic->r3.i;
            Binder *b1 = p->b1,
                   *b2 = p->b2;
            VKLoc *loc, *loc2;
            if (b1 == NULL)
              loc = loc2 = VKLoc_ReverseCopy(bindvklist_(b2)->locs);
            else {
              loc = bindvklist_(b1)->locs;
              loc2 = b2 == NULL ? NULL : bindvklist_(b2)->locs;
            }
            for (; loc != NULL; loc = cdr_(loc))
              if (loc->offset >= size) {
                if (loc2 != NULL) loc2 = cdr_(loc2);
              } else {
                VRegnum r = vregister(SortOfReg(loc->ruse));
                if (b2 == NULL) {
                  INIT_IC(*newic, J_XtoY(LDRV_Op(loc->type), J_LDRV, J_LDRK));
                  newic->r1.r = r;
                  newic->r2 = p->ic->r2;
                  newic->r3.i = loc->offset;
                } else {
                  INIT_IC(*newic, LDRV_Op(loc->type));
                  newic->r1.r = r;
                  newic->r3.b = loc2->bind;
                  loc2 = cdr_(loc2);
                }
                newic++;
                if (b1 == NULL) {
                  INIT_IC(*newic, J_LDtoST(J_XtoY(LDRV_Op(loc->type), J_LDRV, J_LDRK)));
                  newic->r1.r = r;
                  newic->r2 = p->ic->r1;
                  newic->r3.i = loc->offset;
                } else {
                  INIT_IC(*newic, J_LDtoST(LDRV_Op(loc->type)));
                  newic->r1.r = r;
                  newic->r3.b = loc->bind;
                }
                newic++;
              }
            p = cdr_(p);
          }
        }
      }
    }
  }
  { VKList *p;
    for (p = vklist; p != NULL; p = cdr_(p)) {
      bindxx_(p->b) = p->bindxx;
      bindstg_(p->b) ^= u_loctype;
    }
  }
}

struct SRBlockHead {
  VRegSetP reach, gen, kill, use;
};

#define sr_kill_(p) (blksr_(p)->kill)
#define sr_use_(p) (blksr_(p)->use)
#define sr_gen_(p) (blksr_(p)->gen)
#define sr_reach_(p) (blksr_(p)->reach)

typedef struct SR_UseList SR_UseList;
typedef struct SR_DefList SR_DefList;
typedef struct SR_Def SR_Def;
struct SR_Def {
  SR_Def *cdr;
  unsigned32 index;
  BlockHead *block;
  int32 ic;
  SR_UseList *uses;
  VRegSetP usedefs;
};

struct SR_DefList {
  SR_DefList *cdr;
  SR_Def *def;
};
#define mkSR_DefList(a,b) (SR_DefList *)syn_list2(a,b)

typedef struct SR_Use SR_Use;
struct SR_Use {
  SR_Use *cdr;
  BlockHead *block;
  int32 ic;
  VRegSetP def;
};

struct SR_UseList {
  SR_UseList *cdr;
  SR_Use *use;
};
#define mkSR_UseList(a,b) (SR_UseList *)syn_list2(a,b)

typedef struct SR_Binder SR_Binder;
struct SR_Binder {
  SR_Binder *cdr;
  unsigned32 index;
  Binder *binder;
  SR_Def *defs;
  SR_Use *uses;
  VRegSetP defset;
  SuperBinder *super;
};

SuperBinder *superbinders;

#define SRSEGSIZE 512
#define SRINDEXSIZE 64
#define SRSEGBITS 9

static SR_Binder **binderindex[SRINDEXSIZE];

#define sr_binder_(id) (binderindex[(id)>>SRSEGBITS])[(id)&(SRSEGSIZE-1)]

#define SRHASHSIZE 512
#define SRHASH(b) ((((IPtr)b>>2) |((IPtr)b>>11)) & (SRHASHSIZE-1))

static SR_Binder **binderhash;

static unsigned32 bindercount;
static unsigned32 defcount;

static VRegSetAllocRec allocrec;
static unsigned32 nsets, newsets, setbytes;

#define debug_sr debugging(DEBUG_SPILL)

static SR_Binder *LookupBinder(Binder *b) {
  SR_Binder *p, **pp = &binderhash[SRHASH(b)];
  if (bindstg_(b) & (b_addrof+b_spilt+b_globalregvar) || bindxx_(b) == GAP)
    return NULL;
  for (; (p = *pp) != NULL; pp = &cdr_(p))
    if (p->binder == b) return p;
  { unsigned32 id = bindercount++;
    SR_Binder **index = binderindex[id>>SRSEGBITS];
    p = NewSyn(SR_Binder);
    cdr_(p) = NULL; p->index = id; p->binder = b;
    p->defs = NULL; p->uses = NULL; p->defset = NULL;
    p->super = NULL;
    *pp = p;
    if (index == NULL) {
      index = NewSynN(SR_Binder *, SRSEGSIZE);
      binderindex[id>>SRSEGBITS] = index;
      ClearToNull((void **)index, SRSEGSIZE);
    }
    index[id & (SRSEGSIZE-1)] = p;
  }
  return p;
}

static SR_Binder *AddDef(Binder *b, BlockHead *block, int32 ic) {
  SR_Binder *sr = LookupBinder(b);
  if (sr != NULL) {
    unsigned32 n = defcount++;
    SR_Def *p = NewSyn(SR_Def);
    cdr_(p) = sr->defs; sr->defs = p;
    p->index = n;
    p->block = block; p->ic = ic;
    p->uses = NULL;
    sr->defset = vregset_insert(n, sr->defset, NULL, &allocrec);
    if (debug_sr) cc_msg("%ld $b %ld:%ld\n", n, b, lab_name_(blklab_(block)), ic);
  }
  return sr;
}

static void Scan_MakeGenSet(IPtr n, void *arg) {
  BlockHead *b = (BlockHead *)arg;
  SR_Binder *sr = sr_binder_(n);
  sr_gen_(b) = vregset_insert(sr->defs->index, sr_gen_(b), NULL, &allocrec);
}

static void ScanBlock(BlockHead *block) {
  Icode *c, *limit;
  VRegSetP use = NULL, kill = NULL, gen = NULL;
  /* gen   set of binders defined in this blocks whose definition reaches the end.
     kill  set of binders whose definition on block entry is killed before block
           end (since we only concern ourself with simple non-address-taken object
           binders, gen and kill are very similar. In fact, they differ only for
           top_block, where arguments are members of gen but not kill).
     use   the set of binders read in the block where the read is reached by
           definitions entering the block.
   */
  for (c = blkcode_(block), limit = c + blklength_(block); c < limit; ++c)
    switch (c->op & J_TABLE_BITS) {
    case J_LDRBV: case J_LDRWV:
    case J_LDRV:  case J_LDRLV:
    case J_LDRFV: case J_LDRDV:
      { SR_Binder *sr = LookupBinder(c->r3.b);
        if (sr != NULL) {
          SR_Use *p = NewSyn(SR_Use);
          cdr_(p) = sr->uses; sr->uses = p;
          p->block = block; p->ic = c - blkcode_(block);
          /* Uses with a definition in the same block do not get added to   */
          /* the use set, but must be linked to the definition immediately. */
          if (!vregset_member(sr->index, gen)) {
            use = vregset_insert(sr->index, use, NULL, &allocrec);
            p->def = NULL;
          } else
            p->def = vregset_insert(sr->defs->index, NULL, NULL, &allocrec);
        }
        break;
      }

    case J_MOVR: case J_MOVIDR: case J_MOVIFR:
    case J_MOVDR: case J_MOVDFR:
    /* Special case of initialisation of the binder for an argument passed  */
    /* in a register. It's a pain that these aren't handled in the natural  */
    /* way, by stores into the binder.                                      */
      if (block == top_block && isany_realreg_(c->r3.r)) {
        BindList *bl = argument_bindlist;
        for (; bl != NULL; bl = cdr_(bl))
          if (bindxx_(bl->bindlistcar) == c->r1.r) {
            SR_Binder *sr = AddDef(bl->bindlistcar, block, c - blkcode_(block));
            if (sr != NULL) gen = vregset_insert(sr->index, gen, NULL, &allocrec);
            break;
          }
      }
      break;
    case J_LDRV1: case J_LDRLV1:
    case J_LDRFV1: case J_LDRDV1:
    /* Initialisation of the binder for an argument passed on the stack.    */
    case J_INIT: case J_INITF: case J_INITD:
    case J_STRBV: case J_STRWV:
    case J_STRV:  case J_STRLV:
    case J_STRFV: case J_STRDV:
      { SR_Binder *sr = AddDef(c->r3.b, block, c - blkcode_(block));
        if (sr != NULL) {
          kill = vregset_insert(sr->index, kill, NULL, &allocrec);
          gen = vregset_insert(sr->index, gen, NULL, &allocrec);
        }
        break;
      }
    }
  /* We can turn gen directly into a set of binder definitions now: use and kill
     must wait until all blocks have been scanned (when we know the set of all
     definitions for each binder).
   */
  sr_use_(block) = use;
  sr_kill_(block) = kill;
  sr_gen_(block) = NULL;
  sr_reach_(block) = NULL;
  vregset_map(gen, Scan_MakeGenSet, (void *)block);
  vregset_discard(gen);
}

static void SR_MakeKilledSet(IPtr n, void *arg) {
  BlockHead *b = (BlockHead *)arg;
  SR_Binder *sr = sr_binder_(n);
  sr_kill_(b) = vregset_union(sr_kill_(b), sr->defset, &allocrec);
}

static bool ReachSucc(LabelNumber *lab, VRegSetP reachpred) {
  if (!is_exit_label(lab)) {
    BlockHead *b = lab->block;
    if (vregset_compare(reachpred, sr_reach_(b)) > VR_EQUAL) {
      sr_reach_(b) = vregset_union(sr_reach_(b), reachpred, &allocrec);
      return YES;
    }
  }
  return NO;
}

static void ReplaceBinder(SR_Def *def, Binder *newb, Binder *oldb) {
  SR_UseList *p = def->uses;
  Icode *ip = &blkcode_(def->block)[def->ic];
  switch (ip->op & J_TABLE_BITS)
  {
  case J_INIT: case J_INITF: case J_INITD:
    ip->r3.b = newb;
    ip->r1.r = bindxx_(newb);
    if (p != NULL && HasFeature(Feature_Anomoly))
      cc_warn(regalloc_warn_use_before_set, oldb);
    break;
  case J_LDRV1: case J_LDRLV1:
  case J_LDRFV1: case J_LDRDV1:
    ip->r3.b = newb;
    ip->r1.r = bindxx_(newb);
    break;
  case J_MOVR: case J_MOVIDR: case J_MOVIFR:
  case J_MOVDR: case J_MOVDFR:
  /* Special case of initialisation of the binder for an argument passed
   * in registers
   */
    ip->r1.r = bindxx_(newb);
    break;
  default:
    ip->r3.b = newb;
  }
  for (; p != NULL; p = cdr_(p))
    blkcode_(p->use->block)[p->use->ic].r3.b = newb;
}

static Binder *SubBinder(SR_Binder *p, SR_Def *def) {
  Binder *newb;
  Binder *oldb = p->binder;
  if (p->super == NULL) {
    SuperBinder *super = NewBind(SuperBinder);
    cdr_(super) = superbinders; superbinders = super;
    super->binder = oldb;
    super->spillcount = 0;
    p->super = super;
  }
  /* @@@ The following code should share with with addcsebinder(),      */
  /* particularly beware te_int for 64-bit machines.                    */
  { char name[128];
    char *oldname = symname_(bindsym_(oldb));
    sprintf(name, "<%s__%ld:%ld>",
                  oldname, lab_name_(blklab_(def->block)), def->ic);
    newb = SR_NewBinder(name, bindxx_(oldb));
    bindstg_(newb) = (bindstg_(oldb) & ~b_bindaddrlist) | b_pseudonym;
    bindsuper_(newb) = p->super;
    return newb;
  }
}

static BindList *splitranges_i(BindList *local_binders, BindList *regvar_binders) {
  BindList *newbinders = NULL;
  if (!(var_cc_private_flags & 131072L)) {
    phasename = "SplitStructs";
    SplitStructs(local_binders, regvar_binders);
  }
  if (!(var_cc_private_flags & 256L)) {
    BlockHead *b;
    phasename = "SplitRanges";
    defcount = bindercount = 0;
    vregset_init();
    binderhash = NewSynN(SR_Binder *, SRHASHSIZE);
    ClearToNull((void **)binderhash, SRHASHSIZE);
    ClearToNull((void **)binderindex, SRINDEXSIZE);
    for (b = top_block; b != NULL; b = blkdown_(b)) {
      blksr_(b) = NewSyn(SRBlockHead);
      ScanBlock(b);
    }
    for (b = top_block; b != NULL; b = blkdown_(b)) {
      VRegSetP killedbinders = sr_kill_(b);
      sr_kill_(b) = NULL;
      vregset_map(killedbinders, SR_MakeKilledSet, (void *)b);
    }
    { bool changed;
      do {
        if (debug_sr) cc_msg("Reaching definition iteration\n");
        changed = NO;
        for (b = top_block; b != NULL; b = blkdown_(b)) {
          VRegSetP reachend = vregset_copy(sr_reach_(b), &allocrec);
          reachend = vregset_difference(reachend, sr_kill_(b));
          reachend = vregset_union(reachend, sr_gen_(b), &allocrec);
          if (blkflags_(b) & BLKSWITCH) {
            LabelNumber **v = blktable_(b);
            int32 i, n = blktabsize_(b);
            for (i = 0 ; i < n ; i++)
              changed = changed | ReachSucc(v[i], reachend);
          } else {
            changed = changed | ReachSucc(blknext_(b), reachend);
            if (blkflags_(b) & BLK2EXIT)
              changed = changed | ReachSucc(blknext1_(b), reachend);
          }
        }
      } while (changed);
    }

    { unsigned32 bno = 0;
      for (; bno < bindercount; bno++) {
          SR_Binder *p = sr_binder_(bno);
          SR_Use *use; SR_Def *def, *d;
          for (use = p->uses; use != NULL; use = cdr_(use)) {
            if (use->def == NULL) {
              use->def = vregset_copy(sr_reach_(use->block), &allocrec);
              use->def = vregset_intersection(use->def, p->defset);
            }
          }
          for (def = p->defs; def != NULL; def = cdr_(def)) {
            unsigned32 ix = def->index;
            VRegSetP defset = NULL;
            for (use = p->uses; use != NULL; use = cdr_(use))
              if (vregset_member(ix, use->def)) {
                def->uses = mkSR_UseList(def->uses, use);
                defset = vregset_union(defset, use->def, &allocrec);
              }
            def->usedefs = defset;
          }
          { bool changed;
            do {
              changed = NO;
              for (def = p->defs; def != NULL; def = cdr_(def)) {
                VRegSetP defset = def->usedefs;
                for (d = p->defs; d != NULL; d = cdr_(d))
                  if (d != def && vregset_member(d->index, defset) &&
                      vregset_compare(defset, d->usedefs) != VR_EQUAL) {
                    changed = YES;
                    defset = vregset_union(defset, d->usedefs, &allocrec);
                    d->usedefs = vregset_union(d->usedefs, defset, &allocrec);
                  }
                def->usedefs = defset;
              }
            } while (changed);
          }
          { SR_DefList *defl = NULL;
            SR_Def *nextdef;
            for (def = p->defs; def != NULL; def = nextdef) {
              VRegSetP defset = def->usedefs;
              SR_Def *q, **qp;
              nextdef = cdr_(def);
              cdr_(def) = NULL;
              defl = mkSR_DefList(defl, def);
              for (qp = &nextdef; (q = *qp) != NULL;)
                if (vregset_compare(defset, q->usedefs) == VR_EQUAL) {
                  *qp = cdr_(q);
                  cdr_(q) = defl->def;
                  defl->def = q;
                } else
                  qp = &cdr_(q);
            }
            /* defl == NULL is possible here, though curious, thanks to the */
            /* workings of deadcode (otherwise, there's always at least a   */
            /* J_INIT definition).                                          */
            if ( defl != NULL &&
                 cdr_(defl) != NULL &&
            /* Definitions do partition into more than one set              */
            /* Avoid the case where one set is just a J_INIT with no uses   */
                 ( cdr_(cdr_(defl)) != NULL  ||
                   ( (cdr_(defl->def) != NULL || defl->def->uses != NULL) &&
                     (cdr_(cdr_(defl)->def) != NULL || cdr_(defl)->def->uses != NULL)) ) ) {

              if (debug_sr)
                cc_msg("Split $b:", p->binder);
              for (; defl != NULL; defl = cdr_(defl)) {
                SR_Def *d = defl->def;
                Binder *newb = SubBinder(p, d);
                SR_Def *initd = d;
                char *s1 = " {", *s2 = "";
                newbinders = mkBindList(newbinders, newb);
                if (debug_sr)
                  cc_msg(" $b", newb);
                for (; d != NULL; d = cdr_(d)) {
                  ReplaceBinder(d, newb, p->binder);
                  if (debug_sr && d != initd) {
                    cc_msg("%s%ld:%ld", s1, lab_name_(blklab_(d->block)), d->ic);
                    s1 = ", "; s2 = "}";
                  }
                }
                if (debug_sr) cc_msg("%s", s2);
              }
              if (debug_sr) cc_msg("\n");
              bindxx_(p->binder) = GAP;
            }
          }
      }
    }
  }
  if ( debugging(DEBUG_CG) &&
       (var_cc_private_flags & (131072L+256L)) != (131072L+256L))
    flowgraf_print("After range splitting:", NO);
  return newbinders;
}

BindList *splitranges(BindList *local_binders, BindList *regvar_binders) {
  BindList *newbinders = NULL;
  BlockHead *b;
  superbinders = NULL;
  if (!usrdbg(DBG_LINE+DBG_VAR))
    newbinders = splitranges_i(local_binders, regvar_binders);
  for (b = top_block; b != NULL; b = blkdown_(b)) {
    /* Although flowgraf also wants blkusedfrom_() for cross-jumping and
       conditionalising, it wants a version after branch chaining, and the
       branch chaining algorithm can't easily adjust it.
     */
    BlockList *bl = blkusedfrom_(b);
    while (bl != NULL) bl = (BlockList *)discard2((List *)bl);
    blkusedfrom_(b) = NULL;
    vregset_discard(blk_dominators_(b));
    blk_dominators_(b) = NULL;
  }
  return newbinders;
}

void splitrange_init(void) {
  allocrec.alloctype = AT_Syn;
  allocrec.statsloc = &nsets;
  allocrec.statsloc1 = &newsets;
  allocrec.statsbytes = &setbytes;
}
