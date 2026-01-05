/*
 * inline.c: inline function expansion
 * Copyright (C) Advanced Risc Machines Ltd., 1993
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

/* Nasties to tidy up:
** (1) the use of h0_(Binder)
** (2) lab_xname_()/lab_name_(). Use small ints everywhere for labelnumbers?
*/

#include <string.h>
#include <stddef.h>  /* offsetof */

#include "globals.h"
#include "store.h"
#include "flowgraf.h"
#include "codebuf.h"
#include "regalloc.h"
#include "aeops.h"
#include "aetree.h"
#include "bind.h"
#include "jopcode.h"
#include "inline.h"
#include "cg.h"
#include "regsets.h"
#include "simplify.h"
#include "errors.h"
#include "builtin.h"
#include "sem.h"
#include "dump.h"
#include "mcdep.h"

typedef struct SavedFnList SavedFnList;
typedef union { RegSort rs; VRegnum r; } Inline_VRegIndex;

typedef struct {
  Inline_ArgBinderList abl;
  int flags;
  uint8 accesssize,   /* a MEM_xx value or MEM_NONE */
        accessmap;
  int32 mink, maxk;
  Inline_ArgSubstList *argsubst;
} Inline_ArgDesc;

#define argdesc_(p) (*(Inline_ArgDesc **)&(p)->fn.args)
#define adcdr_(p) (*(Inline_ArgDesc **)&cdr_(&(p)->abl))

#define IA_Updated 1
#define IA_OddAccess 2
#define IA_AccessSet 4
#define IA_UpdatedOutsideCore 8
#define IA_OddUseForPlusInCore 16

typedef uint8 BlockMap;

typedef enum {
  IS_Ord,
  IS_Ctor,
  IS_Dtor
} Inline_Sort;

struct SavedFnList {
  SavedFnList *cdr;
  Inline_SavedFn fn;
  int32 maxlabel;
  VRegnum maxreg;
  Inline_VRegIndex *vregtypetab;
  Inline_Sort sort;
  union {
    BlockMap *ctor;
    BlockHead *dtor;
  } a;
  uint8 outoflineflags;
};

#define ol_used 1
#define ol_emitted 2

typedef struct BindListIndex BindListIndex;
struct BindListIndex {
  BindListIndex *cdr;
  BindList *orig;
  BindList *copy;
};

typedef struct SymTrans SymTrans;
struct SymTrans {
  SymTrans *cdr;
  Symstr *oldsym;
  Symstr *newsym;
};

typedef struct {
  SynBindList *copied;
  BindListIndex *sharedbindlists;
  Inline_VRegIndex *vregindex;
  BindList *nullenv;
  SymTrans *symtrans;
} SaveFnState;

static SavedFnList *saved_fns;

Inline_SavedFn *Inline_FindFn(Binder *b) {
  SavedFnList *fn = (SavedFnList *)bindinline_(b);
  if (fn != NULL)
    return &fn->fn;
  return NULL;
}

void Inline_RealUse(Binder *b) {
  SavedFnList *fn = (SavedFnList *)bindinline_(b);
  attributes_(b) |= A_REALUSE;
  if (fn != NULL) fn->outoflineflags |= ol_used;
}

static BindList *GlobalSharedBindListCopy(SaveFnState *st, BindList *bl);

static Binder *GlobalBinderCopy(SaveFnState *st, Binder *b) {
  if (h0_(b) != s_binder) return (Binder *)(IPtr)h0_(b);
  { Symstr *sym = bindsym_(b);
    Binder *bnew;
    size_t n;
    if (bindstg_(b) & (bitofstg_(s_virtual)|b_globalregvar|bitofstg_(s_auto)))
      n = sizeof(Binder);
    else {
      if (attributes_(b) & A_GLOBALSTORE) return b;
      n = SIZEOF_NONAUTO_BINDER;
    }
    if (isgensym(sym)) {
      SymTrans *p = st->symtrans;
      for (; p != NULL; p = cdr_(p))
        if (p->oldsym == sym)
          break;
      if (p == NULL) {
        p = NewSyn(SymTrans);
        cdr_(p) = st->symtrans; st->symtrans = p;
        p->oldsym = sym; p->newsym = gensymvalwithname(YES, symname_(sym));
      }
      sym = p->newsym;
    }
    bnew = global_mk_binder(NULL, sym, bindstg_(b), bindtype_(b));
    memcpy(bnew, b, n);
    bindsym_(bnew) = sym;
    h0_(b) = (AEop)(IPtr)bnew;
    st->copied = mkSynBindList(st->copied, b);
    if (bindstg_(b) & b_bindaddrlist)
      bindbl_(bnew) = GlobalSharedBindListCopy(st, bindbl_(b));
    return bnew;
  }
}

static BindList *GlobalBindListCopy(SaveFnState *st, BindList *bl) {
  BindList *bl_new = NULL;
  BindList *bp, **bpp = &bl_new;
  Binder *prevb = NULL;
  for (; bl != NULL; bl = bl->bindlistcdr, bpp = &bp->bindlistcdr) {
    Binder *b = GlobalBinderCopy(st, bl->bindlistcar);
    if (prevb)
        bindcdr_(prevb) = b;
    prevb = b;
    bp = (BindList *)global_cons2(SU_Inline, NULL, b);
    *bpp = bp;
  }
  return bl_new;
}

static BindList *GlobalSharedBindListCopy(SaveFnState *st, BindList *bl) {
  BindListIndex *p = st->sharedbindlists;
  if (bl == NULL) return NULL;

  for (; p != NULL; p = cdr_(p))
    if (bl == p->orig)
      return p->copy;

  { BindList *bl_new = (BindList *)global_cons2(SU_Inline,
                                                GlobalSharedBindListCopy(st, bl->bindlistcdr),
                                                GlobalBinderCopy(st, bl->bindlistcar));
    st->sharedbindlists = (BindListIndex *)syn_list3(st->sharedbindlists, bl, bl_new);
    return bl_new;
  }
}

static Inline_ArgDesc *ArgDesc_Find(Binder *b, Inline_ArgDesc *ad) {
  for (; ad != NULL; ad = adcdr_(ad))
    if (ad->abl.narrowtype != NULL) {
      if (b == ad->abl.globnarrowarg)
        break;
    } else
      if (b == ad->abl.globarg)
        break;
  return ad;
}

static bool IsSTRWExpansion(Icode *ic, int32 *offset) {
  /* Already checked that ic->op is STRBK */
  Icode *ic2 = ic+1,
        *ic3 = ic+2;
  if ((ic2->op & J_TABLE_BITS) == J_SHRK && ic2->r3.i == 8
      && ic->r1.r == ic2->r2.r
      && (ic3->op & J_TABLE_BITS) == J_STRBK && ic3->r2.r == ic->r2.r
      && ic3->r1.r == ic2->r1.r
      && (target_lsbytefirst ? ic3->r3.i == ic->r3.i+1 :
                               ic3->r3.i+1 == ic->r3.i)) {
    *offset = target_lsbytefirst ? ic->r3.i : ic->r3.i-1;
    return YES;
  }
  return NO;
}

#define MapSize(n) ((size_t)(((n) + 7) / 8))

static BlockMap *NewTempMap(unsigned32 n) {
  size_t size = MapSize(n);
  BlockMap *map = NewSynN(BlockMap, size);
  memset(map, 0, size);
  return map;
}

static BlockMap *NewBlockMap(unsigned32 n) {
  size_t size = MapSize(n);
  BlockMap *map = NewGlobN(BlockMap, SU_Inline, size);
  memset(map, 0, size);
  return map;
}

static bool MapBitSet(BlockMap *map, unsigned32 n) {
  BlockMap *p = &map[n / 8];
  unsigned bit = 1 << (n % 8);
  return ((*p & bit) != 0);
}


static bool SetMapBit(BlockMap *map, unsigned32 n) {
  BlockMap *p = &map[n / 8];
  unsigned bit = 1 << (n % 8);
  if ((*p & bit) == 0) {
    *p |= bit;
    return YES;
  } else
    return NO;
}

static void ClearMapBit(BlockMap *map, unsigned32 n) {
  BlockMap *p = &map[n / 8];
  unsigned bit = 1 << (n % 8);
  *p &= ~bit;
}

static void AddToMap(BlockMap *map, LabelNumber *lab) {
  if (!is_exit_label(lab)) {
    BlockHead *b = lab->block;
    if (SetMapBit(map, lab_name_(lab))) {
      if (blkflags_(b) & BLKSWITCH) {
        int32 n = blktabsize_(b);
        LabelNumber **table = blktable_(b);
        while (--n >= 0) AddToMap(map, table[n]);
      } else {
        if (blkflags_(b) & BLK2EXIT)
          AddToMap(map, blknext1_(b));
        AddToMap(map, blknext_(b));
      }
    }
  }
}

/* The compiler prepends code to call new() to constructors, and postpends
 * code to call delete() to destructors. When called for objects which don't
 * need allocation/deallocation, this gives rise to dead code which latter
 * phases of compilation are capable of removing, but at a cost (the increased
 * number of basic blocks slows down both cse and regalloc). Also, the code
 * to call new() assigns to __this, preventing it from being substituted when
 * the constructor is inlined, and therefore (perhaps spuriously) leaving the
 * constructed object marked as address-taken.
 */
static void FindStructorCore(SavedFnList *p) {
  BlockHead *b = blkdown_(top_block);
  BindList *argbl = currentfunction.argbindlist;
  Binder *arg1 = argbl == NULL ? NULL : argbl->bindlistcar;
  p->sort = IS_Ord;
  if ((blkflags_(b) & BLK2EXIT) &&
      blklength_(b) == 2) {
    Icode *ic1 = blkcode_(b),
          *ic2 = ic1 + 1;
    if (ic1->op == J_LDRV+J_ALIGN4 && ic1->r3.b == arg1
        && (ic2->op & ~Q_MASK) == J_CMPK && Q_issame((ic2->op & Q_MASK), Q_NE)
        && ic2->r3.i == 0 && ic2->r2.r == ic1->r1.r) {
      BlockMap *map = NewBlockMap(p->maxlabel);
      SetMapBit(map, lab_name_(blklab_(top_block)));
      AddToMap(map, blknext1_(b));
      p->a.ctor = map; p->sort = IS_Ctor;
    }
  } else {
    BlockHead *b2 = blkup_(bottom_block);
    BlockHead *b1 = blkup_(b2);
    if (b1 != NULL
        && !(blkflags_(b2) & (BLK2EXIT+BLKSWITCH))
        && blknext_(b2) == blklab_(bottom_block)
        && (blkflags_(b1) & BLK2EXIT) && Q_issame(blkflags_(b1) & Q_MASK, Q_EQ)
        && blknext_(b1) == blklab_(b2) && blknext1_(b1) == blklab_(bottom_block)
        && argbl != NULL && argbl->bindlistcdr != NULL) {
      Binder *arg2 = argbl->bindlistcdr->bindlistcar;
      int32 n = blklength_(b1);
      if (2 <= n) {
        Icode const *ic = &blkcode_(b1)[n-2];
        if ((ic[1].op & ~Q_MASK) == J_CMPK
            && ic[1].r3.i == 0 && ic[1].r2.r == ic[0].r1.r) {
          if (3 <= n
              && ic[-1].op == J_LDRV+J_ALIGN4 && ic[-1].r3.b == arg2
              && ic[0].op == J_ANDK
              && ic[0].r3.i == 1 && ic[0].r2.r == ic[-1].r1.r) {
            p->a.dtor = b1; p->sort = IS_Dtor;
            /* this is tentative: we need to know that arg2 isn't assigned to */
            /* before we're certain                                           */
          }
          else if (ic[0].op == J_LDRV+J_ALIGN4 && ic[0].r3.b == arg2) {
            p->a.dtor = b1; p->sort = IS_Dtor;
            /* this is tentative: we need to know that arg2 isn't assigned to */
            /* before we're certain                                           */
          }
        }
      }
    }
  }
}

typedef struct ABLList ABLList;
struct ABLList {
  ABLList *cdr;
  Inline_ArgDesc *arg;
};

static Inline_ArgDesc *ABL_Find(ABLList *p, Binder *b) {
  for (; p != NULL; p = cdr_(p))
    if (bindsym_(b) == bindsym_(p->arg->abl.globarg))
      return p->arg;
  return NULL;
}

static LabelNumber *LabelNo_NoteRef(LabelNumber *l, uint8 *justoneref, uint8 *anyref) {
  IPtr lno;
  uint32 mapbit;
  if (is_exit_label(l)) {
    lno = (IPtr)l;
    mapbit = 0;
  } else {
    lno = (IPtr)lab_name_(l);
    mapbit = lno;
  }
  if (SetMapBit(anyref, mapbit))
    SetMapBit(justoneref, mapbit);
  else
    ClearMapBit(justoneref, mapbit);
  return (LabelNumber *)(IPtr)lno;
}

bool Inline_Save(Binder *b, BindList *local_binders, BindList *regvar_binders) {
  SavedFnList *p = NewGlob(SavedFnList, SU_Inline);
  SaveFnState st;
  bindinline_(b) = p;
  p->outoflineflags = (attributes_(b) & A_REALUSE) ? ol_used : 0;
  st.copied = NULL;
  st.sharedbindlists = NULL;
  st.symtrans = NULL;
  p->fn.fndetails = currentfunction;
  if (p->fn.fndetails.structresult != NULL)
    p->fn.fndetails.structresult = GlobalBinderCopy(&st, p->fn.fndetails.structresult);
  if (p->fn.fndetails.xrflags & xr_defext)
    Inline_RealUse(b);
  p->fn.fndetails.argbindlist = GlobalBindListCopy(&st, p->fn.fndetails.argbindlist);
  p->fn.var_binders = GlobalBindListCopy(&st, local_binders);
  p->fn.reg_binders = GlobalBindListCopy(&st, regvar_binders);
  p->fn.top_block = p->fn.bottom_block = NULL;
  p->fn.firstblockignoresize = 0; p->fn.firstblockignore = NULL;
  p->fn.ix_narrowspenv = -1;
  p->maxreg = vregister(INTREG);
  p->maxlabel = lab_name_(nextlabel());
  FindStructorCore(p);
  { VRegnum n = p->maxreg;
    Inline_VRegIndex *vt = NewGlobN(Inline_VRegIndex, SU_Inline, p->maxreg);
    while (--n > NMAGICREGS) vt[n].rs = vregsort(n);
    p->vregtypetab = vt;
  }
  { BindList *bl = p->fn.fndetails.argbindlist;
    Inline_ArgDesc **adp = &argdesc_(p);
    FormTypeList *ft = typefnargs_(bindtype_(b));
    ABLList *narrowargs = NULL;
    p->fn.args = NULL;
    for (; bl != NULL; bl = bl->bindlistcdr) {
      Inline_ArgDesc *ad = NewGlob(Inline_ArgDesc, SU_Inline);
      Binder *b = bl->bindlistcar;
      adcdr_(ad) = NULL; ad->abl.globarg = b; ad->flags = 0; ad->accessmap = 0;
      *adp = ad; adp = &adcdr_(ad);
      ad->abl.globnarrowarg = ad->abl.instantiatednarrowarg = NULL;
      ad->abl.narrowtype = NULL;
      ad->mink = MaxMemOffset(J_LDRK+J_ALIGN4);
      ad->maxk = MinMemOffset(J_LDRK+J_ALIGN4);
      /* ft reflects the declared argument types of the function, bl the types
       * of arguments actually passed (they will differ in the type of narrow
       * arguments, and also only bl has an entry for the extra pointer-to-result
       * argument of structure-returning functions).
       */
      if (!(bl == p->fn.fndetails.argbindlist
            && p->fn.fndetails.structresult != NULL)) {
        if (widen_formaltype(ft->fttype) != ft->fttype) {
          ad->abl.narrowtype = ft->fttype;
          narrowargs = (ABLList *)syn_list2(narrowargs, ad);
        }
        ft = ft->ftcdr;
      }
    }
    if (narrowargs != NULL) {
      BlockHead *b = blkdown_(top_block);
      int32 n, len = blklength_(b);
      Icode *ic = blkcode_(b);
      uint8 *map = NewBlockMap(2*len);
      p->fn.firstblockignoresize = 2*len;
      p->fn.firstblockignore = map;
      p->fn.ix_max = len;
      for (n = 0; n < len; ic++, n++) {
        J_OPCODE op = ic->op & J_TABLE_BITS;
        if (op == J_SETSPENV && p->fn.ix_narrowspenv == -1) {
          p->fn.ix_narrowspenv = n;
          SetMapBit(map, n);
        } else if (op == J_STRV || op == J_STRDV) {
          Binder *mb = GlobalBinderCopy(&st, ic->r3.b);
          Inline_ArgDesc *ad = ABL_Find(narrowargs, mb);
          if (ad != NULL && ad->abl.globnarrowarg == NULL) {
            ad->abl.globnarrowarg = mb;
            SetMapBit(map, len+n);
          }
        } else if (op == J_INIT || op == J_INITD) {
          Binder *mb = GlobalBinderCopy(&st, ic->r3.b);
          Inline_ArgDesc *ad = ABL_Find(narrowargs, mb);
          if (ad != NULL && ad->abl.globnarrowarg == NULL)
            SetMapBit(map, n);
        }
      }
    }
  }
  { BlockHead *b = top_block;
    BlockHead *blast = NULL, *bnew;
    uint8 *justoneref = NewTempMap(p->maxlabel),
          *anyref = NewTempMap(p->maxlabel);
    /* to help determine {first,last}blockmergeable */
    for (b = top_block; b != NULL; b = blkdown_(b), blast = bnew) {
      bnew = NewGlob(BlockHead, SU_Inline);
      *bnew = *b;
      blkup_(bnew) = blast;
      if (blast == NULL)
        p->fn.top_block = bnew;
      else
        blkdown_(blast) = bnew;
      if (blkflags_(b) & BLKSWITCH) {
        int32 n = blktabsize_(b);
        LabelNumber **sw_old = blktable_(b);
        LabelNumber **sw_new = NewGlobN(LabelNumber *, SU_Inline, n);
        while (--n >= 0)
          sw_new[n] = LabelNo_NoteRef(sw_old[n], justoneref, anyref);
        blktable_(bnew) = sw_new;
      } else {
        blknext_(bnew) = LabelNo_NoteRef(blknext_(b), justoneref, anyref);
        if (blkflags_(b) & BLK2EXIT)
          blknext1_(bnew) = LabelNo_NoteRef(blknext1_(b), justoneref, anyref);
      }
      blklab_(bnew) = (LabelNumber *)(IPtr)lab_name_(blklab_(b));
      blkstack_(bnew) = GlobalSharedBindListCopy(&st, blkstack_(b));
      { int32 n = blklength_(b), len = n;
        Icode *code_old = blkcode_(b);
        Icode *code_new = n == 0 ? (Icode *)DUFF_ADDR : NewGlobN(Icode, SU_Inline, n);
        bool inctorcore = YES;
        if (p->sort == IS_Ctor)
          inctorcore = MapBitSet(p->a.ctor, lab_name_(blklab_(b)));
        else if (p->sort == IS_Dtor && b == p->a.dtor)
          p->a.dtor = bnew;
        blkcode_(bnew) = code_new;
        while (--n >= 0) {
          Icode *ic_old = &code_old[n];
          Icode *ic_new = &code_new[n];
          J_OPCODE op = ic_old->op & J_TABLE_BITS;
          *ic_new = *ic_old;
          if (op == J_SETSPENV) {
            ic_new->r3.bl = GlobalSharedBindListCopy(&st, ic_new->r3.bl);
            ic_new->r2.bl = GlobalSharedBindListCopy(&st, ic_new->r2.bl);
          } else if (op == J_SETSPGOTO) {
            ic_new->r2.bl = GlobalSharedBindListCopy(&st, ic_new->r2.bl);
            ic_new->r3.l = (LabelNumber *)(IPtr)lab_xname_(ic_new->r3.l);
          } else if (uses_stack(op) || op == J_CALLK || op==J_ADCON
                     || op == J_INIT || op == J_INITF || op == J_INITD) {
            Binder *bnew = ic_new->r3.b = GlobalBinderCopy(&st, ic_new->r3.b);
            Inline_ArgDesc *ad = ArgDesc_Find(bnew, argdesc_(p));
            if (ad != NULL) {
              if (stores_r1(op)) {
                if (ad->abl.narrowtype == NULL
                    || b != blkdown_(top_block)
                    || !MapBitSet(p->fn.firstblockignore, len+n)) {
                  if (inctorcore)
                    ad->flags |= IA_Updated;
                  else
                    ad->flags |= IA_UpdatedOutsideCore;
                }
              } else if (op == J_LDRV) {
                Icode *next1 = ic_new + 1;
                if (n+1 < len) {
                  J_OPCODE nextop = next1->op & J_TABLE_BITS;
                  if (j_is_ldr_or_str(nextop)
                      && reads_r2(nextop)
                      && !reads_r3(nextop)
                      && next1->r2.r == ic_new->r1.r) {
                    int32 accesssize;
#ifdef TARGET_LACKS_HALFWORD_STORE
                    int32 k;
                    if (nextop == J_STRBK
                        && n+3 < len && IsSTRWExpansion(next1, &k) && k == 0)
                      accesssize = MEM_W;
                    else
#endif
                    if (next1->r3.i == 0) {
                      accesssize = j_memsize(nextop);
                    } else
                      accesssize = MEM_NONE;
                    if ((ad->flags & IA_AccessSet)
                        && ad->accesssize != accesssize)
                      accesssize = MEM_NONE;
                    ad->accesssize = accesssize;
                    ad->flags |= IA_AccessSet;
                    ad->accessmap |= (1 << j_memsize(nextop));
                    if (next1->r3.i < ad->mink) ad->mink = next1->r3.i;
                    if (next1->r3.i > ad->maxk) ad->maxk = next1->r3.i;
                    continue;

                  } else if (nextop == J_MOVR)
                    continue;
                }
                if (inctorcore) ad->flags |= IA_OddUseForPlusInCore;

              } else if (op != J_INIT && op != J_INITF && op != J_INITD)
                ad->flags |= IA_OddAccess;
            }
          } else if (op==J_STRING)
            ic_new->r3.s = globalize_strseg(ic_new->r3.s);
        }
      }
    }
    blkdown_(blast) = NULL;
    p->fn.bottom_block = blast;
    p->fn.lastblockmergeable = MapBitSet(justoneref, 0)
                               && !(blkflags_(blast) & (BLK2EXIT+BLKSWITCH))
                               && is_exit_label(blknext_(blast));
    p->fn.firstblockmergeable = MapBitSet(justoneref, (IPtr)blklab_(blkdown_(p->fn.top_block)));
  }
  { SynBindList *bl = st.copied;
    for (; bl != NULL; bl = bl->bindlistcdr)
      h0_(bl->bindlistcar) = s_binder;
  }
  if (p->sort == IS_Dtor) {
    /* retract if the second argument isn't read-only */
    Inline_ArgDesc *ad = adcdr_(argdesc_(p));
    if (ad->flags & (IA_OddAccess + IA_Updated + IA_UpdatedOutsideCore))
      p->sort = IS_Ord;
  }
  if (debugging(DEBUG_CG)) {
    cc_msg("Inline_Save %s", symname_(p->fn.fndetails.symstr));
    if (p->sort == IS_Dtor) {
      cc_msg(": Dtor: %x\n", blklab_(p->a.dtor));
    } else if (p->sort == IS_Ctor) {
      int32 i;
      BlockMap *map = p->a.ctor;
      int c = '{';
      cc_msg(": Ctor: ");
      for (i = 0; i < p->maxlabel; i++)
        if (MapBitSet(map, i)) { cc_msg("%c%ld", c, (long)i); c = ' '; }
      cc_msg("}\n");
    } else
      cc_msg("\n");
  }
  cdr_(p) = saved_fns;
  saved_fns = p;
  return YES;
}

static BindList *FromGlobalSharedBindListCopy(SaveFnState *st, BindList *bl);

static Binder *FromGlobalBinderCopy(SaveFnState *st, Binder *b) {
  if (h0_(b) != s_binder) return (Binder *)(IPtr)h0_(b);
  { Binder *bnew;
    size_t n;
    if (bindstg_(b) & (bitofstg_(s_virtual)|b_globalregvar|bitofstg_(s_auto)))
      n = sizeof(Binder);
    else {
      if (attributes_(b) & A_GLOBALSTORE) return b;
      n = SIZEOF_NONAUTO_BINDER;
    }
    bnew = mk_binder(bindsym_(b), bindstg_(b), bindtype_(b));
    memcpy(bnew, b, n);
    h0_(b) = (AEop)(IPtr)bnew;
    st->copied = mkSynBindList(st->copied, b);
    if (bindstg_(b) & bitofstg_(s_auto)) {
      if (bindstg_(b) & b_bindaddrlist)
        bindbl_(bnew) = FromGlobalSharedBindListCopy(st, bindbl_(b));
      if (bindxx_(b) != GAP) bindxx_(bnew) = st->vregindex[bindxx_(b)].r;
    }
    return bnew;
  }
}

static BindList *FromGlobalBindListCopy(SaveFnState *st, BindList *bl) {
  BindList *bl_new = NULL;
  BindList *bp, **bpp = &bl_new;
  for (; bl != NULL; bl = bl->bindlistcdr, bpp = &bp->bindlistcdr) {
    Binder *b = FromGlobalBinderCopy(st, bl->bindlistcar);
    bp = (BindList *)binder_cons2(NULL, b);
    *bpp = bp;
  }
  return bl_new;
}

static BindList *FromGlobalSharedBindListCopy(SaveFnState *st, BindList *bl) {
  BindListIndex *p = st->sharedbindlists;
  if (bl == NULL) return st->nullenv;
  for (; p != NULL; p = cdr_(p))
    if (bl == p->orig)
      return p->copy;

  { BindList *bl_new = (BindList *)binder_cons2(
                          FromGlobalSharedBindListCopy(st, bl->bindlistcdr),
                          FromGlobalBinderCopy(st, bl->bindlistcar));
    st->sharedbindlists = (BindListIndex *)syn_list3(st->sharedbindlists, bl, bl_new);
    return bl_new;
  }
}

static LabelNumber *FromGlobalLabel(
    LabelNumber **index, Inline_RestoreControl *rc, LabelNumber *old) {
  /* (LabelNumber *) values like 'old' here only hold small ints.       */
  return !is_exit_label(old) ? index[(IPtr)old] :
         rc != NULL && rc->exitlabel != NULL ? rc->exitlabel :
                               old;
}

static BindList *BindListCopy(BindList *bl) {
  BindList *bl_new = NULL;
  BindList *bp, **bpp = &bl_new;
  for (; bl != NULL; bl = bl->bindlistcdr, bpp = &bp->bindlistcdr) {
    bp = (BindList *)binder_cons2(NULL, bl->bindlistcar);
    *bpp = bp;
  }
  return bl_new;
}

static SavedFnList *FindSavedFn(Inline_SavedFn *fn) {
  SavedFnList *p;
  for (p = saved_fns; p != NULL; p = cdr_(p))
    if (fn->fndetails.symstr == p->fn.fndetails.symstr)
      return p;
  return NULL;
}

static bool OverlargeOffset(Inline_ArgDesc const *ad, Expr *ex) {
  uint8 map = ad->accessmap;
  int32 k = intval_(arg2_(ex));
  int32 mink = k + ad->mink,
        maxk = k + ad->maxk;
  int32 align = J_ALIGN4;       /* WD: temp hack - will become parameter!! */

  if ((map & (1 << MEM_B)) &&
      (mink < MinMemOffset(J_LDRBK+align) || maxk > MaxMemOffset(J_LDRBK+align))) return YES;
  if ((map & (1 << MEM_W)) &&
      (mink < MinMemOffset(J_LDRWK+align) || maxk > MaxMemOffset(J_LDRWK+align))) return YES;
  if ((map & (1 << MEM_I)) &&
      (mink < MinMemOffset(J_LDRK+align) || maxk > MaxMemOffset(J_LDRK+align))) return YES;
  if ((map & (1 << MEM_F)) &&
      (mink < MinMemOffset(J_LDRFK+align) || maxk > MaxMemOffset(J_LDRFK+align))) return YES;
  if ((map & (1 << MEM_D)) &&
      (mink < MinMemOffset(J_LDRDK+align) || maxk > MaxMemOffset(J_LDRDK+align))) return YES;
  if ((map & (1 << MEM_LL)) &&
      (mink < MinMemOffset(J_LDRLK+align) || maxk > MaxMemOffset(J_LDRLK+align))) return YES;
  return NO;
}


static void ResultRename_fixdef(VRegnum r, Inline_RestoreControl *rc, int32 *mask)
/* Renames a fixed (non-renamable) result register in the newresultregs */
{
    int i;
    for (i = 0; i < rc->nresults; i++)
        if (((1 << i) & *mask) && rc->resultregs[i] == r)
        {
            rc->newresultregs[i] = r;
            *mask &= ~(1 << i);
        }
}

static void ResultRename_def(VRegnum *r, Inline_RestoreControl *rc, int32 *mask)
/* Renames a result register to newresultregs */
{
    int i;
    for (i = 0; i < rc->nresults; i++)
        if (((1 << i) & *mask) && rc->resultregs[i] == *r)
        {
            if (rc->newresultregs[i] != GAP)
                *r = rc->newresultregs[i];
            *mask &= ~(1 << i);
        }
}


void Inline_Restore(Inline_SavedFn *fn, Inline_RestoreControl *rc) {
  SaveFnState st;
  SavedFnList *p = FindSavedFn(fn);
  Inline_VRegIndex *vt = p->vregtypetab;
  int32 n = p->maxreg;
  BindList *argb_orig = fn->fndetails.argbindlist;
  Inline_ArgDesc *ad;
  BlockMap *map = NULL;
  BlockHead *dtorlast = NULL;
  BlockHead *bottom = p->fn.bottom_block;
  bool skipblock2 = NO;
  while (--n >= 0) vt[n].r = n <= NMAGICREGS ? n : vregister(vt[n].rs);
  st.copied = NULL;
  st.sharedbindlists = NULL;
  st.vregindex = p->vregtypetab;
  if (fn->fndetails.structresult != NULL)
    fn->fndetails.structresult = FromGlobalBinderCopy(&st, fn->fndetails.structresult);
  fn->fndetails.argbindlist = FromGlobalBindListCopy(&st, argb_orig);
  for (ad = argdesc_(p); ad != NULL; ad = adcdr_(ad))
    ad->argsubst = NULL;
  if (rc != NULL) {
    Inline_ArgSubstList *as = rc->argreplace;
    BindList **blp = &fn->fndetails.argbindlist;
    int ia_cantsubst = IA_Updated + IA_OddAccess + IA_UpdatedOutsideCore;
    for (ad = argdesc_(p); ad != NULL; ad = adcdr_(ad)) {
    /* Prune from the argument bindlist those arguments which we know can */
    /* be substituted for                                                 */
      BindList *bl = *blp;
      if (as == NULL) break;
      if (as->arg == ad->abl.globarg || as->arg == ad->abl.globnarrowarg) {
        Inline_ArgSubstList *thisas = as;
        bool subst = YES;
        as = cdr_(as);
        if (ad->abl.narrowtype != NULL
            && ((thisas->sort != T_Int && thisas->sort != T_Binder)
                || ad->abl.globnarrowarg == NULL))

          subst = NO;

        else if (ad == argdesc_(p)
            && p->sort == IS_Ctor
            && !(ad->flags & (IA_Updated + IA_OddAccess))) {
          if (thisas->notnull) {
            if (thisas->sort == T_Plus
                && (OverlargeOffset(ad, thisas->replacement.ex)
                    || (ad->flags & IA_OddUseForPlusInCore)))
              subst = NO;
            map = p->a.ctor;
            ia_cantsubst = IA_Updated + IA_OddAccess;
          } else {
            if (thisas->sort == T_Int && intval_(thisas->replacement.ex) == 0)
              skipblock2 = YES;
            if (ad->flags & IA_UpdatedOutsideCore)
              subst = NO;
          }
        } else if (p->sort == IS_Dtor && ad == adcdr_(argdesc_(p))
                   && !(ad->flags & ia_cantsubst)
                   && thisas->sort == T_Int
                   && intval_(thisas->replacement.ex) == 0)
          dtorlast = p->a.dtor;

        else if ((thisas->sort == T_Plus
                  && (OverlargeOffset(ad, thisas->replacement.ex)
                      || (ad->flags & IA_OddUseForPlusInCore)))
                 || ad->flags & ia_cantsubst)
          subst = NO;

        if (subst) {
          *blp = bl->bindlistcdr;
          ad->argsubst = thisas;
          if (debugging(DEBUG_CG)) {
            cc_msg("Substitution for %s$b: ",
              thisas->sort==T_AdconV ? "*" : "",
              thisas->arg);
            pr_expr_nl(thisas->replacement.ex);
          }
          continue;
        }
        thisas->refsleft = YES;
      }
      blp = &bl->bindlistcdr;
    }
  }
  if (rc != NULL) {
    BindList *bl = BindListCopy(fn->fndetails.argbindlist);
    BindList *argbl = bl;
    n = length((List *)bl);
    rc->env = st.nullenv = (BindList *)nconc((List *)bl, (List *)rc->env);
    for (; --n >= 0; argbl = argbl->bindlistcdr) {
        Binder *b = argbl->bindlistcar;
        bindbl_(b) = argbl;
        bindstg_(b) |= b_bindaddrlist;
    }
  } else
    st.nullenv = NULL;
  fn->var_binders = FromGlobalBindListCopy(&st, fn->var_binders);
  fn->reg_binders = FromGlobalBindListCopy(&st, fn->reg_binders);
  { LabelNumber **labelindex = NewSynN(LabelNumber *, p->maxlabel);
    BlockHead *b = fn->top_block;
    BlockHead *globtop = b;
    BlockHead *blast = NULL, *bnew = NULL;
    Inline_ArgSubstList *sl;
    for (n = 1; n < p->maxlabel; n++) labelindex[n] = nextlabel();
    fn->top_block = fn->bottom_block = NULL;
    for (; b != NULL; b = blkdown_(b), blast = bnew)
      if ( skipblock2 ? b != blkdown_(globtop) :
          map != NULL ? MapBitSet(map, (IPtr)blklab_(b)) :
                        YES) {
      int32 restoload = 0;
      bool resvoided = YES;
      bnew = NewBind(BlockHead);
      *bnew = *b;
      blkup_(bnew) = blast;
      if (blast == NULL)
        fn->top_block = bnew;
      else
        blkdown_(blast) = bnew;
      if (blkflags_(b) & BLKSWITCH) {
        int32 n = blktabsize_(b);
        LabelNumber **sw_old = blktable_(b);
        LabelNumber **sw_new = NewBindN(LabelNumber *, n);
        while (--n >= 0) sw_new[n] = FromGlobalLabel(labelindex, rc, sw_old[n]);
        blktable_(bnew) = sw_new;
      } else {
        BlockHead *b1 = b;
        if (b == dtorlast) {
          b1 = bottom;
          blkflags_(bnew) &= ~BLK2EXIT;
        } else {
          if (skipblock2 && blast == NULL)
            b1 = blkdown_(b);
          if (blkflags_(b) & BLK2EXIT)
            blknext1_(bnew) = FromGlobalLabel(labelindex, rc, blknext1_(b));
        }
        if (is_exit_label(blknext_(b1)) && rc != NULL) {
          restoload = (1L << rc->nresults) - 1;
          if (rc->nresults > 0 && rc->newresultregs[0] != GAP) resvoided = NO;
        }
        blknext_(bnew) = FromGlobalLabel(labelindex, rc, blknext_(b1));
      }
      { LabelNumber *lab = FromGlobalLabel(labelindex, rc, blklab_(b));
        blklab_(bnew) = lab;
        lab->block = bnew;
      }
      blkstack_(bnew) = FromGlobalSharedBindListCopy(&st, blkstack_(b));
      { int32 n_in = blklength_(b), n_out = n_in, n;
        Icode *code_old = blkcode_(b);
        Icode *code_new;
        bool copied = NO;
        VRegnum discardload = GAP;
        int32 noopcount = 0;
        Inline_ArgDesc *ad;
        for (n = n_in; --n >= 0; ) {
          J_OPCODE op = code_old[n].op & J_TABLE_BITS;
          if (op == J_ADCON) {
            Binder *b = code_old[n].r3.b;
            if ((bindstg_(b) & bitofstg_(s_extern))
                && !(bindstg_(b) & (b_undef|b_fnconst))
                && !(binduses_(b) & (u_bss|u_constdata))
                && b != datasegment
                && bindaddr_(b) != 0) {
              n_out++;
            }
          }
        }
        if (b == dtorlast) {
          n_out = n_out - 2 + blklength_(bottom);
          n_in = blklength_(bottom);
          code_old = blkcode_(bottom);
        }
        code_new = n_out == 0 ? (Icode *)DUFF_ADDR :
                                NewBindN(Icode, n_out);
        blkcode_(bnew) = code_new;
        blklength_(bnew) = n_out;
        for (n = n_out; --n, --n_in >= 0; ) {
          J_OPCODE op = code_old[n_in].op;
          uint32 flags = code_old[n_in].flags;
          VRegInt r1 = code_old[n_in].r1,
                  r2 = code_old[n_in].r2,
                  r3 = code_old[n_in].r3,
                  r4 = code_old[n_in].r4;
          J_OPCODE opx = op & J_TABLE_BITS;
          if (uses_r1(op)) r1.r = vt[r1.r].r;
          if (uses_r2(op)) r2.r = vt[r2.r].r;
          if (uses_r3(op)) r3.r = vt[r3.r].r;
          if (uses_r4(op)) r4.r = vt[r4.r].r;
          if (opx == J_SETSPENV) {
            if (r3.bl == r2.bl && !copied && rc != NULL) {
            /* m = r2 only when both are empty, just before function exits
               (deliberately not optimised out to give somewhere for
                CSE-introduced binders to be popped).
             */
              n_out--;
              goto maybeswitchblock;
            }
            r3.bl = FromGlobalSharedBindListCopy(&st, r3.bl);
            r2.bl = FromGlobalSharedBindListCopy(&st, r2.bl);
          } else if (opx == J_SETSPGOTO) {
            r2.bl = FromGlobalSharedBindListCopy(&st, r2.bl);
            r3.l = FromGlobalLabel(labelindex, rc, r3.l);
          } else if (opx == J_STRV
                     && (ad = ArgDesc_Find(r3.b, argdesc_(p))) != NULL
                     && (sl = ad->argsubst) != NULL
                     && sl->sort == T_Int) {
            op = J_MOVK;
            r3.i = intval_(sl->replacement.ex);
          } else if (opx == J_STRV
                     && (ad = ArgDesc_Find(r3.b, argdesc_(p))) != NULL
                     && (sl = ad->argsubst) != NULL
                     && sl->sort == T_Binder
                     && ad->abl.narrowtype != NULL) {
              r3.b = sl->replacement.b;
          } else if (opx == J_LDRV
                     && (ad = ArgDesc_Find(r3.b, argdesc_(p))) != NULL
                     && (sl = ad->argsubst) != NULL) {
            switch (sl->sort) {
            default:        syserr("Inline_Restore"); break;
            case T_Binder:  r3.b = sl->replacement.b; break;
            case T_Adcon:   r3.b = sl->replacement.b; op = J_ADCON; break;
            case T_Int:     op = J_MOVK, r3.i = intval_(sl->replacement.ex); break;
            case T_Plus:
              { Binder *b = exb_(arg1_(sl->replacement.ex));
                int32 k = intval_(arg2_(sl->replacement.ex));
                Icode *next1 = &code_new[n+1];
                J_OPCODE nextop = next1->op & J_TABLE_BITS;
                if (n+1 < n_out) {
                  if (j_is_ldr_or_str(nextop) && reads_r2(nextop)
                      && !reads_r3(nextop)
                      && next1->r2.r == r1.r) {
#ifdef TARGET_LACKS_HALFWORD_STORE
                    int32 k1;
                    if (nextop == J_STRBK
                        && n+3 < n_out && IsSTRWExpansion(next1, &k1)) {
                      code_new[n+3].r3.i += k;
                    }
#endif
                    r3.b = b;
                    next1->r3.i += k;
                    break;
                  } else if (nextop == J_MOVR && next1->r3.r == r1.r) {
                    r3.b = b;
                    next1->op = J_ADDK;
                    next1->r2.r = r1.r;
                    next1->r3.i = k;
                    break;
                  }
                }
                if (loads_r1(op) && r1.r == discardload) {
                  op = J_NOOP;
                  noopcount++;
                  discardload = GAP;
                } else
                  r3.b = FromGlobalBinderCopy(&st, r3.b);
                break;
              }
            case T_AdconV:
              /* Substituting an ADCONV: try to combine it with subsequent */
              /* loads and stores (turning them into VK variants) so that  */
              /* the variable isn't falsely seen to be address-taken.      */
              { int32 i = n;
                bool used = NO;
                r3.b = sl->replacement.b;
                while (++i < n_out) {
                  Icode *next = &code_new[i];
                  J_OPCODE nextop = next->op & J_TABLE_BITS;
                  if (j_is_ldr_or_str(nextop) && reads_r2(nextop) && !reads_r3(nextop)
                      && next->r2.r == r1.r) {
                    if (sl->size == MEM_NONE || sl->size != ad->accesssize) {
#ifdef TARGET_LACKS_HALFWORD_STORE
                      int32 k;
                      if (nextop == J_STRBK
                          && i+2 < n_out && IsSTRWExpansion(next, &k)) {
                        Icode *next3 = &code_new[i+2];
                        next3->op = J_addvk(next3->op);
                        next3->r2.i = next3->r3.i;
                        next3->r3.b = r3.b;
                      }
#endif
                      next->op = J_addvk(next->op);
                      next->r2.i = next->r3.i;
                      next->r3.b = r3.b;
                    } else {
#ifdef TARGET_LACKS_HALFWORD_STORE
                      int32 k;
                      if (nextop == J_STRBK
                          && i+2 < n_out && IsSTRWExpansion(next, &k) && k == 0) {
                        (next+1)->op = J_NOOP;
                        (next+2)->op = J_NOOP;
                        noopcount += 2;
                        next->op = J_STRV+J_ALIGN4;
                        next->r2.r = GAP;
                        next->r3.b = r3.b;
                      } else
#endif
                      if (nextop == J_LDRBK || nextop == J_LDRWK) {
                        next->op = J_LDRV+J_ALIGN4;
                        next->r2.r = GAP;
                        next->r3.b = r3.b;
                      } else if (nextop == J_STRWK || nextop == J_STRBK) {
                        next->op = J_STRV+J_ALIGN4;
                        next->r2.r = GAP;
                        next->r3.b = r3.b;
                      } else {
                        next->op = J_addvk(next->op);
                        next->r2.i = next->r3.i;
                        next->r3.b = r3.b;
                      }
                    }
                  } else if (reads_r1(nextop) && next->r1.r == r1.r ||
                             reads_r2(nextop) && next->r2.r == r1.r ||
                             reads_r3(nextop) && next->r3.r == r1.r ||
                             reads_r4(nextop) && next->r4.r == r1.r)
                    used = YES;
                }
                if (used)
                  op = J_ADCONV;
                else {
                  op = J_NOOP;
                  noopcount++;
                }
              }
              break;
            }
          } else if (opx == J_ADCON) {
            r3.b = FromGlobalBinderCopy(&st, r3.b);
            if ((bindstg_(r3.b) & bitofstg_(s_extern))
                && !(bindstg_(r3.b) & (b_undef|b_fnconst))
                && !(binduses_(r3.b) & (u_bss|u_constdata))
                && r3.b != datasegment) {
              if (bindaddr_(r3.b) != 0) {
                INIT_IC(code_new[n], J_ADDK);
                code_new[n].r1 = r1;
                code_new[n].r2 = r1;
                code_new[n].r3.i = bindaddr_(r3.b);
                code_new[n].r4.r = GAP;
                n--;
              }
              r3.b = datasegment;
            }
          } else if (uses_stack(op) || opx == J_CALLK
                     || opx == J_INIT || opx == J_INITF || opx == J_INITD)
            r3.b = FromGlobalBinderCopy(&st, r3.b);

          if (loads_r1(op)) {
            if (restoload != 0) {
              int i;
              if (isproccall_(op)) {
                restoload = 0;
                for (i = 0; i < rc->nresults; i++)
                  rc->newresultregs[i] = rc->resultregs[i];
              } else
                for (i = 0; i < rc->nresults; i++)
                  if (r1.r == rc->resultregs[i]) {
                    restoload &= ~regbit(i);
                    if (!resvoided) {
                      r1.r = rc->newresultregs[i];
                      blkflags_(b) |= BLKREXPORTED;
                    } else {
                      if (op == J_MOVR) discardload = r3.r;
                      op = J_NOOP;
                      noopcount++;
                    }
                    break;
                  }
            } else if (r1.r == discardload) {
              if (!isproccall_(op)) {
                op = J_NOOP;
                noopcount++;
              }
              discardload = GAP;
            }
          } else if (uses_r1(op) && r1.r == discardload)
            discardload = GAP;

          copied = YES;
          INIT_IC(code_new[n], op);
          code_new[n].flags = flags;
          code_new[n].r1 = r1;
          code_new[n].r2 = r2;
          code_new[n].r3 = r3;
          code_new[n].r4 = r4;


          /* WD: quick HACK for the above code - broken for inline assembler */
          /* does not discard moves (discardload), or voids results (resvoided)
             there doesn't seem to be any point in doing that anyway...
           */
          if (rc != NULL)
          {
            RealRegUse use;
            int i;

            if (!isproccall_(op))
            {
                if (updates_r1(op)) ResultRename_fixdef(code_new[n].r1.r, rc, &restoload);
                else if (loads_r1(op)) ResultRename_def(&code_new[n].r1.r, rc, &restoload);
                if (updates_r2(op)) ResultRename_fixdef(code_new[n].r2.r, rc, &restoload);
                else if (loads_r2(op)) ResultRename_def(&code_new[n].r2.r, rc, &restoload);
            }
            RealRegisterUse(&code_new[n], &use);
            for (i = 0; i < NMAGICREGS; i++)
            {
                if (member_RealRegSet(&use.def, i)) ResultRename_fixdef(i, rc, &restoload);
                /* TODO: need to report a syserr if one of the result registers will be corrupted! */
            }
            blkflags_(b) |= BLKREXPORTED;
          }
          /* TODO: a real implementation would need 2 passes to renumber the registers, because
           *       it needs to rename USES too. BROKEN for inline assembler anyway!
           */

maybeswitchblock :
          if (n_in == 0 && b == dtorlast) {
            n_in = blklength_(dtorlast) - 2;
            code_old = blkcode_(dtorlast);
            b = bottom;
          }
        }
        if (noopcount > 0) {
          int32 n = 0, n_in = 0;
          for (; n_in < n_out; n_in++)
            if (code_new[n_in].op != J_NOOP) {
              if (n != n_in)
                code_new[n] = code_new[n_in];
              n++;
            }
          n_out = n;
        }
        blklength_(bnew) = n_out;
      }
    }
    blkdown_(blast) = NULL;
    fn->bottom_block = blast;
  }
  { Inline_ArgDesc *ad = (Inline_ArgDesc *)(fn->args);
    for (; ad != NULL; ad = adcdr_(ad))
      if (ad->abl.globnarrowarg != NULL)
        ad->abl.instantiatednarrowarg = FromGlobalBinderCopy(&st, ad->abl.globnarrowarg);
  }
  { SynBindList *bl = st.copied;
    for (; bl != NULL; bl = bl->bindlistcdr)
      h0_(bl->bindlistcar) = s_binder;
  }
  { VRegnum n = p->maxreg;
    Inline_VRegIndex *vt = p->vregtypetab;
    while (!isany_realreg_(--n)) vt[n].rs = vregsort(vt[n].r);
  }
}

void Inline_Init(void) {
  saved_fns = NULL;
}

static void Inline_CompileOutOfLineCopy(Inline_SavedFn *fn) {
  char v[128];
  cg_sub_reinit();
  Inline_Restore(fn, NULL);
  currentfunction = fn->fndetails;
  top_block = fn->top_block; bottom_block = fn->bottom_block;
  if (debugging(DEBUG_CG)) {
    sprintf(v, "Out-of-line %s", symname_(fn->fndetails.symstr));
    flowgraf_print(v, NO);
  }
  cg_topdecl2(fn->var_binders, fn->reg_binders);
}

void Inline_Tidy(void) {
  SavedFnList *p;
  for (;;) {
    bool emitted = NO;
    for (p = saved_fns; p != NULL; p = cdr_(p))
      if ((p->outoflineflags & ol_used) && !(p->outoflineflags & ol_emitted)) {
        { char v[128+5];
#ifdef TARGET_IS_THUMB
          /* This must be redone in a more sensible way later */
          strcpy(v, "x$t$");
#else
          strcpy(v, "x$i$");
#endif
          strcpy(v+4, symname_(p->fn.fndetails.symstr));
          obj_setcommoncode();
          codebuf_reinit1(v);
        }
        emitted = YES;
        p->outoflineflags |= ol_emitted;
        Inline_CompileOutOfLineCopy(&p->fn);
      }
    if (!emitted) break;
  }
}

void Inline_LoadState(FILE *f) {
  uint32 w[5];
  int32 nfn;
  fread(w, sizeof(uint32), 1, f);
  nfn = w[0];
  while (--nfn >= 0) {
    SavedFnList *sf = NewGlob(SavedFnList, SU_Inline);
    fread(sf, sizeof(SavedFnList), 1, f);
    cdr_(sf) = saved_fns; saved_fns = sf;
    sf->fn.fndetails.symstr = Dump_LoadedSym((IPtr)sf->fn.fndetails.symstr);
    { Binder *b = bind_global_(sf->fn.fndetails.symstr);
      if (b != NULL) bindinline_(b) = sf;
    }
    sf->fn.fndetails.structresult = Dump_LoadedBinder((IPtr)sf->fn.fndetails.structresult);
    sf->fn.fndetails.argbindlist = Dump_LoadBindList(f);
    sf->fn.var_binders = Dump_LoadBindList(f);
    sf->fn.reg_binders = Dump_LoadBindList(f);
    { Inline_ArgDesc **adp = &argdesc_(sf);
      int32 n;
      fread(w, sizeof(uint32), 1, f);
      for (n = w[0]; --n >= 0; ) {
        Inline_ArgDesc *p = NewGlob(Inline_ArgDesc, SU_Inline);
        *adp = p; adp = &adcdr_(p);
        fread(w, sizeof(uint32), 3, f);
        p->flags = w[0];
        p->abl.globarg = Dump_LoadedBinder(w[1]);
        p->abl.globnarrowarg = Dump_LoadedBinder(w[2]);
        p->abl.narrowtype = Dump_LoadType(f);
      }
      *adp = NULL;
    }
    sf->vregtypetab = NewGlobN(Inline_VRegIndex, SU_Inline, sf->maxreg);
    fread(sf->vregtypetab, sizeof(Inline_VRegIndex), (size_t)sf->maxreg, f);
    if (sf->fn.firstblockignoresize > 0) {
      sf->fn.firstblockignore = NewGlobN(uint8, SU_Inline, sf->fn.firstblockignoresize);
      fread(sf->fn.firstblockignore, sizeof(uint8), MapSize(sf->fn.firstblockignoresize), f);
    } else
      sf->fn.firstblockignore = NULL;

    if (sf->sort == IS_Ctor) {
      sf->a.ctor = NewGlobN(uint8, SU_Inline, sf->maxlabel);
      fread(sf->a.ctor, sizeof(uint8), MapSize(sf->maxlabel), f);
    } else if (sf->sort == IS_Dtor)
      fread(&sf->a.dtor, sizeof(LabelNumber *), 1, f);

    fread(w, sizeof(uint32), 1, f);
    { int32 nb = w[0];
      BlockHead *b, *prev = NULL;
      for (; --nb >= 0; prev = b) {
        Icode *p;
        int32 n;
        int32 nstring;
        StringSegList **stringindex;
        b = NewGlob(BlockHead, SU_Inline);
        blkup_(b) = prev;
        if (prev == NULL)
          sf->fn.top_block = b;
        else
          blkdown_(prev) = b;
        fread(w, sizeof(uint32), 5, f);
        blklength_(b) = w[0];
        blkflags_(b) = w[1];
        blknext1_(b) = (LabelNumber *)(IPtr)w[2];
        blklab_(b) = (LabelNumber *)(IPtr)w[3];
        blkstack_(b) = Dump_LoadedSharedBindList(w[4]);
        blkusedfrom_(b) = NULL;
        blkuse_(b) = 0;
        blknest_(b) = 0;
        if (blkflags_(b) & BLKSWITCH) {
          blktable_(b) = NewGlobN(LabelNumber *, SU_Inline, blktabsize_(b));
          fread(blktable_(b), sizeof(LabelNumber *), (size_t)blktabsize_(b), f);
        } else
          fread(&blknext_(b), sizeof(LabelNumber *), 1, f);

        if (sf->sort == IS_Dtor && (LabelNumber *)sf->a.dtor == blklab_(b))
          sf->a.dtor = b;

        fread(&nstring, sizeof(uint32), 1, f);
        stringindex = NewSynN(StringSegList *, nstring);
        for (n = 0; n < nstring; n++)
          stringindex[n] = Dump_LoadStrSeg(f);

        if (blklength_(b) == 0)
          blkcode_(b) = (Icode *)DUFF_ADDR;
        else {
          blkcode_(b) = NewGlobN(Icode, SU_Inline, blklength_(b));
          fread(blkcode_(b), sizeof(Icode), (size_t)blklength_(b), f);
          for (n = blklength_(b), p = blkcode_(b); --n >= 0; p++) {
            J_OPCODE op = p->op & J_TABLE_BITS;
            if (op == J_SETSPENV) {
              p->r3.bl = Dump_LoadedSharedBindList(p->r3.i);
              p->r2.bl = Dump_LoadedSharedBindList(p->r2.i);
            } else if (op == J_SETSPGOTO) {
              p->r2.bl = Dump_LoadedSharedBindList(p->r2.i);
            } else if (uses_stack(op) || op == J_CALLK || op==J_ADCON
                       || op == J_INIT || op == J_INITF || op == J_INITD) {
              p->r3.b = Dump_LoadedBinder(p->r3.i);
            } else if (op == J_STRING) {
              p->r3.s = stringindex[p->r3.i];
            }
          }
        }
      }
      blkdown_(prev) = NULL;
      sf->fn.bottom_block = prev;
    }
  }
  saved_fns = (SavedFnList *)dreverse((List *)saved_fns);
}

#ifndef NO_DUMP_STATE
void Inline_DumpState(FILE *f) {
  SavedFnList *p = saved_fns;
  uint32 w[5];
  w[0] = length((List *)p);
  fwrite(w, sizeof(uint32), 1, f);
  for (; p != NULL; p = cdr_(p)) {
    SavedFnList sf = *p;
    BlockHead *b;
    sf.fn.fndetails.symstr = (Symstr *)(IPtr)Dump_SymRef(sf.fn.fndetails.symstr);
    sf.fn.fndetails.structresult = (Binder *)(IPtr)Dump_BinderRef(sf.fn.fndetails.structresult);
    fwrite(&sf, sizeof(SavedFnList), 1, f);
    Dump_BindList(sf.fn.fndetails.argbindlist, f);
    Dump_BindList(sf.fn.var_binders, f);
    Dump_BindList(sf.fn.reg_binders, f);
    { Inline_ArgDesc *ad = argdesc_(&sf);
      w[0] = length((List *)&ad->abl);
      fwrite(w, sizeof(uint32), 1, f);
      for (; ad != NULL; ad = adcdr_(ad)) {
        w[0] = ad->flags;
        w[1] = Dump_BinderRef(ad->abl.globarg);
        w[2] = Dump_BinderRef(ad->abl.globnarrowarg);
        fwrite(w, sizeof(uint32), 3, f);
        Dump_Type(ad->abl.narrowtype, f);
      }
    }
    fwrite(sf.vregtypetab, sizeof(Inline_VRegIndex), (size_t)sf.maxreg, f);
    if (sf.fn.firstblockignoresize > 0) {
      fwrite(sf.fn.firstblockignore, sizeof(uint8), MapSize(sf.fn.firstblockignoresize), f);
    }
    if (sf.sort == IS_Ctor)
      fwrite(sf.a.ctor, sizeof(uint8), MapSize(sf.maxlabel), f);
    else if (sf.sort == IS_Dtor)
      fwrite(&blklab_(sf.a.dtor), sizeof(LabelNumber *), 1, f);

    w[0] = 0;
    for (b = sf.fn.top_block; b != NULL; b = blkdown_(b)) w[0]++;
    fwrite(w, sizeof(uint32), 1, f);

    for (b = sf.fn.top_block; b != NULL; b = blkdown_(b)) {
      Icode *p;
      int32 n;
      uint32 nstring;
      w[0] = blklength_(b);
      w[1] = blkflags_(b);
      w[2] = (uint32)(IPtr)blknext1_(b);
      w[3] = (uint32)(IPtr)blklab_(b);
      w[4] = Dump_NoteSharedBindList(blkstack_(b));
      fwrite(w, sizeof(uint32), 5, f);
      if (blkflags_(b) & BLKSWITCH)
        fwrite(blktable_(b), sizeof(LabelNumber *), (size_t)blktabsize_(b), f);
      else
        fwrite(&blknext_(b), sizeof(LabelNumber *), 1, f);

      for (nstring = 0, n = blklength_(b), p = blkcode_(b); --n >= 0; p++)
        if ((p->op & J_TABLE_BITS) == J_STRING)
          nstring++;
      fwrite(&nstring, sizeof(uint32), 1, f);
      for (nstring = 0, n = blklength_(b), p = blkcode_(b); --n >= 0; p++)
        if ((p->op & J_TABLE_BITS) == J_STRING) {
          Dump_StrSeg(p->r3.s, f);
          p->r3.i = nstring++;
        }
      for (n = blklength_(b), p = blkcode_(b); --n >= 0; p++) {
        J_OPCODE op = p->op & J_TABLE_BITS;
        Icode c = *p;
        if (op == J_SETSPENV) {
          c.r3.i = Dump_NoteSharedBindList(p->r3.bl);
          c.r2.i = Dump_NoteSharedBindList(p->r2.bl);
        } else if (op == J_SETSPGOTO) {
          c.r2.i = Dump_NoteSharedBindList(p->r2.bl);
        } else if (uses_stack(op) || op == J_CALLK || op==J_ADCON
                   || op == J_INIT || op == J_INITF || op == J_INITD) {
          c.r3.i = Dump_BinderRef(p->r3.b);
        }
        fwrite(&c, sizeof(Icode), 1, f);
      }
    }
  }
}
#endif /* NO_DUMP_STATE */
