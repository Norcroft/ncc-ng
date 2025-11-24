/*
 * C compiler file arm/gen.c.
 * Copyright (C) Codemist Ltd, 1988.
 * Copyright (C) Acorn Computers Ltd., 1988
 * Copyright (C) Advanced Risc Machines Ltd., 1991
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$  Codemist 48
 * Checkin $Date$
 * Revising $Author$
 */

/* @@@ AM memo: the uses of bind_global_() are spiritually wrong.   */
/* @@@ LDS 30-Oct-92: wrong save when applied to top-level things.  */

/* This file contains mainly arm dependent machine coding routines. */
/* Apr 89: xr_refext removed by AM as unused elsewhere.             */
/* AM 3-Apr-87: add debugger.  Beware that machine *independent* code should
                *not* go in this file.  */
/* AM 10-Mar-87: add peepholer.  Beware local_address() (q.v.)      */

/* exports:
   void show_instruction(Icode *ic);
   RealRegister local_base(Binder *b);
   int32 local_address(Binder *b);
   bool immed_cmp(int32);
   bool fpliteral(FloatCon *val, J_OPCODE op);
      also (unfortunately for peephole):
   void setlabel(LabelNumber *);
   void branch_round_literals(LabelNumber *);
*/

#ifdef __STDC__
#  include <string.h>
#else
#  include <strings.h>
#endif

#define DEFINE_A_JOPTABLE 1

#include "globals.h"
#include "mcdep.h"
#include "mcdpriv.h"
#include "aeops.h"
#include "xrefs.h"
#include "armops.h"
#include "jopcode.h"
#include "store.h"
#include "codebuf.h"
#include "regalloc.h"
#include "builtin.h"   /* for te_xxx */
#include "bind.h"      /* for sym_insert_id */
#include "flowgraf.h"
#include "errors.h"
#include "inlnasm.h"
#include "arminst.h"
#include "ampops.h"
#include "ampdis.h"

unsigned integer_load_max;
unsigned ldm_regs_max;

static int32 nargwords, nregargwords, argwordsbelowfp, realargwordsbelowfp, fp_minus_sp;
static int32 intsavewordsbelowfp, savewordsabovefp, argstopopabovefp;
static uint32 condition_mask;

static int32 mustlitby;
static int32 literal_pool_start;
static bool in_code;
static int literal_pool_number;

static LabelNumber *returnlab;

static Symstr *lib_reloc_sym, *mod_reloc_sym;
#ifndef PROFILE_COUNTS_INLINE
static Symstr *fn_entry_sym, *fn_exit_sym;
#endif

static int32 spareregs;

static void cmp_integer(RealRegister r,int32 n,RealRegister workreg,int32 mask,int32 flags);
static void cmn_integer(RealRegister r,int32 n,RealRegister workreg,int32 mask,int32 flags);
static void load_integer(RealRegister r,int32 n,int32 flags);
static void add_integer(RealRegister r1,RealRegister r2,int32 n,int32 flags);
static void sub_integer(RealRegister r1,RealRegister r2,int32 n,int32 flags);
static void adc_integer(RealRegister r1,RealRegister r2,int32 n,int32 flags);
static void sbc_integer(RealRegister r1,RealRegister r2,int32 n,int32 flags);
static void rsb_integer(RealRegister r1,RealRegister r2,int32 n,int32 flags);
static void rsc_integer(RealRegister r1,RealRegister r2,int32 n,int32 flags);
static void and_integer(RealRegister r1,RealRegister r2,int32 n,int32 peep, bool dead_r1);
static void orr_integer(RealRegister r1,RealRegister r2,int32 n,int32 flags);
static void eor_integer(RealRegister r1,RealRegister r2,int32 n,int32 flags);
static void tst_integer(RealRegister rt,RealRegister r2,int32 n,int32 flags);
static void teq_integer(RealRegister rt,RealRegister r2,int32 n,int32 flags);
static void multiply_integer(RealRegister r1,RealRegister r2,int32 n,int32 scc);
static void mla_integer(RealRegister r1,RealRegister r2,int32 n,RealRegister acc,int32 scc);
static void conditional_branch_to(int32 condition,LabelNumber *destination,bool bxxcase,int32 spadjust);
static void routine_entry(int32 m);
static void routine_saveregs(int32 m);
static void routine_exit(int32 condition,bool to_pc,int32 spadjust);
static void killipvalue(RealRegister r);
static int32 LSBits(int32 mask, int n);


typedef enum {
  UseFP,
  UseSP_Adjust,
  UseSP_NoAdjust
} FP_RestoreBase;

typedef struct {
  void (*show)(PendingOp const *p);
  void (*calleesave)(int32 mask);
  int32 (*restoresize)(int32 mask);
  void (*calleerestore)(int32 mask, int32 condition, FP_RestoreBase base, int32 offset);
  void (*saveargs)(int32);
} FP_Gen;

static FP_Gen const *fp_gen;

static RealRegister local_base_a(int32 p);
static int32 local_addr_a(int32 p);

#define ROR(x, n) (((x)<<(32-(n))) | ((((uint32)x)>>(n)) & ((1L<<(32-(n)))-1L)))

/* The set of registers whose values are potentially destroyed by normal */
/* calls (to finctions whose register usage isn't known)                 */
#define VolatileRegisters \
  (regbit(R_A1) | regbit(R_A2) | regbit(R_A3) | regbit(R_A4) \
   | regbit(R_IP) | M_LR)

#define AllIntRegs 0xffff
#define NoRegister ((RealRegister)-1)


struct { bool known; int32 value; } register_values[16];

static struct {
    bool valid;
    RealRegister base;
    int32 offset;
} ipvalue;


static void KillKnownRegisterValues(uint32 mask) {
  RealRegister r;
  for (r = 0; r < 16; r++)
    if (mask & regbit(r))
      register_values[r].known = NO;
}

static void KillKnownRegisterValue(RealRegister r) {
  if (r < 16) register_values[r].known = NO;
}

static void SetKnownRegisterValue(RealRegister r, int32 n) {
  if (r < 16) {
    register_values[r].value = n;
    register_values[r].known = YES;
  }
}

#define ValueIsKnown(r) (r < 16 && register_values[r].known)
#define KnownValue(r) (register_values[r].value)

static bool ValueBuildable(uint32 value, uint32 target, int flags, ValueDesc *vp) {
  int n;
  if (value == target) { vp->op3.shift = 0; return YES; }
  if (flags & V_ASR)
    for (n = 1; n < 32; n++)
      if (signed_rightshift_(value, n) == target) { vp->op3.shift = K_ASR(n); return YES; }
  if (flags & V_LSR)
    for (n = 1; n < 32; n++)
      if ((value >> n) == target) { vp->op3.shift = K_LSR(n); return YES; }
  if (flags & V_LSL)
    for (n = 1; n < 32; n++)
      if (value << n == target) { vp->op3.shift = K_LSL(n); return YES; }
  if (flags & V_ROR)
    for (n = 1; n < 32; n++)
      if (ROR(value, n) == target) { vp->op3.shift = K_ROR(n); return YES; }
  return NO;
}

static bool ValueBuildableOR(uint32 value, uint32 target, int flags, ValueDesc *vp) {
  int n;
  if (value == target) { vp->op3.shift = 0; return YES; }
  if (flags & V_ASR)
    for (n = 1; n < 32; n++)
      if ((value | signed_rightshift_(value, n)) == target) { vp->op3.shift = K_ASR(n); return YES; }
  if (flags & V_LSR)
    for (n = 1; n < 32; n++)
      if ((value | (value >> n)) == target) { vp->op3.shift = K_LSR(n); return YES; }
  if (flags & V_LSL)
    for (n = 1; n < 32; n++)
      if ((value | (value << n)) == target) { vp->op3.shift = K_LSL(n); return YES; }
  if (flags & V_ROR)
    for (n = 1; n < 32; n++)
      if ((value | ROR(value, n)) == target) { vp->op3.shift = K_ROR(n); return YES; }
  return NO;
}

static bool ValueBuildable_AnyOp(uint32 target, uint32 n, ValueDesc *vp) {
  RealRegister r;
  for (r = 0; r < 16; r++)
    if (register_values[r].known) {
      uint32 value = register_values[r].value;
      if ((value & n) == target)  { vp->op3.rpair.op = OP_ANDR; vp->r = r; return YES; }
      if ((value & ~n) == target) { vp->op3.rpair.op = OP_BICR; vp->r = r; return YES; }
      if ((value | n) == target)  { vp->op3.rpair.op = OP_ORRR; vp->r = r; return YES; }
      if ((value ^ n) == target)  { vp->op3.rpair.op = OP_EORR; vp->r = r; return YES; }
      if ((value - n) == target)  { vp->op3.rpair.op = OP_SUBR; vp->r = r; return YES; }
      if ((n - value) == target)  { vp->op3.rpair.op = OP_RSBR; vp->r = r; return YES; }
      if ((value + n) == target)  { vp->op3.rpair.op = OP_ADDR; vp->r = r; return YES; }
    }
  return NO;
}

static int RegisterContainingValue(uint32 n, int flags, ValueDesc *vp) {
  RealRegister r;
  for (r = 0; r < 16; r++)
    if (register_values[r].known) {
      uint32 value = register_values[r].value;
      if (ValueBuildable(value, n, flags, vp)) {
        vp->r = r;
        return V_Exact;
      }
      if ((flags & V_Negated) && ValueBuildable(value, 0-n, flags, vp)) {
        vp->r = r;
        return V_Negated;
      }
      if ((flags & V_Inverted) && ValueBuildable(value, ~n, flags, vp)) {
        vp->r = r;
        return V_Inverted;
      }
      if ((flags & V_Orred) && ValueBuildableOR(value, n, flags, vp)) {
        vp->r = r;
        return V_Orred;
      }
      if (flags & V_KAdded) {
        int32 ndiff = Arm_EightBits(n - value);
        if (ndiff > 0) {
          vp->r = r;
          vp->op3.add.k = ndiff;
          vp->op3.add.op = OP_ADDN;
          return V_KAdded;
        }
        ndiff = Arm_EightBits(value - n);
        if (ndiff > 0) {
          vp->r = r;
          vp->op3.add.k = ndiff;
          vp->op3.add.op = OP_SUBN;
          return V_KAdded;
        }
      }
      if (flags & V_RegPair) {
        int sh;
        if (ValueBuildable_AnyOp(n, value, vp)) {
          vp->op3.rpair.rm = r;
          return V_RegPair;
        }
        for (sh = 1; sh < 32; sh++)
          if (ValueBuildable_AnyOp(n, signed_rightshift_(value, sh), vp)) {
            vp->op3.rpair.rm = r | K_ASR(sh);
            return V_RegPair;
          }
        for (sh = 1; sh < 32; sh++)
          if (ValueBuildable_AnyOp(n, value >> sh, vp)) {
            vp->op3.rpair.rm = r | K_LSR(sh);
            return V_RegPair;
          }
        for (sh = 1; sh < 32; sh++)
          if (ValueBuildable_AnyOp(n, value << sh, vp)) {
            vp->op3.rpair.rm = r | K_LSL(sh);
            return V_RegPair;
          }
        for (sh = 1; sh < 32; sh++)
          if (ValueBuildable_AnyOp(n, ROR(value, sh), vp)) {
            vp->op3.rpair.rm = r | K_ROR(sh);
            return V_RegPair;
          }
      }
    }
  return 0;
}


static void DestroyIP(void) {
  ipvalue.valid = NO;
  spareregs |= regbit(R_IP);
  regmask |= regbit(R_IP);
  KillKnownRegisterValue(R_IP);
}


/* Claim a temporary register. GetTempReg may only be called once
 * for each JOPCODE. It returns -1 if there are no free registers.
 * As the spare register will be written to, any knowledge of the
 * temp reg is killed.
 */

static int GetTempReg(void)
{   int reg = spareregs & -spareregs;
    if (reg == 0)
        return -1;
    reg = logbase2(reg);
    regmask |= regbit(reg);
    killipvalue(reg);
    KillKnownRegisterValue(reg);
    return reg;
}

#define FreeTempRegs() (spareregs != 0)




#ifdef TARGET_HAS_FP_OFFSET_TABLES

static struct {
    ProcFPDesc desc;
    FPList **tail;
    int32 offset;
} fpd;

static void fpdesc_init(void) {
    fpd.desc.fplist = NULL; fpd.tail = &fpd.desc.fplist;
    fpd.desc.startaddr = fpd.desc.saveaddr = -1;
    fpd.desc.codeseg = bindsym_(codesegment);
    fpd.desc.initoffset = fpd.offset = -4;
}

static void fpdesc_startproc(void) {
    fpd.desc.startaddr = codebase+codep;
}

static void fpdesc_enterproc(void) {
    fpd.desc.saveaddr = codebase+codep;
}

static void fpdesc_setinitoffset(int32 n) {
    fpd.desc.initoffset = fpd.offset = n;
}

static void fpdesc_endproc(void) {
    fpd.desc.endaddr = codebase+codep;
    if (fpd.desc.fplist != NULL) obj_notefpdesc(&fpd.desc);
}

static void fplist_add(int32 n) {
    FPList *p;
/* Suppress generation of fpdesc tables for compatibility with old armsds */
/* Not a user facility! Only used for testing, etc.                       */
    if (var_cc_private_flags & 0x800000) return;
    p = (FPList *)SynAlloc(sizeof(FPList));
    cdr_(p) = NULL;
    p->addr = codebase+codep;
    p->change = n;
    *fpd.tail = p;
    fpd.tail = &cdr_(p);
    fpd.offset += n;
}

static void fpdesc_notespchange(int32 n) {
    if (!(procflags & NONLEAF) || (pcs_flags & PCS_NOFP))
        fplist_add(n);
}

static void fpdesc_newsp(int32 n) {
    if ((!(procflags & NONLEAF) || (pcs_flags & PCS_NOFP)) &&
        fpd.desc.fplist != NULL) {
        n += 4*(intsavewordsbelowfp + realargwordsbelowfp +
                3*bitcount(regmask & M_FVARREGS));
        if (n - 4 - fpd.offset != 0) fplist_add(n - fpd.offset - 4);
    }
}

#else

#define fpdesc_init()  0
#define fpdesc_newsp(n) 0
#define fpdesc_setinitoffset(n)  0
#define fpdesc_startproc() 0
#define fpdesc_enterproc() 0
#define fpdesc_endproc() 0
#define fpdesc_notespchange(n) 0

#endif


#define AddCodeXref3(t, n) (codexrefs = (CodeXref *)global_list3(SU_Xref, codexrefs, t, n))
#define AddCodeXref4(t, n, x) (codexrefs = (CodeXref *)global_list4(SU_Xref, codexrefs, t, n, x))
#define AddCodeXref5(t, n, x, y) (codexrefs = (CodeXref *)global_list5(SU_Xref, codexrefs, t, n, x, y))

static void outinstr(int32 w)
{
    if ((unsigned32 )w >= (unsigned32)0xff000000L)
        syserr(syserr_outinstr, (long)w);
    outcodeword(w ^ condition_mask, LIT_OPCODE);
}

static int32 outinstr3t(int32 w, Symstr *name, int xrflags, int32 tailcall)
{
    int32 d;
    if ((unsigned32)w >= (unsigned32)0xff000000L)
        syserr(syserr_outinstr, (long)w);
    /* the next two lines' data structures may be mergeable. */
    {
        d = obj_symref(name, xr_code | xrflags, 0);
#ifndef TARGET_WANTS_LINKER_TO_RESOLVE_FUNCTION_REFERENCES
        if (d == -1 || tailcall)
#endif
        {   int32 type = tailcall ? X_TailCall : X_PCreloc;
            AddCodeXref4(type | (codebase+codep), name, 0);
            d = 0;
        }
#ifdef AOF_VERSION_150
        else
#endif
          w += ((d - (codebase+codep+8)) >> 2) & 0x00ffffff;
    }
    outcodewordaux(w ^ condition_mask, LIT_RELADDR, name);
    return d;
}

static int32 outinstr3(int32 w, Symstr *name, int xrflags)
{   return outinstr3t(w, name, xrflags, NO);
}


static void out_ldm_instr(uint32 w)
{   /* Convert single register ldm/stm into a load/store - faster on some processors. */
    int reg = power_of_two(w & 65535);

    if (reg >= 0 && !(w & F_PSR))       /* one reg ldm/stm without S-flag */
    {
        w = (w & 0xF1BF0000) | 0x04000004 | F_RD(reg);
        if (!(w & 0x01000000))          /* post inc */
        {
            if (w & F_WRITEBACK)
                w &= ~F_WRITEBACK;      /* Post, WB -> remove writeback */
            else
                w ^= 0x01000004;        /* Post, no WB -> pre inc with 0 */
        }
    }
    outinstr(w);
}

/*
 * Some stuff added by RCC to peephole LDR a, [b, #x]; LDR a, [c, #x+4]
 * and similar into a single LDMIA, and possibly some shuffling of
 * registers.  This is probably of little use unless you have the hacks
 * to earlier stages of the code generator to encourage it to put
 * such things together (LRU-biased regalloc.c, and localopt.c).
 *
 * For the moment I am not going to integrate this with the rest of
 * the peepholing, because I think it is too confusing already.
 */

typedef enum {
  PENDING_NONE,
  PENDING_LD,
  PENDING_ST
} PendingStoreAccess;

typedef struct LoadOrStoreMul {
    int32 offset[16];
       /* offset[i] holds the offset from the current value of basereg  */
       /* at which register i is to be loaded or stored (if bit i set   */
       /* in regbits). Constant additions to or subtractions from       */
       /* basereg (including load/store with writeback) do not generate */
       /* any code, but alter baseadjust. After partial dumping of      */
       /* pending loads/stores which has changed the value in basereg,  */
       /* remaining offset[i]s must be corrected (and of course the     */
       /* value of baseadjust must also have been altered).             */
    PendingStoreAccess state;
    RealRegister basereg;
    int32 regbits;
    int32 deadregs;
       /* The subset of regbits for which the register is dead after its*/
       /* (not yet performed) store. (Cannot be added to spareregs until*/
       /* the store is actually done).                                  */
    /* What about registers not dead in their store, but dead after a /**/
    /* later reference? Should be added to deadregs, but probably added */
    /* to spareregs instead? Not currently a problem, since spareregs   */
    /* used only for MOVC and friends, which do an ldm_flush first, but */
    /* in that case why bother with deadregs anyway?                    */
    int32 baseadjust;
       /* Constant value the addition of which to basereg has been      */
       /* deferred. (See above)                                         */
    int32 baseadjusted;
       /* Use purely internal to ldm_flush, to track modifications to   */
       /* basereg (store location for Ri is offset[i]-baseadjusted)     */
    bool isload;
       /* The same as state == PENDING_LD, except that when flushing    */
       /* state is set to PENDING_NONE early                            */
    bool basedead;
       /* TRUE if basereg is dead (so the update implied by baseadjust  */
       /* need not in fact be done)                                     */
} LoadOrStoreMul;

static LoadOrStoreMul ldm_state;

static void ldm_reinit(void)
{
    ldm_state.state = PENDING_NONE;
}

#define LDRMASK
#define CONDITION(w) ((w) & 0xf0000000L)
#define RN(w)        (((w) >> 16) & 0xf)
#define RD(w)        (((w) >> 12) & 0xf)
#define OFFSET(w)    (((w)&F_UPDOWN_FIELD)==F_UP?((w)&0xfff):-((w)&0xfff))

#define OP_IS_LDR(w) \
  (((w) & (0x0e000000L|F_LDRSTR_FIELD|F_BYTEWORD_FIELD)) ==\
   (OP_POSTN|F_LDR|F_WORD))
#define OP_IS_STR(w) \
  (((w) & (0x0e000000L|F_LDRSTR_FIELD|F_BYTEWORD_FIELD)) ==\
   (OP_POSTN|F_STR|F_WORD))

#define ldm_printf if (localcg_debug(4)) cc_msg

typedef struct SavedLDM {
   struct SavedLDM *cdr;
   int32 startoff;
   int32 endoff;
   int32 regset;
   RealRegister lastreg;
} SavedLDM;

/* While flushing pending loads/stores, s->baseadjusted holds the value */
/* by which s->basereg has been altered since the call to flush, and    */
/* s->baseadjust always holds the amount still to be added to basereg   */
/* (baseadjust and baseadjusted are always changed in step).            */

static int32 ldm_type(int32 op, LoadOrStoreMul *s, int32 end)
{ if (!s->isload) op ^= (OP_LDMIA ^ OP_STMIA);
  if ((end < 0 && s->baseadjust < 0 && end >= s->baseadjust) ||
      (end > 0 && s->baseadjust > 0 && end <= s->baseadjust))
  { s->baseadjusted += end;
    s->baseadjust -= end;
    op |= F_WRITEBACK;
  }
  return op;
}

static void ldmstm_generate(SavedLDM *p, LoadOrStoreMul *s)
{ RealRegister basereg = s->basereg;
  if (p->startoff != p->endoff) {
    /* more than one register: ldm or stm likely */
    int32 op = 0;
    RealRegister b = basereg;
    bool altered = NO;
    int32 start = p->startoff - s->baseadjusted;
    int32 end = p->endoff - s->baseadjusted;
    int32 addon = 0;

    ldm_printf("-- flushing a %s r%ld, {%lx}, offset %ld\n",
                  (s->isload ? "LDM": "STM"), basereg, p->regset, start);
    if (start == 0)
      op = ldm_type(OP_LDMIA, s, end+4);
    else if (start == 4)
      op = ldm_type(OP_LDMIB, s, end);
    else if (end == 0)
      op = ldm_type(OP_LDMDA, s, start-4);
    else if (end == -4)
      op = ldm_type(OP_LDMDB, s, start);
    else if (start > 0 /* && end > 0 */ && s->baseadjust >= end) {
      if (s->baseadjust == end)
        addon = start-4, op = OP_LDMIB;
      else
        addon = start, op = OP_LDMIA, end += 4;
      op = ldm_type(op, s, end);
    } else if (/* start < 0 && */ end < 0 && s->baseadjust <= end) {
      if (s->baseadjust == start)
        addon = end+4, op = OP_LDMDB;
      else
        addon = end, op = OP_LDMDA, start -= 4;
      op = ldm_type(op, s, start);
    } else {
      if (s->isload) {
        b = p->lastreg;
        op = OP_LDMIA;
      } else {
        if (basereg == R_SP || member_RealRegSet(globalregset(), basereg)) {
           if ((b = GetTempReg()) >= 0) {
              ldm_printf("   using spare reg %ld as base\n", (long)b);
              if (regbit(b) & p->regset)
                 syserr(syserr_stm_freeregs, p->regset, spareregs);
          } else {
            ldm_printf("No stm - would modify SP or global reg variable\n");
            goto dosingly;
          }
        } else
          altered = YES;
        op = OP_STMIA;
      }
      if (Arm_EightBits(start) >= 0)
        addon = start;
      else if (Arm_EightBits(start-4) >= 0) {
        op += OP_LDMIB-OP_LDMIA;
        addon = start-4;
      } else if (Arm_EightBits(end) >= 0) {
        addon = end;
        op += OP_LDMDA-OP_LDMIA;
      } else if (Arm_EightBits(end+4) >= 0) {
        addon = end+4;
        op += OP_LDMDB-OP_LDMIA;
      } else
        addon = start;
    }
    if (addon != 0) add_integer(b, basereg, addon, 0);
    out_ldm_instr(op | F_RN(b) | p->regset);
    if (b == R_SP && (op & F_WRITEBACK)) {
      int32 n = 4 * bitcount(p->regset);
      fpdesc_notespchange((op & F_UPDOWN_FIELD) == F_DOWN ? n : -n);
    }
    if (altered) {
      s->baseadjusted += addon;
      s->baseadjust -= addon;
    }
    return;
  }

dosingly:
  { /* Note that we don't need to take here to load the base register last (if
       it's in the set to be loaded), because this code is only executed with
       regset having more than one member for stores (and base R_SP, moreover)
     */
    int32 rbit;
    int32 regset = p->regset;
    for (; (rbit = (regset & -regset)) != 0; p->startoff += 4, regset ^= rbit) {
      RealRegister r = power_of_two(rbit);
      int32 offx = p->startoff - s->baseadjusted;
      int32 op = (s->isload ? OP_LDR : OP_STR);
      ldm_printf("-- flushing %s r%ld, [r%ld, #%ld]\n",
                s->isload ? "LDR" : "STR",
                r, basereg, offx);
      if (offx == 0 && s->baseadjust != 0) {
        if (cdr_(p) == NULL) {
          if (-0xfff <= s->baseadjust && s->baseadjust <= 0xfff)
            offx = s->baseadjust;
        } else {
          int32 nextoff = cdr_(p)->startoff - s->baseadjusted;
          if ((s->baseadjust > 0 && nextoff > 0 && nextoff <= 0xfff && nextoff <= s->baseadjust) ||
              (s->baseadjust < 0 && nextoff < 0 && nextoff >= -0xfff && nextoff >= s->baseadjust))
            offx = nextoff;
        }
        if (offx != 0) {
          op ^= (OP_PREN ^ OP_POSTN);
          s->baseadjusted += offx;
          s->baseadjust -= offx;
        }
      } else if ((s->baseadjust > 0 && offx > 0 && offx <= s->baseadjust) ||
                 (s->baseadjust < 0 && offx < 0 && offx >= s->baseadjust)) {
            op |= F_WRITEBACK;
            s->baseadjusted += offx;
            s->baseadjust -= offx;
      }
      if (offx < 0) {
        op |= F_DOWN | (-offx);
      } else
        op |= F_UP | offx;
      outinstr(op | F_RN(basereg) | F_RD(r));
      if (basereg == R_SP && ((op & OP_CLASS) == OP_POSTN || (op & F_WRITEBACK)))
        fpdesc_notespchange(-offx);
    }
  }
}

static void ldm_flush_r(int32 regbits, bool moreforbase)
{ struct LoadOrStoreMul *s = &ldm_state;
  RealRegister r;
  SavedLDM ldm[16],
           *ldmp = NULL,
           *atend = NULL;
  int ldmix = 0;
  bool basefree;

  if (s->state == PENDING_NONE) return;

  ldm_printf("-- ldm_flush: %lx\n", regbits);

  /* I assume we can generate max 16 instructions. It's easy to get over 10
     generated instructions, so we have to check whether we need to dump the
     literals.
  */
  if (codep + 16*4 >= mustlitby) dumplits2(YES);

  /* If there is no writeback, but the base is dead (and not being reloaded)
     we may produce better code if more than one LDM/STM is to be generated
     if we pretend there is writeback.
   */
  if (s->baseadjust != 0)
    regbits = AllIntRegs;
  else if (s->basedead && !(s->regbits & regbit(s->basereg)) &&
           !usrdbg(DBG_VAR)) {
    int32 maxoffset = 0;
    bool fake_wb = YES;
    for (r = 0; r < 16; r++)
      if (s->regbits & regbit(r)) {
        int32 off = s->offset[r];
        if (maxoffset == 0 ||
            maxoffset >= 0 && off >= 0 ||
            maxoffset <= 0 && off <= 0)
          maxoffset = off;
        else
          fake_wb = NO;
      }
    if (fake_wb) {
      s->baseadjust = maxoffset;
      regbits = AllIntRegs;
    }
  }
  s->baseadjusted = 0;

  basefree = s->basedead && !(regbit(s->basereg) & s->regbits);
  for (r = 0; r < 16; r++)
    if (s->regbits & regbits & regbit(r)) {
      unsigned count = 1;
      RealRegister lastr;
      SavedLDM *cur = &ldm[ldmix];
      s->regbits ^= regbit(r);
      cur->regset = regbit(r);
      cur->endoff = cur->startoff = s->offset[r];
      cur->lastreg = r;
      for (lastr = r-1; lastr >= 0 && count < ldm_regs_max; lastr--, count++)
        if ((s->regbits & regbit(lastr)) && s->offset[lastr] == cur->startoff-4) {
          s->regbits ^= regbit(lastr);
          cur->regset |= regbit(lastr);
          cur->startoff -= 4;
        }
      for (lastr = r+1; lastr < 16 && count < ldm_regs_max; lastr++, count++)
        if ((s->regbits & regbit(lastr)) && s->offset[lastr] == cur->endoff+4) {
          s->regbits ^= regbit(lastr);
          cur->regset |= regbit(lastr);
          cur->endoff += 4;
          cur->lastreg = lastr;
        }
      { SavedLDM *p, **pp = &ldmp;
        if (cur->regset & regbit(s->basereg)) {
        /* if the base register is in the set to be loaded, it must be done last. */
          for (; (p = *pp) != NULL; pp = &cdr_(p)) /* nothing */;
          atend = cur;
        } else {
        /* if there is writeback, sort into order of offset (increasing if increment,
           decreasing if decrement).  If not, any order will do.  This is all in aid
           of not pushing stuff on the stack before SP is advanced / popping it after
           SP retreats (in case base is R_SP).
         */
          for (; (p = *pp) != atend; pp = &cdr_(p))
            if ((s->baseadjust > 0 && cur->startoff < p->startoff) ||
                (s->baseadjust < 0 && cur->startoff > p->startoff))
              break;
        }
        *pp = cur; cdr_(cur) = p;
        ldmix++;
      }
    }

  if (s->regbits == 0) {
    s->state = PENDING_NONE;
  }
  for (; ldmp != NULL; ldmp = cdr_(ldmp))
  {
    if (s->basedead && cdr_(ldmp) == NULL)
        s->baseadjust = 0;      /* remove writeback of last transfer if base is dead */
    ldmstm_generate(ldmp, s);
    if (s->isload)
    {
        KillKnownRegisterValues(ldmp->regset);
        spareregs &= ~ldmp->regset;
    }
    else
        spareregs |= ldmp->regset & s->deadregs;
  }
  s->deadregs &= s->regbits;        /* clear deadbits */
  if (s->regbits == 0 && basefree)
      spareregs |= regbit(s->basereg);
  if (s->baseadjusted != 0)         /* basereg updated */
      KillKnownRegisterValue(s->basereg);

  if (s->regbits != 0) {
    for (r = 0; r < 16; r++)
      if (s->regbits & regbit(r))
        s->offset[r] -= s->baseadjusted;
  } else if (s->baseadjust != 0 && !s->basedead && !moreforbase) {
    add_integer(s->basereg, s->basereg, s->baseadjust, 0);
    s->baseadjust = 0;
  }
}

static void ldm_flush(void) {
  ldm_flush_r(AllIntRegs, NO);
}

static void ldm_setpending(LoadOrStoreMul *s, int32 w) {
  if (OP_IS_LDR(w)) {
    s->state = PENDING_LD; s->isload = YES;
  } else {
    s->state = PENDING_ST; s->isload = NO;
  }
}

static int ldm_addregoff(LoadOrStoreMul *s, RealRegister reg, int32 w, int32 deadbits)
{ int32 off;
  int32 newadjust;

  if ((w & OP_CLASS) == OP_PREN) {
    off = s->baseadjust + OFFSET(w);
    newadjust = (w & F_WRITEBACK) ? off : s->baseadjust;
  } else {
    off = s->baseadjust;
    newadjust = s->baseadjust + OFFSET(w);
  }

  if ((reg == s->basereg || (regbit(s->basereg) & s->regbits)) &&
      newadjust != 0)
    return NO;

  if (regbit(reg) & s->regbits) { /* already have this reg */
    if (s->state == PENDING_ST) {
      if (s->offset[reg] != off) { /* storing to different place */
        return NO; /* handle it yourself! */
      }
    }
  } else {
    if (s->state == PENDING_ST) {
    /* if a store, we must check there isn't already a store to the same
       place pending.  If there is, we may just throw it away - it hasn't
       been used
     */
      RealRegister r;
      for (r = 0; r < 16; r++)
        if ((s->regbits & regbit(r)) && s->offset[r] == off) {
          ldm_printf("--- ldm discard store %ld : [%ld, %ld]\n",
                     r, s->basereg, off);
          s->regbits ^= regbit(r);
          break;
        }
    }
    s->regbits |= regbit(reg);
  }
  s->offset[reg] = off;
  s->baseadjust = newadjust;
  s->basedead = (deadbits & J_DEAD_R2) != 0;
  if (deadbits & J_DEAD_R1) s->deadregs |= regbit(reg);
  if (s->isload && s->basereg != reg)
      spareregs |= regbit(reg);
  /*
   * Now if this LDR has loaded the basereg, must not allow any
   * more to get peepholed onto it...
   */
  ldm_printf("-- ldm add %s %ld : [%ld, %ld]\n",
             s->state == PENDING_ST ? "store": "load",
             reg, s->basereg, off);

  if (reg == s->basereg) ldm_flush();
  return YES;
}

static void ldm_outinstr(int32 w, int32 deadbits)
{ struct LoadOrStoreMul *s = &ldm_state;
  bool mustdonow = var_ldm_enabled==0;
  RealRegister base = RN(w),
               rd = RD(w);

  if ((w & OP_CLASS) == OP_POSTN && (w & F_WRITEBACK))
    /* LDRT or STRT special case */
    mustdonow = YES;

  if (s->state != PENDING_NONE) {
    PendingStoreAccess access = OP_IS_LDR(w) ? PENDING_LD : PENDING_ST;
    if (mustdonow
        || s->state != access || base != s->basereg
        || (rd == base && access == PENDING_ST))
      ldm_flush();
    else {
      if (ldm_addregoff(s, rd, w, deadbits)) return;
      ldm_flush_r(AllIntRegs, YES);
      ldm_setpending(s, w);
      s->regbits = 0;
      s->deadregs = 0;
      ldm_addregoff(s, rd, w, deadbits);
      return;
    }
  }
  if (mustdonow || base == R_PC || base == rd) {
    outinstr(w);
    killipvalue(rd);
    KillKnownRegisterValue(rd);
    killipvalue(base);
    KillKnownRegisterValue(base);
    if (base == R_SP && ((w & OP_CLASS) == OP_POSTN || (w & F_WRITEBACK))) {
      int32 n = w & 0xfffL;
      fpdesc_notespchange((w & F_UPDOWN_FIELD) == F_DOWN ? n : -n);
    }
    return;
  }

   /* Now we are starting a fresh LDM/STM. */
  ldm_setpending(s, w);
  s->basereg = base;
  s->regbits = 0;
  s->deadregs = 0;
  s->baseadjust = 0;
  ldm_addregoff(s, rd, w, deadbits);
}

static void ldm_c_flush(int32 regbits, int32 setscond) {
  if (ldm_state.state != PENDING_NONE) {
    if ((regbits & regbit(ldm_state.basereg)) ||
        (setscond && condition_mask != C_ALWAYS))
      ldm_flush();
    else if (ldm_state.regbits & regbits)
      ldm_flush_r(regbits, NO);
  }
}

/*
 * End of the stuff to peephole LDM and STM.
 */

#define LABREF_BRANCH 0x00000000  /* ARM addressing modes for forw. refs. */
#define LABREF_B4096  0x01000000
#define LABREF_W256   0x02000000
#ifdef TARGET_HAS_DATA_VTABLES
#define LABREF_WORD32 0x03000000
#endif

struct DispDesc { int32 u_d, m; RealRegister r; };

static void bigdisp(struct DispDesc *x, int32 m, int32 mask, RealRegister r2r)
{   int32 w, modm;
    if (m<0)
        w = F_DOWN, modm = -m;
    else
        w = F_UP, modm = m;
    if (modm & ~mask)  /* This can happen via LDRV/STRV with big frames */
    {
        int32 n;
        ldm_c_flush(regbit(r2r) | regbit(R_IP), 0);
        if (ipvalue.valid && ipvalue.base == r2r) {
            int32 xw, offset = m - ipvalue.offset;
            if (offset < 0)
                xw = F_DOWN, offset = -offset;
            else
                xw = F_UP;
            if (offset <= mask) {
                x->u_d = xw; x->m = offset; x->r = R_IP;
                return;
            }
        }
        n = modm & ~mask;
        if (!(w & F_UP)) n = -n;
        add_integer(R_IP, r2r, n, 0);
        if (condition_mask == C_ALWAYS) {
            ipvalue.valid = YES; ipvalue.base = r2r; ipvalue.offset = n;
            spareregs &= ~regbit(R_IP);
            KillKnownRegisterValue(R_IP);
        } else
            DestroyIP();
        r2r = R_IP;
        modm &= mask;
    }
    x->u_d = w;
    x->m = modm;
    x->r = r2r;
}

typedef union count_position
{
    struct
    {   unsigned int posn:12,
                     line:16,
                     file:4;
    } s;
    int32 i;
} count_position;

static void arthur_module_relocation(void)
{
  /*
   * Dump relocation directives to relocate refs to
   * sl, -#_Lib$Reloc$Off and sl, -#_Mod$Reloc$off.
   */
  Symstr *name;

  if (arthur_module == 1) {
    name = mod_reloc_sym;
  } else if (arthur_module == 2) {
    name = lib_reloc_sym;
  } else {
    syserr(syserr_module_reloc, arthur_module);
    return;
  }
  obj_symref(name, 0, 0);  /* really a sort of xr_abs -- not code not data */
  AddCodeXref3(X_backaddrlit | (codebase+codep), name);
}

/* The notion of addressability is common, but w.r.t what varies
   between machines.
*/
static void addressability(int32 n)
{
/* the next line does not hide sloppy programming, but allows us to test
 * whether we have run out of addressability before we know exactly how
 * many (less than 5!) arm instructions a JOPCODE will generate.
 * WD: well, it's actually nearer to 32 instructions. Eg. max 15 instr for
 * the LDM peepholer followed by a CLRC using 8 registers (15 instr again)...
 * Therefore the MOVC/CLRC/PUSHC and ldm peepholer now have seperate checks.
 */
    n -= 5;
    if (litpoolp>=n) dumplits2(YES);
    if (codep-4*litpoolp+4*n < mustlitby) mustlitby = codep-4*litpoolp+4*n;
}

#define call_k(name, tail, xrflags, t) outinstr3t((tail) ? OP_B : OP_BL, name, xrflags, t)

static void killipvalue(RealRegister r)
{
    if (r == R_IP || r == ipvalue.base) ipvalue.valid = NO;
}

static void adjustipvalue(RealRegister r1, RealRegister r2, int32 k)
{
    if (ipvalue.valid && r1 == r2) {
        if (r1 == R_IP) {
            if (condition_mask == C_ALWAYS)
                ipvalue.offset += k;
            else
                ipvalue.valid = NO, spareregs |= regbit(R_IP);
        } else if (r1 == ipvalue.base) {
            if (condition_mask == C_ALWAYS)
                ipvalue.offset -= k;
            else
                ipvalue.valid = NO, spareregs |= regbit(R_IP);
        }
    } else
        killipvalue(r1);
    KillKnownRegisterValue(r1);
}


static int32 C_FROMQ(int32 q)
{   switch (q)
    {
/* We could exploit Q_NOT to simplify this code... */
case Q_EQ: case Q_UEQ: return C_EQ;
case Q_NE: case Q_UNE: return C_NE;
case Q_HS: return C_HS;
case Q_LO: return C_LO;
case Q_PL: return C_PL;
case Q_MI: return C_MI;
case Q_VS: return C_VS;
case Q_VC: return C_VC;
case Q_HI: return C_HI;
case Q_LS: return C_LS;
case Q_GE: return C_GE;
case Q_LT: return C_LT;
case Q_GT: return C_GT;
case Q_LE: return C_LE;
default: syserr("C_FROMQ(%lx)", (long)q);
case Q_AL|Q_UBIT: /* ask HCM about this in flowgraf.c */
case Q_AL: return 0;
    }
}

static void tailcallxk(RealRegister r4, int32 m, int32 inst) {
    int32 restored = (regmask & (M_VARREGS|M_LR)) | regbit(R_SP);
    if (!(pcs_flags & PCS_NOFP)) restored |= regbit(R_FP);
    inst |= F_RN(r4) | m;
    if (!(restored & regbit(r4))) {
        routine_exit(C_FROMQ(Q_AL), NO, 0);
        outinstr(inst | F_RD(R_PC));
    } else {
    /* r4 is something restored by routine_exit() */
        outinstr(inst | F_RD(R_IP));
        routine_exit(C_FROMQ(Q_AL), NO, 0);
        outinstr(OP_MOVR | F_RD(R_PC) | R_IP);
    }
}

static void tailcallxr(RealRegister r4, RealRegister r3, int32 inst) {
    int32 restored = (regmask & (M_VARREGS|M_LR)) | regbit(R_SP);
    if (!(pcs_flags & PCS_NOFP)) restored |= regbit(R_FP);
    inst |= F_RN(r4) | r3;
    if (!(restored & (regbit(r4)|regbit(r3)))) {
        routine_exit(C_FROMQ(Q_AL), NO, 0);
        outinstr(inst | F_RD(R_PC));
    } else {
    /* r3 or r4 is something restored by routine_exit() */
        outinstr(inst | F_RD(R_IP));
        routine_exit(C_FROMQ(Q_AL), NO, 0);
        outinstr(OP_MOVR | F_RD(R_PC) | R_IP);
    }
}

static void out_ldr_str(unsigned32 op, int32 offset) {

    if (offset < 0)
        op |= F_DOWN, offset = -offset;
    else
        op |= F_UP;
    if (offset > 0xfff) syserr("out_ldr_str");
    outinstr(op | offset);
}

int32 CheckSWIValue(int32 n) {
    if ((uint32)n > 0xffffff) {
        cc_err(gen_err_swi, n);
        n = 0xffffff;
    }
    return n;
}

typedef enum
{   RU_ALL = 0, RU_NONE = 1, RU_DONT_UPDATE_IP = 2, RU_DONT_UPDATE_REGVALUES = 4
}   RegisterUsageFlags;

#define SPAREREGS_MASK  0x5fff  /* R0-R11, IP, LR */


static void UpdateRegisters(RegisterUsage *reguse, RegisterUsageFlags flags)
{
    uint32 regswritten = regs_written(reguse);

    if (!(flags & RU_NONE))
    {
                if (flags & RU_DONT_UPDATE_IP)
                        regswritten &= ~regbit(R_IP);
        spareregs &= ~regs_out(reguse);
        spareregs |= regs_free(reguse);
        spareregs &= SPAREREGS_MASK;
                if (!(flags & RU_DONT_UPDATE_REGVALUES))
                        KillKnownRegisterValues(regswritten);
                if (regswritten & regbit(R_IP))
                        ipvalue.valid = NO;
        }
}

#define BaseIsWordAligned(op, peep) (((op) & J_BASEALIGN4) || ((peep) & P_BASEALIGNED))

void show_inst_direct(PendingOp *p)
/* The types of the arguments here are rather unsatisfactory - in        */
/* particular r3 is really a big union.                                   */
{
    struct DispDesc dispdesc;
    int32 w, msh = 0, illbits;
    J_OPCODE op = p->ic.op;
    RealRegister r1 = p->ic.r1.i, r2 = p->ic.r2.i, r3 = p->ic.r3.i, r4 = p->ic.r4.i;
    uint32 flags = p->ic.flags;
    int32 peep = p->peep, dataflow = p->dataflow;
    RegisterUsage regusage;
    RegisterUsageFlags regflags = RU_ALL;

    if (localcg_debug(4)) a_pr_jopcode(p);
    CheckJopcodeP(p, JCHK_MEM | JCHK_REGS | JCHK_SYSERR);
    if (codep >= mustlitby) dumplits2(YES);

    GetRegisterUsage(p, &regusage);

    msh = (op & J_SHIFTMASK) >> J_SHIFTPOS;
    if ((msh & SHIFT_RIGHT) == 0) {
        if (msh & SHIFT_ARITH)
        /* this encoding for ROR (left + arith) is somewhat delicate */
            msh = K_ROR(msh & SHIFT_MASK);
        else
            msh = K_LSL(msh & SHIFT_MASK);
    } else if (msh & SHIFT_ARITH) msh = K_ASR(msh & SHIFT_MASK);
    else msh = K_LSR(msh & SHIFT_MASK);
    if (peep & P_RSHIFT)
    {   if (msh) syserr(syserr_shifts);
        switch (peep & P_RSHIFT)
        {
    case P_LSL: msh = R_LSL(r4);    break;
    case P_LSR: msh = R_LSR(r4);    break;
    case P_ASR: msh = R_ASR(r4);    break;
    case P_ROR: msh = R_ROR(r4);    break;
        }
    }

/* to enable future JOPCODE peephole optimisation expand_jop_macros()
   tries quite hard not to call show_inst() with instructions with
   no effect.
*/
    /* illbits (and peep) check that unexpected (erroneous!) bits are not set */
    illbits = op & (Q_MASK | J_SIGNED | J_UNSIGNED | J_NEGINDEX | J_SHIFTMASK);
    switch (op & ~(Q_MASK | J_SIGNED | J_UNSIGNED | J_NEGINDEX | J_SHIFTMASK))

#define TRANS(op) ((peep & P_TRANS) ? (peep &= ~P_TRANS, (op)|F_WRITEBACK) : (op))

#define prepost_H(op) \
    ((peep & P_POST) ? (peep &= ~P_POST, TRANS(OP_H_POSTN)) : \
     (peep & P_PRE) ? (peep &= ~P_PRE, OP_H_PREN | F_WRITEBACK) : OP_H_PREN)

#define prepost(op) \
    ((peep & P_POST) ? (peep &= ~P_POST, TRANS(OP_POSTN)) : \
     (peep & P_PRE) ? (peep &= ~P_PRE, OP_PREN | F_WRITEBACK) : OP_PREN)

#define prepostr_H(op) \
    ((peep & P_POST) ? (peep &= ~P_POST, TRANS(OP_H_POSTR)) : \
     (peep & P_PRE) ? (peep &= ~P_PRE, OP_H_PRER | F_WRITEBACK) : OP_H_PRER)

#define prepostr(op) \
    ((peep & P_POST) ? (peep &= ~P_POST, TRANS(OP_POSTR)) : \
     (peep & P_PRE) ? (peep &= ~P_PRE, OP_PRER | F_WRITEBACK) : OP_PRER)

    {
case J_ORG:
        /* pad with OP_NOOP's -- here mov r0,r0.  Proper code?          */
        while (codep < r3) outinstr(OP_MOVR);
        if (codep != r3) syserr("J_ORG");
        break;
case J_WORD:
        ldm_flush();
        outinstr(r3 ^ C_ALWAYS);
        break;
case J_CMPK:
/* N.B. that CMPK can use R_IP as a work register               */
        ldm_c_flush(regs_used(&regusage), 1);
        cmp_integer(r2, r3, R_IP, op & Q_MASK, peep);
        peep &= ~(P_CMPZ | P_SETCC | P_SETPSR);
        illbits &= ~Q_MASK;
        break;
case J_CMNK:
/* N.B. that CMNK can use R_IP as a work register               */
        ldm_c_flush(regs_used(&regusage), 1);
        cmn_integer(r2, r3, R_IP, op & Q_MASK, peep);
        peep &= ~(P_CMPZ | P_SETCC | P_SETPSR);
        illbits &= ~Q_MASK;
        break;

#ifdef RANGECHECK_SUPPORTED
case J_CHKLK:
        ldm_flush();
        cmp_integer(r2, r3, R_IP, Q_LT, 0);
        outinstr3(OP_BL ^ Q_LT, sim.abcfault, 0);
        break;
case J_CHKUK:
        ldm_flush();
        cmp_integer(r2, r3, R_IP, Q_GT, 0);
        outinstr3(OP_BL ^ Q_GT, sim.abcfault, 0);
        break;

case J_CHKLR:
        ldm_flush();
        outinstr(OP_CMPR | F_RN(r2) | mr | msh);
        outinstr3(OP_BL ^ Q_LT, sim.abcfault, 0);
        break;
case J_CHKUR:
        ldm_flush();
        outinstr(OP_CMPR | F_RN(r2) | mr | msh);
        outinstr3(OP_BL ^ Q_GT, sim.abcfault, 0);
        break;

case J_CHKNEK:
        ldm_flush();
        cmp_integer(r2, r3, R_IP, Q_EQ, 0);
        outinstr3(OP_BL ^ Q_EQ, sim.valfault, 0);
        break;

#endif /* RANGECHECK_SUPPORTED */

/* N.B. having someone (e.g. show_instruction) changing the next 3 ops into */
/* ADDK 0; RSBK 0; and RSBK -1; would simplify peepholing them with CMP 0   */
/* and remove 3 cases from this table but using more general code           */
/* No - a better idea: use the peepholer to squash shifts and ops together  */
/* (via V_INTERNAL reg), but also turn solitary shifts into J_MOV+J_SHIFTM  */
/* N.B. This would make J_SHIFTM a P_PEEPn bit local to this file           */
case J_MOVR:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        if (r1!=r3 || (peep & P_CMPZ))
            outinstr(OP_MOVR | F_RD(r1) | r3 | SCC_of_PEEP(peep));
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        break;
case J_NEGR:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        outinstr(OP_RSBN | F_RD(r1) | F_RN(r3) | SCC_of_PEEP(peep));
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        illbits &= ~J_SHIFTMASK;
        break;
case J_NOTR:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        outinstr(OP_MVNR | F_RD(r1) | r3 | msh | SCC_of_PEEP(peep));
        peep &= ~(P_RSHIFT | P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        illbits &= ~J_SHIFTMASK;
        break;
case J_MOVK:
        ldm_c_flush(regs_used(&regusage), 0);
        load_integer(r1, r3, peep);
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        regflags = RU_DONT_UPDATE_REGVALUES;
        break;

case J_ADDK:
        if (r1 == r2 && ldm_state.state != PENDING_NONE
            && r1 == ldm_state.basereg && !(peep & P_CMPZ)
            && r3 <= 0xfff) {
            ldm_state.baseadjust += r3;
        } else {
            if (r1 == R_SP &&
                (   (r3 < 0 && ldm_state.state != PENDING_LD)
                    /* If the stack is being extended, its ok to move loads  */
                    /* before the stack movement (they can't be from the new */
                    /* bit of stack without an intervening store which will  */
                    /* flush the LDM state.                                  */
                 || (r3 > 0 && ldm_state.state != PENDING_ST)))
                    /* Similarly, if the stack is being contracted, stores   */
                    /* are OK.                                               */
              ldm_flush();
            else
              ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
            add_integer(r1, r2, r3, peep);
            adjustipvalue(r1, r2, r3);
            regflags |= RU_DONT_UPDATE_IP;  /* as adjustipvalue has already done this */
            peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        }
        break;
case J_SUBK:
        {   ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
            sub_integer(r1, r2, r3, peep);
            peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        }
        break;
case J_ADCK:
        {   ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
            adc_integer(r1, r2, r3, peep);
            peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        }
        break;
case J_SBCK:
        {   ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
            sbc_integer(r1, r2, r3, peep);
            peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        }
        break;
case J_RSBK:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        rsb_integer(r1, r2, r3, peep);
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        break;
case J_RSCK:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        rsc_integer(r1, r2, r3, peep);
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        break;
case J_ANDK:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        if ((dataflow & J_DEAD_R1) && (peep & P_CMPZ))
            tst_integer(r1, r2, r3, peep);
        else
            and_integer(r1, r2, r3, peep, dataflow & J_DEAD_R1);
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        break;
case J_TSTK:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        tst_integer(R_IP, r2, r3, peep);
        peep &= ~(P_CMPZ | P_SETCC | P_SETPSR | P_ZONLY | Q_MASK);
        break;
case J_ORRK:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        orr_integer(r1, r2, r3, peep);
        peep &= ~(P_CMPZ | P_SETCC | P_SETPSR | P_ZONLY | Q_MASK);
        break;
case J_EORK:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        if ((dataflow & J_DEAD_R1) && (peep & P_CMPZ))
            teq_integer(r1, r2, r3, peep);
        else
            eor_integer(r1, r2, r3, peep);
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        break;
case J_TEQK:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        teq_integer(R_IP, r2, r3, peep);
        peep &= ~(P_CMPZ | P_SETCC | P_SETPSR | P_ZONLY | Q_MASK);
        break;

case J_MULK:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        multiply_integer(r1, r2, r3, SCC_of_PEEP(peep));
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        break;
case J_MLAK:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        mla_integer(r1, r2, r3, r4, SCC_of_PEEP(peep));
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        break;
case J_SHRK:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        if (r3!=0)
        {   if (r3<=0 || r3>32) syserr(syserr_silly_shift, (long)r3);
            outinstr(OP_MOVR | F_RD(r1) | r2 | SCC_of_PEEP(peep) |
                (op & J_SIGNED ? K_ASR(r3) : K_LSR(r3)));
            illbits &= ~(J_SIGNED|J_UNSIGNED);
            peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
            break;
        }
        /* drop through if shift by 0 */
case J_SHLK:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        if (r3<0 || r3>31) syserr(syserr_silly_shift, (long)r3);
        outinstr(OP_MOVR | F_RD(r1) | r2 | SCC_of_PEEP(peep) | K_LSL(r3));
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        break;
case J_RORK:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        if (r3<0 || r3>31) syserr(syserr_silly_shift, (long)r3);   /* r3=0 is RRX */
        outinstr(OP_MOVR | F_RD(r1) | r2 | SCC_of_PEEP(peep) | (r3 == 0 ? K_RRX : K_ROR(r3)));
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        break;

case J_SHLR:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        outinstr(OP_MOVR | F_RD(r1) | r2 | SCC_of_PEEP(peep) | R_LSL(r3));
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        break;
case J_SHRR:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        outinstr(OP_MOVR | F_RD(r1) | r2 | SCC_of_PEEP(peep) |
                 (op & J_SIGNED ? R_ASR(r3) : R_LSR(r3)));
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        break;
case J_RORR:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        outinstr(OP_MOVR | F_RD(r1) | r2 | SCC_of_PEEP(peep) | R_ROR(r3));
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        break;
case J_CMPR:
        ldm_c_flush(regs_used(&regusage), 1);
        outinstr(OP_CMPR | SCC_of_PEEP(peep) | F_RN(r2) | r3 | msh);
        illbits &= ~(Q_MASK|J_SHIFTMASK);
        peep &= ~(P_RSHIFT|P_SWAPCOND|P_CMPZ|P_SETCC|P_SETPSR);
        break;
case J_CMNR:
        ldm_c_flush(regs_used(&regusage), 1);
        outinstr(OP_CMNR | SCC_of_PEEP (peep) | F_RN(r2) | r3 | msh);
        illbits &= ~(Q_MASK|J_SHIFTMASK);
        peep &= ~(P_RSHIFT|P_SWAPCOND|P_CMPZ|P_SETCC|P_SETPSR);
        break;

case J_ANDR:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        {   int32 opc = OP_ANDR, rd = F_RD(r1);
            if ((dataflow & J_DEAD_R1) && (peep & P_CMPZ))
                opc = OP_TSTR, rd = 0;
            outinstr(opc | SCC_of_PEEP(peep) | rd | F_RN(r2) | r3 | msh);
            illbits &= ~J_SHIFTMASK;
            peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK | P_RSHIFT);
            break;
        }

case J_EORR:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        {   int32 opc = OP_EORR, rd = F_RD(r1);
            if ((dataflow & J_DEAD_R1) && (peep & P_CMPZ))
                opc = OP_TEQR, rd = 0;
            outinstr(opc | SCC_of_PEEP(peep) | rd | F_RN(r2) | r3 | msh);
            illbits &= ~J_SHIFTMASK;
            peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK | P_RSHIFT);
            break;
        }

case J_TSTR:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        {   outinstr(OP_TSTR | SCC_of_PEEP(peep) | F_RN(r2) | r3 | msh);
            illbits &= ~J_SHIFTMASK;
            peep &= ~(P_CMPZ | P_SETCC | P_SETPSR| P_ZONLY | Q_MASK | P_RSHIFT);
            break;
        }

case J_TEQR:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        {   outinstr(OP_TEQR | SCC_of_PEEP(peep) | F_RN(r2) | r3 | msh);
            illbits &= ~J_SHIFTMASK;
            peep &= ~(P_CMPZ | P_SETCC | P_SETPSR | P_ZONLY | Q_MASK | P_RSHIFT);
            break;
        }
#ifdef ARM_INLINE_ASSEMBLER
case J_MRS:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        {   outinstr(OP_MRS | F_RD(r1) | (r2 & SPSR ? K_SPSR : 0));
            peep &= ~(Q_MASK);
            break;
        }

case J_MSR:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        {   outinstr(OP_MSR | r3 | (r2 & SPSR ? K_SPSR : 0) | F_RN(r2 & PSR_FLAGS));
            peep &= ~(Q_MASK);
            break;
        }

case J_MSK:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        {   r3 = Arm_EightBits(r3);
            outinstr(OP_MSR | OP_RXN | r3 | (r2 & SPSR ? K_SPSR : 0) | F_RN(r2 & PSR_FLAGS));
            peep &= ~(Q_MASK);
            break;
        }

case J_SWPB:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        {
            outinstr(OP_SWPB | F_RD(r1) | F_RN(r2) | r3);
            peep &= ~(Q_MASK);
            break;
        }

case J_SWP:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        {
            outinstr(OP_SWP | F_RD(r1) | F_RN(r2) | r3);
            peep &= ~(Q_MASK);
            break;
        }
case J_NULLOP:
        outinstr(OP_MOVR);
        break;
#endif

#define irrop(alu)                                                  \
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));       \
        outinstr((alu) | SCC_of_PEEP(peep) |                        \
                 F_RD(r1) | F_RN(r2) | r3 | msh);                   \
        illbits &= ~J_SHIFTMASK;                                    \
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK | P_RSHIFT);

case J_BICR:
        irrop(OP_BICR); break;
case J_ORRR:
        irrop(OP_ORRR); break;
case J_ADDR:
        irrop(OP_ADDR); break;
case J_ADCR:
        irrop(OP_ADCR); break;
case J_SUBR:
        irrop(OP_SUBR); break;
case J_SBCR:
        irrop(OP_SBCR); break;
case J_RSBR:
        irrop(OP_RSBR); break;
case J_RSCR:
        irrop(OP_RSCR); break;

#undef irrop

case J_MLAR:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        outinstr(OP_MLA | F_RN(r1) | F_RD(r4) |  (r2 << 8) | r3 | SCC_of_PEEP(peep));
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        break;
case J_MULR:
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        outinstr(OP_MUL | F_RN(r1) | (r2 << 8) | r3 | SCC_of_PEEP(peep));
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        break;
case J_MULL:
case J_MLAL:
    {   uint32 mulop = ((op & ~J_SIGNED) == J_MULL) ? OP_UMULL : OP_UMLAL;
        ldm_c_flush(regs_used(&regusage), SCC_of_PEEP(peep));
        if (p->ic.op & J_SIGNED) mulop += (OP_SMULL - OP_UMULL);
        outinstr(mulop | F_RN(r2) | F_RD(r1) | (r4 << 8) | r3 | SCC_of_PEEP(peep));
        peep &= ~(P_CMPZ | P_SETCC | P_ZONLY | Q_MASK);
        illbits &= ~J_SIGNED;
        break;
    }
#ifdef ARM_INLINE_ASSEMBLER
case J_SWI:
        ldm_flush();
        outinstr(OP_SWI | r1);
        break;
case J_BL:
        ldm_flush();
        call_k(bindsym_((Binder *) r1), 0, 0, 0);
        break;
#endif
case J_OPSYSK:
        ldm_flush();
        outinstr(OP_SWI | r3);
        break;

case J_CALLK:
        ldm_flush();
        call_k((Symstr *)r3, 0, (k_fltregs_(r2) != 0 ? aof_fpreg : 0), 0);
        break;

case J_TAILCALLK:
        ldm_flush();
        if (pcs_flags & PCS_REENTRANT)
            outinstr(OP_MOVR | F_RD(R_IP) | R_SB | SCC_of_PEEP(peep));
        routine_exit(C_FROMQ(Q_AL), NO, 0);
        call_k((Symstr *)r3, 1, (k_fltregs_(r2) != 0 ? aof_fpreg : 0), pcs_flags & PCS_REENTRANT);
        break;

case J_CALLR:
        /* c.regalloc has ensured that r3 and R_LR clash */
        ldm_flush();
        outinstr(OP_MOVR | F_RD(R_LR) | R_PC);
        if (pcs_flags & PCS_INTERWORK)
          outinstr(OP_BX | r3);
        else
          outinstr(OP_MOVR | F_RD(R_PC) | r3);
        break;
case J_CALLX:
        if (pcs_flags & PCS_INTERWORK) syserr(syserr_interwork);
        ldm_flush();
        {   int32 iop = OP_ADDN;
            int32 n = Arm_EightBits(r3);
            if (n < 0) {
                n = Arm_SplitForAdd(r4, r3, &iop);
                if (iop == OP_ADDN)
                    r3 -= n;
                else
                    r3 += n;
                add_integer(R_IP, r4, r3, 0);
                r4 = R_IP; r3 = n;
            }
            outinstr(OP_MOVR | F_RD(R_LR) | R_PC);
            outinstr(iop | F_RD(R_PC) | F_RN(r4) | Arm_EightBits(r3));
        }
        break;
case J_CALLI:
        if (pcs_flags & PCS_INTERWORK) syserr(syserr_interwork);
        ldm_flush();
        bigdisp(&dispdesc, r3, 0xfff, r4);
        outinstr(OP_MOVR | F_RD(R_LR) | R_PC);
        outinstr(prepost(op) | F_LDR | dispdesc.u_d | F_WORD | F_RD(R_PC) |
                 F_RN(dispdesc.r) | dispdesc.m);
        break;
case J_CALLXR:
        if (pcs_flags & PCS_INTERWORK) syserr(syserr_interwork);
        ldm_flush();
        outinstr(OP_MOVR | F_RD(R_LR) | R_PC);
        outinstr(((op & J_NEGINDEX) ? OP_SUBR : OP_ADDR) | F_RD(R_PC) | F_RN(r4) | r3 | msh);
        illbits &= ~(J_NEGINDEX|J_SHIFTMASK);
        break;
case J_CALLIR:
        if (pcs_flags & PCS_INTERWORK) syserr(syserr_interwork);
        ldm_flush();
        outinstr(OP_MOVR | F_RD(R_LR) | R_PC);
        outinstr(OP_LDRR | (op & J_NEGINDEX ? F_DOWN : F_UP) | F_RD(R_PC) | F_RN(r4) | r3 | msh);
        illbits &= ~(J_NEGINDEX|J_SHIFTMASK);
        break;
case J_TAILCALLX:
        if (pcs_flags & PCS_INTERWORK) syserr(syserr_interwork);
        ldm_flush();
        {   int32 iop = OP_ADDN;
            int32 n = Arm_EightBits(r3);
            if (n < 0) {
                n = Arm_SplitForAdd(r4, r3, &iop);
                if (iop == OP_ADDN)
                    r3 -= n;
                else
                    r3 += n;
                add_integer(R_IP, r4, r3, 0);
                r4 = R_IP; r3 = n;
            }
            tailcallxk(r4, Arm_EightBits(r3), iop);
        }
        break;
case J_TAILCALLI:
        if (pcs_flags & PCS_INTERWORK) syserr(syserr_interwork);
        ldm_flush();
        bigdisp(&dispdesc, r3, 0xfff, r4);
        tailcallxk(dispdesc.r, dispdesc.m, prepost(op) | F_LDR | dispdesc.u_d | F_WORD);
        break;
case J_TAILCALLXR:
        if (pcs_flags & PCS_INTERWORK) syserr(syserr_interwork);
        ldm_flush();
        tailcallxr(r4, r3, ((op & J_NEGINDEX) ? OP_SUBR : OP_ADDR) | msh);
        illbits &= ~(J_NEGINDEX|J_SHIFTMASK);
        break;
case J_TAILCALLIR:
        if (pcs_flags & PCS_INTERWORK) syserr(syserr_interwork);
        ldm_flush();
        tailcallxr(r4, r3, OP_LDRR | (op & J_NEGINDEX ? F_DOWN : F_UP) | msh);
        illbits &= ~(J_NEGINDEX|J_SHIFTMASK);
        break;
case J_TAILCALLR:
        ldm_flush();
        if (pcs_flags & PCS_INTERWORK) {
            if (!((regmask & (M_VARREGS|M_LR)) & regbit(r3))) {
                routine_exit(C_FROMQ(Q_AL), NO, 0);
                outinstr(OP_BX | r3);
            } else {
                /* mr is restored by routine exit */

                outinstr(OP_MOVR | F_RD(R_IP) | r3);
                routine_exit(C_FROMQ(Q_AL), NO, 0);
                outinstr(OP_BX | R_IP);
            }
        } else
            tailcallxk(r3, 0, OP_ADDN);
        break;
case J_COUNT:
        ldm_flush();
#ifndef TARGET_IS_UNIX
#  ifndef PROFILE_COUNTS_INLINE
        outinstr3(OP_BL, fn_entry_sym, 0);
#  else
/* (int)r1 is ? (I would like the character on the line) ????              */
/* (char *)r2 is the name of the file, and (int)r3 is the line number      */
/* within that file. I will assume here a sensible limit on the length     */
/* of files and hence pack these two pieces of information into a single   */
/* 32-bit word. The structure used is count_position, and up to 16 files   */
/* can be referenced. If there is any danger of running out of same I will */
/* flush out the table used to decode files names and start again.         */
        {   count_position k;
            k.i = 0;         /* just to stop compiler winging */
            /* beware that the next line may flush literals etc. */
            k.s.file = lit_of_count_name((char *)r2);
            k.s.line = (unsigned int)r3;
            k.s.posn = 0;   /* Not available here */
            outinstr3(OP_BL, count1routine, 0);
            outcodeword(0, LIT_NUMBER);              /* what it increments */
            outcodeword(k.i, LIT_NUMBER);
        }
#  endif
#endif
        break;
case J_INFOLINE:
        ldm_flush(); /* ensure codep is correct */
        dbg_addcodep((VoidStar)r1, codebase+codep);  /* hack -- see armdbg.c */
        break;
case J_INFOSCOPE:
        ldm_flush(); /* ensure codep is correct */
        dbg_addcodep(NULL, codebase+codep); /* hack -- see armdbx.c */
        break;
case J_INFOBODY:
        dbg_bodyproc(/*codebase+codep*/);
        break;
case J_STRING:
        ldm_flush();
/* flowgraf.c has replaced J_STRING by J_ADCON if Feature_WRStrLits.    */
          /*
           * Standard ANSI mode - string lits read-only in the code seg.
           * Ensure that the literal will be dumped in time for it to be
           * addressable. Note that by using coarser alignment than 4-bytes
           * I could often cover a longer span of addresses - but that does
           * not seem worthwhile here.
           */
        {   int32 disp, offset = (int32)r2, addon = 0;
            StringSegList *s = (StringSegList *)r3;
            if ((offset & 3) != 0) addon = offset, offset = 0;
            if ((disp = lit_findstringincurpool(s)) >= 0) {
            /* This reference must be addressable if the previous one was */
                addfref_(litlab, codep | LABREF_W256);
                outinstr(OP_ADDN | F_RD(r1) | F_RN(R_PC) | ((disp+offset) >> 2) | 0xf00);
                if (addon != 0) add_integer(r1, r1, addon, 0);
                break;
            }
/* NB here that on the ARM a backwards displacement can go as far as 0x3fc */
/* (=1020) but NOT as far as 0x400 (sign & magnitude, not 2's comp offset) */
            disp = lit_findstringinprevpools(s, codebase+codep+8-1020+offset);
            if (disp >= 0) {
                disp = (codebase+codep+8-disp+offset)>>2;
                outinstr(OP_SUBN | F_RD(r1) | F_RN(R_PC) | disp | 0xf00);
                if (addon != 0) add_integer(r1, r1, addon, 0);
                break;
            }
        /* For sufficiently long strings, we ensure that there's just one copy
         * even at the expense of more expensive access.
         */
            if (stringlength(s) <= 8 ||
                (disp = lit_findstringinprevpools(s, 0)) < 0)
            {
                addressability(256-offset/4);
                addfref_(litlab, codep | LABREF_W256);
                outinstr(OP_ADDN | F_RD(r1) | F_RN(R_PC) | (litpoolp + (offset>>2)) | 0xf00);
                codeseg_stringsegs((StringSegList *)r3, YES);
                if (addon != 0) add_integer(r1, r1, addon, 0);
                break;
            }
            r3 = (IPtr)bindsym_(codesegment);
            r2 = disp + addon + offset;
            /* fall through to generate an ADCON */
        }
case J_ADCON:
case J_ADCON+J_BASEALIGN4:
        ldm_flush();
        { Symstr *name = (Symstr *)r3;
#ifdef TARGET_HAS_AOF
# ifdef CONST_DATA_IN_CODE
          if (name == bindsym_(constdatasegment) &&
               ((pcs_flags & PCS_REENTRANT) ||
                (pcs_flags & PCS_ACCESS_CONSTDATA_WITH_ADR))) {
            int32 offset, op = OP_ADDN;
            int32 maskhi = 0x3fc00L,
                  masklo = 0x3ffL;
            ldm_flush(); /* ensure codep is correct */
            AddCodeXref4(X_DataAddr1+codebase+codep, name, 0);
            offset = (int32)r2-(codebase+codep+8);
            if (offset < 0) op = OP_SUBN, offset = -offset;
            if (offset & 3) {
              maskhi = 0xff00L;
              masklo = 0xffL;
            }
            outcodewordaux(condition_mask | op | F_RD(r1) |
                             F_RN(R_PC) | Arm_EightBits(offset & maskhi),
                           LIT_RELADDR, (VoidStar)name);
            outinstr(op | F_RD(r1) | F_RN(r1) | Arm_EightBits(offset & masklo));
          } else
# endif
#endif
          if (pcs_flags & PCS_REENTRANT) {
            int i = adconpool_find((int32)r2, LIT_ADCON, name);
            ldm_flush(); /* ensure codep is correct */
            AddCodeXref4(X_DataVal+codebase+codep, adconpool_lab, 0);
            outcodewordaux(condition_mask | OP_LDR | F_UP |
                             F_RD(r1) | F_RN(R_SB) | i,
                           LIT_RELADDR, (VoidStar)adconpool_lab);
          } else {
            int32 offset = (int32)r2;
            int32 i;
/* Try to find adcon in following order: 1. current literal pool,        */
/* 2. previous addressable pools, 3. new allocation in current pool.     */
            if ((i = lit_findword(offset, LIT_ADCON, name,
                       LITF_INCODE|LITF_FIRST|LITF_LAST|LITF_PEEK)) >= 0)
            { /* adcon available in current literal pool */
              /* if previous ref was addressable this one will be */
              addfref_(litlab, codep | LABREF_B4096);
              outinstr(OP_LDR | F_UP | F_RD(r1) | F_RN(R_PC) | i);
            }
            else if ((i = lit_findadcon(name,offset,codebase+codep+8-0xffc))
                     >= 0)
              outinstr(OP_LDR | F_DOWN | F_RD(r1) | F_RN(R_PC) | codebase+codep+8-i);
            else
            {
/* ensure that the literal that I am about to issue can be addressed     */
              addressability(1024);
              i = lit_findword(offset, LIT_ADCON, name,
                               LITF_INCODE|LITF_FIRST|LITF_LAST|LITF_NEW);
              addfref_(litlab, codep | LABREF_B4096);
              outinstr(OP_LDR | F_UP | F_RD(r1) | F_RN(R_PC) | i);
            }
/*@@@ AM: generalise the next routine into a obj_symflag() routine? */
/*@@@ or would the J_FNCON approach be better?  Discuss.            */
/*@@@ Hmm: what happens to static int a, *b=&a in arthur mode?      */
/*@@@ ... we should really fault this.                              */
            if (arthur_module)
            { ExtRef *x = symext_(name);
              /* flowgraf's obj_symref should ensure x!=0, but be careful */
              if (x && !(x->extflags & xr_code))
              { /* The next line relocates the following LDR# */
                arthur_module_relocation();
                outinstr(OP_LDR | F_DOWN | F_RD(R_IP) | F_RN(R_SL));
                outinstr(OP_ADDR | F_RD(r1) | F_RN(R_IP) | r1);
                DestroyIP();
              }
            }
          }
        }
        break;

case J_ADCONLL:
        ldm_flush();
/* I do so hope very much that these instructions are used in a          */
/* compatible way wrt floating point operands.                           */
        { int32 *w = (int32 *)&p->ic.r3.i64->bin.i;
          int size = sizeof_longlong / sizeof_long;
          int32 direction = F_UP, adconop = OP_ADDN;
          int32 disp = lit_findwordsincurpool(w, size, LIT_INT64_1);
          if (disp < 0) {
            disp = lit_findwordsinprevpools(w, size, LIT_INT64_1,
                      codebase+codep+8-1020);
            if (disp >= 0) {
              disp = codebase+codep+8-disp;
              direction = F_DOWN, adconop = OP_SUBN;
            } else {
              addressability(256);
              (void)lit_findword(w[0], LIT_INT64_1, NULL, LITF_INCODE|LITF_FIRST);
              /* use the second address in case overflow */
              disp = lit_findword(w[1], LIT_INT64_2, NULL, LITF_INCODE|LITF_LAST) - 4;
            }
          }
          disp >>= 2;
          if (direction == F_UP)
            addfref_(litlab, codep | LABREF_W256);
          outinstr(adconop | F_RD(r1) | F_RN(R_PC) | disp | 0xf00);
          break;
        }
case J_CONDEXEC:
        ldm_flush();
        { int32 cond = op & Q_MASK;
          int32 old_condmask = condition_mask;
          static bool mipl;
          if (cond == Q_MI || cond == Q_PL)
            mipl = YES;
          else if (cond == Q_AL)
            mipl = NO;
          else if (mipl) {
            if (cond == Q_LT)
              cond = Q_MI;
            else if (cond == Q_GE)
              cond = Q_PL;
          }
          /* Here we work round a problem with the peepholer turning (eg)
               ADD x.. + CMPK x,#0 + CONDEXEC(LT)
               into ADDS x.. + CONDEXEC(MI)
             (The problem is that if both arms have been conditionalised,
             the peepholer won't see the second).  This code is vulnerable
             to improvement in flowgraf's ability to conditionalise, but
             all is probably well because the real place to do improved
             conditionalisation is in gen.c instead.
           */
          condition_mask = C_FROMQ(cond) ^ C_ALWAYS;
          illbits &= ~Q_MASK;
          peep &= ~P_SWAPPEDOPS;
          if ((old_condmask ^ (C_FROMQ(Q_AL) ^ C_ALWAYS)) != 0) {
            /* Could remember the state at the last condexec, and discard */
            /* only if it's changed.                                      */
            spareregs = 0;
            KillKnownRegisterValues(AllIntRegs);
            ipvalue.valid = NO;
          }
          break;
        }
case J_B:
        ldm_flush();
        conditional_branch_to(op & Q_MASK, (LabelNumber *)r3, NO, (peep & P_ADJUSTSP) ? r4 : 0);
        /* only assemble literals after a guaranteed unconditional branch */
        if (op==J_B && condition_mask == C_ALWAYS) dumplits2(NO);
        illbits &= ~Q_MASK; peep &= ~(P_ADJUSTSP|P_SWAPPEDOPS);
        break;
case J_BXX:             /* Used with case tables */
        ldm_flush();
        conditional_branch_to(Q_AL, (LabelNumber *)r3, YES, 0);
        break;
case J_CASEBRANCH:
/* N.B. that J_CASEBRANCH can use R_IP as a work register                 */
        ldm_flush();
        cmp_integer(r1, r3-2, R_IP, Q_LS, 0);   /* -1 for default   */
        if (codep + 4*r3 >= mustlitby) dumplits2(YES);
        outinstr(OP_ADDR | C_LS | F_RD(R_PC) | F_RN(R_PC) | r1 | K_LSL(2));
        break;
case J_LABEL:
        ldm_flush();
        setlabel((LabelNumber *)r3);
        spareregs = 0;
        ipvalue.valid = NO;
        KillKnownRegisterValues(AllIntRegs);
        break;
case J_STACK:
        fpdesc_newsp(r3);
        break;
case J_LDRBK+J_ALIGN1:
        ldm_flush();
        { bool in_ms_byte = NO;
          int32 adj = 0;
          if (target_has_halfword_support && (op & J_SIGNED)) {
            bigdisp(&dispdesc, r3, 0xff, r2);
            w = dispdesc.u_d, r3 = dispdesc.m, r2 = dispdesc.r;
            if (peep & (P_PRE|P_POST)) adjustipvalue(r2, r2, adj = (w & F_UP ? r3 : -r3));
            outinstr(prepost_H(op) | F_LDR | w | F_SBYTE | F_RD(r1) | F_RN(r2) | (r3 & 0x0f) | ((r3 & 0xf0) << 4));
            if (r2 == R_SP && adj != 0) fpdesc_notespchange(-adj);
          } else {
            if ((op & J_SIGNED) && !(peep & (P_PRE|P_POST))) {
              if (!(config & CONFIG_NO_UNALIGNED_LOADS)) {
              /* For signed loads, we can use the barrel shifter to rotate the
                 byte we want into the MS byte of the word, saving a shift in
                 propagating the sign, provided that we know that the base is
                 word-aligned.  (Unfortunately, the hardware doesn't do the
                 sensible thing on big-endian ARMs, rotating the desired byte
                 into the MS byte only for offsets 0 and 2 mod 4)
               */
                if (BaseIsWordAligned(op, peep)) {
                  if (!target_lsbytefirst)
                    in_ms_byte = (r3 & 1) == 0;
                  else {
                    r3 = (r3 & ~3L) | ((r3+1) & 3L);
                    in_ms_byte = YES;
                  }
                }
              } else /* CONFIG_NO_UNALIGNED_LOADS */
                if (BaseIsWordAligned(op, peep)) {
                  if ((r3 & 3L) == (target_lsbytefirst ? 3L : 0L)) {
                    in_ms_byte = YES;
                    r3 &= ~3L;
                  }
                }
            }
            bigdisp(&dispdesc, r3, 0xfff, r2);
            w = dispdesc.u_d, r3 = dispdesc.m, r2 = dispdesc.r;
            if (peep & (P_PRE|P_POST)) adjustipvalue(r2, r2, adj = (w & F_UP ? r3 : -r3));
            outinstr(prepost(op) | F_LDR | w | (in_ms_byte ? F_WORD : F_BYTE) |
                                   F_RD(r1) | F_RN(r2) | r3);
            if (r2 == R_SP && adj != 0) fpdesc_notespchange(-adj);
            if (op & J_SIGNED) {
              if (!in_ms_byte)
                outinstr(OP_MOVR | F_RD(r1) | r1 | K_LSL(24));
              if (!(peep & P_MS))
                outinstr(OP_MOVR | F_RD(r1) | r1 | K_ASR(24));
            }
          }
        }
        regflags = RU_DONT_UPDATE_IP;  /* (ip state has already been set) */
        peep &= ~(P_BASEALIGNED | P_MS);
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        break;
case J_LDRBR+J_ALIGN1:
        ldm_flush();
        w = (op & J_NEGINDEX) ? F_DOWN : F_UP;
        if (target_has_halfword_support && (op & J_SIGNED)) {
            if (msh) {
              outinstr(OP_MOVR | F_RD(R_IP) | r3 | msh);
              r3 = R_IP;
              DestroyIP();
            }
            outinstr(prepostr_H(op) | F_LDR | w | F_SBYTE | F_RD(r1) | F_RN(r2) | r3);
        } else {
            outinstr(prepostr(op) | F_LDR | F_BYTE | w | F_RD(r1) | F_RN(r2) | r3 | msh);
            if (op & J_SIGNED) {
              outinstr(OP_MOVR | F_RD(r1) | r1 | K_LSL(24));
              if (!(peep & P_MS))
                outinstr(OP_MOVR | F_RD(r1) | r1 | K_ASR(24));
            }
        }
        peep &= ~(P_BASEALIGNED|P_MS|P_RSHIFT);
        illbits &= ~(J_SIGNED|J_UNSIGNED|J_NEGINDEX|J_SHIFTMASK);
        break;
case J_LDRWK+J_ALIGN2:
case J_LDRWK+J_ALIGN1:
        ldm_flush();
        illbits &= ~(J_SIGNED|J_UNSIGNED);
/* note that LDRWK with neither J_UNSIGNED nor J_SIGNED is valid and leaves */
/* junk in top 16 bits                                                      */
        if (target_has_halfword_support && (op & J_ALIGNMENT) == J_ALIGN2) {
          if (peep & P_MS) syserr(syserr_jop_mode, (long)op, (long)peep);
          bigdisp(&dispdesc, r3, 0xff, r2);
          w = dispdesc.u_d, r3 = dispdesc.m, r2 = dispdesc.r;
          { int32 adj = 0;
            if (peep & (P_PRE|P_POST)) adjustipvalue(r2, r2, adj = (w & F_UP ? r3 : -r3));
            outinstr(prepost_H(op) | F_LDR | w | ((op & J_SIGNED) ? F_SHALF : F_UHALF) |
                                 F_RD(r1) | F_RN(r2) | (r3 & 0x0f) | ((r3 & 0xf0) << 4));
            if (r2 == R_SP && adj != 0) fpdesc_notespchange(-adj);
          }
          regflags = RU_DONT_UPDATE_IP;  /* (ip state has already been set) */
        } else
        { bool in_ms_half = !target_lsbytefirst;
          bool forcetwobytes = NO;
          int32 offset = r3 & 3L;
          int32 adj = 0;
          if ((op & J_ALIGNMENT) == J_ALIGN1)
            forcetwobytes = !BaseIsWordAligned(op, peep) ||
                            offset > 2 ||
                            (!target_lsbytefirst && offset == 1);

          if ((config & CONFIG_NO_UNALIGNED_LOADS) || forcetwobytes) {
            bool twobytes = YES;
            if (BaseIsWordAligned(op, peep) && !forcetwobytes) {
              /* base register of known alignment: we may be able to use
                 normal access code
               */
              if (peep & P_POST)
                twobytes = NO;
              else if (peep & P_PRE)
                twobytes = (r3 & 2L) != 0;
              else {
                if (r3 & 2L) in_ms_half = !in_ms_half;
                r3 &= ~2L;
                twobytes = NO;
              }
            }
            if (twobytes) {
              int32 lsbyte, msbyte;
              int32 p = peep; /* prepost() removes P_PRE, P_POST from peep */
              bigdisp(&dispdesc, r3, 0xffe, r2);
              w = dispdesc.u_d, r3 = dispdesc.m, r2 = dispdesc.r;
              if (peep & (P_PRE | P_POST))
                adjustipvalue(r2, r2, adj = (w & F_UP ? r3 : -r3));
              outinstr(prepost(op) | F_LDR | w | F_BYTE | F_RD(r1) |
                                                          F_RN(r2) | r3);
              if (r2 == R_SP && adj != 0) fpdesc_notespchange(-adj);
              if (p & P_PRE)
                r3 = 1 | F_UP;
              else if ((p & P_POST) && r3 != 0) {
                if (w & F_UP)
                  r3 = (r3-1) | F_DOWN;
                else
                  r3 = (r3+1) | F_UP;
              } else if (w == F_UP)
                r3 = (r3 + 1) | w;
              else
                r3 = (r3 - 1) | w;
              outinstr(OP_LDRB | F_RD(R_IP) | F_RN(r2) | r3);
              if (target_lsbytefirst)
                lsbyte = r1, msbyte = R_IP;
              else
                lsbyte = R_IP, msbyte = r1;
              if (peep & P_MS) {
                outinstr(OP_MOVR | F_RD(msbyte) | msbyte | K_LSL(24));
                outinstr(OP_ORRR | F_RD(r1) | F_RN(msbyte) | lsbyte | K_LSL(16));
              } else if (op & J_SIGNED) {
                outinstr(OP_MOVR | F_RD(msbyte) | msbyte | K_LSL(24));
                outinstr(OP_ORRR | F_RD(r1) | F_RN(lsbyte) | msbyte | K_ASR(16));
              } else
                outinstr(OP_ORRR | F_RD(r1) | F_RN(lsbyte) | msbyte | K_LSL(8));
              peep &= ~(P_BASEALIGNED | P_MS);
              DestroyIP();
              break;
            }
          } else if (target_lsbytefirst
                     && BaseIsWordAligned(op, peep) && !(peep & (P_PRE|P_POST))
                     && ((peep & P_MS)
                         || (op & (J_SIGNED | J_UNSIGNED)))) {
            /* on a little-endian ARM, we can save one shift in zero or sign
             * extension by addressing the halfword we don't want (provided we
             * know that the base is word-aligned).
             */
            r3 ^= 2;
            in_ms_half = YES;
          } else if (!target_lsbytefirst
                     && BaseIsWordAligned(op, peep) && !(peep & (P_PRE|P_POST))
                     && !(op & (J_SIGNED | J_UNSIGNED))
                     && !(peep & P_MS)) {
            /* for a plain load on a big-endian ARM, we can save a shift by
             * addressing the halfword we don't want (provided we know that
             * the base is word-aligned).
             */
            r3 ^= 2;
            in_ms_half = NO;
          }
          bigdisp(&dispdesc, r3, 0xfff, r2);
          w = dispdesc.u_d, r3 = dispdesc.m, r2 = dispdesc.r;
          if (peep & (P_PRE | P_POST))
            adjustipvalue(r2, r2, adj = (w & F_UP ? r3 : -r3));
/* the following line uses that non-aligned 32 bits loads go via the       */
/* ARM barrel shifter.  Hence all is OK for aligned 16 bit loads!          */
          outinstr(prepost(op) | F_LDR | w | F_WORD | F_RD(r1) | F_RN(r2) | r3);
          if (r2 == R_SP && adj != 0) fpdesc_notespchange(-adj);
          if (in_ms_half || (op & (J_SIGNED | J_UNSIGNED)) || (peep & P_MS)) {
            if (!in_ms_half)
              outinstr(OP_MOVR | F_RD(r1) | r1 | K_LSL(16));
            if (!(peep & P_MS)) {
              if (op & J_SIGNED)
                outinstr(OP_MOVR | F_RD(r1) | r1 | K_ASR(16));
              else
                outinstr(OP_MOVR | F_RD(r1) | r1 | K_LSR(16));
            }
          }
          regflags = RU_DONT_UPDATE_IP;  /* (ip state has already been set) */
        }
        peep &= ~(P_BASEALIGNED | P_MS);
        break;
case J_LDRWR+J_ALIGN2:
        ldm_flush();
        w = (op & J_NEGINDEX) ? F_DOWN : F_UP;
        if (target_has_halfword_support) {
          if (msh) {
            outinstr(OP_MOVR | F_RD(R_IP) | r3 | msh);
            r3 = R_IP;
            DestroyIP();
          }
          outinstr(prepostr_H(op) | F_LDR | w | ((op & J_SIGNED) ? F_SHALF : F_UHALF) |
                                    F_RD(r1) | F_RN(r2) | r3);
        } else if (config & CONFIG_NO_UNALIGNED_LOADS) {
          int32 lsbyte, msbyte;
          if (op & J_NEGINDEX)
            outinstr(OP_SUBR | F_RD(R_IP) | F_RN(r2) | r3 | msh);
          else
            outinstr(OP_ADDR | F_RD(R_IP) | F_RN(r2) | r3 | msh);
          outinstr(OP_LDRB | F_UP | F_RD(r1) | F_RN(R_IP) | 0);
          outinstr(OP_LDRB | F_UP | F_RD(R_IP) | F_RN(R_IP) | 1);
          if (target_lsbytefirst)
            lsbyte = r1, msbyte = R_IP;
          else
            lsbyte = R_IP, msbyte = r1;
          if (op & J_SIGNED) {
            outinstr(OP_MOVR | F_RD(msbyte) | msbyte | K_LSL(24));
            outinstr(OP_ORRR | F_RD(r1) | F_RN(lsbyte) | msbyte | K_ASR(16));
          } else
            outinstr(OP_ORRR | F_RD(r1) | F_RN(lsbyte) | msbyte | K_LSL(8));
          DestroyIP();
        } else {
          outinstr(OP_LDRR | w | F_RD(r1) | F_RN(r2) | r3 | msh);
          if (!target_lsbytefirst || (op & (J_SIGNED | J_UNSIGNED)) || (peep & P_MS)) {
            if (target_lsbytefirst)
              outinstr(OP_MOVR | F_RD(r1) | r1 | K_LSL(16));
            if (!(peep & P_MS)) {
              if (op & J_SIGNED)
                outinstr(OP_MOVR | F_RD(r1) | r1 | K_ASR(16));
              else
                outinstr(OP_MOVR | F_RD(r1) | r1 | K_LSR(16));
            }
            peep &= ~P_MS;
          }
        }
        peep &= ~(P_BASEALIGNED|P_RSHIFT);
        illbits &= ~(J_SIGNED|J_UNSIGNED|J_NEGINDEX|J_SHIFTMASK);
        break;
case J_STRK+J_ALIGN1:
        if (BaseIsWordAligned(op, peep) && (r3 & 3) == 0) {
            peep &= ~P_BASEALIGNED;
            goto AlignedStore;
        }
        {
            uint32 value = 0x01020304;      /* unknown value - all bytes different */
            uint32 lastval;
            uint32 storebits = 0x01010101;
            int32 shift;
            RealRegister valreg = r1;
            int32 inc = 1;
            if (ValueIsKnown(r1))
                value = KnownValue(r1);
            ldm_flush();
            if (!target_lsbytefirst) inc = -1, r3 += 3;
            lastval = value & 255;              /* skip the first LSR */
            while (storebits != 0)
            {
                for (shift = 0; shift < 32; shift += 8)
                    if (storebits & (1 << shift) &&
                        lastval == ((value >> shift) & 255)) break;
                if (shift == 32)                /* didn't find the same value */
                {
                    for (shift = 0; !(storebits & (1 << shift)); shift += 8) continue;
                    lastval = (value >> shift) & 255;
                    outinstr(OP_MOVR | F_RD(R_IP) | r1 | K_LSR(shift));
                    valreg = R_IP;
                }
                out_ldr_str(OP_STRB | F_RN(r2) | F_RD(valreg), r3 + inc * (shift >> 3));
                storebits ^= 1 << shift;
            }
            peep &= ~P_BASEALIGNED;
            if (valreg == R_IP) DestroyIP();
            break;
        }
case J_LDRK+J_ALIGN1:
        if (r1 == R_A4 || r1 == R_IP) syserr("LDRK unaligned: dest r%ld", (long)r1);
        if (!BaseIsWordAligned(op, peep)) {
            bool l_e = target_lsbytefirst;
            RealRegister w1 = R_A4, w2 = R_IP;

            ldm_flush();
            if (r3 != 0) {
                add_integer(r1, r2, r3, 0);
                r2 = r1;
            }
            DestroyIP();
            KillKnownRegisterValue(R_A1+3);
            outinstr(OP_LDMIA | F_RN(r2) | regbit(w1) | regbit(w2));
            outinstr(OP_ANDN | F_RD(r1) | F_RN(r2) | 3);
            outinstr(OP_MOVR | F_RD(r1) | r1 | K_LSL(3));
            outinstr(OP_MOVR | F_RD(w1) | w1 | (l_e ? R_LSR(r1) : R_LSL(r1)));
            outinstr(OP_RSBN | F_RD(r1) | F_RN(r1) | 32);
            outinstr(OP_ORRR | F_RD(r1) | F_RN(w1) | w2 | (l_e ? R_LSL(r1) : R_LSR(r1)));
            break;
        } else if ((r3 & 3) != 0) {
            bool l_e = target_lsbytefirst;
            int32 w = r3 & ~3;
            int32 n = r3 & 3;
            RealRegister w1 = R_A4, w2 = R_IP;
            /* It's just possible we may be able to peephole the loads here with
               pending loads from the same base, so we don't generate the LDM
               directly.
             */
            ldm_c_flush(regbit(w1) | regbit(w2), 0);
            DestroyIP();
            if (r2 == w1)
            {
                ldm_outinstr(OP_LDR | F_UP | F_RD(w2) | F_RN(r2) | (w+4), 0);
                ldm_outinstr(OP_LDR | F_UP | F_RD(w1) | F_RN(r2) | w, dataflow);
            }
            else
            {
                ldm_outinstr(OP_LDR | F_UP | F_RD(w1) | F_RN(r2) | w, 0);
                ldm_outinstr(OP_LDR | F_UP | F_RD(w2) | F_RN(r2) | (w+4), dataflow);
            }
            ldm_flush();
            outinstr(OP_MOVR | F_RD(r1) | w1 | (l_e ? K_LSR(8*n) : K_LSL(8*n)));
            outinstr(OP_ORRR | F_RD(r1) | F_RN(r1) | w2 | (l_e ? K_LSL(8*(4-n)) : K_LSR(8*(4-n))));
            peep &= ~P_BASEALIGNED;
            break;
        }
        /* else fall through to correctly aligned case */
case J_LDRK+J_ALIGN4:
case J_STRK+J_ALIGN4:
AlignedStore:
        w = loads_r1(op) ? F_LDR : F_STR;
        bigdisp(&dispdesc, r3, 0xfff, r2);
        w |= dispdesc.u_d, r3 = dispdesc.m, r2 = dispdesc.r;
        /* Only free a to be loaded register if it's not equal to the base register */
        { int32 adj = 0;
          if (peep & (P_PRE | P_POST)) adjustipvalue(r2, r2, adj = (w & F_UP ? r3 : -r3));
          ldm_outinstr((prepost(op) | w | F_WORD | F_RD(r1) | F_RN(r2) | r3),
                       dataflow);
          if (r2 == R_SP && adj != 0) fpdesc_notespchange(-adj);
        }
        regflags = RU_NONE | RU_DONT_UPDATE_IP;
        /* instr is buffered, so don't update register usage            */
        /* (and ip state has already been set)                          */
        peep &= ~P_BASEALIGNED;
        break;
case J_LDRR+J_ALIGN4:
case J_STRR+J_ALIGN4:
        ldm_flush();
        w = loads_r1(op) ? F_LDR : F_STR;
        w |= (op & J_NEGINDEX) ? F_DOWN : F_UP;
        outinstr(prepostr(op) | w | F_RD(r1) | F_RN(r2) | r3 | msh);
        peep &= ~(P_BASEALIGNED|P_RSHIFT);
        illbits &= ~(J_NEGINDEX|J_SHIFTMASK);
        break;
case J_STRBK+J_ALIGN1:
        ldm_flush();
        bigdisp(&dispdesc, r3, 0xfff, r2);
        w = dispdesc.u_d, r3 = dispdesc.m, r2 = dispdesc.r;
        { int32 adj = 0;
          if (peep & (P_PRE | P_POST)) adjustipvalue(r2, r2, adj = (w & F_UP ? r3 : -r3));
          outinstr(prepost(op) | F_STR | F_BYTE | w | F_RD(r1) | F_RN(r2) | r3);
          if (r2 == R_SP && adj != 0) fpdesc_notespchange(-adj);
        }
        regflags = RU_DONT_UPDATE_IP;  /* (ip state has already been set) */
        peep &= ~P_BASEALIGNED;
        break;
case J_STRBR+J_ALIGN1:
        ldm_flush();
        w = (op & J_NEGINDEX) ? F_DOWN : F_UP;
        outinstr(prepostr(op) | F_STR | F_BYTE | w | F_RD(r1) | F_RN(r2) | r3 | msh);
        peep &= ~(P_BASEALIGNED|P_RSHIFT);
        illbits &= ~(J_NEGINDEX|J_SHIFTMASK);
        break;
/* J_STRW is done by cg.c for the ARM */
case J_STRWK+J_ALIGN1:
        if (!BaseIsWordAligned(op, peep) || (r3 & 1) != 0)
        {
            int32 inc = 1;
            bool bytesequal = NO;
            RealRegister ip = R_IP;
            if (target_lacks_halfword_store)
                syserr("J_STRW issued with no halfword store");
            if (ValueIsKnown(r1)) {
                int32 value = KnownValue(r1);
                int32 b0 = value & 0xff,
                      b1 = (value >> 8) & 0xff;
                if (b0 == b1) bytesequal = YES;
                /* Expected to be useful really only for 0 / -1 */
            }

            ldm_flush();
            if (!target_lsbytefirst) inc = -1, r3 += 1;
            out_ldr_str(OP_STRB | F_RN(r2) | F_RD(r1), r3);
            if (bytesequal)
                ip = r1;
            else {
                outinstr(OP_MOVR | F_RD(ip) | r1 | K_LSR(8));
                DestroyIP();
            }
            out_ldr_str(OP_STRB | F_RN(r2) | F_RD(ip), r3+inc);
            peep &= ~P_BASEALIGNED;
            break;
        }
case J_STRWK+J_ALIGN2:
        if (target_lacks_halfword_store)
            syserr("J_STRW issued with no halfword store");
        ldm_flush();
        bigdisp(&dispdesc, r3, 0xff, r2);
        w = dispdesc.u_d, r3 = dispdesc.m, r2 = dispdesc.r;
        { int32 adj = 0;
          if (peep & (P_PRE | P_POST)) adjustipvalue(r2, r2, adj = (w & F_UP ? r3 : -r3));
          outinstr(prepost_H(op) | F_STR | w | F_UHALF | F_RD(r1) | F_RN(r2) | (r3 & 0x0f) | ((r3 & 0xf0) << 4));
          if (r2 == R_SP && adj != 0) fpdesc_notespchange(-adj);
        }
        peep &= ~P_BASEALIGNED;
        break;
case J_STRWR+J_ALIGN2:
        if (target_lacks_halfword_store)
            syserr("J_STRW issued with no halfword store");
        ldm_flush();
        w = (op & J_NEGINDEX) ? F_DOWN : F_UP;
        if (msh) {
            outinstr(OP_MOVR | F_RD(R_IP) | r3 | msh);
            r3 = R_IP;
            DestroyIP();
        }
        outinstr(prepostr_H(op) | F_STR | w | F_UHALF | F_RD(r1) | F_RN(r2) | r3);
        peep &= ~(P_BASEALIGNED|P_RSHIFT);
        illbits &= ~(J_NEGINDEX|J_SHIFTMASK);
        break;

case J_ENDPROC:
        ldm_flush();
        if (!lab_isset_(returnlab) && returnlab->u.frefs != NULL)
            /* at least one pending ref */
            conditional_branch_to(Q_AL, RETLAB, NO, 0);
        dumplits2(NO); /* to ensure that all literals for a proc get put out */
        dump_count_names();
        fpdesc_endproc();
/* Fill in argument binders with offsets which can be used to access the
 * arguments in a containing procedure from a base of 'local 0'.  The need
 * to do something like this is target-independent, but what exactly needs
 * doing is of course strongly target-dependent.
 * (Not used in C or C++, of course)
 */
        {   BindList *b;
            /* /* work to be done here for NOFP */
            for (b = argument_bindlist; b != NULL; b = b->bindlistcdr) {
                Binder *v = b->bindlistcar;
                int32 p = bindaddr_(v) & ~BINDADDR_MASK;
                if (p >= 4*argwordsbelowfp)
                    p += 4 * bitcount(regmask & M_VARREGS) + 16;
                p += 12*bitcount(regmask & M_FVARREGS);
                bindaddr_(v) = (bindaddr_(v) & BINDADDR_MASK) | p;
            }
        }
        break;
case J_ENTER:
        routine_entry(r3);
#ifdef TARGET_HAS_SAVE
        break;
case J_SAVE:
#endif
        routine_saveregs(r3);
        break;

/* J_PUSHR should never reach armgen (removed in flowgraf) */
case J_PUSHM:
        ldm_flush();
        {
            int32 count = 4 * bitcount(r3);
            out_ldm_instr(OP_STMFD | F_WRITEBACK | F_RN(R_SP) | r3);
            fpdesc_notespchange(count);
            adjustipvalue(R_SP, R_SP, -count);
        }
        break;
case J_POPMB:  /* version of POP with a specified base */
        ldm_flush();
        {   int32 ldmop = OP_LDMDB;
            int32 count = 4 * bitcount(r3);
            if (peep & P_PRE) {
                add_integer(r2, r2, r1-count, 0);
                r1 = count;
                peep &= ~P_PRE;
            }
            if (r1 != 0) {
                if (count == r1)
                    ldmop = OP_LDMIA;
                else {
                    int32 r = power_of_two(r3 & (-r3));
                    add_integer(r, r2, r1, 0);
                    r2 = r;
                }
            }
            out_ldm_instr(ldmop | F_RN(r2) | r3);
            spareregs &= ~r3;
            KillKnownRegisterValues(r3);
        }
        break;
#ifdef ARM_INLINE_ASSEMBLER
case J_LDM:
case J_LDMW:
case J_STM:
case J_STMW:
    {   uint32 ldmop = 0;
        switch (flags & MM_TYPE)
        {
            case MM_IA: ldmop = OP_LDMIA; break;
            case MM_IB: ldmop = OP_LDMIB; break;
            case MM_DA: ldmop = OP_LDMDA; break;
            case MM_DB: ldmop = OP_LDMDB; break;
        }
        if (op == J_STM || op == J_STMW)
            ldmop -= OP_LDMIA - OP_STMIA;
        else
            KillKnownRegisterValues(r3);
        if (op == J_STMW || op == J_LDMW)
            ldmop += F_WRITEBACK;
        if (flags & SET_CC) ldmop += F_PSR;
        ldm_flush();
        out_ldm_instr(ldmop | F_RN(r1) | r3);
        peep &= ~(P_SETCC | P_CMPZ);
        break;
    }

case J_CDP:
    outinstr(OP_CDP | r4);
    break;
case J_MRC:
    outinstr(OP_MRC | r4 | F_RD(r1));
    break;
case J_MCR:
    outinstr(OP_MCR | r4 | F_RD(r1));
    break;
case J_LDC:
case J_LDCW:
case J_STC:
case J_STCW:
    {
        uint32 op = OP_LDC | F_UP;
        if (OPCODE(flags) == A_STC) op = OP_STC | F_UP;
        if (r3 < 0) r3 = -r3, op ^= F_UP;
        if (flags & M_LONG) op |= F_LONG;
        if (flags & M_WB) op |= F_WB;
        if (flags & M_PREIDX) op |= F_PRE;
        outinstr(op | F_RN(r2) | r3 | r4);
    }
    break;

#endif
case J_USE:
case J_VSTORE:
        ldm_flush();
case J_USEF:
case J_USED:
        break;

case J_INLINE1:
        syserr(syserr_inline1);
        break;

case J_CLRC+J_ALIGN4:
case J_MOVC+J_ALIGN4:
case J_PUSHC+J_ALIGN4:
        ldm_flush();
        {   RealRegister loopreg = NoRegister;
            int32 regs;
            unsigned rcount;
            unsigned count = (unsigned)r3 / 4;
            bool useloop = r3 > MOVC_LOOP_THRESHOLD;
            /* That is, we are prepared to compile 3 load+store pairs.  This
               number is also used in regalloc (for number of registers
               believed corrupted) and flowgraf (for conditionalisability).
               Later, we may revise our ideas about whether a loop is
               indicated.
             */
            J_OPCODE baseop = op & J_TABLE_BITS;
            int32 ldm, stm;
            bool ismove = (baseop != J_CLRC);

            p->ic.r4.i |= spareregs;
            regs = movc_workregs(p);
            rcount = bitcount(regs);
            if (baseop == J_PUSHC)
                ldm = OP_LDMDB | F_WRITEBACK, stm = OP_STMDB | F_WRITEBACK;
            else if (peep & P_POST)
                ldm = OP_LDMIA | F_WRITEBACK, stm = OP_STMIA;
            else
                ldm = OP_LDMIA, stm = OP_STMIA;
            if (useloop) {
                if ( (ismove && count <= 3*rcount) ||
                     (count <= 4*rcount))
                    useloop = NO;
                else
                {
                 /* We really do want to compile a loop - we will need
                    a register for the count. We take an arbitrary
                    register from the work registers.
                  */
                    uint32 rbit = regs & -regs;
                    rcount--;
                    loopreg = logbase2(rbit);
                    regs ^= rbit;
                    KillKnownRegisterValues(rbit);
                }
            }
            {   /* Remove unneeded registers if the register count either
                   exeeds ldm_regs_max or rcount. Update the register set
                   used by this function.
                */
                int i, num_instr;
                if (count < ldm_regs_max)
                    i = rcount - count;
                else
                    i = rcount - ldm_regs_max;
                if (i > 0)
                {   rcount -= i;
                    regs = LSBits(regs, rcount);
                }
                regmask |= regs;
                KillKnownRegisterValues(regs);
                /* Count the number of instructions required to be sure we dump the
                   literal pool before it overflows.
                   A loop takes 4 instr max, plus max 3 for loading the loop counter
                   No loop: max 3*2 or 4*1 instr. CLRC needs an additional rcount instr
                   to initialize the registers to zero. Thus 7 for MOVC & PUSHC,
                   rcount+6 for CLRC.
                */
                num_instr = ismove ? 7 : rcount + 6;
                if (codep + 4*num_instr >= mustlitby) dumplits2(YES);
            }
            if (!ismove) {
                int32 i = R_A1;
                for (; i <= R_LR; i++)
                    if (regs & regbit(i))
                        load_integer(i, 0, 0);
            }

            if (!useloop)
                for (; count > rcount; count -= rcount) {
                    if (ismove && count == rcount+1 && rcount < ldm_regs_max &&
                        (dataflow & J_DEAD_R2) && !(peep & P_POST)) {
                        rcount++; regs |= regbit(r2);
                        ldm &= ~F_WRITEBACK;
                        break;
                    }
                    if (ismove)
                        out_ldm_instr(ldm | F_WRITEBACK | F_RN(r2) | regs);
                    out_ldm_instr(stm | F_WRITEBACK | F_RN(r1) | regs);
                }
            else {
                LabelNumber *lab = nextlabel();
                unsigned n = count / rcount;
                count = count % rcount;
                load_integer(loopreg, n, 0);
                setlabel(lab);
                if (ismove)
                    out_ldm_instr(ldm | F_WRITEBACK | F_RN(r2) | regs);
                out_ldm_instr(stm | F_WRITEBACK | F_RN(r1) | regs);
                add_integer(loopreg, loopreg, -1, P_CMPZ);
                conditional_branch_to(Q_NE, lab, NO, 0);
            }
            if (count > 0) {
                regs = LSBits(regs, count);
                if (ismove)
                    outinstr(ldm | F_RN(r2) | regs);
                outinstr(stm | F_RN(r1) | regs);
            }
        }
        peep &= ~(P_POST);
        break;

case J_CMPFK:
case J_CMPDK:
case J_CMPFR:
case J_CMPDR:
        ldm_c_flush(regs_used(&regusage), 1);
        fp_gen->show(p);
        illbits = peep = 0;     /* already checked in show_fp */
        break;
#ifdef RANGECHECK_SUPPORTED
case J_CHKNEFR:
case J_CHKNEDR:
        ldm_flush();
        fp_gen->show(p);
        illbits = peep = 0;     /* already checked in show_fp */
        break;
#endif

#ifdef TARGET_HAS_DATA_VTABLES
case J_WORD_ADCON:
        obj_symref((Symstr *)r3, xr_code, 0);
        AddCodeXref4(X_absreloc | codebase+codep, (Symstr *)r3, 0);
        outcodeword(0, LIT_ADCON);
        break;

case J_WORD_LABEL:
        addfref_((LabelNumber *)r3, codep | LABREF_WORD32);
        outcodeword(0, LIT_ADCON);
        break;
#endif

case J_TYPECASE:
        break;

default:
        ldm_c_flush(regs_used(&regusage), 0);
        fp_gen->show(p);
        illbits = peep = 0;     /* already checked in show_fp */
        break;
    }
    if (localcg_debug(4))
        cc_msg("              use %4lx def %4lx corrupt %4lx spare %4lx",
               (long)regusage.use, (long)regusage.def, (long)regusage.corrupt, (long)spareregs);
    UpdateRegisters(&regusage, regflags);
    if (localcg_debug(4))
        cc_msg(" -> spare %4lx\n", (long)spareregs);

#ifdef PARANOID_CONSISTENCY_CHECK
    {   /* Consistency check on spareregs: kill the values in all free regs... */
        /* BEWARE: For debugging purposes only as it affects code quality... */
        if (spareregs != 0 && ((op & J_TABLE_BITS) != J_CASEBRANCH) &&
            ((op & J_TABLE_BITS) != J_BXX))
            out_ldm_instr (OP_LDMIA | F_RN(R_PC) | spareregs);
    }
#endif
    if (illbits | peep)
        syserr(syserr_jop_mode, (long)op, (long)peep);
}

static Uint saved_fpreg_words;
static Uint fp_arg_words;

#define NFPLITERALS 16

typedef struct {
    FloatCon *val;
    int32 immop;
} FPLiteral;

static FPLiteral fpliterals[NFPLITERALS] = {
    {NULL, 0 | F_CONSTOP}, {NULL, 1 | F_CONSTOP}, {NULL, 2 | F_CONSTOP}, {NULL, 3 | F_CONSTOP},
    {NULL, 4 | F_CONSTOP}, {NULL, 5 | F_CONSTOP}, {NULL, 6 | F_CONSTOP}, {NULL, 7 | F_CONSTOP},
    {NULL, 0 | F_CONSTOP}, {NULL, 1 | F_CONSTOP}, {NULL, 2 | F_CONSTOP}, {NULL, 3 | F_CONSTOP},
    {NULL, 4 | F_CONSTOP}, {NULL, 5 | F_CONSTOP}, {NULL, 6 | F_CONSTOP}, {NULL, 7 | F_CONSTOP}
};

static int32 posfpliteral(FloatCon const *val)
{
    int i;
    if (fpu_type == fpu_fpa)
      for ( i = 0 ; i != NFPLITERALS ; i++ )
        if (fpliterals[i].val->floatlen == (val->floatlen & TYPEDEFINHIBITORS) &&
            fpliterals[i].val->floatbin.irep[0] == val->floatbin.irep[0] &&
            ( (val->floatlen & bitoftype_(s_short)) ||
              fpliterals[i].val->floatbin.irep[1] == val->floatbin.irep[1]))
           return fpliterals[i].immop;
    return 0;
}

static int32 negfpliteral(FloatCon const *val)
{
    int i;
    if (fpu_type == fpu_fpa)
      for ( i = 0 ; i != NFPLITERALS ; i++ )
        if (fpliterals[i].val->floatlen == (val->floatlen & TYPEDEFINHIBITORS) &&
            (fpliterals[i].val->floatbin.irep[0] ^ 0x80000000) == (uint32)val->floatbin.irep[0] &&
            ( (val->floatlen & bitoftype_(s_short)) ||
              fpliterals[i].val->floatbin.irep[1] == val->floatbin.irep[1]))
           return fpliterals[i].immop;
    return 0;
}

bool fpliteral(FloatCon const *val, J_OPCODE op)
{
    int32 n = posfpliteral(val);
    if ( n != 0 &&
          /* disgusting bodge to ensure we can't fall foul of FPE bug -
             MULxK x, x, #0.0 non-functional
             This case should never arise, anyhow
           */
         !(n == F_CONSTOP && (op == J_MULFK || op == J_MULDK)))
        return YES;
    /* -ve cases also valid for ADDxK/SUBxK */
    if ((op == J_ADDFK || op == J_SUBFK ||
         op == J_ADDDK || op == J_SUBDK) && negfpliteral(val)) return YES;
    return NO;
}

static int32 checkfreg(RealRegister r)
{
    if (r < R_F0) /* already checked to be <= R_F7 */
        syserr(syserr_gen_freg, (long)r);
    return r & 0xf;
}


static void fpa_show(const PendingOp *p)
{   struct DispDesc dispdesc;
    J_OPCODE op = p->ic.op;
    RealRegister r1 = p->ic.r1.i, r2 = p->ic.r2.i, r3 = p->ic.r3.i;
    int peep = p->peep;
    int32 w, illbits;
    illbits = op & (Q_MASK | J_SIGNED | J_UNSIGNED | J_NEGINDEX | J_SHIFTMASK);
    switch (op & ~(Q_MASK | J_SIGNED | J_UNSIGNED | J_NEGINDEX | J_SHIFTMASK))
    {

/* Now the floating point part of the instruction set */
/* This is a version for FPE2 */
#define cpprepost(op) \
    ((peep & P_POST) ? (peep &= ~P_POST, OP_CPPOST | F_WRITEBACK) : \
     (peep & P_PRE) ? (peep &= ~P_PRE, OP_CPPRE | F_WRITEBACK) : OP_CPPRE)
case J_PUSHD:
        {
            ldm_flush();
            outinstr(OP_CPPRE | F_DOWN | F_WRITEBACK | F_STR |
                            F_RN(R_SP) | F_RD(checkfreg(r1)) | F_DOUBLE | 2);
            adjustipvalue(R_SP, R_SP, -8);
        }
        break;
case J_PUSHF:
        {
            ldm_flush();
            outinstr(OP_CPPRE | F_DOWN | F_WRITEBACK | F_STR |
                            F_RN(R_SP) | F_RD(checkfreg(r1)) | F_SINGLE | 1);
            adjustipvalue(R_SP, R_SP, -4);
        }
        break;
case J_MOVFK:
case J_MOVDK:       /* load single & double literals the same way        */
        {   int32 imm = posfpliteral((FloatCon *) r3);
            if (imm != 0) {
                outinstr(OP_CPOP | F_MVF | CPDO_FLTOFJ(op) |
                         F_RD(checkfreg(r1)) | imm);
                break;
            }
            if ((imm = negfpliteral((FloatCon *) r3)) != 0) {
                outinstr(OP_CPOP | F_MNF | CPDO_FLTOFJ(op) |
                         F_RD(checkfreg(r1)) | imm);
                break;
            }
        }
        /* Otherwise, drop through to create a FP literal */
case J_ADCONF:
case J_ADCOND:
        ldm_flush();
/* I do so hope very much that these instructions are used in a          */
/* compatible way wrt floating point operands.                           */
        {   FloatCon *fc = (FloatCon *)r3;
            int size = (op==J_MOVDK || op==J_ADCOND) ? 2 : 1;
            int32 direction = F_UP, adconop = OP_ADDN;
            int32 disp = lit_findwordsincurpool(fc->floatbin.irep, size, LIT_FPNUM);
            if (disp < 0) {
                disp = lit_findwordsinprevpools(fc->floatbin.irep, size, LIT_FPNUM,
                          codebase+codep+8-1020);
                if (disp >= 0) {
                    disp = codebase+codep+8-disp;
                    direction = F_DOWN, adconop = OP_SUBN;
                } else {
                    addressability(256);
                    if (size == 1)
                        disp = lit_findwordaux(fc->floatbin.fb.val,
                                  LIT_FPNUM, fc->floatstr,
                                  LITF_INCODE|LITF_FIRST|LITF_LAST);
                    else {
                        (void)lit_findwordaux(fc->floatbin.db.msd,
                                  LIT_FPNUM1, fc->floatstr,
                                  LITF_INCODE|LITF_FIRST);
                        /* use the second address in case overflow */
                        disp = lit_findwordaux(fc->floatbin.db.lsd,
                                  LIT_FPNUM2, fc->floatstr,
                                  LITF_INCODE|LITF_LAST) - 4;
                    }
                }
            }
            disp >>= 2;
            if (direction == F_UP)
                addfref_(litlab, codep | LABREF_W256);
            if (op == J_ADCONF || op==J_ADCOND)
                outinstr(adconop | F_RD(r1) | F_RN(R_PC) | disp | 0xf00);
            else
                outinstr(OP_CPPRE | F_LDR | CPDT_FLTOFJ(op) | direction |
                          F_RD(checkfreg(r1)) | F_RN(R_PC) | disp);
            break;
        }
case J_CMPFR:
case J_CMPDR:
/* Note that in FPE2 it is not necessary to specify the width of         */
/* numbers to be compared.                                               */
        {   int32 test = op & Q_MASK;
            outinstr(OP_CPOP | ((test==Q_EQ || test==Q_NE) ? F_CMF : F_CMFE) |
                     F_REGOP | F_RN(checkfreg(r2)) | (checkfreg(r3)));
        }
        illbits &= ~Q_MASK;
        break;
case J_MOVFDR:   /* With FPE2 conversion to double is a noop */
        /* drop through */
case J_MOVFR:
case J_MOVDR:
        if (r1==r3) syserr(syserr_remove_fp_noop);
        outinstr(OP_CPOP | F_MVF | F_REGOP | CPDO_FLTOFJ(op) |
                 F_RD(checkfreg(r1)) | (checkfreg(r3)));
        break;
case J_NEGFR:
case J_NEGDR:
        outinstr(OP_CPOP | F_MNF | F_REGOP | CPDO_FLTOFJ(op) |
                 F_RD(checkfreg(r1)) | (checkfreg(r3)));
        break;
case J_FIXDRM:
case J_FIXFRM:   /* signed fix towards minus infinity */
        outinstr(OP_CPOP | F_FIX | CPDO_SINGLE | CPDO_RNDDN | F_RD(r1) |
            checkfreg(r3));
        illbits ^= J_SIGNED;
        break;
case J_FIXFR:
case J_FIXDR:    /* C signed 'fix' is truncate towards zero */
        outinstr(OP_CPOP | F_FIX | CPDO_SINGLE | CPDO_RNDZ | F_RD(r1) |
            checkfreg(r3));
        illbits ^= J_SIGNED;
        break;
case J_FLTFR:
case J_FLTDR:
        outinstr(OP_CPOP | F_FLT | CPDO_FLTOFJ(op) | F_RD(r3) | F_RN(checkfreg(r1)));
        illbits ^= J_SIGNED;   /* only signed version acceptable */
        break;
case J_MOVIFR:
/* Load FP register from an integer one                                  */
        {
            out_ldm_instr(OP_STMFD | F_WRITEBACK | F_RN(R_SP) | regbit(r3));
            outinstr(OP_CPPOST | F_UP | F_LDR | F_WRITEBACK  |
                     F_RN(R_SP) | F_RD(checkfreg(r1)) | F_SINGLE | 1);
        }
        break;
case J_MOVFIR:
/* Load integer register from fp register                                */
        {
            ldm_flush();
            outinstr(OP_CPPRE | F_DOWN | F_STR | F_WRITEBACK |
                     F_RN(R_SP) | F_RD(checkfreg(r3)) | F_SINGLE | 1);
            out_ldm_instr(OP_LDMFD | F_WRITEBACK | F_RN(R_SP) |
                     regbit(r1));
        }
        break;
case J_MOVDIR:
/* Load integer register pair from fp register                           */
        {
            ldm_flush();
            if (r2 <= r1) syserr(syserr_bad_regpair);
            outinstr(OP_CPPRE | F_DOWN | F_STR | F_WRITEBACK |
                     F_RN(R_SP) | F_RD(checkfreg(r3)) | F_DOUBLE | 2);
            outinstr(OP_LDMFD | F_WRITEBACK | F_RN(R_SP) |
                     regbit(r1) | regbit(r2));
        }
        break;
case J_MOVIDM:
/* Load n FP registers from 2n integer registers. r3 holds a bitmap of   */
/* integer registers, r1 a bitmap of the fp registers.                   */
        {
            int32 r;
            ldm_flush();
            out_ldm_instr(OP_STMFD | F_WRITEBACK | F_RN(R_SP) | r3);
            for (r = R_F0; r1 != 0; r++)
                if (r1 & regbit(r)) {
                    outinstr(OP_CPPOST | F_UP | F_LDR | F_WRITEBACK |
                             F_RN(R_SP) | F_RD(checkfreg(r)) | F_DOUBLE | 2);
                    r1 ^= regbit(r);
                }
        }
        break;
case J_MOVDIM:
/* Load 2n integer registers from n FP registers. r3 holds a bitmap of   */
/* fp registers, r1 a bitmap of the integer registers. There may be more */
/* than 2n registers in the r1 map because unconnected individual        */
/* pops (of an object split between registers and stack) may have been   */
/* added.                                                                */
        {
            int32 r;
            int32 netpush = 2 * bitcount(r3) - bitcount(r1);
            ldm_flush();
            for (r = R_F0+NFLTREGS-1; r3 != 0; r--)
                if (r3 & regbit(r)) {
                    outinstr(OP_CPPRE | F_DOWN | F_STR | F_WRITEBACK |
                             F_RN(R_SP) | F_RD(checkfreg(r)) | F_DOUBLE | 2);
                    r3 ^= regbit(r);
                }
            out_ldm_instr(OP_LDMFD | F_WRITEBACK | F_RN(R_SP) | r1);
            adjustipvalue(R_SP, R_SP, -netpush);
            KillKnownRegisterValues(r1);
        }
        break;
case J_MOVIDR:
/* Load FP register from 2 integer registers.  Only happens just after   */
/* function entry, with the integer registers being argument rgisters.   */
/* If arguments have been pushed on the stack, we can load the fp value  */
/* directly.  (It would be nice to ensure that if anything had been      */
/* pushed on entry, the argument registers of the MOVIDR had).           */
        {
            ldm_flush();
            if (r3 <= r2) syserr(syserr_bad_regpair);
            if (!(procflags & PROC_ARGPUSH)) {
                out_ldm_instr(OP_STMFD | F_WRITEBACK | F_RN(R_SP) |
                         regbit(r3) | regbit(r2));
                outinstr(OP_CPPOST | F_UP | F_LDR | F_WRITEBACK |
                         F_RN(R_SP) | F_RD(checkfreg(r1)) | F_DOUBLE | 2);
                break;
            }
            {   int32 addr = BINDADDR_ARG + r2*4;
                op = J_LDRDK;
                r3 = local_addr_a(addr); r2 = local_base_a(addr);
                /* and fall through to handle the load */
            }
        }
case J_LDRFK+J_ALIGN4:
case J_LDRDK+J_ALIGN4:
case J_LDRDK+J_ALIGN8:
case J_STRFK+J_ALIGN4:
case J_STRDK+J_ALIGN4:
case J_STRDK+J_ALIGN8:
        ldm_flush();
        w = loads_r1(op) ? F_LDR : F_STR;
        bigdisp(&dispdesc, r3, 0x3fc, r2);
        w |= dispdesc.u_d, r3 = dispdesc.m, r2 = dispdesc.r;
        outinstr(cpprepost(op) | w | CPDT_FLTOFJ(op) | F_RD(checkfreg(r1)) |
                                                       F_RN(r2) | (r3>>2));
        if (r2 == R_SP && (op & F_WRITEBACK))
            fpdesc_notespchange(dispdesc.u_d == F_DOWN ? r3 : -r3);
        peep &= ~P_BASEALIGNED;
        break;
case J_MOVDFR:  /* Round from double to single precision */
                /* I guess I hope this gives exponent overflow if necessary */
        outinstr(OP_CPOP | F_MVF | F_REGOP | CPDO_SINGLE |
                 F_RD(checkfreg(r1)) | (checkfreg(r3)));
        break;

case J_ADDFR:
case J_ADDDR:
        outinstr(OP_CPOP | F_ADF | F_REGOP | CPDO_FLTOFJ(op) |
                 F_RD(checkfreg(r1)) | F_RN(checkfreg(r2)) | (checkfreg(r3)));
        break;
case J_SUBFR:
case J_SUBDR:
        outinstr(OP_CPOP | F_SUF | F_REGOP | CPDO_FLTOFJ(op) |
                 F_RD(checkfreg(r1)) | F_RN(checkfreg(r2)) | (checkfreg(r3)));
        break;
case J_RSBFR:
case J_RSBDR:
        outinstr(OP_CPOP | F_RSF | F_REGOP | CPDO_FLTOFJ(op) |
                 F_RD(checkfreg(r1)) | F_RN(checkfreg(r2)) | (checkfreg(r3)));
        break;
case J_MULFR:
case J_MULDR:
        outinstr(OP_CPOP | F_MUF | F_REGOP | CPDO_FLTOFJ(op) |
                 F_RD(checkfreg(r1)) | F_RN(checkfreg(r2)) | (checkfreg(r3)));
        break;
case J_DIVFR:
case J_DIVDR:
        outinstr(OP_CPOP | F_DVF | F_REGOP | CPDO_FLTOFJ(op) |
                 F_RD(checkfreg(r1)) | F_RN(checkfreg(r2)) | (checkfreg(r3)));
        break;
case J_RDVFR:
case J_RDVDR:
        outinstr(OP_CPOP | F_RDF | F_REGOP | CPDO_FLTOFJ(op) |
                 F_RD(checkfreg(r1)) | F_RN(checkfreg(r2)) | (checkfreg(r3)));
        break;

case J_ADDFK:
case J_ADDDK:
    {   FloatCon *f = (FloatCon *) r3;
        int32 imm = posfpliteral(f);
        if (imm != 0)
            outinstr(OP_CPOP | F_ADF | CPDO_FLTOFJ(op) |
                     F_RD(checkfreg(r1)) | F_RN(checkfreg(r2)) | imm);
        else if ((imm = negfpliteral(f)) != 0)
            outinstr(OP_CPOP | F_SUF | CPDO_FLTOFJ(op) |
                     F_RD(checkfreg(r1)) | F_RN(checkfreg(r2)) | imm);
        else
            syserr(syserr_fp_const, f->floatbin.irep[0]);
        break;
    }
case J_SUBFK:
case J_SUBDK:
    {   FloatCon *f = (FloatCon *) r3;
        int32 imm = posfpliteral(f);
        if (imm != 0)
            outinstr(OP_CPOP | F_SUF | CPDO_FLTOFJ(op) |
                     F_RD(checkfreg(r1)) | F_RN(checkfreg(r2)) | imm);
        else if ((imm = negfpliteral(f)) != 0)
            outinstr(OP_CPOP | F_ADF | CPDO_FLTOFJ(op) |
                     F_RD(checkfreg(r1)) | F_RN(checkfreg(r2)) | imm);
        else
            syserr(syserr_fp_const, f->floatbin.irep[0]);
        break;
    }
case J_RSBFK:
case J_RSBDK:
        outinstr(OP_CPOP | F_RSF | CPDO_FLTOFJ(op) |
                 F_RD(checkfreg(r1)) | F_RN(checkfreg(r2)) |
                 posfpliteral((FloatCon *) r3));
        break;
case J_MULDK:
case J_MULFK:
        outinstr(OP_CPOP | F_MUF | CPDO_FLTOFJ(op) |
                 F_RD(checkfreg(r1)) | F_RN(checkfreg(r2)) |
                 posfpliteral((FloatCon *) r3));
        break;
case J_DIVFK:
case J_DIVDK:
        outinstr(OP_CPOP | F_DVF | CPDO_FLTOFJ(op) |
                 F_RD(checkfreg(r1)) | F_RN(checkfreg(r2)) |
                 posfpliteral((FloatCon *) r3));
        break;
case J_RDVFK:
case J_RDVDK:
        outinstr(OP_CPOP | F_RDF | CPDO_FLTOFJ(op) |
                 F_RD(checkfreg(r1)) | F_RN(checkfreg(r2)) |
                 posfpliteral((FloatCon *) r3));
        break;
case J_CMPFK:
case J_CMPDK:
        {   int32 test = op & Q_MASK;
            outinstr(OP_CPOP | ((test==Q_EQ || test==Q_NE) ? F_CMF : F_CMFE) |
                     F_RN(checkfreg(r2)) | posfpliteral((FloatCon *) r3)); }
        illbits &= ~Q_MASK;
        break;

case J_INLINE1F:
case J_INLINE1D:
        outinstr(r3 | F_RD(checkfreg(r1)) | (checkfreg(r2)));
        break;

#ifdef RANGECHECK_SUPPORTED
case J_CHKNEFR:
case J_CHKNEDR:
        outinstr(OP_CPOP | F_CMF | F_REGOP | F_RN(checkfreg(r2)) | (checkfreg(r3)));
        outinstr3(OP_BL ^ Q_EQ, sim.valfault, 0);
        break;
#endif

default:
        syserr(syserr_show_inst_dir, (long)op);
        illbits = 0;
        break;
    }
    if (illbits | peep) syserr(syserr_jop_mode, (long)op, (long)peep);
#undef cpprepost
}

static int32 amp_checkfreg(RealRegister r)
{
    if (r < R_F0) /* already checked to be <= R_F7 */
        syserr(syserr_gen_freg, (long)r);
    return r - R_F0 + AMP_F0;
}

static void amp_show(const PendingOp *p)
{   struct DispDesc dispdesc;
    J_OPCODE op = p->ic.op;
    RealRegister r1 = p->ic.r1.i, r2 = p->ic.r2.i, r3 = p->ic.r3.i;
    int peep = p->peep;
    int32 w, illbits;
    illbits = op & (Q_MASK | J_SIGNED | J_UNSIGNED | J_NEGINDEX | J_SHIFTMASK);
    switch (op & ~(Q_MASK | J_SIGNED | J_UNSIGNED | J_NEGINDEX | J_SHIFTMASK))
    {
/* Now the floating point part of the instruction set */
#define cpprepost(w) \
    ((peep & P_POST) ? (peep &= ~P_POST, w | CPDT_POST) : \
     (peep & P_PRE) ? (peep &= ~P_PRE, w | CPDT_PRE | CPDT_WB) : w | CPDT_PRE)
case J_PUSHF:
        ldm_flush();
        outinstr(AMP_DT(CPDT_PRE | CPDT_DOWN | CPDT_WB | CPDT_ST,
                        R_SP, amp_checkfreg(r1), 4));
        adjustipvalue(R_SP, R_SP, -4);
        break;
case J_MOVFK:
case J_ADCONF:
case J_ADCOND:
/* Although AMP supports only single-precision floating point, ADCONDs   */
/* can still arise (via software floating point) from use of doubles.    */
/* (but MOVDKs can't)                                                    */
        ldm_flush();
        {   FloatCon *fc = (FloatCon *)r3;
            int size = (op==J_ADCOND) ? 2 : 1;
            int32 direction = CPDT_UP, adconop = OP_ADDN;
            int32 disp = lit_findwordsincurpool(fc->floatbin.irep, size, LIT_FPNUM);
            if (disp < 0) {
                disp = lit_findwordsinprevpools(fc->floatbin.irep, size, LIT_FPNUM,
                          codebase+codep+8-1020);
                if (disp >= 0) {
                    disp = codebase+codep+8-disp;
                    direction = CPDT_DOWN, adconop = OP_SUBN;
                } else {
                    addressability(256);
                    if (size == 1)
                        disp = lit_findwordaux(fc->floatbin.fb.val,
                                  LIT_FPNUM, fc->floatstr,
                                  LITF_INCODE|LITF_FIRST|LITF_LAST);
                    else {
                        (void)lit_findwordaux(fc->floatbin.db.msd,
                                  LIT_FPNUM1, fc->floatstr,
                                  LITF_INCODE|LITF_FIRST);
                        /* use the second address in case overflow */
                        disp = lit_findwordaux(fc->floatbin.db.lsd,
                                  LIT_FPNUM2, fc->floatstr,
                                  LITF_INCODE|LITF_LAST) - 4;
                    }
                }
            }
            if (direction == CPDT_UP)
                addfref_(litlab, codep | LABREF_W256);
            if (op == J_ADCONF || op==J_ADCOND)
                outinstr(adconop | F_RD(r1) | F_RN(R_PC) | (disp >> 2) | 0xf00);
            else
              outinstr(AMP_DT(CPDT_LD | CPDT_PRE | direction, R_PC, amp_checkfreg(r1), disp));
            break;
        }
case J_CMPFR:
/* Note that in FPE2 it is not necessary to specify the width of         */
/* numbers to be compared.                                               */
        {   int32 test = op & Q_MASK;
            int32 fop = test==Q_EQ || test==Q_NE ? AMP_FCMPEQ :
                        test==Q_LT || test==Q_GE ? AMP_FCMPLT :
                                                   AMP_FCMPLE;
            outinstr(AMP_TCM_EXU(fop, AMP_WorkReg, amp_checkfreg(r2), amp_checkfreg(r3)));
            outinstr(AMP_MRC(MCR_32, R_IP, AMP_WorkReg));
            outinstr(OP_RSBN | F_SCC | F_RD(R_IP) | F_RN(R_IP) | (test==Q_LT || test==Q_GE ? 0 : 1));
            DestroyIP();
        }
        illbits &= ~Q_MASK;
        break;
case J_MOVFR:
        if (r1==r3) syserr(syserr_remove_fp_noop);
        outinstr(AMP_TCM_EXU(AMP_FMAX, amp_checkfreg(r1), amp_checkfreg(r3), amp_checkfreg(r3)));
        break;
case J_NEGFR:
        outinstr(AMP_TCM_EXU(AMP_FSUB, amp_checkfreg(r1), AMP_ZeroReg, amp_checkfreg(r3)));
        break;
case J_FIXFR:
case J_FIXFRM:
        outinstr(AMP_TCM_MBU(AMP_MFCSR, AMP_WorkReg, 0, AMP_FPCR));
        outinstr(AMP_MRC(MCR_32, R_IP, AMP_WorkReg));
        and_integer(r1, R_IP, ~AMP_FPCR_RND, 0, NO);
        orr_integer(r1, r1, (op & J_TABLE_BITS == J_FIXFR ? AMP_FPCR_RND_Z : AMP_FPCR_RND_D), 0);
        outinstr(AMP_MCR(MCR_32, r1, AMP_WorkReg));
        outinstr(AMP_TCM_MBU(AMP_MTCSR, 0, AMP_WorkReg, AMP_FPCR));
        outinstr(AMP_TCM_EXU(AMP_FCVTFI, AMP_WorkReg, amp_checkfreg(r3), AMP_ZeroReg));
        outinstr(AMP_MRC(MCR_32, r1, AMP_WorkReg));
        outinstr(AMP_MCR(MCR_32, R_IP, AMP_WorkReg));
        outinstr(AMP_TCM_MBU(AMP_MTCSR, 0, AMP_WorkReg, AMP_FPCR));
        illbits ^= J_SIGNED;   /* only signed version acceptable */
        break;
case J_FLTFR:
        outinstr(AMP_MCR(MCR_32, r3, AMP_WorkReg));
        outinstr(AMP_TCM_EXU(AMP_FCVTIF, amp_checkfreg(r1), AMP_WorkReg, AMP_ZeroReg));
        illbits ^= J_SIGNED;   /* only signed version acceptable */
        break;
case J_MOVIFR:
/* Load FP register from an integer one                                  */
        outinstr(AMP_MCR(MCR_32, r3, amp_checkfreg(r1)));
        break;
case J_MOVFIR:
/* Load integer register from fp one                                     */
        outinstr(AMP_MRC(MCR_32, r1, amp_checkfreg(r3)));
        break;
case J_LDRFK+J_ALIGN4:
case J_STRFK+J_ALIGN4:
        ldm_flush();
        w = loads_r1(op) ? CPDT_LD : CPDT_ST;
        bigdisp(&dispdesc, r3, 0x3fc, r2);
        w |= dispdesc.u_d, r3 = dispdesc.m, r2 = dispdesc.r;
        outinstr(AMP_DT(cpprepost(w), r2, amp_checkfreg(r1), r3));
        if (r2 == R_SP && (op & F_WRITEBACK))
            fpdesc_notespchange(dispdesc.u_d == F_DOWN ? r3 : -r3);
        peep &= ~P_BASEALIGNED;
        break;
case J_ADDFR:
        outinstr(AMP_TCM_EXU(AMP_FADD, amp_checkfreg(r1), amp_checkfreg(r2), amp_checkfreg(r3)));
        break;
case J_SUBFR:
        outinstr(AMP_TCM_EXU(AMP_FSUB, amp_checkfreg(r1), amp_checkfreg(r2), amp_checkfreg(r3)));
        break;
case J_RSBFR:
        outinstr(AMP_TCM_EXU(AMP_FSUB, amp_checkfreg(r1), amp_checkfreg(r3), amp_checkfreg(r2)));
        break;
case J_MULFR:
        outinstr(AMP_TCM_EXU(AMP_FMUL0, amp_checkfreg(r1), amp_checkfreg(r2), amp_checkfreg(r3)));
        break;
case J_DIVFR:
        outinstr(AMP_TCM_EXU(AMP_FDIV, 0, amp_checkfreg(r2), amp_checkfreg(r3)));
        outinstr(AMP_TCM_EXU(AMP_FMFQ, amp_checkfreg(r1), 0, 0));
        break;
case J_RDVFR:
        outinstr(AMP_TCM_EXU(AMP_FMUL0, 0, amp_checkfreg(r3), amp_checkfreg(r2)));
        outinstr(AMP_TCM_EXU(AMP_FMFQ, amp_checkfreg(r1), 0, 0));
        break;

#ifdef RANGECHECK_SUPPORTED
case J_CHKNEFR:
        DestroyIP();
        outinstr(AMP_TCM_EXU(AMP_FCMPEQ, AMP_WorkReg, amp_checkfreg(r2), amp_checkfreg(r3)));
        outinstr(AMP_MRC(MCR_32, R_IP, AMP_WorkReg));
        outinstr(OP_RSBN | F_SCC | F_RD(R_IP) | F_RN(R_IP) | 1);
        outinstr3(OP_BL ^ Q_EQ, sim.valfault, 0);
        break;
#endif

default:
        syserr(syserr_show_inst_dir, (long)op);
        illbits = 0;
        break;
    }
    if (illbits | peep) syserr(syserr_jop_mode, (long)op, (long)peep);
#undef cpprepost
}

int32 power_of_two(int32 n)
{
/* If n is an exact power of two this returns the power, else -1         */
    if (n == 0 || n != (n&(-n))) return -1;
    return logbase2(n);
}

bool ImmediateOperand(int32 n, J_OPCODE op)
{
    switch (op & J_TABLE_BITS) {
    case J_ADDK:
    case J_SUBK:
    case J_CMPK: return Arm_EightBits(n) >= 0 || Arm_EightBits(-n) >= 0;
    case J_ANDK:
    case J_MOVK: return Arm_EightBits(n) >= 0 || Arm_EightBits(~n) >= 0;
    case J_ORRK:
    case J_EORK: return Arm_EightBits(n) >= 0;
    default:     return NO;
    }
}

static void describe_literal_pool(void) {
    if (!in_code) {
        if (codebase+codep != literal_pool_start) {
            char b[32];
            sprintf(b, "x$litpool$%d", literal_pool_number);
            obj_symref(sym_insert_id(b), xr_code+xr_defloc+xr_dataincode, literal_pool_start);
            sprintf(b, "x$litpool_e$%d", literal_pool_number++);
            obj_symref(sym_insert_id(b), xr_code+xr_defloc+xr_dataincode, codebase+codep-1);
        }
        in_code = YES;
    }
}

/* although the idea of setlabel is machine independent, it stays here
   because it back-patches code.  In the long term setlabel should be
   in codebuf.c and call a machine dependent backpatch routine.
*/
void setlabel(LabelNumber *l)
{
    List *p = l->u.frefs;
    Symstr *labname = NULL;
    for (; p!=NULL; p = (List*) discard2(p))
    {   int32 v = car_(p);
        int32 q = (v & 0x00ffffff);   /* BYTE address */
        int32 w = code_inst_(q);
        unsigned32 d;
        switch (v & 0xff000000)
        {
    case LABREF_BRANCH:   /* Bxx instruction */
/* note the assumption that the address field contained zero */
            d = (codep-q-8 >> 2) & 0x00ffffffL;
            w = (w & 0xff000000) | d;
            break;
    case LABREF_B4096:    /* LDR r1, [pc, #nn] forward ref */
            d = (codep-q-8) + (w & 0xfff);
            if (d >= 0x1000) syserr(syserr_displacement, (long)d);
            w = (w & 0xfffff000) | d;
            break;
    case LABREF_W256:     /* ADD r1, pc, #nn  with nn shifted left 2 bits */
                          /* LDFD f1, [pc, #nn] - again nn is a word offset */
            d = (codep-q-8 >> 2) + (w & 0xff);
            if (d >= 0x100) syserr(syserr_displacement, (long)d);
            w = (w & 0xffffff00) | d;
            break;
#ifdef TARGET_HAS_DATA_VTABLES
    case LABREF_WORD32: { /* DCD L<N> */
            if (labname == NULL) {
                char b[256];
                sprintf(b, "L%.6lx.J%ld.%s", codebase+codep, lab_name_(l) & 0x7fffffff, symname_(currentfunction.symstr));
                labname = sym_insert_id(b);
                obj_symdef(labname, xr_code+xr_defloc, codebase+codep);
            }
            AddCodeXref4(X_absreloc | codebase+q, labname, 0);
            break;
        }
#endif
    default:
            syserr(syserr_unknown_label, (long)v);
        }
        code_inst_(q) = w;
    }
    lab_setloc_(l, codep | 0x80000000); /* cheapo union checker for ->frefs */
    asm_lablist = (LabList *) syn_cons2((VoidStar) asm_lablist, (VoidStar) l);
    if (l != litlab) describe_literal_pool();
}

static void move_register(RealRegister r1, RealRegister r2, int32 scc)
{   /* r1 = r2    */
    if (r1!=r2 || scc!=0) outinstr(OP_MOVR | scc | F_RD(r1) | r2);
}

static void negate_register(RealRegister r1, RealRegister r2, int32 scc)
{   /*  r1 = -r2  */
    outinstr(OP_RSBN | scc | F_RD(r1) | F_RN(r2));
}

static int32 *adc_integer_i(RealRegister r1, RealRegister r2, int32 n,
                            int32 scc, int32 *v)
{ /* Generate code for r1 = r2 + n + carry.                              */
    int32 packed;

    packed = Arm_EightBits(n);
    if (packed>=0)
    {   *v++ = (OP_ADCN | scc | F_RD(r1) | F_RN(r2) | packed);
        return v;
    }
    packed = Arm_EightBits(~n);     /* ADC x,y,#N is equivalent SBC x,y,#NOT N ! */
    if (packed>=0)
    {   *v++ = (OP_SBCN | scc | F_RD(r1) | F_RN(r2) | packed);
        return v;
    }
    {   ValueDesc vd;
        int rc = RegisterContainingValue(n, V_Inverted+V_AnyShift, &vd);
        if (rc != 0) {
            int32 w = F_RD(r1) | F_RN(r2) | scc | vd.r | vd.op3.shift;
            if (rc == V_Inverted)
                w |= OP_SBCR;
            else
                w |= OP_ADCR;
            *v++ = w;
            return v;
        }
    }
/*
 * here it will take at least two instructions...
 */
    {   int32 op;
        int32 n1 = Arm_SplitForAdd(r1, n, &op);
        if (op == OP_SUBN)
            n += n1;
        else
            n -= n1;
        *v++ = (op | F_RD(r1) | F_RN(r2) | Arm_EightBits(n1));
        return adc_integer_i(r1, r1, n, scc, v);
    }
}

static void add_integer(RealRegister r1, RealRegister r2, int32 n, int32 flags)
{   int32 v[4];
    int32 *ve;
    int32 *p;

    ve = arm_add_integer(r1, r2, n, SCC_of_PEEP(flags), RegisterContainingValue, v);
    if (ve - v > 1 && (flags & P_SETCC)) {      /* correct overflow & carry flags required */
        load_integer(R_IP, n, 0);
        outinstr (OP_ADDR | SCC_of_PEEP (flags) | F_RD(r1) | F_RN(r2) | R_IP);
        return;
    }
    for (p = &v[0]; p != ve; p++) {
        int32 w = *p;
        outinstr(w);
        if (r1 == R_SP) {
            int32 op = w & F_DPOP;
            int32 n = w & 0xff;
            int32 sh = 2 * ((w >> 8) & 0xf);
            n = ROR(n, sh);
            if (op == F_ADD)
                fpdesc_notespchange(-n);
            else if (op == F_SUB)
                fpdesc_notespchange(n);
        }
    }
}

static void sub_integer(RealRegister r1, RealRegister r2, int32 n, int32 flags)
{   int32 packed = Arm_EightBits(n);

    if (packed >= 0) {
        outinstr(OP_SUBN | SCC_of_PEEP(flags) | F_RD(r1) | F_RN(r2) | packed);
    } else if (flags & P_SETCC) {
        load_integer(R_IP, n, 0);
        outinstr(OP_SUBR | SCC_of_PEEP(flags) | F_RD(r1) | F_RN(r2) | R_IP);
    } else
        add_integer(r1, r2, -n, flags);
}

static void adc_integer(RealRegister r1, RealRegister r2, int32 n, int32 flags)
{   int32 v[4];
    int32 *ve;
    int32 *p;

    ve = adc_integer_i(r1, r2, n, SCC_of_PEEP(flags), v);
    if (ve - v > 1 && (flags & P_SETCC)) {      /* correct overflow & carry flags required */
        load_integer(R_IP, n, 0);
        outinstr(OP_ADCR | SCC_of_PEEP(flags) | F_RD(r1) | F_RN(r2) | R_IP);
        return;
    }
    for (p = &v[0]; p != ve; p++) {
        int32 w = *p;
        outinstr(w);
    }
}

static void sbc_integer(RealRegister r1, RealRegister r2, int32 n, int32 flags)
{   int32 packed = Arm_EightBits(n);

    if (packed >= 0) {
        outinstr(OP_SBCN | SCC_of_PEEP(flags) | F_RD(r1) | F_RN(r2) | packed);
    } else if (flags & P_SETCC) {
        load_integer(R_IP, n, 0);
        outinstr(OP_SBCR | SCC_of_PEEP(flags) | F_RD(r1) | F_RN(r2) | R_IP);
    } else
        adc_integer(r1, r2, ~n, flags);
}


static void rsb_integer(RealRegister r1, RealRegister r2, int32 n, int32 flags)
{ /* Generate code for r1 = n - r2.                                      */
    int32 packed = Arm_EightBits(n);
    int32 scc = SCC_of_PEEP (flags);
    if (packed >= 0)
        outinstr(OP_RSBN | scc | F_RD(r1) | F_RN(r2) | packed);
    else if (flags & P_SETCC) {
        load_integer(R_IP, n, 0);
        outinstr(OP_RSBR | scc | F_RD(r1) | F_RN(r2) | R_IP);
    } else {
        ValueDesc vd;
        int rc = RegisterContainingValue(n, V_AnyShift, &vd);
        if (rc != 0) {
            outinstr(OP_RSBR | scc | F_RD(r1) | F_RN(r2) | vd.r | vd.op3.shift);
        } else {
            int32 tail = 0x3, mask = 0xff;
            while ((n & tail)==0) tail = tail << 2, mask = mask << 2;
            mask &= n;
            n -= mask;
            outinstr(OP_RSBN | F_RD(r1) | F_RN(r2) | Arm_EightBits(mask));
            add_integer(r1, r1, n, flags);
        }
    }
}

static void rsc_integer(RealRegister r1, RealRegister r2, int32 n, int32 flags)
{ /* Generate code for r1 = n - r2 + carry.                              */
    int32 packed = Arm_EightBits(n);
    int32 scc = SCC_of_PEEP (flags);
    if (packed >= 0)
        outinstr(OP_RSCN | scc | F_RD(r1) | F_RN(r2) | packed);
    else if (flags & P_SETCC) {
        load_integer(R_IP, n, 0);
        outinstr(OP_RSCR | scc | F_RD(r1) | F_RN(r2) | R_IP);
    } else {
        ValueDesc vd;
        int rc = RegisterContainingValue(n, V_AnyShift, &vd);
        if (rc != 0) {
            outinstr(OP_RSCR | scc | F_RD(r1) | F_RN(r2) | vd.r | vd.op3.shift);
        } else {
            int32 tail = 0x3, mask = 0xff;
            while ((n & tail)==0) tail = tail << 2, mask = mask << 2;
            mask &= n;
            n -= mask;
            outinstr(OP_RSCN | F_RD(r1) | F_RN(r2) | Arm_EightBits(mask));
            add_integer(r1, r1, n, flags);
        }
    }
}

static int32 *load_integer_i(RealRegister r, int32 n, int32 scc, int32 *v);

static int32 *symmetricload(RealRegister r, uint32 n, uint32 mask,
                            int shift, int32 scc, int32 *v)
{
    int c;
    for (c = 0 ; c < shift ; mask <<= 2, c += 2) {
        int k;
        for (k = 1-shift ; k < shift ; k++)
            if ((n & mask) == ROR((n & ~mask), shift+k)) {
                v = load_integer_i(r, n & mask, 0, v);
                *v++ = (OP_ADDR | scc | F_RD(r) | F_RN(r) | r | K_ROR(32L-shift-k));
                return v;
             }
     }
     return v;
}

static int32 *load_integer_i(RealRegister r, int32 n, int32 scc, int32 *v)
{ /* Set register r to the integer n, setting condition codes on scc     */

    int32 op = OP_MOVN, packed = Arm_EightBits(n);
    ValueDesc vd;
    int rc;
    if (packed<0) op = OP_MVNN, packed = Arm_EightBits(~n);
    if (packed>=0) {
        *v++ = (op | F_RD(r) | scc | packed);
        return v;
    }
    if ((rc = RegisterContainingValue(n, V_KAdded+V_Orred+V_Inverted+V_AnyShift+V_RegPair, &vd)) != 0) {
        int32 w = F_RD(r) | scc;
        if (rc == V_Inverted)
            w |= OP_MVNR | vd.r | vd.op3.shift;
        else if (rc == V_Orred)
            w |= OP_ORRR | F_RN(vd.r) | vd.r | vd.op3.shift;
        else if (rc == V_KAdded || rc == V_RegPair)
            w |= vd.op3.add.op | F_RN(vd.r) | vd.op3.add.k;
        else if (vd.r != r || vd.op3.shift != 0)
            w |= OP_MOVR | vd.r | vd.op3.shift;
        else
            return v;
        *v++ = w;
        return v;
    } else {
        int32 pos1 = 0, size1 = 0, value1 = -1;
        int32 pos2 = 0, size2 = 0, value2 = -1;
        int32 startsize = 0, startvalue = -1;
        int32 pos = 0, value = -1, start = -1;
        int32 mask = 3;
        /* find the two longest strings of pairs of 00 or 11 (on an even bit
           boundary), setting sizen to the number of bits, posn to the ls bit,
           valuen to 0 for 00, 1 for 11 (n=1 longest)
         */
        for ( ; pos <= 32; mask = mask<<2, pos += 2) {
            int32 newvalue = mask == 0            ? -1 :
                             ((n & mask) == mask) ? 3 :
                             ((n & mask) == 0)    ? 0 :
                                                    -1;
            if (value != newvalue) {
                if (value != -1) {
                    int32 size = pos - start;
                    if (start == 0) {
                        startsize = size;
                        startvalue = value;
                        /* disregard a string in the ls bits if these are the
                           same as the ms bits (it will be included in the
                           string including the ms bits).
                         */
                        if (((n >> 30) & 3) == value) size = -1;
                    }
                    if (pos == 32 && value == startvalue)
                        size += startsize;
                    if (size >= size1) {
                        pos2 = pos1; size2 = size1; value2 = value1;
                        size1 = size; pos1 = start; value1 = value;
                    } else if (size >= size2) {
                        size2 = size; pos2 = start; value2 = value;
                    }
                }
                value = newvalue;
                start = pos;
            }
        }
        {   int32 remainder, k;
            int32 nextpos = pos1 + size1;
            if (nextpos >= 32) nextpos -= 32;
            if ( value1 == 3 && size1 > 8 &&
                 (value2 == 3 || pos1 == 0)) {
            /* both longest strings are 1s, or the longest is 1s and starts
               at the ls bit.  And in any case, the length of the longest
               string is sensible (eg beware 55aa3355).
               Maybe should also look for a (shorter) sensible length for the
               second string.
               Use MVN to construct the 8-bit chunk above the longest string
               (which will give us 1s in the two longest strings for free)
             */
                op = OP_MVNN;
                k = (~n) & ROR(255L, (32-nextpos));
                remainder = n - ~k;
            } else if ((value1 == 3 && size1 > 8) ||
                       (value2 == 3 && size2 > 8)) {
            /* one of the two longest strings is a sensible length and of 1s
               (the other is 0s).  Take the 8-bit chunk above the string of 1s
               incremented by 1 in its last place unless that is bit 0 of n.
               (The idea being that we will generate the string of 1s by
                subtracting something)
             */
                if (value2 == 3) {
                    nextpos = pos2 + size2;
                    if (nextpos >= 32) nextpos -= 32;
                }
                op = OP_MOVN;
                if (nextpos != 0)
                    k = (n & ROR(255L, (32 - nextpos))) + (1L << nextpos);
                   /* (k has only 8 bits - (n & ...) cannot be 255<<nextpos
                      or it would have been included in the string of 1s)
                    */
                else {
                    if (startvalue == 0) nextpos += startsize;
                    k = n & ROR(255L, (32 - nextpos));
                }
                remainder = n - k;
            } else {
                /* The longest two strings are of 0s.  Take the 8-bit chunk above
                   the longer.
                 */
                op = OP_MOVN;
                k = n & ROR(255L, (32 - nextpos));
                remainder = n - k;
            }
            if (Arm_EightBits(remainder) < 0 && Arm_EightBits(-remainder) < 0) {
                int32 *v1 = symmetricload(r, n, 0xffff, 16, scc, v);
                if (v1 != v) return v1;
                v1 = symmetricload(r, n, 0xff00ff, 8, scc, v);
                if (v1 != v) return v1;
            }
            *v++ = (op | F_RD(r) | Arm_EightBits(k));
            KillKnownRegisterValue(r);
            return arm_add_integer(r, r, remainder, scc, RegisterContainingValue, v);
        }
    }
}

static void load_integer_literal(RealRegister r, int32 n) {
    int32 dirn = F_UP;
    int32 i;
    ldm_flush();
    i = lit_findwordsincurpool(&n, 1, LIT_NUMBER);
    if (i < 0) {
        i = lit_findwordsinprevpools(&n, 1, LIT_NUMBER, codebase+codep+8-4092);
        if (i >= 0) {
            i = codebase+codep+8-i;
            dirn = F_DOWN;
        } else {
            addressability(1024);
            i = lit_findword(n, LIT_NUMBER, 0, LITF_INCODE|LITF_FIRST|LITF_LAST);
        }
    }
    if (dirn == F_UP) addfref_(litlab, codep | LABREF_B4096);
    outinstr(OP_LDR | dirn | F_RD(r) | F_RN(R_PC) | i);
}

static void load_integer(RealRegister r, int32 n, int32 flags)
{   int32 v[5];  /* Pessimism here about the number of instructions add_integer
                    may decide to generate */
    int32 scc = SCC_of_PEEP (flags);
    int32 *ve = load_integer_i(r, n, scc, v);
    int max = (scc == 0) ? integer_load_max : integer_load_max+1;
    if (ve-v <= max) {
        int32 *p = v;
        for (; p != ve; p++) outinstr(*p);
    } else {
        load_integer_literal(r, n);
        /* This should never happen, since load_integer gets called with */
        /* scc non-zero only perhaps from multiply_integer by 0, when n  */
        /* is zero, so shouldn't get into this code at all               */
        if (scc != 0)
           /* last three arguments to compare_integer irrelevant for     */
           /* comparison against 0.                                      */
            cmp_integer(r, 0, 0, 0, 0);
    }
    killipvalue(r);
    SetKnownRegisterValue(r, n);
}

static int clears_lobits(int32 n)
{   int shift;
    for (shift = 0; shift < 32; ++shift) {
        int32 lobits = (1L << shift) - 1L;
        if (n == ~lobits) return shift;
    }
    return 0;
}

static int clears_hibits(int32 n)
{   int shift;
    for (shift = 0; shift < 32; ++shift) {
        int32 hibits = (~0L) << (32-shift);
        if (n == ~hibits) return shift;
    }
    return 0;
}

static void and_integer(RealRegister r1, RealRegister r2, int32 n, int32 peep, bool dead_r1)
{ /* Generate code for r1 = r2 & n.                                      */
  int shift;
  int32 op = OP_ANDN, packed = Arm_EightBits(n);
  int32 scc = SCC_of_PEEP(peep);
  int32 mask = peep & Q_MASK;
  if (n == -1) {
    move_register(r1, r2, scc);
    return;
  }
  if (packed < 0)
    op = OP_BICN, packed = Arm_EightBits(~n);
  if (packed >= 0) {
    outinstr(op | scc | F_RD(r1) | F_RN(r2) | packed);
    return;
  }
  { ValueDesc vd;
    int rc = RegisterContainingValue(n, V_Inverted+V_AnyShift, &vd);
    if (rc != 0) {
      int32 w = scc | F_RD(r1) | F_RN(r2) | vd.r | vd.op3.shift;
      if (rc == V_Inverted)
        outinstr(OP_BICR | w);
      else
        outinstr(OP_ANDR | w);
      return;
    }
  }
  if ((shift = clears_hibits(n)) != 0) {
    if (dead_r1 || (peep & P_ZONLY)) {
      mask &= ~Q_UBIT;
      if (mask == Q_EQ || mask == Q_NE) {
        if (scc)
          outinstr(OP_MOVR | scc | F_RD(r1) | r2 | K_LSL(shift));
        return;
      }
    }
    outinstr(OP_MOVR | 0   | F_RD(r1) | r2 | K_LSL(shift));
    outinstr(OP_MOVR | scc | F_RD(r1) | r1 | K_LSR(shift));
    return;
  }
  if ((shift = clears_lobits(n)) != 0) {
    if (dead_r1 || (peep & P_ZONLY)) {
      if (scc)
        outinstr(OP_MOVR | scc | F_RD(r1) | r2 | K_ASR(shift));
      return;
    }
    outinstr(OP_MOVR | 0   | F_RD(r1) | r2 | K_LSR(shift));
    outinstr(OP_MOVR | scc | F_RD(r1) | r1 | K_LSL(shift));
    return;
  }
  { int32 tail=0x3, mask = 0xff;
    while ((~n & tail)==0) tail = tail << 2, mask = mask << 2;
    and_integer(r1, r2, n | mask, 0, NO);
    outinstr(OP_BICN | scc | F_RD(r1) | F_RN(r1) | Arm_EightBits(~n & mask));
  }
}

static void orr_integer(RealRegister r1, RealRegister r2, int32 n, int32 flags)
{ /* Generate code for r1 = r2 | n.                                      */
    int32 packed = Arm_EightBits(n);
    int32 scc = SCC_of_PEEP(flags);
    if (n == 0) {
      move_register(r1, r2, scc);
    } else if (packed >= 0) {
      outinstr(OP_ORRN | scc | F_RD(r1) | F_RN(r2) | packed);
    } else {
      ValueDesc vd;
      int rc = RegisterContainingValue(n, V_AnyShift, &vd);
      if (rc != 0) {
        outinstr(OP_ORRR | scc | F_RD(r1) | F_RN(r2) | vd.r | vd.op3.shift);
      } else {
        int32 tail=0x3, mask = 0xff;
        while ((n & tail)==0) tail = tail << 2, mask = mask << 2;
        orr_integer(r1, r2, n & (~mask), 0);
        outinstr(OP_ORRN | scc | F_RD(r1) | F_RN(r1) | Arm_EightBits(n & mask));
      }
    }
}

static void eor_integer(RealRegister r1, RealRegister r2, int32 n, int32 flags)
{ /* Generate code for r1 = r2 ^ n.                                      */
    int32 packed = Arm_EightBits(n);
    int32 scc = SCC_of_PEEP(flags);
    if (n == 0) {
      move_register(r1, r2, scc);
    } else if (packed >= 0) {
      outinstr(OP_EORN | scc | F_RD(r1) | F_RN(r2) | packed);
    } else {
      ValueDesc vd;
      int rc = RegisterContainingValue(n, V_AnyShift, &vd);
      if (rc != 0) {
        outinstr(OP_EORR | scc | F_RD(r1) | F_RN(r2) | vd.r | vd.op3.shift);
      } else {
        int32 tail=0x3, mask = 0xff;
        while ((n & tail)==0) tail = tail << 2, mask = mask << 2;
        eor_integer(r1, r2, n & (~mask), 0);
        outinstr(OP_EORN | scc | F_RD(r1) | F_RN(r1) | Arm_EightBits(n & mask));
      }
    }
}

static void teq_integer(RealRegister rt, RealRegister r2, int32 n, int32 flags)
{ /* Generate code for r2 ^ n.                                          */
    int32 packed = Arm_EightBits(n);
    int32 scc = SCC_of_PEEP(flags);
    if (packed >= 0) {
      outinstr(OP_TEQN | scc | F_RN(r2) | packed);
    } else {
      ValueDesc vd;
      int rc = RegisterContainingValue(n, V_AnyShift, &vd);
      if (rc != 0) {
        outinstr(OP_TEQR | scc | F_RN(r2) | vd.r | vd.op3.shift);
      } else if (flags & P_SETPSR) { /* TEQP */
        load_integer(rt, n, 0);
        outinstr (OP_TEQR | scc | F_RN(r2) | rt);
      } else
        eor_integer(rt, r2, n, flags);
    }
}

static void tst_integer(RealRegister rt, RealRegister r2, int32 n, int32 flags)
{ /* Generate code for r2 & n.                                          */
    int32 packed = Arm_EightBits(n);
    int32 scc = SCC_of_PEEP(flags);
    if (packed >= 0) {
      outinstr(OP_TSTN | scc | F_RN(r2) | packed);
    } else {
      ValueDesc vd;
      int rc = RegisterContainingValue(n, V_AnyShift, &vd);
      if (rc != 0) {
        outinstr(OP_TSTR | scc | F_RN(r2) | vd.r | vd.op3.shift);
      } else if (flags & P_SETPSR) { /* TSTP */
        load_integer(rt, n, 0);
        outinstr (OP_TSTR | scc | F_RN(r2) | rt);
      } else
        and_integer(rt, r2, n, flags, YES);
    }
}

static int32 eightbit_floor(int32 n)
/* n is a positive integer - find a number representable as an ARM       */
/* operand that is less than (or ==) n but as close to it as possible    */
{
    unsigned32 m1 = 0xff000000, m2 = 0xc0000000;
    /* the special case is needed to cover n==0                          */
    if ((n & 0xff)==n) return n;
    while ((n & m2)==0)
    {   m1 = m1 >> 2;
        m2 = m2 >> 2;
    }
    return (n & m1);
}

static int32 eightbit_ceiling(int32 n)
/* n is a positive integer - find a number >= n that is representable    */
/* as an ARM operand.                                                    */
{
    unsigned32 m1 = 0xff000000, m2 = 0xc0000000;
    if ((n & 0xff)==n) return n;
    while ((n & m2)==0)
    {   m1 = m1 >> 2;
        m2 = m2 >> 2;
    }
/* In the next line I increment an 8-bit value by the lowest bit of m1,  */
/* which operation can certainly cause overflow from 0xff to 0x100, but  */
/* 0x100 is representable in 8-bits on ARM so this does not matter. Also */
/* there can be the generation of 0x80000000 as (e.g.) the nearest value */
/* above 0x7fxxxxxx - I will need to be careful about that when I call   */
/* this horrid function.                                                 */
    return (n & m1) + (m1 & (0-m1));
}

static int32 *compare_integer_i(RealRegister r, int32 n, RealRegister workreg,
                                int32 mask, int32 when, int32 *v)
{
/* Compare register r with integer n, setting condition codes            */
    int32 op = OP_CMPN, packed = Arm_EightBits(n);
    if (packed < 0) {
      op = OP_CMNN;
      packed = Arm_EightBits(-n);
    }
    if (packed >= 0)
      *v++ = (when | op | F_RN(r) | packed);
    else {
      ValueDesc vd;
      int rc = RegisterContainingValue(n, V_Negated+V_AnyShift, &vd);
      if (rc != 0) {
        int32 w = when | F_RN(r) | vd.r | vd.op3.shift;
        if (rc == V_Negated)
          w |= OP_CMNR;
        else
          w |= OP_CMPR;
        *v++ = w;
      } else {
        int32 m = 0, cond = 0;
/* Note that n!=0 here                                                   */
        if (mask == Q_EQ || mask == Q_NE || mask == Q_UNE || mask == Q_UEQ) {
            m = (n > 0) ? eightbit_floor(n) : -eightbit_floor(-n);
        } else if (mask == Q_UNDEF || condition_mask != C_ALWAYS) {
            /* nothing */
        } else if (mask & Q_UBIT) {
            if (n > 0) m = eightbit_floor(n), cond = C_HS;
            else m = -eightbit_floor(-n), cond = C_LS;
            when |= F_SCC;
        } else {
            if (n > 0) m = eightbit_floor(n), cond = C_GE;
            else m = -eightbit_floor(-n), cond = C_LE;
            when |= F_SCC;
        }
        if (m != 0) {
            v = arm_add_integer(workreg, r, -m, when, RegisterContainingValue, v);
            v = compare_integer_i(workreg, n-m, workreg, mask, cond, v);
        }
      }
    }
    return v;
}

static void compare_integer(RealRegister r, int32 n, RealRegister workreg,
                            int32 mask, int32 when)
{
    int32 v[5], w[5];
    int32 *ve = compare_integer_i(r, n, workreg, mask, when, v);
    unsigned iv = ve - v;
    int32 *we = load_integer_i(workreg, n, 0, w);
    unsigned iw = we - w + 1;
    if (0 < iv && iv <= integer_load_max+1 && iv <= iw && when == 0)
    {
        for (iv = 0; &v[iv] != ve; iv++) outinstr(v[iv]);
        killipvalue(workreg);
        KillKnownRegisterValue(workreg);
    }
    else {
        if (iw <= integer_load_max+1) {
            for (iw = 0; &w[iw] != we; iw++) outinstr(w[iw]);
        } else
            load_integer_literal(workreg, n);
        outinstr(OP_CMPR | F_RN(r) | workreg | when);
        killipvalue(workreg);
        SetKnownRegisterValue(workreg, n);
    }
}

static void cmp_integer(RealRegister r, int32 n, RealRegister workreg,
                        int32 condition, int32 flags)
{
    int32 op = OP_CMPN, packed = Arm_EightBits(n);
    if (packed < 0) {
      op = OP_CMNN;
      packed = Arm_EightBits(-n);
    }
    if (flags & P_SETPSR) op |= F_RD(15);
    if (packed >= 0)
      outinstr(op | F_RN(r) | packed);
    else
      compare_integer(r, n, workreg, condition, flags & P_SETPSR ? F_RD(15) : 0);
}

static void cmn_integer(RealRegister r, int32 n, RealRegister workreg,
                        int32 condition, int32 flags)
{
    int32 op = OP_CMNN, packed = Arm_EightBits(n);
    if (packed < 0) {
      op = OP_CMPN;
      packed = Arm_EightBits(-n);
    }
    if (flags & P_SETPSR) op |= F_RD(15);
    if (packed>=0)
      outinstr(op | F_RN(r) | packed);
    else
      compare_integer(r, -n, workreg, condition, flags & P_SETPSR ? F_RD(15) : 0);
}


typedef struct {
    int32 i[32];
    RealRegister workreg;
    int n;
} InstDesc;

static int32 multiply_1(RealRegister r1, RealRegister r2, int32 n, int32 scc)
{   int32 s;
    if ((s = power_of_two(n)) >= 0)
      return OP_MOVR | scc | F_RD(r1) | r2 | K_LSL(s);
    else if ((s = power_of_two(n-1)) >= 0)
      return OP_ADDR | scc | F_RD(r1) | F_RN(r2) | r2 | K_LSL(s);
    else if ((s = power_of_two(1-n)) >= 0)
      return OP_SUBR | scc | F_RD(r1) | F_RN(r2) | r2 | K_LSL(s);
    else if ((s = power_of_two(n+1)) >= 0)
      return OP_RSBR | scc | F_RD(r1) | F_RN(r2) | r2 | K_LSL(s);
    return 0;
}

static bool multiply_2(RealRegister r1, RealRegister r2,
                       int32 n, int32 scc, InstDesc *i) {
    /* is n of the form (2^p +/- 1)(2^q +/- 1) ?
     *             (2^(p+q)+/-2^p+/-2^q+/-1)
     * thus if n is of this form (and p != q), one factor is s+/-1 where s is
     * the bottom bit of n after adding or subtracting 1.
     * if p == q, this is wrong, but we can still do the multiply in two
     * instructions as 2^(2*p)+/-2^(p+1)+/-1 using a work register
     */
    int32 k = (n & 2) == 0 ? n - 1 : n + 1;
    int32 s = k & (-k);
    int32 factor;
    int32 i0;
    if ( ((n % (factor = s - 1)) == 0
          && (i0 = multiply_1(r1, r2, n / factor, 0)) != 0)
         || ((n % (factor = s + 1)) == 0
             && (i0 = multiply_1(r1, r2, n / factor, 0)) != 0)) {
      i->i[i->n] = i0;
      i->i[i->n+1] = multiply_1(r1, r1, factor, scc);
      i->workreg = NoRegister;
      i->n += 2;
      return YES;
    }

    if (i->workreg != NoRegister) {
      RealRegister r3 = i->workreg;
      int32 sh;
        /* is n of the form 2^a +/- 2^b +/- 1 ? */
      if ((sh = power_of_two(k-s)) >= 0) {
        i->i[i->n] = multiply_1(r3, r2, s+n-k,0);
        i->i[i->n+1] = OP_ADDR | scc | F_RD(r1) | F_RN(r3) | r2 | K_LSL(sh);
        i->n += 2;
        return YES;
      } else if ((sh = power_of_two(k+s)) >= 0) {
        i->i[i->n] = multiply_1(r3, r2, s-n+k, 0);
        i->i[i->n+1] = OP_RSBR | scc | F_RD(r1) | F_RN(r3) | r2 | K_LSL(sh);
        i->n += 2;
        return YES;
      }
    }
    return NO;
}

static bool multiply_3(RealRegister r1, RealRegister r2,
                       int32 n, int32 scc, InstDesc *i) {
    int32 k;
      /* is n of the form (2^p+/-1)*m,
         where m can be multiplied by in two instructions?
       */
    for (k = 0x00010000; k >= 4; k = k >> 1) {
      if ((n % (k-1)) == 0 && multiply_2(r1, r2, n/(k-1), 0, i)) {
        i->i[i->n++] = multiply_1(r1, r1, k-1, scc);
        return YES;
      }
      if ((n % (k+1)) == 0 && multiply_2(r1, r2, n/(k+1), 0, i)) {
        i->i[i->n++] = multiply_1(r1, r1, k+1, scc);
        return YES;
      }
    }
    if (i->workreg != NoRegister) {
      /* is n of the form +/-2^p+/-m,
         where m can be multiplied by in two instructions?
       */
      RealRegister r3 = i->workreg;
      k = (n & 2) == 0 ? n - 1 : n + 1;
      while (k != 0) {
        int32 s = k & (-k);
        if (multiply_2(r3, r2, n-s, 0, i)) {
          s = power_of_two(s);
          i->i[i->n++] = OP_ADDR | scc | F_RD(r1) | F_RN(r3) | r2 | K_LSL(s);
          i->workreg = r3;
          return YES;
        } else if (multiply_2(r3, r2, n+s, 0, i)) {
          s = power_of_two(s);
          i->i[i->n++] = OP_SUBR | scc | F_RD(r1) | F_RN(r3) | r2 | K_LSL(s);
          i->workreg = r3;
          return YES;
        }
        if (k & (s << 1))
          k += s;
        else
          k -= s;
      }
    }
    return NO;
}

static void multiply_i(RealRegister r1, RealRegister r2, int32 n, int32 scc,
                       InstDesc *i)
{   int32 s, k;
    RealRegister r3 = i->workreg;

    if ((s = multiply_1(r1, r2, n, scc)) != 0) {
      i->i[i->n++] = s;
      i->workreg = NoRegister;
      return;

    } else if ((s = n & (-n)) != 1) {   /* divisible by a power of 2 */
      multiply_i(r1, r2, n/s, 0, i);
      i->i[i->n++] = multiply_1(r1, r1, s, scc);
      return;
    }

    if (multiply_2(r1, r2, n, scc, i) ||
        multiply_3(r1, r2, n, scc, i)) {
      return;
    }

/* Determine whether our number has a factor of the form 2^s+1 or 2^s-1  */
/* Note that since various cases have already been checked the number n  */
/* is not of any of the forms 2^s+1, 2^s-1, 1-2^s.                       */
    for (k = 0x00010000; k >= 4; k = k >> 1) {
      if ((n % (k-1)) == 0) {
        k = k-1;
        break;
      } else if ((n % (k+1)) == 0) {
        k = k+1;
        break;
      }
    }
    if (k > 2) {
      multiply_i(r1, r2, n/k, 0, i);
      i->i[i->n++] = multiply_1(r1, r1, k, scc);
      return;
    }

    if ((n&2) == 0) {
      k = n - 1;
      s = k & (-k);
      multiply_i(r3, r2, k/s, 0, i);
      s = power_of_two(s);
      i->i[i->n++] = OP_ADDR | scc | F_RD(r1) | F_RN(r2) | r3 | K_LSL(s);
    } else {
      k = n + 1;
      s = k & (-k);
      multiply_i(r3, r2, k/s, 0, i);
      s = power_of_two(s);
      i->i[i->n++] = OP_RSBR | scc | F_RD(r1) | F_RN(r2) | r3 | K_LSL(s);
    }
    i->workreg = r3;
}

static void multiply_integer(RealRegister r1, RealRegister r2, int32 n,
                             int32 scc)
/* **** Keep this in step with MultiplyNeedsWorkreg below **** */

{ /* Generate code for r1 = r2 * n.  scc can be used to set condn codes. */
    if (codep >= mustlitby) dumplits2(YES);
    if (n==0)
      load_integer(r1, 0, scc);
    else if (n==1)
      move_register(r1, r2, scc);
    else if (n==-1)
      negate_register(r1, r2, scc);
    else {
      InstDesc insts;
      RealRegister workreg;
      int32 w[5];
      int load_time, multiply_time;
      bool use_multiply = NO;

      if (r1 != r2)
        workreg = r1;           /* if source != dest, can use dest reg */
      else
        workreg = R_IP;         /* otherwise a fixed register */
      insts.n = 0;
      insts.workreg = workreg;
      multiply_i(r1, r2, n, scc, &insts);
      load_time = load_integer_i(r1, n, 0, w) - w;

      multiply_time = (config & CONFIG_OPTIMISE_SPACE) ? 1 : multiply_cycles(n, NO);
      if (load_time + multiply_time < insts.n)
          use_multiply = YES;

      if (use_multiply) {
        load_integer(workreg, n, 0);
        /* /* Maybe n is available in a register */
        if (r1 == r2)
          outinstr(OP_MUL | F_RN(r1) | (r2 << 8) | workreg | scc);
        else
          outinstr(OP_MUL | F_RN(r1) | (workreg << 8) | r2 | scc);
      } else {
        int i = 0;
        if (insts.workreg != NoRegister) {
          killipvalue(insts.workreg);
          KillKnownRegisterValue(insts.workreg);
        }
        for (; i < insts.n; i++) outinstr(insts.i[i]);
      }
    }
}

bool MultiplyNeedsWorkreg(int32 n)
/* **** Keep this in step with multiply_integer above **** */
{ InstDesc insts;
  static struct { int32 n; bool res; } last = {0, 0};
  int load_time, multiply_time;
  bool use_multiply = NO;

  if (last.n == n) return last.res;
  if (n >= -1 && n <= 1) return NO;
  last.n = n;
  insts.n = 0; insts.workreg = 0;
  /* This may be called before registers have been assigned (hence the 0s below).
     Fortunately, the pattern of instructions generated isn't affected, just the
     register used as workreg if one is needed.
   */
  multiply_i(0, 0, n, 0, &insts);
  load_time = integer_load_max;     /* cannot call load_integer_i!!! */
  multiply_time = (config & CONFIG_OPTIMISE_SPACE) ? 1 : multiply_cycles(n, NO);
  if (load_time + multiply_time < insts.n)
      use_multiply = YES;

  if (use_multiply)
    return last.res = (insts.workreg != NoRegister);
  else
    return last.res = YES;
}


static void mla_integer(RealRegister r1, RealRegister r2, int32 n,
                        RealRegister acc, int32 scc)
/* **** Keep this in step with MultiplyNeedsWorkreg below **** */

{ /* Generate code for r1 = r2 * n + acc.  scc can be used to set condn codes. */
    if (codep >= mustlitby) dumplits2(YES);
    if (n==0)
      move_register(r1, acc, scc);
    else if (n==1)
      outinstr(OP_ADDR | F_RD(r1) | F_RN(acc) | r2 | scc);
    else if (n==-1)
      outinstr(OP_SUBR | F_RD(r1) | F_RN(acc) | r2 | scc);
    else {
      InstDesc insts;
      RealRegister workreg;
      int32 w[5];
      int32 shift, m;
      int load_time, multiply_time;
      bool use_multiply = NO;

      shift = n & -n;
      m = n / shift;            /* remove trailing zeroes of n */
      shift = logbase2(shift);
      workreg = R_IP;           /* always use a fixed register */
      insts.n = 0;
      insts.workreg = workreg;
      multiply_i(workreg, r2, m, 0, &insts);
      load_time = load_integer_i(r1, n, 0, w) - w;

      multiply_time = (config & CONFIG_OPTIMISE_SPACE) ? 1 : multiply_cycles(n, YES);
      if (load_time + multiply_time < insts.n + 1)
          use_multiply = YES;

      if (use_multiply) {
        load_integer(workreg, n, 0);
        if (r1 == r2)
          outinstr(OP_MLA | F_RN(r1) | F_RD(acc) | (r2 << 8) | workreg | scc);
        else
          outinstr(OP_MLA | F_RN(r1) | F_RD(acc) | (workreg << 8) | r2 | scc);
      } else {
        int i = 0;
        if (insts.workreg != NoRegister) {
          killipvalue(insts.workreg);
          KillKnownRegisterValue(insts.workreg);
        }
        for (; i < insts.n; i++) outinstr(insts.i[i]);
        outinstr(OP_ADDR | F_RD(r1) | F_RN(acc) | K_LSL(shift) | workreg | scc);
      }
    }
}



#if DEBUG_X
/* For truly grim debugging I can make each compiled function display    */
/* its name each time it is entered. This is arranged here. Ugh.         */
static void desperate_codetrace(void)
    {   int32 w = 0, c, i = 0;
        outinstr(0x0f000001);       /* SWI KString */
            while ((c=symname_(currentfunction.symstr)[i++]) != 0)
            {   w = ((w>>8) & 0x00ffffff) | (c << 24);
                if ((w & 0xff)!=0)
                    outcodeword(w, LIT_STRING), w=0;
            }
            w = ((w>>8) & 0x00ffffff) | (((int32)'\r')<<24);
            if ((w & 0xff)!=0)
                outcodeword(w, LIT_STRING), w=0;
            w = ((w>>8) & 0x00ffffff) | (((int32)'\n')<<24);
            if ((w & 0xff)!=0)
            {   outcodeword(w,LIT_STRING);
                outcodeword(0,LIT_STRING);
            }
            else
            {   while ((w & 0xff)==0) w = (w>>8) & 0x00ffffff;
                outcodeword(w,LIT_STRING);
            }
    }
#endif /* DEBUG_X */


static RealRegister local_base_a(int32 p)
{
    switch (p & BINDADDR_MASK)
    {   default: syserr(syserr_local_base, (long)p);
        case BINDADDR_ARG: if ((procflags & NONLEAF) && !(pcs_flags & PCS_NOFP) &&
                               !(procauxflags & bitoffnaux_(s_irq)))
                               return R_FP;
                           /* drop through */
        case BINDADDR_LOC: return R_SP;
    }
}

RealRegister local_base(Binder const *b) {
    return local_base_a(bindaddr_(b));
}

static bool saveregs_done;

static int32 local_addr_a(int32 p)
{
    /* fp_minus_sp is now maintained by show_instruction_direct, so is
       up to date even if the instruction to modify the sp hasn't yet been
       generated thanks to peepholing.
     */
    switch (p & BINDADDR_MASK)
    {
default:
        syserr(syserr_local_addr, (long)p);
case BINDADDR_LOC:
        p = fp_minus_sp - (p & ~BINDADDR_MASK);
/*
 * You might have thought that the next line was a sensible thing to have
 * put in as a consistency check, but CSE elimination can lift an ADCONV
 * outside the scope of the variable being addressed.  The result is that
 * the address is sometimes computed as a negative offset relative to sp,
 * ready for when sp gets dropped later.  Ugh!
 *      if (p < 0) syserr(syserr_neg_addr, (long)p, (long)p, b);
 */
        return p;
case BINDADDR_ARG:
        p &= ~BINDADDR_MASK;
#if 0
        if (!(procflags & NONLEAF))
        {   /* LDRV1 only - hence nargwords > NARGREGS.  SP relative.   */
            if (p < 4*nregargwords) syserr(syserr_local_addr1);
            p += fp_minus_sp;
            return p - 16 + 4*(bitcount(regmask & (M_VARREGS | regbit(R_LR)))
                               + saved_fpreg_words * bitcount(regmask & M_FVARREGS));
        }
#endif
        /* on the ARM the args go in different places depending on      */
        /* their number.  This saves one STM for <= NARGREGS args.      */
        p -= (p >= 4*argwordsbelowfp) ?
                   4*(argwordsbelowfp - savewordsabovefp) :
                   4*(argwordsbelowfp + intsavewordsbelowfp);
        return (!(procflags & NONLEAF) || (pcs_flags & PCS_NOFP) ||
                (procauxflags & bitoffnaux_(s_irq))) ?
                   p + fp_minus_sp + 4*(intsavewordsbelowfp +
                                        realargwordsbelowfp +
                                        saved_fpreg_words * bitcount(regmask & M_FVARREGS)) :
                   p;
    }
}

int32 local_address(Binder const *b) {
    return local_addr_a(bindaddr_(b));
}

#ifdef TARGET_HAS_DEBUGGER
/* The miserable debugger cannot cope with SP relative addresses so we */
/* have to calculate FP relative ones specially!                       */
/* Lets hope that we have calculated these correctly!                  */
/* This means that cg.c has set PROC_ARGPUSH which thereby inhibits    */
/* leaf procedure optimisation (else there would be no FP!)            */
int32 local_fpaddress(Binder const *b)
/* exported for debugger */
{   int32 p = bindaddr_(b) & ~BINDADDR_MASK;
    switch (bindaddr_(b) & BINDADDR_MASK)
    {
case BINDADDR_LOC:
        p = -(p + 4*(intsavewordsbelowfp
                     + realargwordsbelowfp
                     + saved_fpreg_words * bitcount(regmask & M_FVARREGS)));
        break;
case BINDADDR_ARG:
        if (p >= 4*argwordsbelowfp)
            p -= 4*(argwordsbelowfp - savewordsabovefp);
        else
            p -= 4*(argwordsbelowfp + intsavewordsbelowfp);
        break;
default:
        syserr(syserr_debug_addr);
        return 0;
    }
    return (!(procflags & NONLEAF) || (pcs_flags & PCS_NOFP) ||
            (procauxflags & bitoffnaux_(s_irq))) ?
               p + 4 :
               p;
}

RealRegister local_fpbase(Binder const *b) {
    IGNORE(b);
    return !(procflags & NONLEAF) || (pcs_flags & PCS_NOFP) ||
            (procauxflags & bitoffnaux_(s_irq)) ? R_NOFPREG : R_FP;
}

#endif /* TARGET_HAS_DEBUGGER */

static int32 const fm_countbits[] = { F_FM_1, F_FM_2, F_FM_3, F_FM_4 };

static void fpa_saveregs(int32 mask)
{
    RealRegister r1;
    for (r1 = R_F7; r1 >= R_F4; r1--)
        if (mask & regbit(r1))
        {   if (pcs_flags & PCS_FPE3) {
                int32 count = 1;
                while (--r1 >= R_F4 && count < 4 && (mask & regbit(r1)))
                    count++;
                outinstr(OP_CPPRE | F_DOWN | F_WRITEBACK | F_STR |
                         F_RN(R_SP) | F_RD((r1+1) & 0xf) | fm_countbits[count-1] |
                         (3 * count));
                fpdesc_notespchange(count * 3 * 4);
            } else {
                outinstr(OP_CPPRE | F_DOWN | F_WRITEBACK | F_STR |
                         F_RN(R_SP) | F_RD(r1 & 0xf) | F_EXTENDED | 3);
                fpdesc_notespchange(3 * 4);
            }
        }
}

static int32 fpa_restoresize(int32 mask) {
    RealRegister r1;
    int32 n = 0;
    for (r1 = R_F7; r1 >= R_F4; r1--)
        if (mask & regbit(r1))
            n += 3 * 4;
    return n;
}

static void fpa_restoreregs(int32 mask, int32 condition, FP_RestoreBase base, int32 offset)
{
    RealRegister r;
    int32 n = intsavewordsbelowfp +
              3 * bitcount(regmask & M_FVARREGS) +
              realargwordsbelowfp;
    for (r = R_F4; r <= R_F7; r++)
        if (regbit(r) & mask) {
            if (base == UseSP_Adjust) {
                int32 count = 1;
                if (pcs_flags & PCS_FPE3)
                {   RealRegister r1 = r;
                    while (count < 4 && ++r <= R_F7 && (mask & regbit(r)))
                        count++;
                    outinstr(OP_CPPOST | condition | F_UP | F_LDR | F_WRITEBACK |
                             F_RN(R_SP) | F_RD(r1 & 0xf) | fm_countbits[count-1] |
                             (3 * count));
                } else
                    outinstr(OP_CPPOST | condition | F_UP | F_LDR | F_WRITEBACK |
                             F_RN(R_SP) | F_RD(r & 0xf) | F_EXTENDED | 3);
                fpdesc_notespchange(-count * 3 * 4);
            } else if (base == UseSP_NoAdjust) {
                int32 count = 1;
                if (pcs_flags & PCS_FPE3)
                {   RealRegister r1 = r;
                    while (count < 4 && ++r <= R_F7 && (mask & regbit(r)))
                        count++;
                    outinstr(OP_CPPRE | condition | F_UP | F_LDR |
                             F_RN(R_SP) | F_RD(r1 & 0xf) | fm_countbits[count-1] |
                             (offset/4));
                    offset += 12 * count;
                } else {
                    outinstr(OP_CPPRE | condition | F_UP | F_LDR |
                             F_RN(R_SP) | F_RD(r & 0xf) | F_EXTENDED | (offset/4));
                    offset += 12;
                }
            } else {
                int32 count = 1;
                if (pcs_flags & PCS_FPE3)
                {   RealRegister r1 = r;
                    while (++r <= R_F7 && (mask & regbit(r)))
                        count++;
                    outinstr(OP_CPPRE | condition | F_DOWN | F_LDR | F_RN(R_FP) |
                             F_RD(r1 & 0xf) | fm_countbits[count-1] | n);
                } else
                    outinstr(OP_CPPRE | condition | F_DOWN | F_LDR | F_RN(R_FP) |
                             F_RD(r & 0xf) | F_EXTENDED | n);
                n -= 3 * count;
            }
        }
}

static void fpa_saveargs(int32 n) {
    for (; --n >= 0; ) {
        outinstr(OP_CPPRE | F_DOWN | F_WRITEBACK | F_STR |
                 F_RN(R_SP) | F_RD(R_F0+n) | F_DOUBLE | 2);
        fpdesc_notespchange(2 * 4);
    }
}

static FP_Gen const fpa_gen = {
    fpa_show,
    fpa_saveregs,
    fpa_restoresize,
    fpa_restoreregs,
    fpa_saveargs
};

static void amp_saveregs(int32 mask)
{
    RealRegister r1;
    for (r1 = R_F7; r1 >= R_F4; r1--)
        if (mask & regbit(r1))
            outinstr(AMP_DT(CPDT_PRE | CPDT_DOWN | CPDT_WB | CPDT_ST,
                            R_SP, amp_checkfreg(r1), 4));
}

static int32 amp_restoresize(int32 mask) {
    RealRegister r1;
    int32 n = 0;
    for (r1 = R_F7; r1 >= R_F4; r1--)
        if (mask & regbit(r1))
            n += 4;
    return n;
}

static void amp_restoreregs(int32 mask, int32 condition, FP_RestoreBase base, int32 offset)
{
    RealRegister r;
    int32 n = intsavewordsbelowfp +
              bitcount(regmask & M_FVARREGS) +
              realargwordsbelowfp;
    for (r = R_F4; r <= R_F7; r++)
        if (regbit(r) & mask) {
            if (base == UseSP_Adjust) {
                outinstr(AMP_DT(CPDT_POST | CPDT_UP | CPDT_WB | CPDT_LD,
                                R_SP, amp_checkfreg(r), 4)
                         | condition);
                fpdesc_notespchange(-4);
            } else if (base == UseSP_NoAdjust) {
                outinstr(AMP_DT(CPDT_PRE | CPDT_UP | CPDT_LD,
                                R_SP, amp_checkfreg(r), offset)
                         | condition);
                offset += 4;
            } else {
                outinstr(AMP_DT(CPDT_PRE | CPDT_DOWN | CPDT_LD,
                                R_FP, amp_checkfreg(r), n*4)
                         | condition);
                n -= 1;
            }
        }
}

static void amp_saveargs(int32 n) {
    for (; --n >= 0; ) {
        outinstr(AMP_DT(CPDT_PRE | CPDT_DOWN | CPDT_WB | CPDT_ST,
                        R_SP, amp_checkfreg(R_F0+n), 4));
        fpdesc_notespchange(4);
    }
}

static FP_Gen const amp_gen = {
    amp_show,
    amp_saveregs,
    amp_restoresize,
    amp_restoreregs,
    amp_saveargs
};

static int32 LSBits(int32 mask, int n) {
    int32 mask1 = 0;
    for (; --n >= 0;) {
        int32 bit = mask & (-mask);
        mask1 |= bit;
        mask ^= bit;
    }
    return mask1;
}

static int32 MSBits(int32 mask, int n) {
    int n1 = (int)bitcount(mask) - n;
    for (; --n1 >= 0;) {
        mask ^= mask & (-mask);
    }
    return mask;
}

static void PushRegs(int32 mask) {
    unsigned count = (unsigned)bitcount(mask);
    int32 stm = OP_STMFD | F_WRITEBACK | F_RN(R_SP);
    for (; count > ldm_regs_max; count -= ldm_regs_max) {
        int32 mask1 = MSBits(mask, ldm_regs_max);
        mask ^= mask1;
        outinstr(stm | mask1);
        fpdesc_notespchange(bitcount(mask1) * 4);
    }
    outinstr(stm | mask);
    fpdesc_notespchange(bitcount(mask) * 4);
}

static void routine_entry(int32 m)
{   condition_mask = C_ALWAYS;
#if DEBUG_X
    if (debugging(DEBUG_X)) desperate_codetrace();
#endif

    {   Symstr *name = currentfunction.symstr;
        int flags = currentfunction.xrflags;
        if ((pcs_flags & PCS_REENTRANT) &&
            (procflags & PROC_USESADCONS))
            flags |= aof_usessb;
        if (!(procflags & NONLEAF)) {
#ifndef TARGET_IS_UNIX
            if (!(procflags & BLK0EXIT))
                flags |= aof_leaf;
#endif
        } else if (HasFeature(Feature_SaveName))
/* Dump a function name only if the function will have a stack frame... */
/* Without a frame the name isn't locatable (RISC OS and RISCiX kernel) */
            codeseg_function_name(name, /* nargwords, unused on ARM */ m);
        if (k_fltregs_(m) != 0) flags |= aof_fpreg;
        dbg_enterproc();
        fpdesc_startproc();
        show_entry(name, flags);
    }

#ifdef TARGET_IS_UNIX
    if (profile_option) {
        int32 loc = data_size();
        gendcI(4, 0);
        move_register(R_IP, R_LR, 0);
        outinstr3(OP_BL, countroutine, 0);
        obj_symref(bindsym_(datasegment), xr_data, 0);
        AddCodeXref4(X_backaddrlit | (codebase + codep), bindsym_(datasegment), loc);
        outcodeword(loc, LIT_ADCON);
    }
#endif
    fp_minus_sp = 0;
    returnlab = nextlabel();
    saveregs_done = NO;
    argwordsbelowfp = realargwordsbelowfp = 0;
    intsavewordsbelowfp = savewordsabovefp = argstopopabovefp = 0;
    ipvalue.valid = NO;
    spareregs = 0;
    if (!(pcs_flags & PCS_REENTRANT))
        spareregs |= regbit(R_IP);      /* IP free on entry of non-reentrant fn */
    if (!k_isvariadic_(m) && k_intregs_(m) < NARGREGS)
        spareregs |= M_ARGREGS & ~(regbit(k_intregs_(m)) - 1);
    spareregs &= regmask;               /* only add registers that are really free */
}

static void routine_saveregs(int32 m)
{
    int32 intregs = k_intregs_(m),
          fltregs = k_fltregs_(m);
    saveregs_done = YES;
    if (m < 0) syserr(syserr_enter, (long)m);
    nargwords = k_argwords_(m);
    nregargwords = intregs + fp_arg_words*fltregs;
#if DEBUG_X
    if (debugging(DEBUG_X)) desperate_codetrace();
#endif

    if (!(procflags & NONLEAF) || (pcs_flags & PCS_NOFP) ||
         (procauxflags & bitoffnaux_(s_irq)))
    {
        int32 mask;
        if (HasFeature(Feature_DontUseLinkReg))
            regmask |= M_LR;
        if ((regmask & M_VARREGS) != 0 && (config & CONFIG_OPTIMISE_SPACE))
            regmask |= M_LR;
        if (procauxflags & bitoffnaux_(s_irq)) {
            mask = regmask & (M_VARREGS | M_ARGREGS | regbit(R_IP) | M_LR);
        } else {
            mask = regmask & (M_VARREGS | M_LR);
            if (procflags & PROC_ARGPUSH) {
                bool maybevariadic = fltregs == 0 && intregs < nargwords;
                if (maybevariadic) {
                    fpdesc_setinitoffset(-4-NARGREGS*4);
                    PushRegs(M_ARGREGS);
                    argstopopabovefp = NARGREGS;
                } else {
                    argwordsbelowfp = nregargwords;
                    mask |= (regbit(R_A1+intregs) - regbit(R_A1));
                        realargwordsbelowfp = nregargwords;
                }
            } else
                argwordsbelowfp = nregargwords;
        }
        if ((pcs_flags & PCS_REENTRANT) &&
            (procflags & (PROC_USESADCONS+BLK0EXIT)))
        {   outinstr(OP_MOVR | F_RD(R_IP) | R_SB);
            DestroyIP();
            regmask |= regbit(R_SB); mask |= regbit(R_SB);
            fpdesc_enterproc();
            PushRegs(mask);
            outinstr(OP_MOVR | F_RD(R_SB) | R_IP);
        } else if (mask != 0) {
            fpdesc_enterproc();
            PushRegs(mask);
        }
        intsavewordsbelowfp = bitcount(mask & ~M_ARGREGS);
        if (procflags & PROC_ARGPUSH) fp_gen->saveargs(fltregs);
        fp_gen->calleesave(regmask);
    }
    else
    {
        bool saveargs = HasFeature(Feature_SaveName) || (procflags & PROC_ARGPUSH);
        bool maybevariadic = fltregs == 0 && intregs < nargwords && saveargs;
        int32 mask;
        savewordsabovefp = 1;
        if (pcs_flags & PCS_REENTRANT) {
            int32 fpoff;
            regmask |= regbit(R_SB);
            mask = (regmask & M_VARREGS) | regbit(R_FP);
            intsavewordsbelowfp = bitcount(mask) + 2; /* + sp and lr */
            fpoff = intsavewordsbelowfp;

            outinstr(OP_MOVR | F_RD(R_IP) | R_SB);
            DestroyIP();
            if (!maybevariadic)
            {   PushRegs(regbit(R_SP) | M_LR | M_PC);
                argwordsbelowfp = nregargwords;
                if (saveargs) {
                    mask |= (regbit(R_A1+intregs) - regbit(R_A1));
                    realargwordsbelowfp = nregargwords;
                }
                PushRegs(mask);
                if (saveargs) {
                    fp_gen->saveargs(fltregs);
                    fpoff += argwordsbelowfp;
                }
                outinstr(OP_MOVR | F_RD(R_SB) | R_IP);
            } else {
                PushRegs(M_ARGREGS);
                PushRegs(mask | regbit(R_SP) | M_LR | M_PC);
                outinstr(OP_MOVR | F_RD(R_SB) | R_IP);
                add_integer(R_IP, R_SP, 28+4*bitcount(mask), 0);
                outinstr(OP_STR | F_DOWN | F_RD(R_IP) | F_RN(R_IP) | 28);
            }
            add_integer(R_FP, R_SP, 4*fpoff, 0);

        } else {
            int32 fpoff = 4;
            mask = (regmask & M_VARREGS) | regbit(R_FP) | regbit(R_IP) | M_LR | M_PC;
            intsavewordsbelowfp = bitcount(mask) - 1; /* not pc */

            outinstr(OP_MOVR | F_RD(R_IP) | R_SP);
            DestroyIP();
            if (!maybevariadic)
            {   argwordsbelowfp = nregargwords;
                if (saveargs) {
                    mask |= (regbit(R_A1+intregs) - regbit(R_A1));
                    realargwordsbelowfp = nregargwords;
                }
            } else {
                fpoff += NARGREGS*4;
                PushRegs(M_ARGREGS);
            }
            PushRegs(mask);
            if (saveargs) fp_gen->saveargs(fltregs);
            add_integer(R_FP, R_IP, -fpoff, 0);
        }
        fp_gen->calleesave(regmask);
        if ((procflags & STACKCHECK) &&      /* not a leaf function and no large frame */
            !no_stack_checks &&              /* not locally turned off (pragma -s) */
            !(pcs_flags & PCS_NOSTACKCHECK)) /* not globally turned of (-apcs 3/noswst) */
        {   Symstr *name = stackoverflow;
            if (greatest_stackdepth > 256)
            {   int32 n = eightbit_ceiling(greatest_stackdepth);
                add_integer(R_IP, R_SP, -n, 0);
                DestroyIP();
                outinstr(OP_CMPR | F_RN(R_IP) | R_SL);
                name = stack1overflow;
            }
            else
                outinstr(OP_CMPR | F_RN(R_SP) | R_SL);
            outinstr3(OP_BL | C_MI, name, 0);
        }
    }
    spareregs |= regmask & (regbit(R_IP) | regbit(R_LR) | (regbit(R_V6+1) - regbit(R_V1)));
    /* Could add V8, and V7 if FP not used */
}

static void PopRegs(int32 condition, int32 mask) {
    int32 setsp = mask & F_PSR;
    mask &= ~F_PSR;
    {   unsigned count = (unsigned)bitcount(mask);
        unsigned maxcount = ldm_regs_max < 3 ? 3 : ldm_regs_max;
        int32 ldm = OP_LDMFD | condition | F_WRITEBACK | F_RN(R_SP);
        if (maxcount < count) {
            setsp |= MSBits(mask, maxcount);
            mask &= ~setsp;
            count -= maxcount;
            do {
                unsigned n = count > maxcount ? maxcount : count;
                int32 mask1 = LSBits(mask, n);
                mask ^= mask1;
                outinstr(ldm | mask1);
                fpdesc_notespchange(-4L * n);
                count -= n;
            } while (count != 0);
            mask = setsp;
        }
        if (mask & regbit(R_SP)) ldm &= ~F_WRITEBACK;
        outinstr(ldm | mask | setsp);
        fpdesc_notespchange(-bitcount(mask) * 4);
    }
}

static bool ReturnIsSingleInstruction(void) {
   /* This must be kept up to date with routine_exit(), or code will
      be broken in places which assume a return is a single instruction
      (principly in switches).  To help, its structure follows that
      of routine_exit().
    */
    if ((procflags & NONLEAF) && (pcs_flags & PCS_INTERWORK)) return NO;
    if (target_stack_moves_once && !(procflags & NONLEAF)) return NO;
#ifndef PROFILE_COUNTS_INLINE
    if (profile_option) return NO;
#endif
    if (regmask & M_FVARREGS ||
        procauxflags & bitoffnaux_(s_irq))
        return NO;
    if ((procflags & NONLEAF) && !(pcs_flags & PCS_NOFP)) {
        return bitcount(regmask & M_VARREGS) + 3 <= ldm_regs_max;
    } else {
        if (realargwordsbelowfp != 0 || argstopopabovefp != 0 ||
            (!(regmask & M_LR) && (regmask & M_VARREGS)) ||
            bitcount(regmask & M_VARREGS)+1 > ldm_regs_max)
            return NO;
        return YES;
    }
}

/* Restore all registers for routine exit.  Normally to_pc is set to give */
/* a return, but if unset causes LR to be restored for a TAILCALL.        */
static void routine_exit(int32 condition, bool to_pc, int32 adjustsp)
{
    int32 mask = regmask;
    int32 ldm_link = (to_pc == 0 || (pcs_flags & PCS_INTERWORK)) ? M_LR :
                     procauxflags & bitoffnaux_(s_irq) ? M_LR :
                     (pcs_flags & PCS_CALLCHANGESPSR) ? M_PC :
                              M_PC | F_PSR;
    bool isleaf = !(procflags & NONLEAF) || !saveregs_done;

    if (!saveregs_done) mask = 0;

    /* Simulate J_SETSP, and its ARM elision before NONLEAF return.       */
    /* Use the condition mask to get the correct condition                */
    if (target_stack_moves_once && isleaf && saveregs_done)
    {
      /* don't update fp_minus_fp, since next basic block requires.       */
        condition_mask ^= condition;
        add_integer(R_SP, R_SP, greatest_stackdepth, 0);
        condition_mask ^= condition;
    }
    if (!saveregs_done)
        mask = 0;
    else if (HasFeature(Feature_DontUseLinkReg))
        mask |= M_LR;
#ifndef PROFILE_COUNTS_INLINE
    if (profile_option)
        outinstr3(OP_BL | condition, fn_exit_sym, NO);
#endif
    if ( !isleaf && !(pcs_flags & PCS_NOFP) &&
         !(procauxflags & bitoffnaux_(s_irq))) {
        unsigned count = (unsigned)bitcount(mask & M_VARREGS);
        fp_gen->calleerestore(mask, condition, UseFP, 0);
        mask = (mask & M_VARREGS) | regbit(R_FP) | regbit(R_SP) | ldm_link;
        if (count+3 <= ldm_regs_max)
            outinstr(OP_LDMDB | condition | F_RN(R_FP) | mask);
        else {
          /* sp may already be right, but I can't know because SETSPs have
             been peepholed out before returns
           */
            outinstr(OP_SUBN | condition | F_RD(R_SP) | F_RN(R_FP) |
                     4*(count + 3L));
            PopRegs(condition, mask);
        }
        if (mask & M_PC) return;
    } else {
        int32 realmask = mask;
        int32 extra_adjust = 0;
        FP_RestoreBase base = UseSP_Adjust;
        if (procauxflags & bitoffnaux_(s_irq)) {
            if (adjustsp != 0)
            {
                condition_mask ^= condition;
                add_integer(R_SP, R_SP, adjustsp, 0);
                condition_mask ^= condition;
            }
            mask &= M_VARREGS | M_ARGREGS | regbit(R_IP) | M_LR;
        } else {
            if (realargwordsbelowfp == 0 && adjustsp != 0)
            {
                condition_mask ^= condition;
                add_integer(R_SP, R_SP, adjustsp, 0);
                condition_mask ^= condition;
                adjustsp = 0;
            } else if (adjustsp != 0) {
                base = UseSP_NoAdjust;
                extra_adjust = fp_gen->restoresize(mask);
            }

            mask &= M_VARREGS;
        }
        fp_gen->calleerestore(realmask, condition, base, adjustsp);
        if (realargwordsbelowfp != 0 || adjustsp != 0) {
            condition_mask ^= condition;
            add_integer(R_SP, R_SP, (4*realargwordsbelowfp)+adjustsp+extra_adjust, 0);
            condition_mask ^= condition;
        }
        if (!saveregs_done)
            /* nothing */;
        else if ((regmask & M_LR) == 0 || argstopopabovefp != 0)
        {   mask |= (regmask & M_LR);
            if (mask != 0)    /* AM: for odd circ's in tail recursion */
                PopRegs(condition, mask);
            if (argstopopabovefp != 0)
                outinstr(OP_ADDN | condition | F_RD(R_SP) | F_RN(R_SP) |
                         (4*argstopopabovefp));
        } else {
            PopRegs(condition, mask | ldm_link);
            if (ldm_link & M_PC) return;
        }
    }
    if (to_pc) {
        if (procauxflags & bitoffnaux_(s_irq))
            outinstr(OP_SUBN | condition | F_RD(R_PC) | F_RN(R_LR) | F_SCC | 4);
        else if ((pcs_flags & PCS_INTERWORK))
            outinstr(OP_BX | condition | R_LR);
        else
            outinstr(OP_MOVR | condition | F_RD(R_PC) | R_LR |
                     ((pcs_flags & PCS_CALLCHANGESPSR) ? 0 : F_SCC));
    }
}

static void conditional_branch_to(int32 condition,
                                  LabelNumber *destination,
                                  bool bxxcase,
                                  int32 adjustsp)
{
    condition = C_FROMQ(condition);
    if (destination == RETLAB)
/* The test here is expected to detect all cases where the return ought    */
/* to expand into just one instruction.  Such cases are: 1. in a switch    */
/* branchtable, 2. returns with fp regs to restore when we try (harder)    */
/* to generate a single return sequence.  The latter trades a little loss  */
/* of speed for a (bigger?) improvement in code density.                   */
    {   if (adjustsp == 0 &&
             ( (bxxcase && !ReturnIsSingleInstruction()) ||
/* AM: extra test to avoid generating conditional returns as (a) there will  */
/* will probably be an unconditional one (main reason) and (b) slow on ARM-1 */
                ( (condition != (C_ALWAYS^C_ALWAYS) || condition_mask != C_ALWAYS
                                                    || lab_isset_(returnlab)) &&
                  (regmask & M_FVARREGS)!=0)))
        {   destination = returnlab;
        }
        else
        {   /* Only set a return label if this is an UNCONDITIONAL return. */
            if (condition == (C_ALWAYS^C_ALWAYS) &&
                condition_mask == C_ALWAYS &&
                adjustsp == 0 &&
                saveregs_done &&
                !lab_isset_(returnlab)) setlabel(returnlab);
            dbg_return(codebase+codep);
            routine_exit(condition, YES, adjustsp);
            return;
        }
    }
/* This is where I need to discriminate between the two sorts of things  */
/* that I put in the ->frefs field of a label entry.                     */
    if (lab_isset_(destination))
    {   int32 w = destination->u.defn;          /* ->frefs */
        outinstr(OP_B | condition |
                 ((((w & 0x00ffffff) - codep - 8) >> 2) & 0x00ffffff));
    }
    else
    {   addfref_(destination, codep | LABREF_BRANCH);
        outinstr(OP_B | condition);
    }
}

/* Exported routines...                                               */

static uint32 cond = Q_AL;

static void show_instruction_1(Icode const *ic)
{   PendingOp cur;

    cur.ic = *ic;
    cur.dataflow = cur.ic.op & J_DEADBITS;
    cur.ic.op &= ~J_DEADBITS;                  /* remove dataflow bits         */
    cur.cond = cond;
    cur.peep = 0;

    if (is_asminstr(cur.ic.op))
        translate_asm_instr (&cur);

    CheckJopcodeP(&cur, JCHK_MEM | JCHK_REGS | JCHK_SYSERR);

/* While code is still in flux, we assume all STRW's coming here have   */
/* J_ALIGN4&J_ALIGNWR set...                                            */
/* /* apparently, they don't have ALIGNWR...                            */
    { int32 op1 = cur.ic.op & (J_TABLE_BITS | J_ALIGNMENT);
      if (op1 == J_STRWK+J_ALIGN4 || op1 == J_STRWR+J_ALIGN4)
        cur.ic.op += J_STRK - J_STRWK;
    }
    switch (cur.ic.op) {
    case J_SETSP:
        {   int32 oldstack = cur.ic.r2.i, newstack = cur.ic.r3.i;
            int32 diff = newstack - oldstack;
            if (fp_minus_sp != oldstack)
                syserr(syserr_setsp_confused,
                       (long)fp_minus_sp, (long)oldstack, (long)newstack);
            fp_minus_sp = newstack;
            cur.ic.op = J_ADDK; cur.ic.r1.rr = R_SP; cur.ic.r2.rr = R_SP; cur.ic.r3.i = -diff;
            cur.dataflow = J_DEAD_R2;
        }
        break;
    case J_STACK:  fp_minus_sp = cur.ic.r3.i; break;
    case J_PUSHM:  fp_minus_sp += (4 * bitcount(cur.ic.r3.i)); break;
    case J_PUSHD:  cur.ic.r3.i = 0; fp_minus_sp += 8; break;
/* case J_PUSHR: should never reach armgen (removed in flowgraf.c) */
    case J_PUSHF:  cur.ic.r3.i = 0; fp_minus_sp += 4; break;

    case J_SUBK:   if ((cur.peep & P_SETCC) == 0 || cur.ic.r3.i != 0)
                   {    cur.ic.op = J_ADDK;
                        cur.ic.r3.i = -cur.ic.r3.i;
                   }    /* don't transform SUBS Rx, Ry, #0 into ADDS Rx, Ry, #0!!! */
                   break;
    case J_BICK:   cur.ic.op = J_ANDK;
                   cur.ic.r3.i = ~cur.ic.r3.i;
                   break;
    case J_CMNK:   if ((cur.peep & (P_SETPSR | P_SETCC)) == 0 || cur.ic.r3.i != 0)
                   {    cur.ic.op = J_CMPK;
                        cur.ic.r3.i = -cur.ic.r3.i;
                   }
                   break;

    case J_SHLK+J_SIGNED:
    case J_SHLK+J_UNSIGNED:
                   cur.ic.r3.i &= 255;
                   if (cur.ic.r3.i >= 32) {
                       cur.ic.op = J_MOVK; cur.dataflow &= ~J_DEAD_R2;
                       cur.ic.r3.i = 0;
                   }
                   break;
    case J_SHRK+J_UNSIGNED:
                   cur.ic.r3.i &= 255;             /* allow LSR #32 if the PSR is altered */
                   if (cur.ic.r3.i > 32 || (cur.ic.r3.i == 32 && !(cur.peep & P_SETCC))) {
                       cur.ic.op = J_MOVK; cur.dataflow &= ~J_DEAD_R2;
                       cur.ic.r3.i = 0;
                   }
                   break;
    case J_SHRK+J_SIGNED:
                   cur.ic.r3.i &= 255;
                   if (cur.ic.r3.i > 32) cur.ic.r3.i = 32;  /* allow ASR #32 */
                   break;
    }
    {   bool flush = NO;
        switch (cur.ic.op & ~Q_MASK) {
        case J_ENTER: case J_ENDPROC:
            cond = Q_AL; flush = YES; break;
        case J_SAVE:
        case J_INFOLINE: case J_INFOBODY: case J_INFOSCOPE:
        case J_OPSYSK: case J_CALLK: case J_CALLR: case J_CALLI:
#ifdef ARM_INLINE_ASSEMBLER
        case J_SWI:
#endif
        case J_CASEBRANCH: case J_BXX:
        case J_WORD: case J_ORG:
        case J_VSTORE: case J_USE:
            flush = YES; break;
        case J_ADDK:
            if (target_stack_moves_once && cur.ic.r1.r == R_SP && cur.ic.r2.r == R_SP)
                flush = YES;
            break;
        case J_CONDEXEC:
            cond = cur.ic.op & Q_MASK; /*flush = YES; */ break;
        case J_LABEL:
            cond = Q_AL;
        case J_B:
        case J_STACK:
            /*flush = YES;*/ break;
        }
        if ((cur.ic.op & J_BASEALIGN4) && !j_is_adcon(cur.ic.op)) {
            cur.ic.op = cur.ic.op & ~J_BASEALIGN4;
            cur.peep |= (cur.ic.op & J_ALIGNMENT) < J_ALIGN4 ? P_BASEALIGNED : 0;
        }
        if (cur.ic.flags & SET_CC)
            cur.peep |= (P_CMPZ | P_SETCC);
        peephole_op(&cur, flush);
        if (flush) ldm_flush();
    }
}

static bool ExpandInline(Symstr const *target, bool resinflags) {
    Icode op;
    if (target == bindsym_(exb_(sim.llfroml))) {
        INIT_IC(op, J_SHRK+J_SIGNED); op.r1.rr = R_A1+1; op.r2.rr = R_A1; op.r3.i = 31;
        show_instruction_1(&op);
        return YES;
    }
    if (target == bindsym_(exb_(sim.llfromu))) {
        INIT_IC(op, J_MOVK); op.r1.rr = R_A1+1; op.r3.i = 0;
        show_instruction_1(&op);
        return YES;
    }
    if (target == bindsym_(exb_(sim.lltol))) {
        return YES;
    }
    if (target == bindsym_(exb_(sim.lland))) {
        INIT_IC(op, J_ANDR+J_DEAD_R3); op.r1.rr = R_A1+1; op.r2.rr = R_A1+1; op.r3.rr = R_A1+3;
        show_instruction_1(&op);
        op.r1.rr = R_A1; op.r2.rr = R_A1; op.r3.rr = R_A1+2;
        show_instruction_1(&op);
        return YES;
    }
    if (target == bindsym_(exb_(sim.llor))) {
        INIT_IC(op, J_ORRR+J_DEAD_R3); op.r1.rr = R_A1+1; op.r2.rr = R_A1+1; op.r3.rr = R_A1+3;
        show_instruction_1(&op);
        op.r1.rr = R_A1; op.r2.rr = R_A1; op.r3.rr = R_A1+2;
        show_instruction_1(&op);
        return YES;
    }
    if (target == bindsym_(exb_(sim.lleor))) {
        INIT_IC(op, J_EORR+J_DEAD_R3); op.r1.rr = R_A1+1; op.r2.rr = R_A1+1; op.r3.rr = R_A1+3;
        show_instruction_1(&op);
        op.r1.rr = R_A1; op.r2.rr = R_A1; op.r3.rr = R_A1+2;
        show_instruction_1(&op);
        return YES;
    }
    if (target == bindsym_(exb_(sim.llnot))) {
        INIT_IC(op, J_NOTR); op.r1.rr = R_A1+1; op.r3.rr = R_A1+1;
        show_instruction_1(&op);
        op.r1.rr = R_A1; op.r3.rr = R_A1;
        show_instruction_1(&op);
        return YES;
    }
    if (target == bindsym_(exb_(sim.lladd)) && cond == Q_AL) {
        INIT_IC(op, J_ABINRR+J_DEAD_R3); op.flags = MKOP(A_ADD,CL_BIN)+SET_CC; op.r1.rr = R_A1; op.r2.rr = R_A1; op.r3.rr = R_A1+2;
        show_instruction_1(&op);
        op.flags = MKOP(A_ADC,CL_BIN); op.r1.rr = R_A1+1; op.r2.rr = R_A1+1; op.r3.rr = R_A1+3;
        show_instruction_1(&op);
        return YES;
    }
    if (target == bindsym_(exb_(sim.llsub)) && cond == Q_AL) {
        INIT_IC(op, J_ABINRR+J_DEAD_R3); op.flags = MKOP(A_SUB,CL_BIN)+SET_CC; op.r1.rr = R_A1; op.r2.rr = R_A1; op.r3.rr = R_A1+2;
        show_instruction_1(&op);
        op.flags = MKOP(A_SBC,CL_BIN); op.r1.rr = R_A1+1; op.r2.rr = R_A1+1; op.r3.rr = R_A1+3;
        show_instruction_1(&op);
        return YES;
    }
    if (target == bindsym_(exb_(sim.llrsb)) && cond == Q_AL) {
        INIT_IC(op, J_ABINRR+J_DEAD_R3); op.flags = MKOP(A_RSB,CL_BIN)+SET_CC; op.r1.rr = R_A1; op.r2.rr = R_A1; op.r3.rr = R_A1+2;
        show_instruction_1(&op);
        op.flags = MKOP(A_RSC,CL_BIN); op.r1.rr = R_A1+1; op.r2.rr = R_A1+1; op.r3.rr = R_A1+3;
        show_instruction_1(&op);
        return YES;
    }
    if (target == bindsym_(exb_(sim.llneg)) && cond == Q_AL) {
        INIT_IC(op, J_ABINRK); op.flags = MKOP(A_RSB+RN_CONST,CL_BIN)+SET_CC; op.r1.rr = R_A1; op.r2.rr = R_A1; op.r3.i = 0;
        show_instruction_1(&op);
        op.flags = MKOP(A_RSC+RN_CONST,CL_BIN); op.r1.rr = R_A1+1; op.r2.rr = R_A1+1; op.r3.i = 0;
        show_instruction_1(&op);
        return YES;
    }
    if (resinflags && cond == Q_AL)
    {
        if (target == bindsym_(exb_(sim.llcmpeq)) ||
            target == bindsym_(exb_(sim.llcmpne)) ||
            target == bindsym_(exb_(sim.llucmplt)) ||
            target == bindsym_(exb_(sim.llucmple)) ||
            target == bindsym_(exb_(sim.llucmpgt)) ||
            target == bindsym_(exb_(sim.llucmpge)))
        {
            INIT_IC(op, J_CMPR+J_DEAD_R2+J_DEAD_R3);
            op.r1.rr = GAP; op.r2.rr = R_A2; op.r3.rr = R_A4;
            show_instruction_1(&op);
            INIT_IC(op, J_CONDEXEC+Q_EQ);
            show_instruction_1(&op);
            INIT_IC(op, J_CMPR+J_DEAD_R2+J_DEAD_R3+Q_EQ);
            op.r1.rr = GAP; op.r2.rr = R_A1; op.r3.rr = R_A3;
            show_instruction_1(&op);
            INIT_IC(op, J_CONDEXEC+Q_AL);
            show_instruction_1(&op);
            return YES;
        }
        if (target == bindsym_(exb_(sim.llscmpge)) ||
            target == bindsym_(exb_(sim.llscmplt)))
        {
            INIT_IC(op, J_ABINRR+J_DEAD_R1+J_DEAD_R2+J_DEAD_R3);
            op.flags = MKOP(A_SUB,CL_BIN)+SET_CC; op.r1.rr = R_A1; op.r2.rr = R_A1; op.r3.rr = R_A1+2;
            show_instruction_1(&op);
            op.flags = MKOP(A_SBC,CL_BIN)+SET_CC; op.r1.rr = R_A1+1; op.r2.rr = R_A1+1; op.r3.rr = R_A1+3;
            show_instruction_1(&op);
            return YES;
        }
        if (target == bindsym_(exb_(sim.llscmple)) ||
            target == bindsym_(exb_(sim.llscmpgt)))
        {
            INIT_IC(op, J_ABINRR+J_DEAD_R1+J_DEAD_R2+J_DEAD_R3);
            op.flags = MKOP(A_SUB,CL_BIN)+SET_CC; op.r1.rr = R_A1; op.r2.rr = R_A3; op.r3.rr = R_A1;
            show_instruction_1(&op);
            op.flags = MKOP(A_SBC,CL_BIN)+SET_CC; op.r1.rr = R_A2; op.r2.rr = R_A4; op.r3.rr = R_A2;
            show_instruction_1(&op);
            return YES;
        }
    }
    return NO;
}

void show_instruction(Icode const *const ic)
{   if (ic->op == J_SAVE && target_stack_moves_once) {
        Icode op;
        show_instruction_1(ic);
        INIT_IC(op, J_SETSP); op.r1.rr = 0; op.r2.i = fp_minus_sp; op.r3.i = fp_minus_sp+greatest_stackdepth;
        show_instruction_1(&op);
        return;
    } else if (ic->op == J_CALLK && ExpandInline(ic->r3.sym, ic->r2.i & K_RESULTINFLAGS)) {
        return;
    } else if (ic->op == J_TAILCALLK && ExpandInline(ic->r3.sym, ic->r2.i & K_RESULTINFLAGS)) {
        Icode op;
        INIT_IC(op, J_B); op.r3.l = RETLAB;
        show_instruction_1(&op);
        return;
    }
    show_instruction_1(ic);
}

/* the next routine is required for the machine independent codebuf.c */
void branch_round_literals(LabelNumber *m)
{
    int32 c = condition_mask;
    condition_mask = C_ALWAYS;   /* in case conditional instructions */
    literal_pool_start = codebase+codep+4;
    conditional_branch_to(Q_AL, m, NO, 0);
    condition_mask = c;
}

static struct { char *name; Symstr const *sym; int32 op; } inlinetable[] = {
#ifdef FORTRAN
    {"__r_sqrt", 0, OP_CPOP | CPDO_SINGLE | F_SQT},
    {"__r_exp",  0, OP_CPOP | CPDO_SINGLE | F_EXP},
    {"__r_log",  0, OP_CPOP | CPDO_SINGLE | F_LGN},
    {"__r_lg10", 0, OP_CPOP | CPDO_SINGLE | F_LOG},
    {"__r_sin",  0, OP_CPOP | CPDO_SINGLE | F_SIN},
    {"__r_cos",  0, OP_CPOP | CPDO_SINGLE | F_COS},
    {"__r_tan",  0, OP_CPOP | CPDO_SINGLE | F_TAN},
    {"__r_asin", 0, OP_CPOP | CPDO_SINGLE | F_ASN},
    {"__r_acos", 0, OP_CPOP | CPDO_SINGLE | F_ACS},
    {"__r_atan", 0, OP_CPOP | CPDO_SINGLE | F_ATN},
    {"__r_abs", 0, OP_CPOP | CPDO_SINGLE | F_ABS},

    {"__d_sqrt", 0, OP_CPOP | CPDO_DOUBLE | F_SQT},
    {"__d_exp",  0, OP_CPOP | CPDO_DOUBLE | F_EXP},
    {"__d_log",  0, OP_CPOP | CPDO_DOUBLE | F_LGN},
    {"__d_lg10", 0, OP_CPOP | CPDO_DOUBLE | F_LOG},
    {"__d_tan",  0, OP_CPOP | CPDO_DOUBLE | F_TAN},
    {"__d_asin", 0, OP_CPOP | CPDO_DOUBLE | F_ASN},
    {"__d_acos", 0, OP_CPOP | CPDO_DOUBLE | F_ACS},
#endif
    {"__d_sin",  0, OP_CPOP | CPDO_DOUBLE | F_SIN},
    {"__d_cos",  0, OP_CPOP | CPDO_DOUBLE | F_COS},
    {"__d_atan", 0, OP_CPOP | CPDO_DOUBLE | F_ATN},
    {"__d_abs", 0, OP_CPOP | CPDO_DOUBLE | F_ABS},
    {0,0,0}};

static void initinlinetable(void)
{
    int i;
    for (i = 0; ; i++) {
        char *name = inlinetable[i].name;
        if (name == NULL) return;
        inlinetable[i].sym = sym_insert_id(name);
    }
}

int32 target_inlinable(Binder const *b, int32 nargs)
{
    if (nargs == 1) {
        int i;
        Symstr const *sym = bindsym_(b);
        for (i = 0; ; i++) {
            Symstr const *tsym = inlinetable[i].sym;
            if (tsym == 0) return 0;
            if (tsym == sym) return inlinetable[i].op;
        }
    }
    return 0;
}

#define TYPESPEC_DOUBLE typespecmap_(te_double)
#define TYPESPEC_FLOAT typespecmap_(te_float)

#define INFINITY 0x10000000

void localcg_newliteralpool(void) {
    if (in_code) {
        literal_pool_start = codebase+codep;
        in_code = NO;
    }
    mustlitby = INFINITY;
}

void localcg_endcode(void) {
    describe_literal_pool();
}

void localcg_reinit(void) {
    ipvalue.valid = NO;
    spareregs = 0;
    fpdesc_init();
    peephole_reinit();
    KillKnownRegisterValues(AllIntRegs);
}

void mcdep_init(void)
{
    ldm_reinit();
    adconpool_init();
    in_code = YES;
    literal_pool_number = 0;
    localcg_newliteralpool();
    condition_mask = C_ALWAYS;
    if (fpu_type == fpu_amp) {
      fp_gen = &amp_gen;
      disass_addcopro(AMP_DisassCP);
      saved_fpreg_words = 1;
      fp_arg_words = 1;
    } else {
      fp_gen = &fpa_gen;
      saved_fpreg_words = 3;
      fp_arg_words = 2;
    }
    lib_reloc_sym = sym_insert_id("_Lib$Reloc$Off");
    mod_reloc_sym = sym_insert_id("_Mod$Reloc$Off");
#ifndef PROFILE_COUNTS_INLINE
    fn_entry_sym = sym_insert_id("__fn_entry");
    fn_exit_sym = sym_insert_id("__fn_exit");
#endif
    /* we must do the following initialisations once per module to     */
    /* avoid the store being reallocated (misapprehension & bug fix).  */
    fpliterals[0].val = fc_zero.d;
    fpliterals[1].val = fc_one.d;
    fpliterals[2].val = fc_two.d;
    fpliterals[3].val = real_of_string("3.0", TYPESPEC_DOUBLE);
    fpliterals[4].val = real_of_string("4.0", TYPESPEC_DOUBLE);
    fpliterals[5].val = real_of_string("5.0", TYPESPEC_DOUBLE);
    fpliterals[6].val = real_of_string("0.5", TYPESPEC_DOUBLE);
    fpliterals[7].val = real_of_string("10.0", TYPESPEC_DOUBLE);
    fpliterals[8].val = fc_zero.s;
    fpliterals[9].val = fc_one.s;
    fpliterals[10].val = fc_two.s;
    fpliterals[11].val = real_of_string("3.0", TYPESPEC_FLOAT);
    fpliterals[12].val = real_of_string("4.0", TYPESPEC_FLOAT);
    fpliterals[13].val = real_of_string("5.0", TYPESPEC_FLOAT);
    fpliterals[14].val = real_of_string("0.5", TYPESPEC_FLOAT);
    fpliterals[15].val = real_of_string("10.0", TYPESPEC_FLOAT);

    if (HasFeature(Feature_DontUseLinkReg)) avoidallocating(R_LR);
#ifdef TARGET_IS_UNIX
    avoidallocating(R_SL);
#else
    if (!(pcs_flags & PCS_NOSTACKCHECK)) {
        avoidallocating(R_SL);
        asm_setregname(R_SL, "sl");
    } else
        asm_setregname(R_SL, "v7");
#endif
    if (!(pcs_flags & PCS_NOFP)) {
        avoidallocating(R_FP);
        asm_setregname(R_FP, "fp");
    } else
        asm_setregname(R_FP, "v8");
    if (pcs_flags & PCS_REENTRANT) {
        avoidallocating(R_SB);
        asm_setregname((int)R_SB, "sb");
    } else
        asm_setregname((int)R_SB, "v6");

    initinlinetable();
    peephole_init();
}

void localcg_tidy(void)
{
    dbg_finalise();
    peephole_tidy();
}

/* End of section arm/gen.c */
