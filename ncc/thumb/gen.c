/* C compiler file thumb/gen.c :  Copyright (C) Codemist Ltd, 1994.      */
/* SPDX-Licence-Identifier: Apache-2.0 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

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
#include <assert.h>
#include <stdlib.h>

#define DEFINE_A_JOPTABLE 1

#include "globals.h"
#include "builtin.h"
#include "mcdep.h"
#include "target.h"
#include "mcdpriv.h"
#include "xrefs.h"
#include "ops.h"
#include "jopcode.h"
#include "store.h"
#include "codebuf.h"
#include "regalloc.h"
#include "cg.h"        /* for procflags, greatest_stackdepth */
#include "simplify.h"  /* for MCR_SIZE_MASK */
#include "errors.h"
#include "bind.h"
#include "aeops.h"
#include "arminst.h"

#define NONLEAF (PROC_ARGPUSH | PROC_ARGADDR | PROC_BIGSTACK | BLKCALL)
/* STACKCHECK (NONLEAF subset) defines when stack check is REALLY needed */
#define STACKCHECK (PROC_BIGSTACK | BLKCALL)
#define ARGS2STACK (PROC_ARGPUSH | PROC_ARGADDR)
#define IS_VARIADIC(m) ((m) == 0xfff)

#define USES_BL_AS_B 1

#define ALL_REGS (0xffff)
#define NoRegister ((RealRegister)-1)

#define disable_opt (gen_opt_disabled)

static int32 firstargoff;
static int32 fp_minus_sp;

typedef struct Branch {
  struct Branch *cdr;
  int32 codep;
  int32 condition;
  LabelNumber *dest;
} Branch;

Branch *available_branches;

#define FREF_BRANCH     0
#define FREF_DCB        1
#define FREF_DCW        2

#define FREF_CONDITION(x) ((x) & 0xffff0000)
#define FREF_TYPE(x) ((x) & 0xff)

typedef struct FRef_Branch {
  struct FRef_Branch *cdr;
  int32 pcref;
  int32 codep;
  int32 flags;
  LabelNumber *real_dest;
  LabelNumber *chained_dest;
} FRef_Branch;

int32 mustbranchlitby = 0x10000000;
int32 mustlitby       = 0x10000000;
static bool in_code;
static int32 literal_pool_start;
static int literal_pool_number;

FRef_Branch *fref_branches;
FRef_Branch **fref_branches_head;
int32 branchpoolsize;

static LabelNumber *returnlab;
static LabelNumber *entrylab;

/* 'spareregs' is a mask of the free regs at the start of the current opcode passed
 * to show instruction.
 * 'nspareregs' is the mask of the free regs when is opcode is finished.
 */
static int32 spareregs, nspareregs;

#define AddCodeXref3(t, n) (codexrefs = (CodeXref *)global_list3(SU_Xref, codexrefs, t, n))
#define AddCodeXref4(t, n, x) (codexrefs = (CodeXref *)global_list4(SU_Xref, codexrefs, t, n, x))
#define AddCodeXref5(t, n, x, y) (codexrefs = (CodeXref *)global_list5(SU_Xref, codexrefs, t, n, x, y))

bool immed_cmp(int32 n) { return n >= 0 && n <= 0xff; }

int integer_load_max;
int ldm_regs_max;

static LabelNumber *deadcode;

static Symstr *call_via[8];

static Symstr *t_sym;

#if 0
#undef addfref_
static void addfref_(LabelNumber *l, int32 v)
{
    fprintf(stderr, "%.8x: (addfref_ @ %08x) F%dL%d\n", codebase + codep, v, current_procnum, lab_name_(l) & 0xfffff);
    l->u.frefs = (List *)binder_icons2((l)->u.frefs,(v));
}
#endif

RealRegister local_base(Binder const *b)
{
    IGNORE(b);
    return R_SP;
}

static int32 c_of_q(int32 q)
{
    switch (q & ~Q_UBIT) {
      case Q_EQ & ~Q_UBIT: return C_EQ;
      case Q_NE & ~Q_UBIT: return C_NE;
      case Q_HS & ~Q_UBIT: return C_HS;
      case Q_LO & ~Q_UBIT: return C_LO;
      case Q_PL & ~Q_UBIT: return C_PL;
      case Q_MI & ~Q_UBIT: return C_MI;
      case Q_HI & ~Q_UBIT: return C_HI;
      case Q_LS & ~Q_UBIT: return C_LS;
      case Q_GE & ~Q_UBIT: return C_GE;
      case Q_LT & ~Q_UBIT: return C_LT;
      case Q_GT & ~Q_UBIT: return C_GT;
      case Q_LE & ~Q_UBIT: return C_LE;
      case Q_AL & ~Q_UBIT: return C_AL;
      default:
        syserr("Unknown condition %lx", q);
        return 0;
    }
}

static int32 procmask;          /* int regs to restore.                 */
static int32 pushed_args;
static bool stack_args_split;
static bool pushed_lr;
static int32 r_fr;
static int32 intsavewordsbelowfp, argwordsbelowfp, realargwordsbelowfp;

#ifdef TARGET_HAS_FP_OFFSET_TABLES

static struct {
    ProcFPDesc desc;
    FPList **tail;
    int32 offset;
} fpd;

static void fpdesc_init(void) {
    fpd.desc.fplist = NULL; fpd.tail = &fpd.desc.fplist;
    fpd.desc.startaddr = codebase+codep;
    fpd.desc.saveaddr = -1;
    fpd.desc.codeseg = bindsym_(codesegment);
    fpd.desc.initoffset = fpd.offset = -4;
    /* Ensure fpdesc_newsp gets the correct offset if called before routine_entry */
    intsavewordsbelowfp = 0;
    realargwordsbelowfp = 0;
    argwordsbelowfp = 0;
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
    FPList *p = (FPList *)SynAlloc(sizeof(FPList));
    cdr_(p) = NULL;
    p->addr = codebase+codep;
    p->change = n;
    *fpd.tail = p;
    fpd.tail = &cdr_(p);
    fpd.offset += n;
}

static void fpdesc_notespchange(int32 n) {
    fplist_add(n);
}

static void fpdesc_newsp(int32 n) {
    n += 4*(intsavewordsbelowfp + realargwordsbelowfp) - 4;
    if (n - fpd.offset != 0) fplist_add(n - fpd.offset);
}

#else

#define fpdesc_init()  0
#define fpdesc_newsp(n) 0
#define fpdesc_setinitoffset(n)  0
#define fpdesc_enterproc() 0
#define fpdesc_endproc() 0

#endif

int32 local_address(Binder const *b)
{
    int32 p = bindaddr_(b);
    int32 n = p & ~BINDADDR_MASK;
#if 0
    printf("BINDADDR = %x/%d for %s\n", p, p & ~BINDADDR_MASK,
           symname_(bindsym_(b)));
#endif
    switch (p & BINDADDR_MASK)
    {
default:
        syserr("local_address %lx", (long)p);
case BINDADDR_LOC:
        return fp_minus_sp - n;
case BINDADDR_ARG:
        if (stack_args_split) {
            if (n < NARGREGS * 4) {
                return fp_minus_sp + n;
            } else {
                return fp_minus_sp + firstargoff - NARGREGS * 4 + n;
            }
        }
        return fp_minus_sp + firstargoff + (p & ~BINDADDR_MASK);
    }
}

int32 local_fpaddress(Binder const *b)
{
    int32 p = bindaddr_(b);
    int32 n = p & ~BINDADDR_MASK;

    switch (p & BINDADDR_MASK) {
case BINDADDR_LOC:
        n = -(n + 4 * (intsavewordsbelowfp + realargwordsbelowfp));
        break;
case BINDADDR_ARG:
        n = (n >= 4*argwordsbelowfp) ?
                (n - 4 * argwordsbelowfp) :
                (n - 4 * (realargwordsbelowfp + intsavewordsbelowfp));
        break;
default:
        syserr(syserr_debug_addr);
        break;
    }
    return n+4;
}

RealRegister local_fpbase(Binder const *b) {
    IGNORE(b);
    return R_NOFPREG;
}

int32 power_of_two(int32 n)
{
/* If n is an exact power of two this returns the power, else -1         */
    int32 s = 0, w;
    if (n != (n&(-n))) return(-1);
    for(w=1; w!=0; w = w<<1)
        if (w==n) return(s);
        else s++;
    return (-1);
}

static int32 casebranch_litpool = 0;
static int32 casebranch_pending = -1;
static int32 casebranch_pending_m;
static int32 casebranch_codep;

#define USE_DCB_FOR_CASEBRANCH 32
#define USE_DCW_FOR_CASEBRANCH 64

#define use_dcw use_bl
static int use_bl;

static void outDCB(unsigned32 w)
{
    if (w & ~0xffL) syserr("outDCB(%lx)", (long)w);
    if ((codep & 3) == 0) {
        outcodeword(0, LIT_OPCODE);
        codep -= 4; /* ensure room */
    }
    if ((codep & 1) == 0)
        code_flag_(codep) = LIT_BB;
    code_byte_(codep) = w;
    codep += 1;
}

static void outDCW(unsigned32 w)
{
    if (w & ~0xffffL) syserr("outDCB(%lx)", (long)w);
    if (codep & 1) outDCB(0);
    if ((codep & 2) == 0) {
        outcodeword(0, LIT_OPCODE);
        codep -= 4;  /* ensure room */
    }
    code_flag_(codep) = LIT_H;
    code_hword_(codep) = w;
    codep += 2;
}

static void outHW(unsigned32 w)
{
    if (w & ~0xffffL) syserr("outHW(%lx)", (long)w);
    if (codep & 1) outDCB(0);
    if ((codep & 2) == 0) {
        outcodeword(0, LIT_OPCODE);
        codep -= 4;  /* ensure room */
    }
    code_hword_(codep) = w;
    codep += 2;
}

static void outHWaux(unsigned32 w, void *s)
{
    if (w & ~0xffffL) syserr("outHW(%lx)", (long)w);
    if (codep & 1) outDCB(0);
    if ((codep & 2) == 0) {
        outcodeword(0, LIT_OPCODE);
        codep -= 4;  /* ensure room */
    }
    code_hword_(codep) = (unsigned16)w;
/*
 * To ensure that I have room here for the information needed I have to be
 * clear that consecutive instructions may NOT both contain an AUX entry.
 */
#ifndef NO_ASSEMBLER_OUTPUT
    if (asmstream) code_aux_(codep & (-2)) = s;
#endif
    codep += 2;
}

typedef struct LDM_STM {
  int32 op;               /* 0 / F_LDRI5 / F_STRI5 */
  int32 base;             /* Base reg */
  int32 mask;
  int32 reg_off[8];       /* Offset from base of each reg loaded, -ve => not loaded */
} LDM_STM;

static LDM_STM ldm_stm;

#define CLM_MAX 16

typedef struct CLM {
  int32 z_reg;
  int32 base;
  int32 n;
  int32 offset[CLM_MAX];
} CLM;

static CLM clm;

#define REGV_UNKNOWN    0       /* Contents of reg are unknown */
#define REGV_CONSTANT   1       /* Register contains a constant */
#define REGV_BASE       2       /* Register contains reg + offset */
#define REGV_ADCON      3       /* Register contains adcon + offset */

typedef struct RegValue {
    char typ;
    int32 reg;
    Symstr *name;
    int32 value;
} RegValue;

static int32 pending_regs;
static RegValue reg_values[16];

/* Set to a value to indicate the register which last affected the N & Z flags */
static RealRegister flags_reg;
/* Set if the flags should have been set as the result of a cmp <flags_reg>, #0
 * which was elided.
 * This is necessary if one of BCC, BCS, BVS, BVC, BHI, BLS, BGE, BLT, BGT or BLE
 * is issued in which case we must perform the following transformations
 * BCC, BCS, BVS, BVC -> ??? (syserr probably as this should never happen)
 * BHI -> BNE
 * BLS -> BEQ
 * BGE -> BPL
 * BLT -> BMI
 * BGT, BLE -> Reinsert CMP <flags_reg>, #0
 */
static int cmpz_flag;

static uint32 andk_flag;

static RealRegister cmp_reg;
static int32 cmp_value;

static void outop(int32 op, int32 r1, int32 r2, int32 m);
static bool outop0(int32 op, int32 r1, int32 r2, int32 m);
static void outop2(int32 op, int32 r1, int32 r2, int32 m);
static void outop_direct(int32 op, int32 r1, int32 r2, int32 m);
static void flush_spareregs(int32 mask);
static void flush_pending(int32 mask);
static void check_pending(int32 op, int32 r1, int32 r2, int32 m, int nospcheck);

int32 CheckSWIValue(int32 n) {
    if ((uint32)n > 0xff) {
        cc_err(gen_err_swi, n);
        n = 0xff;
    }
    return n;
}

#define InstructionFieldOverflow(op, r1, r2, m) \
  syserr("Instruction field overflow, op = %x, r1 = %x, r2 = %x, m = %x",\
         (int)(op), (int)(r1), (int)(r2), (int)(m))

static void outop_direct(int32 op, int32 r1, int32 r2, int32 m)
{
    int32 spchange = 0;
    int i;

#if 0
    if (!(disable_opt)) {
      switch (op) {
        case F_CMP:
        case F_CMN:
          if (reg_values[m].typ == REGV_CONSTANT) {
            cmp_reg = r2;
            cmp_value = reg_values[m].value;
            if (op == F_CMN) cmp_value = -cmp_value;
          } else
            cmp_reg = NoRegister;
          flags_reg = NoRegister;
          cmpz_flag = 0;
          andk_flag = 0;
          break;

        case F_CMP8:
          andk_flag = 0;
          cmp_reg = r1;
          cmp_value = m;
          if (m == 0) {
            if (r1 == flags_reg) {
              cmpz_flag = 1;
              return;
            } else
              flags_reg = r1;
          } else
            flags_reg = NoRegister;
          cmpz_flag = 0;
          break;

        case F_ADDI8:
        case F_SUBI8:
        case F_ADDI3:
        case F_SUBI3:

        case F_ADD3R:
        case F_SUB3R:

        case F_LSLK:
        case F_LSRK:
        case F_ASRK:

        case F_MOV8:
          cmp_reg = r1;
          cmp_value = 0;
          flags_reg = r1;
          cmpz_flag = 0;
          andk_flag = 0;
          reg_values[r1].typ = REGV_UNKNOWN;
          if (pending_regs & (1L << r1)) syserr("op = %.4x: R%d pending", (int)op, (int)r1);
          break;

        case F_LDRSP:
        case F_LDRLIT:
        case F_ADDRPC:
        case F_ADDRSP:
          if (flags_reg == r1) {
            cmp_reg = NoRegister;
            flags_reg = NoRegister;
          }
          reg_values[r1].typ = REGV_UNKNOWN;
          if (pending_regs & (1L << r1)) syserr("op = %.4x: R%d pending", (int)op, (int)r1);
          break;

        case F_AND:
        case F_OR:
        case F_EOR:
        case F_BIC:
        case F_NEG:
        case F_MUL:
        case F_MVN:
        case F_LSL:
        case F_LSR:
        case F_ASR:
        case F_ROR:
        case F_ADC:
        case F_SBC:
          cmp_reg = r2;
          cmp_value = 0;
          flags_reg = r2;
          cmpz_flag = 0;
          andk_flag = 0;
        case F_MOVHL:
        case F_ADDHL:
          reg_values[r2].typ = REGV_UNKNOWN;
          if (pending_regs & (1L << r2)) syserr("op = %.4x: R%d pending", (int)op, (int)r2);
          break;

        case F_LDRHADDR:
        case F_LDSBADDR:
        case F_LDSHADDR:
        case F_LDRHI5:

        case F_LDRADDR:
        case F_LDRBADDR:
        case F_LDRI5:
        case F_LDRBI5:
          if (flags_reg == r2) {
            cmp_reg = NoRegister;
            flags_reg = NoRegister;
          }
          reg_values[r2].typ = REGV_UNKNOWN;
          if (pending_regs & (1L << r2)) syserr("op = %.4x: R%d pending", (int)op, (int)r2);
          break;

        case F_LDM:
        case F_STM:
        case F_POP:
        case F_PUSH:
          if (op == F_POP || op == F_PUSH)
            r1 = R_SP;
          reg_values[r1].typ = REGV_UNKNOWN;
          if (pending_regs & (1L << r1)) syserr("op = %.4x: R%d pending", (int)op, (int)r1);
          if (op == F_LDM || op == F_POP) {
              for (i = 0; i < 8; i++) {
                if (m & (1L << i)) {
                  if (flags_reg == i) {
                    cmp_reg = NoRegister;
                    flags_reg = NoRegister;
                  }
                  reg_values[i].typ = REGV_UNKNOWN;
                  if (pending_regs & (1L << i)) syserr("op = %.4x: R%d pending", (int)op, (int)i);
                }
              }
          }
          break;

        case F_ADDSP:
        case F_SUBSP:
          reg_values[R_SP].typ = REGV_UNKNOWN;
          if (pending_regs & (1 << R_SP)) syserr("op = %.4x: R%d pending", (int)op, R_SP);
          break;
      }
    }
    switch (op) {
      case F_ADDI3:
      case F_SUBI3:
      case F_ADD3R:
      case F_SUB3R:
        if ((unsigned32)m > 7)
            syserr("Instruction field overflow, op = %x, r1 = %x, r2 = %x, m = %x",
                   (int)op, (int)r1, (int)r2, (int)m);

      case F_LSLK:
      case F_LSRK:
      case F_ASRK:
        if ((unsigned32)m > 31 || (unsigned32)r1 > 7 || (unsigned32)r2 > 7)
            syserr("Instruction field overflow, op = %x, r1 = %x, r2 = %x, m = %x",
                   (int)op, (int)r1, (int)r2, (int)m);
        op |= (m << 6) | (r2 << 3) | r1;
        break;

      case F_STRHADDR:
      case F_LDRHADDR:
      case F_LDSBADDR:
      case F_LDSHADDR:

      case F_STRADDR:
      case F_STRBADDR:
      case F_LDRADDR:
      case F_LDRBADDR:
        if ((unsigned32)m > 7)
            syserr("Instruction field overflow, op = %x, r1 = %x, r2 = %x, m = %x",
                   (int)op, (int)r1, (int)r2, (int)m);

      case F_STRHI5:
      case F_LDRHI5:

      case F_STRI5:
      case F_LDRI5:
      case F_STRBI5:
      case F_LDRBI5:
        if ((unsigned32)m > 31 || (unsigned32)r1 > 7 || (unsigned32)r2 > 7)
            syserr("Instruction field overflow, op = %x, r1 = %x, r2 = %x, m = %x",
                   (int)op, (int)r1, (int)r2, (int)m);

        op |= (m << 6) | (r1 << 3) | r2;
        break;

      case F_AND:
      case F_EOR:
      case F_LSL:
      case F_LSR:
      case F_ASR:
      case F_ADC:
      case F_SBC:
      case F_ROR:
      case F_TST:
      case F_NEG:
      case F_CMP:
      case F_CMN:
      case F_OR:
      case F_MUL:
      case F_BIC:
      case F_MVN:

      case F_ADDHL:
      case F_ADDLH:
      case F_ADDHH:

      case F_CMPHL:
      case F_CMPLH:
      case F_CMPHH:

      case F_MOVHL:
      case F_MOVLH:
      case F_MOVHH:
        if ((unsigned32)m > 7 || (unsigned32)r2 > 7)
            syserr("Instruction field overflow, op = %x, r1 = %x, r2 = %x, m = %x",
                   (int)op, (int)r1, (int)r2, (int)m);
        op |= (m << 3) | r2;
        break;

      case F_BX_L:
      case F_BX_H:
        if ((unsigned32)r2 > 7)
            syserr("Instruction field overflow, op = %x, r1 = %x, r2 = %x, m = %x",
                   (int)op, (int)r1, (int)r2, (int)m);
        op |=  r2 << 3;
        break;

      case F_MOV8:
      case F_CMP8:
      case F_ADDI8:
      case F_SUBI8:

      case F_LDRLIT:

      case F_STRSP:
      case F_LDRSP:

      case F_STM:
      case F_LDM:

      case F_ADDRPC:
      case F_ADDRSP:
        if ((unsigned32)m > 255 || (unsigned32)r1 > 7)
            syserr("Instruction field overflow, op = %x, r1 = %x, r2 = %x, m = %x",
                   (int)op, (int)r1, (int)r2, (int)m);
        op |= (r1 << 8) | m;
        break;

      case F_PUSH:
      case F_POP:
        if ((unsigned32)m > 511)
            syserr("Instruction field overflow, op = %x, r1 = %x, r2 = %x, m = %x",
                   (int)op, (int)r1, (int)r2, (int)m);
        spchange = bitcount(m) * 4;
        if (op == F_POP) spchange = -spchange;
        op |= m;
        break;

      case F_ADDSP:
      case F_SUBSP:
        if ((unsigned32)m > 127)
            syserr("Instruction field overflow, op = %x, r1 = %x, r2 = %x, m = %x",
                   (int)op, (int)r1, (int)r2, (int)m);
        spchange = m * 4;
        if (op == F_ADDSP) spchange = - spchange;
        op |= m;
        break;

      case F_SWI:
        if ((unsigned32)m > 255)
            syserr("Instruction field overflow, op = %x, r1 = %x, r2 = %x, m = %x",
                   (int)op, (int)r1, (int)r2, (int)m);

      case F_B:
      case F_CALL1:
      case F_CALL:
        if ((unsigned32)m > 0x7ff)
            syserr("Instruction field overflow, op = %x, r1 = %x, r2 = %x, m = %x",
                   (int)op, (int)r1, (int)r2, (int)m);
        op |= m;
        break;

      case F_BC:
        if ((unsigned32)m > 255)
            syserr("Instruction field overflow, op = %x, r1 = %x, r2 = %x, m = %x",
                   (int)op, (int)r1, (int)r2, (int)m);
        op |= r2 | m;
        break;

      default:
        syserr("unknown op 0x%x in outop_direct\n", op);
        break;
    }
#else
    if (!(disable_opt)) {
        if (op == F_CMP || op == F_CMN) {
          if (reg_values[m].typ == REGV_CONSTANT) {
            cmp_reg = r2;
            cmp_value = reg_values[m].value;
            if (op == F_CMN) cmp_value = -cmp_value;
          } else
            cmp_reg = NoRegister;
          flags_reg = NoRegister;
          cmpz_flag = 0;
          andk_flag = 0;
        } else if (op == F_CMP8) {
          andk_flag = 0;
          cmp_reg = r1;
          cmp_value = m;
          if (m == 0) {
            if (r1 == flags_reg) {
              cmpz_flag = 1;
              return;
            } else
              flags_reg = r1;
          } else
            flags_reg = NoRegister;
          cmpz_flag = 0;
        } else if (op == F_ADDI8 || op == F_SUBI8 || op == F_ADDI3 ||
                op == F_SUBI3 || op == F_ADD3R || op == F_SUB3R ||
                op == F_LSLK || op == F_LSRK || op == F_ASRK || op == F_MOV8) {
          cmp_reg = r1;
          cmp_value = 0;
          flags_reg = r1;
          cmpz_flag = 0;
          andk_flag = 0;
          reg_values[r1].typ = REGV_UNKNOWN;
          if (pending_regs & (1L << r1)) syserr("op = %.4x: R%d pending", (int)op, (int)r1);
        } else if (op == F_LDRSP || op == F_LDRLIT || op == F_ADDRPC || op == F_ADDRSP) {
          if (flags_reg == r1) {
            cmp_reg = NoRegister;
            flags_reg = NoRegister;
          }
          reg_values[r1].typ = REGV_UNKNOWN;
          if (pending_regs & (1L << r1)) syserr("op = %.4x: R%d pending", (int)op, (int)r1);
        } else if (op == F_AND || op == F_OR || op == F_EOR || op == F_BIC ||
                op == F_NEG || op == F_MUL || op == F_MVN || op == F_LSL ||
                op == F_LSR || op == F_ASR || op == F_ROR || op == F_ADC ||
                op == F_SBC) {
          cmp_reg = r2;
          cmp_value = 0;
          flags_reg = r2;
          cmpz_flag = 0;
          andk_flag = 0;
          reg_values[r2].typ = REGV_UNKNOWN;
          if (pending_regs & (1L << r2)) syserr("op = %.4x: R%d pending", (int)op, (int)r2);
        } else if (op == F_MOVHL || op == F_ADDHL) {
          reg_values[r2].typ = REGV_UNKNOWN;
          if (pending_regs & (1L << r2)) syserr("op = %.4x: R%d pending", (int)op, (int)r2);
        } else if (op == F_LDRHADDR || op == F_LDSBADDR || op == F_LDSHADDR ||
                op == F_LDRHI5 || op == F_LDRADDR || op == F_LDRBADDR ||
                op == F_LDRI5 || op == F_LDRBI5) {
          if (flags_reg == r2) {
            cmp_reg = NoRegister;
            flags_reg = NoRegister;
          }
          reg_values[r2].typ = REGV_UNKNOWN;
          if (pending_regs & (1L << r2)) syserr("op = %.4x: R%d pending", (int)op, (int)r2);
        } else if (op == F_LDM || op == F_POP || op == F_STM || op == F_PUSH) {
          if (op == F_POP || op == F_PUSH)
            r1 = R_SP;
          reg_values[r1].typ = REGV_UNKNOWN;
          if (pending_regs & (1L << r1)) syserr("op = %.4x: R%d pending", (int)op, (int)r1);
          if (op == F_LDM || op == F_POP) {
              for (i = 0; i < 8; i++) {
                if (m & (1L << i)) {
                  if (flags_reg == i) {
                    cmp_reg = NoRegister;
                    flags_reg = NoRegister;
                  }
                  reg_values[i].typ = REGV_UNKNOWN;
                  if (pending_regs & (1L << i)) syserr("op = %.4x: R%d pending", (int)op, (int)i);
                }
              }
          }
        } else if (op == F_ADDSP || op == F_SUBSP) {
          reg_values[R_SP].typ = REGV_UNKNOWN;
          if (pending_regs & (1 << R_SP)) syserr("op = %.4x: R%d pending", (int)op, (int)R_SP);
        }
    }
    if (op == F_ADDI3 || op == F_SUBI3 || op == F_ADD3R || op == F_SUB3R) {
        if ((unsigned32)m > 7)
            InstructionFieldOverflow(op, r1, r2, m);
        if ((unsigned32)m > 31 || (unsigned32)r1 > 7 || (unsigned32)r2 > 7)
            InstructionFieldOverflow(op, r1, r2, m);
        op |= (m << 6) | (r2 << 3) | r1;
    } else if (op == F_LSLK || op == F_LSRK || op == F_ASRK) {
        if ((unsigned32)m > 31 || (unsigned32)r1 > 7 || (unsigned32)r2 > 7)
            InstructionFieldOverflow(op, r1, r2, m);
        op |= (m << 6) | (r2 << 3) | r1;
    } else if (op == F_STRHADDR || op == F_LDRHADDR || op == F_LDSBADDR ||
                op == F_LDSHADDR || op == F_STRADDR || op == F_STRBADDR ||
                op == F_LDRADDR || op == F_LDRBADDR) {
        if ((unsigned32)m > 7)
            InstructionFieldOverflow(op, r1, r2, m);
        if ((unsigned32)m > 31 || (unsigned32)r1 > 7 || (unsigned32)r2 > 7)
            InstructionFieldOverflow(op, r1, r2, m);
        op |= (m << 6) | (r1 << 3) | r2;
    } else if (op == F_STRHI5 || op == F_LDRHI5 || op == F_STRI5 ||
                op == F_LDRI5 || op == F_STRBI5 || op == F_LDRBI5) {
        if ((unsigned32)m > 31 || (unsigned32)r1 > 7 || (unsigned32)r2 > 7)
            InstructionFieldOverflow(op, r1, r2, m);
        op |= (m << 6) | (r1 << 3) | r2;
    } else if (op == F_AND || op == F_EOR || op == F_LSL || op == F_LSR ||
                op == F_ASR || op == F_ADC || op == F_SBC || op == F_ROR ||
                op == F_TST || op == F_NEG || op == F_CMP || op == F_CMN ||
                op == F_OR || op == F_MUL || op == F_BIC || op == F_MVN ||
                op == F_ADDHL || op == F_ADDLH || op == F_ADDHH || op == F_CMPHL ||
                op == F_CMPLH || op == F_CMPHH || op == F_MOVHL || op == F_MOVLH ||
                op == F_MOVHH) {
        if ((unsigned32)m > 7 || (unsigned32)r2 > 7)
            InstructionFieldOverflow(op, r1, r2, m);
        op |= (m << 3) | r2;
    } else if (op == F_BX_L || op == F_BX_H) {
        if ((unsigned32)r2 > 7)
            InstructionFieldOverflow(op, r1, r2, m);
        op |=  r2 << 3;
    } else if (op == F_MOV8 || op == F_CMP8 || op == F_ADDI8 || op == F_SUBI8 ||
                op == F_LDRLIT || op == F_STRSP || op == F_LDRSP || op == F_STM ||
                op == F_LDM || op == F_ADDRPC || op == F_ADDRSP) {
        if ((unsigned32)m > 255 || (unsigned32)r1 > 7)
            InstructionFieldOverflow(op, r1, r2, m);
        op |= (r1 << 8) | m;
    } else if (op == F_ADDSP || op == F_SUBSP) {
        if ((unsigned32)m > 127)
            InstructionFieldOverflow(op, r1, r2, m);
        spchange = m * 4;
        if (op == F_ADDSP) spchange = - spchange;
        op |= m;
    } else if (op == F_SWI) {
        if ((unsigned32)m > 255)
            InstructionFieldOverflow(op, r1, r2, m);
        op |= m;
    } else if (op == F_PUSH || op == F_POP) {
        if ((unsigned32)m > 511)
            InstructionFieldOverflow(op, r1, r2, m);
        spchange = bitcount(m) * 4;
        if (op == F_POP) spchange = -spchange;
        op |= m;
    } else if (op == F_B || op == F_CALL1 || op == F_CALL) {
        if ((unsigned32)m > 0x7ff)
            InstructionFieldOverflow(op, r1, r2, m);
        op |= m;
    } else if (op == F_BC) {
        if ((unsigned32)m > 255)
            InstructionFieldOverflow(op, r1, r2, m);
        op |= r2 | m;
    } else
        syserr("unknown op 0x%x in outop_direct\n", (int)op);
#endif
    outHW((unsigned)op);
    if (spchange) fpdesc_notespchange(spchange);
}

static void outop2(int32 op, int32 r1, int32 r2, int32 m)
{
#if 0
    if (!(disable_opt)) {
      switch (op) {
        case F_ADDI8:
        case F_SUBI8:
          r2 = r1;
        case F_ADDI3:
        case F_SUBI3:
          reg_values[r1].typ = REGV_BASE;
          reg_values[r1].reg = r2;
          if (op == F_SUBI8 || op == F_SUBI3) m = -m;
          reg_values[r1].value = m;
          pending_regs |= 1L << r1;
          flags_reg = r1;
          andk_flag = 0;
          return;
        case F_ADDRSP:
          reg_values[r1].typ = REGV_BASE;
          reg_values[r1].reg = R_SP;
          reg_values[r1].value = m * 4;
          pending_regs |= 1L << r1;
          return;
        case F_ADDSP:
        case F_SUBSP:
          reg_values[R_SP].typ = REGV_BASE;
          reg_values[R_SP].reg = R_SP;
          if (op == F_SUBSP) m = -m;
          reg_values[R_SP].value = m * 4;
          pending_regs |= 1 << R_SP;
          return;
      }
    }
#else
    if (!(disable_opt)) {
        if (op == F_ADDI8 || op == F_SUBI8 || op == F_ADDI3 || op == F_SUBI3) {
          if (op == F_ADDI8 || op == F_SUBI8) r2 = r1;
          reg_values[r1].typ = REGV_BASE;
          reg_values[r1].reg = r2;
          if (op == F_SUBI8 || op == F_SUBI3) m = -m;
          reg_values[r1].value = m;
          pending_regs |= 1L << r1;
          flags_reg = r1;
          andk_flag = 0;
          return;
        }
        if (op == F_ADDRSP) {
          reg_values[r1].typ = REGV_BASE;
          reg_values[r1].reg = R_SP;
          reg_values[r1].value = m * 4;
          pending_regs |= 1L << r1;
          return;
        }
        if (op == F_ADDSP || op == F_SUBSP) {
          reg_values[R_SP].typ = REGV_BASE;
          reg_values[R_SP].reg = R_SP;
          if (op == F_SUBSP) m = -m;
          reg_values[R_SP].value = m * 4;
          pending_regs |= 1 << R_SP;
          return;
        }
    }
#endif
    outop_direct(op, r1, r2, m);
}

static void ldm_flush0(void)
{
  int32 n = 0;
  unsigned32 regbits = 0;
  int32 offset, initial_offset;
  int32 op = ldm_stm.op;
  int32 base_loaded = 0;
  RealRegister i;
  RealRegister base = ldm_stm.base;
  RealRegister ldm_base = NoRegister;

  for (i = 0; i < 8; i++) {
    if ((offset = ldm_stm.reg_off[i]) != -1)
      break;
  }
  if (i == 8) {
    ldm_stm.op = 0;
    return;
  }
  if (offset < 0) syserr("ldm/stm offset < 0");
  initial_offset = offset;
  for (; i < 8; i++) {
    if (offset == ldm_stm.reg_off[i]) {
      if (i == base) {
        if (op == F_STRI5 && regbits != 0) break;
        base_loaded = 1;
      }
      ldm_base = i;
      regbits |= 1L << i;
      n++;
      ldm_stm.reg_off[i] = -1;
      offset += 4;
    }
  }
  /* If the base is going to be destroyed in this LDR/LDM make
   * sure all other regs are flushed first.
   */
  if (op == F_LDRI5) {
    if (base_loaded) ldm_flush0();
    if ((n >= 2 && initial_offset <= 4 && base != R_SP) || n >= 3) {
      /* ECN: Now adjust offset for any pending offset in the base */
      if (pending_regs & regbit(base) && reg_values[base].typ == REGV_BASE && reg_values[base].reg == base)
      {
        pending_regs &= ~regbit(base);
        offset -= reg_values[base].value;
        reg_values[base].value = 0;
      }
      if (base == R_SP) {
        outop_direct(F_ADDRSP, ldm_base, 0, initial_offset/4);
        outop_direct(F_LDM, ldm_base, 0, regbits);
      } else if (initial_offset == 4 && !base_loaded) {
        outop_direct(F_ADDI3, ldm_base, base, initial_offset);
        outop_direct(F_LDM, ldm_base, 0, regbits);
      } else {
        if (initial_offset)
          outop_direct(F_ADDI8, base, 0, initial_offset);
        outop_direct(F_LDM, base, 0, regbits);
        for (i = 0; i < 8; i++)
          if (ldm_stm.reg_off[i] != -1) break;
        if ((!base_loaded && !(spareregs & (1L << base))) || i < 8)
          outop_direct(F_SUBI8, base, 0, offset);
        else {
          for (i= 0; i < 8; i++)
            if (reg_values[i].typ == REGV_BASE && reg_values[i].reg == base)
              reg_values[i].value -= offset;
          if (reg_values[base].typ == REGV_BASE && reg_values[base].reg != base)
            reg_values[base].value += offset;
        }
      }
      regbits = 0;
    }
  } else {
    if ((n >= 2 && initial_offset == 0) || n >= 3) {
      /* ECN: Now adjust offset for any pending offset in the base */
      if (pending_regs & regbit(base) && reg_values[base].typ == REGV_BASE && reg_values[base].reg == base)
      {
        pending_regs &= ~regbit(base);
        offset -= reg_values[base].value;
        reg_values[base].value = 0;
      }
      if (initial_offset)
        outop_direct(F_ADDI8, base, 0, initial_offset);
      outop_direct(F_STM, base, 0, regbits);
      for (i = 0; i < 8; i++)
        if (ldm_stm.reg_off[i] != -1) break;
      if (!(spareregs & (1L << base)) || i < 8)
        outop_direct(F_SUBI8, base, 0, offset);
      else {
          for (i= 0; i < 8; i++)
            if (reg_values[i].typ == REGV_BASE && reg_values[i].reg == base)
              reg_values[i].value -= offset;
          if (reg_values[base].typ == REGV_BASE && reg_values[base].reg != base)
            reg_values[base].value += offset;
      }
      regbits = 0;
    }
  }
  n = 0;
  base_loaded = -1;
  for (i = 0; regbits != 0; regbits >>= 1, i++) {
    if (regbits & 1) {
      if (i == base)
        base_loaded = n;
      else {
        if (base == R_SP)
            outop_direct(F_LDRSP, i, 0, initial_offset/4 + n);
        else
            outop_direct(op, base, i, initial_offset/4 + n);
      }
      n++;
    }
  }
  if (base_loaded >= 0) outop_direct(op, base, base, initial_offset/4 + base_loaded);
  /* Tailcall to finish off the rest of them */
  ldm_flush0();
}

static void clm_flush(void)
{
  int32 i, n;
  int32 final_offset;

#if 0
  if (clm.n > 1) {
      printf("CLM [R%d", clm.base);
      for (i = 0; i < clm.n; i++)
        printf(", #&%x", clm.offset[i]);
      printf("] @ %.8x\n", codebase+codep);
  }
#endif
  while (clm.n != 0) {
    int32 m = clm.offset[0];
    int32 init_offset = m;
    RealRegister r = NoRegister;
    int32 regs = 0;
    int32 initregs = 0;
    int32 k = 0;
    for (n = 1; n < clm.n; n++) {
      m += 4;
      if (clm.offset[n] != m) break;
    }
    final_offset = init_offset + n * 4;
    for (i = 0; i < 8; i++) {
      if (reg_values[i].typ == REGV_CONSTANT && reg_values[i].value == 0) {
        if (r < 0) r = i;
        regs |= 1L << i;
        k++;
      }
    }
    if (n > 3 && k < 4 && k < (n+1)/2) {
      for (i = 0; i < 8; i++) {
        if (i != clm.base && (spareregs & (1L << i)) && !(regs & (1L << i))) {
          regs |= 1L << i;
          initregs |= 1L << i;
          k++;
          if (k >= 4 || k >= (n + 1)/2) break;
        }
      }
    }
/* /* syserr, not assert */
    assert(r != NoRegister);
    assert(init_offset >= 0 && (init_offset & 3) == 0);
    assert(init_offset > -256 && init_offset < 256);
    assert(final_offset > -256 && final_offset < 256);
    assert((init_offset & 3) == 0);
    assert((final_offset & 3) == 0);
    if ((n > 3 && k > 1) ||
            (n == 3 && (k >= 3 || (k == 2 && init_offset == 0))) ||
            (n == 2 && (k >= 2 && init_offset == 0))) {
      if (init_offset != 0)
        outop_direct(init_offset < 0 ? F_SUBI8 : F_ADDI8, clm.base, 0, init_offset);
      flush_spareregs(initregs);
      for (i = 0; i < 8; i++) {
        if (initregs & (1L << i)) {
          outop_direct(F_MOV8, i, 0, 0);
          reg_values[i].typ = REGV_CONSTANT;
          reg_values[i].value = 0;
        }
      }
      m = n;
      while (m >= k) {
        outop_direct(F_STM, clm.base, 0, regs);
        m -= k;
      }
      if (m > 0) {
        for (i = k-m; i!= 0; i--)
          regs ^= (regs & -regs);
        outop_direct(F_STM, clm.base, 0, regs);
      }
      if ((!(spareregs & (1L << clm.base)) && final_offset) || n < clm.n)
        outop_direct(final_offset < 0 ? F_ADDI8 : F_SUBI8, clm.base, 0, final_offset);
      else {
        for (i= 0; i < 8; i++)
          if (reg_values[i].typ == REGV_BASE && reg_values[i].reg == clm.base && i != clm.base)
            reg_values[i].value -= final_offset;
        if (reg_values[clm.base].typ == REGV_BASE)
          reg_values[clm.base].value += final_offset;
      }
    } else {
      for (i = 0; i < n; i++) {
        assert(clm.offset[i] >= 0 && clm.offset[i] < 128);
        assert((clm.offset[i] & 3) == 0);
        outop_direct(F_STRI5, clm.base, r, clm.offset[i]/4);
      }
    }
    for (i = n; i < clm.n; i++)
      clm.offset[i-n] = clm.offset[i];
    clm.n -= n;
  }
}

static bool ldm_flush(void)
{
  int r = NO;

  if (ldm_stm.op) ldm_flush0(), r = YES;
  if (clm.n > 0) clm_flush(), r = YES;
  return r;
}

static void ldm_op(int32 op, int32 r1, int32 r2, int32 m)
{
  int32 i;

  if (op == F_LDRSP) {
      op = F_LDRI5;
      r2 = r1;
      r1 = R_SP;
  }
  m = m * 4;
  if (op == F_STRI5 && reg_values[r2].typ == REGV_CONSTANT && reg_values[r2].value == 0 && r1 != R_SP) {
      /* Storing a zero - add to clear memory struct */
      if (ldm_stm.op != 0 || clm.n == CLM_MAX || (clm.n > 0 && r1 != clm.base)) ldm_flush();
      clm.z_reg = r2;
      clm.base = r1;
      for (i = 0; i < clm.n; i++)
        if (clm.offset[i] == m) return;
      for (i = clm.n; i > 0; i--) {
        if (clm.offset[i-1] < m) break;
        clm.offset[i] = clm.offset[i-1];
      }
      clm.offset[i] = m;
      clm.n++;
      return;
  }
  if (clm.n > 0) ldm_flush();
  if (op != ldm_stm.op || r1 != ldm_stm.base ||
        (ldm_stm.reg_off[r2] >= 0 && op == F_STRI5)) {
    ldm_flush();
    ldm_stm.op = op;
    ldm_stm.base = r1;
    for (i = 0; i < 8; i++)
      ldm_stm.reg_off[i] = -1;
    ldm_stm.mask = 0;
  }
  /* If there are two stores to the same location, then we ensure we always
   * do the second one by removing all prior stores to that location from
   * the LDM/STM list
   */
  if (op == F_STRI5) {
    for (i = 0; i < 8; i++)
        if (ldm_stm.reg_off[i] == m) {
            ldm_stm.reg_off[i] = -1;
            ldm_stm.mask &= ~(1L << i);
        }
  }
  ldm_stm.reg_off[r2] = m;
  ldm_stm.mask |= 1L << r2;
  if (op == F_LDRI5) reg_values[r2].typ = REGV_UNKNOWN;
  if (r2 == ldm_stm.base && op == F_LDRI5) ldm_flush();
}

static void reissue_cmp(void)
{
    int32 t = flags_reg;
    flags_reg = NoRegister;
    outop(F_CMP8, t, 0, 0);
    /* Flags *are* set as a result of cmp so cmpz_flag is 0 */
    cmpz_flag = 0;
}

static int32 check_cmp(int32 condition)
{
    if (andk_flag != 0) {
        switch (condition) {
            case Q_PL:
                if (andk_flag != 0x80000000) syserr("ANDK condition = Q_PL, n = %.8x", andk_flag);
            case Q_EQ:
            case Q_UEQ:
                condition = Q_LO;
                break;
            case Q_MI:
                if (andk_flag != 0x80000000) syserr("ANDK condition = Q_MI, n = %.8x", andk_flag);
            case Q_NE:
            case Q_UNE:
                condition = Q_HS;
                break;
            case Q_AL:
                break;
            default:
                syserr("ANDK condition = %lx\n", condition);
                break;
        }
    } else if (cmpz_flag && flags_reg != NoRegister) {
        switch (condition) {
          case Q_HS:
            condition = Q_AL;
            break;
          case Q_LO:
            condition = Q_NOT;
            break;
          case Q_HI:
            condition = Q_NE;
            break;
          case Q_LS:
            condition = Q_EQ;
            break;
          case Q_GE:
            condition = Q_PL;
            break;
          case Q_LT:
            condition = Q_MI;
            break;
          case Q_GT:
          case Q_LE:
            reissue_cmp();
            break;
        }
    }
    return condition;
}

static void reg_flush(void)
{
    RealRegister i;

    for (i = 0; i < 16; i++)
        reg_values[i].typ = REGV_UNKNOWN;
    flags_reg = NoRegister;
    cmp_reg = NoRegister;
    pending_regs = 0;
    andk_flag = 0;
}

/*
 * Here I do not even pretend to insert information about the name of
 * the thing called into any tables that the object code formatter will see,
 * I just stick info in the "aux" entry assocuated with the first part of the
 * CALL instruction pair.
 */
static int32 call_k(Symstr *name)
{
    int32 d, w;
    int i;

    w = 0;
    ldm_flush();
    flush_pending(0xff | (1 << R_SP));
    /* the next two lines' data structures may be mergeable. */
    d = obj_symref(name, xr_code, 0);
    if (d == -1) {
        AddCodeXref4(X_PCreloc | codebase+codep, name, 0);
        d = 0;
    } else
        obj_symdef(t_sym, xr_code+xr_defloc+xr_dataincode, codebase+codep);
    w += ((d - (codebase+codep+PC_OFFSET)) >> 1) & 0x003fffff;
    outHWaux(F_CALL1 + ((w >> 11) & 0x7ff), name);
    outHW(F_CALL + (w & 0x7ff));
    for (i = 0; i < 4; i++)
        reg_values[i].typ = REGV_UNKNOWN;
    flags_reg = NoRegister;
    cmp_reg = NoRegister;
    andk_flag = 0;
    return d;
}

#ifdef THUMB_CPLUSPLUS
static void arm_tailcall_k(Symstr *name)
{
    if (pcs_flags & PCS_INTERWORK) {
        int32 w, d = obj_symref(name, xr_code, 0);
        if (d == -1) {
            AddCodeXref4(X_PCreloc_32 | codebase+codep, name, 0);
            d = 0;
        }
        w = ((d - (codebase+codep+8)) >> 2) & 0x00ffffff;
        outcodewordaux(ARM_AL|ARM_B|w, LIT_OPCODE_32, name);
    } else {
        outcodeword(ARM_AL|ARM_LDR_IP_PC_0, LIT_OPCODE_32);
        outcodeword(ARM_AL|ARM_BX|ARM_R_IP, LIT_OPCODE_32);
        obj_symref(name, xr_code, 0);
        AddCodeXref4(X_absreloc | codebase+codep, name, 0);
        outcodeword(0, LIT_ADCON);
    }
}
#endif

static int reads_mem1(int32 op, int32 r1, int32 r2, int32 m)
{
    assert(op != F_LDRI5 && op != F_STRI5);
    IGNORE(r1); IGNORE(r2); IGNORE(m);
    switch(op) {
      case F_LDRHADDR:
      case F_LDRHI5:
      case F_LDRSP:
      case F_LDRADDR:
      case F_LDRBADDR:
      case F_LDRBI5:
      case F_POP:
      case F_LDM:
        return 1;
    }
    return 0;
}

static int alters_mem(int32 op, int32 r1, int32 r2, int32 m)
{
    assert(op != F_LDRI5 && op != F_STRI5);
    IGNORE(r1); IGNORE(r2); IGNORE(m);
    switch (op) {
      case F_STRHADDR:
      case F_STRHI5:
      case F_STRSP:
      case F_STRADDR:
      case F_STRBADDR:
      case F_STRBI5:
      case F_PUSH:
      case F_STM:
        return 1;
    }
    return 0;
}

#define destroys_r(op, r1, r2, m, r) destroys(op, r1, r2, m, 1L << (r))

static int32 destroys(int32 op, int32 r1, int32 r2, int32 m, int32 mask)
{
#if 0
    switch (op) {
      case F_ADDI3:
      case F_SUBI3:
      case F_ADD3R:
      case F_SUB3R:

      case F_LSLK:
      case F_LSRK:
      case F_ASRK:

      case F_MOV8:
      case F_ADDI8:
      case F_SUBI8:

      case F_LDRSP:
      case F_LDRLIT:
      case F_ADDRPC:
      case F_ADDRSP:
        return mask & (1L << r1);

      case F_AND:
      case F_OR:
      case F_EOR:
      case F_BIC:
      case F_NEG:
      case F_MUL:
      case F_MVN:
      case F_LSL:
      case F_LSR:
      case F_ASR:
      case F_ROR:
      case F_ADC:
      case F_SBC:

      case F_MOVHL:
      case F_ADDHL:

      case F_LDRHADDR:
      case F_LDSBADDR:
      case F_LDSHADDR:
      case F_LDRHI5:

      case F_LDRADDR:
      case F_LDRBADDR:
      case F_LDRBI5:
      case F_LDRI5:
        return mask & (1L << r2);

      case F_ADDHH:
      case F_MOVHH:
      case F_ADDLH:
      case F_MOVLH:
        return mask & (1L << (r2 + 8));

      case F_PUSH:
        return mask & (1L << R_SP);
      case F_POP:
        return mask & ((m & 0xff) | (1L << R_SP));
      case F_STM:
        return mask & (1L << r1);
      case F_LDM:
        return mask & ((m & 0xff) | (1L << r1));

      case F_ADDSP:
      case F_SUBSP:
        return mask & (1L << R_SP);
    }
#else
      if (op == F_ADDI3 || op == F_SUBI3 || op == F_ADD3R || op == F_SUB3R ||
                op == F_LSLK || op == F_LSRK || op == F_ASRK || op == F_MOV8 ||
                op == F_ADDI8 || op == F_SUBI8 || op == F_LDRSP || op == F_LDRLIT ||
                op == F_ADDRPC || op == F_ADDRSP)
        return mask & (1L << r1);

      if (op == F_AND || op == F_OR || op == F_EOR || op == F_BIC || op == F_NEG ||
                op == F_MUL || op == F_MVN || op == F_LSL || op == F_LSR || op == F_ASR ||
                op == F_ROR || op == F_ADC || op == F_SBC || op == F_MOVHL ||
                op == F_ADDHL || op == F_LDRHADDR || op == F_LDSBADDR ||
                op == F_LDSHADDR || op == F_LDRHI5 || op == F_LDRADDR ||
                op == F_LDRBADDR || op == F_LDRBI5 || op == F_LDRI5)
        return mask & (1L << r2);

      if (op == F_ADDHH || op == F_MOVHH || op == F_ADDLH || op == F_MOVLH)
        return mask & (1L << (r2 + 8));

      if (op == F_PUSH)
        return mask & (1L << R_SP);
      if (op == F_POP)
        return mask & ((m & 0xff) | (1L << R_SP));
      if (op == F_STM)
        return mask & (1L << r1);
      if (op == F_LDM)
        return mask & ((m & 0xff) | (1L << r1));

      if (op == F_ADDSP || op == F_SUBSP)
        return mask & (1L << R_SP);
#endif
    return 0;
}

#define uses_r(op, r1, r2, m, r) uses(op, r1, r2, m, 1L << (r))

static int32 uses(int32 op, int32 r1, int32 r2, int32 m, int32 mask)
{
    if (op == F_STRHADDR || op == F_STRADDR || op == F_STRBADDR)
      return  mask & ((1L << r1) | (1L << r2) | (1L << m));
    if (op == F_STRHI5 || op == F_STRBI5 || op == F_STRI5)
      return mask & ((1L << r1) | (1L << r2));
    if (op == F_LDRHADDR || op == F_LDRADDR || op == F_LDRBADDR || op == F_LDSBADDR || op == F_LDSHADDR)
      return mask & ((1L << r1) | (1L << m));
    if (op == F_ADD3R || op == F_SUB3R || op == F_AND || op == F_OR || op == F_EOR || op == F_BIC || op == F_MUL || op == F_LSL || op == F_LSR || op == F_ASR || op == F_ROR || op == F_ADC || op == F_SBC)
      return mask & ((1L << r2) | (1L << m));
    if (op == F_ADDI8 || op == F_SUBI8 || op == F_LDRHI5 || op == F_LDRBI5 || op == F_LDRI5)
      return mask & (1L << r1);
    if (op == F_STRSP)
      return mask & ((1L << r1) | (1L << R_SP));
    if (op == F_ADDI3 || op == F_SUBI3 || op == F_LSLK || op == F_LSRK || op == F_ASRK)
      return mask & (1L << r2);
    if (op == F_NEG || op == F_MVN)
      return mask & (1L << m);
    if (op == F_MOVLH)
      return mask & (1L << m);
    if (op == F_MOVHH || op == F_MOVHL)
      return mask & (1L << (m+8));
    if (op == F_ADDHL || op == F_CMPHL)
      return mask & ((1L << (m+8)) | (1L << r2));
    if (op == F_ADDLH || op == F_CMPLH)
      return mask & ((1L << (r2+8)) | (1L << m));
    if (op == F_ADDHH || op == F_CMPHH)
      return mask & ((1L << (r2+8)) | (1L << (m+8)));
    if (op == F_PUSH)
      return mask & ((m & 0xff) | (1L << R_SP));
    if (op == F_ADDRSP || op == F_ADDSP || op == F_SUBSP || op == F_LDRSP || op == F_POP)
      return mask & (1L << R_SP);
    if (op == F_LDM)
      return mask & (1L << r1);
    if (op == F_STM)
      return mask & ((m & 0xff) | (1L << r1));
    return 0;
}

static int is_cmp_op(int32 op)
{
    return op == F_CMP8 || op == F_CMP || op == F_CMN || op == F_TST;
}

static void flush_spareregs(int32 mask)
{
    int32 pending;
    int i;

    pending = 0;
    for (i = 0; i < 8; i++) {
        if (reg_values[i].typ == REGV_BASE && (mask & (1L << reg_values[i].reg)))
            pending |= 1L << i;
    }
    if (pending) flush_pending(pending);
}

static void flush_pending(int32 mask)
{
    int i;
    int32 r;
    int32 op;
    int32 m, n;

    mask &= pending_regs;
    pending_regs &= ~mask;
    for (i = 0; i < 8; i++) {
      if (mask & (1L << i)) {
        if (reg_values[i].typ != REGV_BASE) syserr("Not register based in flush pending");
        m = reg_values[i].value;
        r = reg_values[i].reg;
        if (ldm_stm.op != 0 && i == ldm_stm.base) {
            for (n = 0; n < 8; n++)
                if (ldm_stm.reg_off[n] != -1) ldm_stm.reg_off[n] -= m;
        }
        if (r == R_SP) {
          n = (m & 0x3fc);
          if (m < 0) n = 0;
          outop_direct(F_ADDRSP, i, 0, n/4);
          m ^= n;
          r = i;
        }
        op = F_ADDI3;
        if (m < 0) op = F_SUBI3, m = -m;
        if (i != r) {
          n = m;
          if (m > 7) n = 7;
          outop_direct(op, i, r, n);
          m -= n;
        }
        op = (op == F_ADDI3) ? F_ADDI8 : F_SUBI8;
        while (m) {
          n = m;
          if (m > 255) n = 255;
          outop_direct(op, i, 0, n);
          m -= n;
        }
        reg_values[i].typ = REGV_BASE;
      }
    }
    if (mask & (1 << R_SP)) {
      if (reg_values[R_SP].typ != REGV_BASE) syserr("Not register based in flush pending");
      assert(reg_values[R_SP].reg == R_SP);
      m = reg_values[R_SP].value;
      if (m & 3) syserr("Non word aligned offset from sp");
      op = F_ADDSP;
      if (m < 0) op = F_SUBSP, m = -m;
      m /= 4;
      while (m) {
        n = m;
        if (m > 127) n = 127;
        outop_direct(op, 0, 0, n);
        m -= n;
      }
    }
}

static bool outop0(int32 op, int32 r1, int32 r2, int32 m)
{
    assert(op != F_LDRI5 && op != F_STRI5);
    if (clm.n > 0) {
      if (destroys_r(op, r1, r2, m, clm.base) ||
          destroys_r(op, r1, r2, m, clm.z_reg) ||
          alters_mem(op, r1, r2, m) || reads_mem1(op, r1, r2, m)) {
        return ldm_flush();
      }
    }
    if (ldm_stm.op) {
      if (ldm_stm.op == F_LDRI5) {
        if (uses(op, r1, r2, m, ldm_stm.mask) ||
            destroys_r(op, r1, r2, m, ldm_stm.base) ||
            destroys(op, r1, r2, m, ldm_stm.mask) ||
            alters_mem(op, r1, r2, m)) {
          return ldm_flush();
        }
      } else {
        if (destroys(op, r1, r2, m, ldm_stm.mask) ||
            destroys_r(op, r1, r2, m, ldm_stm.base) ||
            alters_mem(op, r1, r2, m) || reads_mem1(op, r1, r2, m)) {
          return ldm_flush();
        }
      }
    }
    return NO;
}

static void check_pending(int32 op, int32 r1, int32 r2, int32 m, int nospcheck)
{
    int i;
    int32 mask;
    int r;

    r = 0;
    mask = uses(op, r1, r2, m, pending_regs);
    if (nospcheck) mask &= ~(1 << R_SP);
    if (mask)
      flush_pending(mask);
    if ((mask = destroys(op, r1, r2, m, pending_regs)) != 0)
      pending_regs &= ~mask;
    for (i = 0; i < 8; i++) {
      if (reg_values[i].typ == REGV_BASE) {
        if (destroys_r(op, r1, r2, m, reg_values[i].reg)) {
          if (pending_regs & (1L << i))
            flush_pending(1L << i);
          reg_values[i].typ = REGV_UNKNOWN;
        }
      }
    }
    if (!nospcheck) {
      if (reg_values[R_SP].typ == REGV_BASE) {
        if (destroys_r(op, r1, r2, m, R_SP)) {
          if (pending_regs & (1 << R_SP))
            flush_pending(1 << R_SP);
          reg_values[R_SP].typ = REGV_UNKNOWN;
        }
      }
    }
}

static void outop(int32 op, int32 r1, int32 r2, int32 m)
{
    int32 op_e, r1_e, r2_e, m_e;
    int32 i;
    int32 n;
    int32 f_r1;
    int nospcheck;

    op_e = op, r1_e = r1, r2_e = r2, m_e = m;
    op &= ~0x80000000;
    if (op == F_ADDI3 && r1 == r2) op = F_ADDI8, r2 = 0;
    if (op == F_SUBI3 && r1 == r2) op = F_SUBI8, r2 = 0;
    if (disable_opt) {
      outop_direct(op, r1, r2, m);
    } else {
      f_r1 = r1;
      nospcheck = 0;
#if 0
      if (op == F_LDRSP || op == F_STRSP) {
        if (pending_regs & (1 << R_SP)) {
          n = reg_values[R_SP].value;
          assert(reg_values[R_SP].reg == R_SP);
          n = (n >> 2) + m;
          if (n >= 0 && n < 256) {
            m = n;
            nospcheck = 1;
          }
        }
      }
#endif
      if (op == F_ADDRSP) {
        if (reg_values[r1].typ == REGV_BASE && reg_values[r1].reg == R_SP) {
            n = reg_values[r1].value;
            n = m*4 - n;
            i = m;
            if (n >= 0 && n < 256) op = F_ADDI8, m = n;
            if (n <= 0 && n > -256) op = F_SUBI8, m = -n;
            if (n == 0) return;
        }
      }
      if (op == F_STRI5 || op == F_STRBI5 || op == F_LDRI5 || op == F_LDRBI5 ||
          op == F_STRHI5 || op == F_LDRHI5) {
        if (pending_regs & (1L << r1)) {
          n = reg_values[r1].value;
          i = reg_values[r1].reg;
          if (op == F_LDRI5 || op == F_STRI5) {
            if (n & 3) i = NoRegister;
            n = (n >> 2) + m;
#if 0
            if (i == R_SP && n >= 0 && n < 256) {
              m = n;
              r1 = r2;
              r2 = 0;
              f_r1 = r1;
              nospcheck = 1;
              assert(!(pending_regs & (1 << R_SP)));
              op = op == F_LDRI5 ? F_LDRSP : F_STRSP;
            }
#endif
          } else if (op == F_LDRHI5 || op == F_STRHI5) {
            if (n & 1) i = NoRegister;
            n = (n >> 1) + m;
          } else {
            n = n + m;
          }
          if (i != NoRegister && i < 8 && n >= 0 && n < 32) {
            /* STR Rs, [Rb, #N] where Rs == Rb but value of Rs if offset from Rb
             * causes problems so we must revert to
             * ADD/SUB Rs, Rs, #M
             * STR     Rs, [Rb, #N]  ; Rs != Rb
             */
            if (!((pending_regs & (1L << i)) && i == r2 && !(op & 0x0800))) {
              m = n;
              r1 = i;
              f_r1 = 16;
            }
          }
        }
      }
      if (op == F_STRHADDR || op == F_STRBADDR || op == F_STRADDR ||
          op == F_STRHI5 || op == F_STRBI5 || op == F_STRI5 ||
          op == F_LSLK || op == F_LSRK || op == F_ASRK ||
          op == F_ADDI3 || op == F_SUBI3 || op == F_ADD3R || op == F_SUB3R) {
        if (pending_regs & (1L << r2) && reg_values[r2].value == 0) {
          i = reg_values[r2].reg;
          if (i < 8) r2 = i;
        }
      }
      if (op == F_CMP8 && m != 0) {
        if (pending_regs & (1L << r1) && reg_values[r1].value == 0) {
          i = reg_values[r1].reg;
          if (i < 8) r1 = i;
        }
      }
      if (op == F_STRSP) {
        if (pending_regs & (1L << r1) && reg_values[r1].value == 0) {
          i = reg_values[r1].reg;
          if (i < 8) r1 = i;
        }
      }
      if (op == F_ADD3R || op == F_SUB3R ||
          op == F_STRHADDR || op == F_LDRHADDR || op == F_LDSBADDR || op == F_LDSHADDR ||
          op == F_STRADDR || op == F_STRBADDR || op == F_LDRADDR || op == F_LDRBADDR ||
          IS_DATAPROC(op)) {
        if (pending_regs & (1L << m) && reg_values[m].value == 0) {
          i = reg_values[m].reg;
          if (i < 8) m = i;
        }
      }
      if (op == F_ADDI8 || op == F_SUBI8) {
        if (pending_regs & (1L << r1)) {
          if (op == F_SUBI8) m = -m;
          m += reg_values[r1].value;
          reg_values[r1].value = m;
          if (ldm_stm.op != 0 && r1 == ldm_stm.base) {
            for (i = 0; i < 8; i++) {
                if (ldm_stm.reg_off[i] != -1 && (ldm_stm.reg_off[i] - m < 0)) {
                    ldm_flush();
                    break;
                }
            }
            for (i = 0; i < 8; i++) {
                if (ldm_stm.reg_off[i] != -1)
                    ldm_stm.reg_off[i] -= m;
            }
          }
          if (r1 == clm.base) {
            for (i = 0; i < clm.n; i++)
                clm.offset[i] -= m;
          }
          return;
        }
      }
      if (op == F_ADDSP || op == F_SUBSP) {
        if (pending_regs & (1 << R_SP)) {
          if (op == F_SUBSP) m = -m;
          reg_values[R_SP].value += m * 4;
          return;
        }
      }
      if (is_cmp_op(op)) {
        if (ldm_flush()) {
            /* If ldm/stm flushes this may have invalidated some assumptions
             * about the register values earlier in this function, so we call
             * ourselves again with the original arguments
             */
            if (op_e & 0x80000000) syserr("re-entry in outop(%lx)", op);
            outop(op_e | 0x80000000, r1_e, r2_e, m_e);
            return;
        }
        if (op == F_CMP8 && m == 0)
            flush_pending(0xff ^ (1L << r1));
        flush_pending(0xff | (1 << R_SP));
      }
      check_pending(op, f_r1, r2, m, nospcheck);
      if (op == F_LDRI5 || op == F_STRI5 || (op == F_LDRSP &&  m >= 0 && m < 512)) {
        ldm_op(op, r1, r2, m);
      } else {
        if (outop0(op, r1, r2, m)) {
            /* If ldm/stm flushes this may have invalidated some assumptions
             * about the register values earlier in this function, so we call
             * ourselves again with the original arguments
             */
            if (op_e & 0x80000000) syserr("re-entry in outop(%lx)", op);
            outop(op_e | 0x80000000, r1_e, r2_e, m_e);
            return;
        }
        outop2(op, r1, r2, m);
      }
    }
}

void cnop(void)
{
    if (codep & 1) outDCB(0);
    if (((codebase+codep) & 2) != 0) outop_direct(F_ADDI3, 0, 0, 0);
}

/* although the idea of setlabel is machine independent, it stays here
   because it back-patches code.  In the long term setlabel should be
   in codebuf.c and call a machine dependent backpatch routine.
*/

List3 *label_values, *label_references;
#define AddLabelReference(pos, lab) \
  label_references = (List3 *)syn_list3(label_references, (pos),\
        lab_name_(lab) & 0xfffff)
#define AddLitPoolReference(pos, off) \
  label_references = (List3 *)syn_list3(label_references, (pos),\
        (lab_name_(litlab) & 0xfffff) | ((off) << 20))

int32 current_procnum;

static void setlabel2(LabelNumber *ll, int32 codep)
{
    List3 *l, **l_p;

    l_p = &label_values;
    while ((l = *l_p) != 0) {
        if ((int32)car_(l) <= codep)
            break;
        l_p = (List3 **)&cdr_(l);
    }
    *l_p = (List3 *)binder_icons3(l, codep, lab_name_(ll) & 0xfffff);
    lab_setloc_(ll, codep | 0x80000000); /* cheapo union checker for ->frefs */
}

#define LABREF_B        0x01000000
#define LABREF_BC       0x02000000
#define LABREF_BL       0x03000000
#define LABREF_WORD8    0x04000000
#define LABREF_BXX_8    0x05000000
#define LABREF_BXX_16   0x06000000
#ifdef THUMB_CPLUSPLUS
#define LABREF_WORD32   0x08000000
#endif

static void setlabel1(LabelNumber *l)
{
    List *p;

#if 0
    fprintf(stderr, "%.8x: (setlabel1) F%dL%d = %.8x (isset = %d)\n", codebase + codep, current_procnum, lab_name_(l) & 0xfffff, codebase + codep, lab_isset_(l));
#endif
    p = l->u.frefs;
    while (p) {
      int32 v = car_(p);
      int32 q = (v & 0x00ffffff);
      int32 w;
      unsigned32 d;

      switch (v & 0xff000000) {
        case LABREF_B:     /* B xxx */
          w = code_hword_(q);
          d = (codep-q-PC_OFFSET >> 1);
          if ((int32)d < -0x400 || (int32)d >= 0x400) syserr(syserr_displacement, (long)d);
          w = (w & ~0x7ff) | (d & 0x7ff);
          code_hword_(q) = (unsigned16)w;
          break;
        case LABREF_BC:    /* BC xxx */
          w = code_hword_(q);
          d = (codep-q-PC_OFFSET >> 1);
          if ((int32)d < -0x80 || (int32)d >= 0x80) syserr(syserr_displacement, (long)d);
          w = (w & ~0xff) | (d & 0xff);
          code_hword_(q) = (unsigned16)w;
          break;
        case LABREF_BL:    /* BL xxx */
          w = code_hword_(q);
          d = (codep-q-PC_OFFSET >> 1);
          w = (w & ~0x7ff) | ((d >> 11) & 0x7ff);
          code_hword_(q) = (unsigned16)w;
          w = code_hword_(q+2);
          w = (w & ~0x7ff) | (d & 0x7ff);
          code_hword_(q+2) = (unsigned16)w;
          break;
        case LABREF_WORD8: /* ADD Rd, pc, #nn */
                           /* LDR Rd, [pc, #nn] */
          w = code_hword_(q);
          d = ((codebase+codep)-((codebase+q)&~3)-PC_OFFSET >> 2) + (w & 0xff);
          if (d >= 0x100) syserr(syserr_displacement, (long)d);
          w = (w & ~0xff) | d;
          code_hword_(q) = (unsigned16)w;
          break;
#ifdef THUMB_CPLUSPLUS
        case LABREF_WORD32: { /* DCD L<N> */
            Symstr *labname;
            char b[20];

            sprintf(b, "$F%dL%d", current_procnum, lab_name_(l));
            labname = sym_insert_id(b);
            obj_symdef(labname,
                       xr_code+xr_defloc+xr_code_32,
                       codebase+codep);
            AddCodeXref4(X_absreloc | codebase+q, labname, 0);
            AddLabelReference(q, l);
            break;
        }
#endif
        case LABREF_BXX_8:
            w = code_byte_(q);
            d = (codep-(q&~1)-PC_OFFSET >> 1) + (w & 0xff);
            if (d >= 0x100) syserr(syserr_displacement, (long)d);
            code_byte_(q) = d;
            break;

        case LABREF_BXX_16:
            w = code_hword_(q);
            d = codep-q-PC_OFFSET + (w & 0xffff);
            if (d >= 0x10000) syserr(syserr_displacement, (long)d);
            code_hword_(q) = d;
            break;
      }
      p = (List *)discard2(p);
    }
    label_values = (List3 *)binder_icons3(label_values, codep, lab_name_(l) & 0xfffff);
    lab_setloc_(l, codep | 0x80000000); /* cheapo union checker for ->frefs */
}

static int32 branch_range(int32 flags)
{
  if (FREF_TYPE(flags) == FREF_DCB) return 512 - 24L;
  if (FREF_TYPE(flags) == FREF_DCW) return 65536 - 24L;
  return (FREF_CONDITION(flags) == Q_AL ? 2048L : 256L) - 24L; /* Margin for safety */
}

static void describe_literal_pool(void) {
    if (!in_code) {
        if (codebase+codep != literal_pool_start) {
            char b[32];
            sprintf(b, "x$litpool$%d", literal_pool_number);
            obj_symref(sym_insert_id(b), xr_code+xr_defloc+xr_dataincode, (literal_pool_start+3) & ~3);
            sprintf(b, "x$litpool_e$%d", literal_pool_number++);
            obj_symref(sym_insert_id(b), xr_code+xr_defloc+xr_dataincode, codebase+codep-1);
        }
        in_code = YES;
    }
}

static void recalc_mustbranchlitby(void)
{
    FRef_Branch *fref = fref_branches;
    int32 litby = 0x10000000;
    int32 poolsize = 0;

    for (; fref != NULL; fref = cdr_(fref)) {
        if (fref->pcref + branch_range(fref->flags) - poolsize < litby)
          litby = fref->pcref + branch_range(fref->flags) - poolsize;
        poolsize += 2;
    }
    mustbranchlitby = litby;
}

void setlabel(LabelNumber *l)
{
    FRef_Branch *fref;
    FRef_Branch **fref_p = &fref_branches;
    while ((fref = *fref_p) != 0) {
      if (l == fref->real_dest) {
        *fref_p = cdr_(fref);
        setlabel1(fref->chained_dest);
        branchpoolsize -= 2;
      } else
        fref_p = &cdr_(fref);
    }
    fref_branches_head = fref_p;
    recalc_mustbranchlitby();
    setlabel1(l);
    if (l != litlab) describe_literal_pool();
}

static void dump_branch_lits(int needs_jump, int32 poolsize)
{
    FRef_Branch *fref, **fref_p;
    LabelNumber *ll = NULL;

    mustbranchlitby = 0x10000000;
    ldm_flush();
    flush_pending(0xff | (1 << R_SP));
    poolsize += branchpoolsize;
    if (needs_jump) {
      ll = nextlabel();
      branch_round_literals(ll);
    }
    fref_p = &fref_branches;
    while ((fref = *fref_p) != 0) {
      int range = branch_range(fref->flags);
      range = range * 7 / 8;
      if (codep - fref->pcref + poolsize > range)
      {
        *fref_branches_head = fref;
        *fref_p = cdr_(fref);
        cdr_(fref) = 0;
        fref_branches_head = &cdr_(fref);
        setlabel1(fref->chained_dest);
        fref->chained_dest = nextlabel();
        fref->flags = Q_AL | FREF_BRANCH;
        fref->pcref = codep;
        fref->codep = codep;
        AddLabelReference(codep, fref->chained_dest);
        addfref_(fref->chained_dest, codep | LABREF_B);
        outop(F_B, 0, 0, 0);
        poolsize -= 2;
      } else
        fref_p = &cdr_(fref);
    }
    if (needs_jump)
      setlabel(ll); /* recalculates mustbranchlitby */
    else
      recalc_mustbranchlitby();
}

static void dumplits(int needs_jump)
{
    LabelNumber *ll = NULL;

    if (needs_jump) {
      ll = nextlabel();
      branch_round_literals(ll);
    }
    dump_branch_lits(0, litpoolp * 4);
    literal_pool_start = codebase+codep;
    dumplits2(0);
    if (needs_jump)
      setlabel(ll);
}

static void addressability(int32 n)
/*
 * "I can address up to n bytes beyond where I am now"
 */
{
    int32 litpoolsize;;

    n -= 24;  /* margin for safety */
    litpoolsize = 4*litpoolp;
    if (litpoolsize>=n) dumplits(YES);
    if (codep-litpoolsize+n < mustlitby) mustlitby = codep-litpoolsize+n;
}

static void load_lit(RealRegister r1, int32 n)
{
    int32 i;

    ldm_flush();
    flush_pending(0xff | (1 << R_SP));
    if ((i = lit_findwordaux(n, LIT_NUMBER, 0, LITF_INCODE|LITF_FIRST|LITF_LAST|LITF_PEEK)) >=0) {
        addfref_(litlab, codep | LABREF_WORD8);
        AddLitPoolReference(codep, i);
        outop(F_LDRLIT, r1, 0, i/4);
    } else {
        addressability(1024);
        i = lit_findwordaux(n, LIT_NUMBER, 0, LITF_INCODE|LITF_FIRST|LITF_LAST|LITF_NEW);
        addfref_(litlab, codep | LABREF_WORD8);
        AddLitPoolReference(codep, i);
        outop(F_LDRLIT, r1, 0, i/4);
    }
}

static int add_integer0(RealRegister r1, RealRegister r2, int32 n, int len_only);
static void add_integer(RealRegister r1, RealRegister r2, int32 n);

static void load_adcon(RealRegister r1, Symstr *name, int32 offset)
{
    int32 i;
    int32 d;
    RealRegister r;
/* Try to find adcon in following order: 1. current literal pool,        */
/* 2. new allocation in current pool.                                    */
    ldm_flush();
    flush_pending(0xff | (1 << R_SP));
    d = offset-reg_values[r1].value;
    if (pcs_flags & PCS_REENTRANT) {
        i = adconpool_find(offset, LIT_ADCON, name);
        AddCodeXref4(X_DataVal+codebase+codep, adconpool_lab, 0);
        outop_direct(F_MOV8, r1, 0, (i >> 7) & 0xff);
        outop_direct(F_LSLK, r1, r1, 7);
        outop_direct(F_ADDHL, 0, r1, R_SB-8);
        outop_direct(F_LDRI5, r1, r1, (i >> 2) & 0x1f);
    } else {
        if (reg_values[r1].typ == REGV_ADCON && reg_values[r1].name == name &&
                add_integer0(r1, r1, d, 1) <= 1) {
            add_integer(r1, r1, d);
        } else if ((i = lit_findword(offset, LIT_ADCON, name,
                              LITF_INCODE|LITF_FIRST|LITF_LAST|LITF_PEEK)) >= 0) {
            addfref_(litlab, codep | LABREF_WORD8);
            AddLitPoolReference(codep, i);
            outop(F_LDRLIT, r1, 0, i/4);
        } else {
            for (r = 0; r < 8; r++) {
                d = offset-reg_values[r].value;
                if (reg_values[r].typ == REGV_ADCON && reg_values[r].name == name &&
                        add_integer0(r1, r, d, 1) <= 2) {
                    add_integer(r1, r, d);
                    break;
                }
            }
            if (r >= 8) {
                addressability(1024);
                i = lit_findword(offset, LIT_ADCON, name,
                                  LITF_INCODE|LITF_FIRST|LITF_LAST|LITF_NEW);
                addfref_(litlab, codep | LABREF_WORD8);
                AddLitPoolReference(codep, i);
                outop(F_LDRLIT, r1, 0, i/4);
            }
        }
    }
    flush_pending(1<<r1); /* Make sure it really has this value */
    if (!(disable_opt)) {
        reg_values[r1].typ = REGV_ADCON;
        reg_values[r1].name = name;
        reg_values[r1].value = offset;
    }
}


static void load_fp_adcon(RealRegister r1, J_OPCODE op, FloatCon *fc)
{
    int32 disp;
    int size = (op==J_MOVDK || op==J_ADCOND) ? 2 : 1;

    ldm_flush();
    flush_pending(0xff | (1 << R_SP));
    addressability(1024);
    disp = lit_findwordsincurpool(fc->floatbin.irep, size, LIT_FPNUM);
    if (disp < 0)   /* not found in current pool - don't look in previous */
    {
        if (size == 1) {
            disp = lit_findwordaux(fc->floatbin.fb.val,
                    LIT_FPNUM, fc->floatstr,
                    LITF_INCODE|LITF_FIRST|LITF_LAST);
        } else {
            (void) lit_findwordaux(fc->floatbin.db.msd,
                    LIT_FPNUM1, fc->floatstr,
                    LITF_INCODE|LITF_FIRST);
            disp = lit_findwordaux(fc->floatbin.db.lsd,
                    LIT_FPNUM2, fc->floatstr,
                    LITF_INCODE|LITF_LAST) - 4;
        }
    }
    addfref_(litlab, codep | LABREF_WORD8);
    AddLitPoolReference(codep, disp);
    outop(F_ADDRPC, r1, 0, disp/4);
}


static void load_ll_adcon(RealRegister r1, J_OPCODE op, Int64Con *c)
{
    int32 *w = (int32 *)&c->bin.i;
    int size = sizeof_longlong / sizeof_long;
    int32 disp;

    IGNORE(op);
    ldm_flush();
    flush_pending(0xff | (1 << R_SP));
    addressability(1024);
    disp = lit_findwordsincurpool(w, size, LIT_INT64_1);
    if (disp < 0)
    {   (void)lit_findword(w[0], LIT_INT64_1, NULL, LITF_INCODE|LITF_FIRST);
        disp = lit_findword(w[1], LIT_INT64_2, NULL, LITF_INCODE|LITF_LAST) - 4;
    }
    addfref_(litlab, codep | LABREF_WORD8);
    AddLitPoolReference(codep, disp);
    outop(F_ADDRPC, r1, 0, disp/4);
}


static bool uses_IP;
static bool return_pending;

static int load_integer0(RealRegister r, int32 n, int len_only);
static void load_integer(RealRegister r, int32 n);

static void move_register(RealRegister r1, RealRegister r2)
{   /* r1 = r2   */
    if (r1 == r2) return;
    if (r1 >= 8) {
        if (r2 >= 8)
            outop(F_MOVHH, 0, r1-8, r2-8);
        else
            outop(F_MOVLH, 0, r1-8, r2);
    } else {
        if (r2 >= 8)
            outop(F_MOVHL, 0, r1, r2-8);
        else
            outop(F_ADDI3, r1, r2, 0);
    }
}

static bool register_holds_value(RealRegister r, int32 n)
{   return !disable_opt
           && reg_values[r].typ == REGV_CONSTANT
           && !(ldm_stm.op != 0 && ldm_stm.reg_off[r] >= 0)
           && reg_values[r].value == n;
}

static bool value_is_constant(RealRegister r)
{   return !disable_opt
           && reg_values[r].typ == REGV_CONSTANT
           && !(ldm_stm.op != 0 && ldm_stm.reg_off[r] >= 0);
}

static RealRegister constant_available(int32 n)
{
    RealRegister r;

    if (!disable_opt)
        for (r = 0; r < 8; r++)
            if (register_holds_value(r, n))
                return r;
    return NoRegister;
}

static RealRegister get_register(void)
{
    RealRegister r;

    for (r = 7; r >= 0; r--)
        if (r != R_IP && (spareregs & (1L << r)))
            return r;
    return R_IP;
}

static int add_integer0(RealRegister r1, RealRegister r2, int32 n, int len_only)
{
    int l, minlen;
    unsigned32 m, v;
    int32 op1, op2;
    int32 r;

    m = n;
    op1 = F_ADDI3;
    op2 = F_ADDI8;
    if (n < 0) {
      m = -n;
      op1 = F_SUBI3;
      op2 = F_SUBI8;
    }
    if (m > 255 || (r1 != r2 && m > 7)) {
        if ((r = constant_available(n)) >= 0) {
            if (!len_only) outop(F_ADD3R, r1, r2, r);
            return 1;
        } else if ((r = constant_available(-n)) >= 0) {
            if (!len_only) outop(F_SUB3R, r1, r2, r);
            return 1;
        }
    }
    if (r1 == r2) {
      if (m <= 3 * 255) {
        l = 0;
        while (m) {
          v = m > 255 ? 255 : m;
          if (!len_only) outop(op2, r1, 0, v);
          m -= v;
          l++;
        }
        return l;
      }
    } else {
      if (m <= 2 * 255 + 7) {
        v = m > 7 ? 7 : m;
        if (!len_only) outop(op1, r1, r2, v);
        m -= v;
        l = 1;
        while (m) {
          v = m > 255 ? 255 : m;
          if (!len_only) outop(op2, r1, 0, v);
          m -= v;
          l++;
        }
        return l;
      }
    }
    uses_IP = YES;
    if (r2 == R_IP)
    {   if (len_only) return 1000;  /* cannot generate code for this, so return large number */
        syserr("add_integer0: IP clash @ %.8lx", codebase+codep);
    }
    minlen = load_integer0(R_IP, n, 1);
    l = load_integer0(R_IP, -n, 1);
    if (l < minlen) {
      minlen = l;
      if (!len_only) {
        load_integer(R_IP, -n);
        outop(F_SUB3R, r1, r2, R_IP);
      }
    } else {
      if (!len_only) {
        load_integer(R_IP, n);
        outop(F_ADD3R, r1, r2, R_IP);
      }
    }
    return minlen+1;
}

static void add_integer(RealRegister r1, RealRegister r2, int32 n)
{
    if (r2 == R_SP)
    {   /* Magic special for SP-relative address calculation */
      if (r1 < 8) {
        if ((n & 3) || n >= 1024 || n < 0) {
          int32 n1;

          n1 = n & 0x3fc;
          if ((n ^ n1) < 256 && (n ^ n1) > -256) {
            outop(F_ADDRSP, r1, 0, n1/4);
            add_integer0(r1, r1, n ^ n1, 0);
          } else {
            load_integer(r1, n);
            outop(F_ADDHL, 0, r1, R_SP-8);
          }
          return;
        }
        outop(F_ADDRSP, r1, 0, n/4);
        return;
      } else if (r1 == R_SP) {
        /* Change value in SP. Needn't set flags */
        int32 n1 = n;
        int32 sign = 0;
        int loadlen;

        if (n & 3) syserr("Non word aligned offset from sp %.8lx\n", codebase+codep);
        if (n == 0) return;
        if (n1 < 0) { sign = 1; n1 = -n1; }
        n1 = n1 >> 2;
        loadlen = load_integer0(R_IP, n, 1);
        if (loadlen < (n1 >> 7)) {
          uses_IP = YES;
          load_integer0(R_IP, n, 0);
          outop(F_ADDLH, 0, R_SP-8, R_IP);
        } else
          while (n1 != 0) {
            int32 m = (n1 >= (1 << 7)) ? (1 << 7) - 1 : n1;
            outop(sign ? F_SUBSP : F_ADDSP, 0, 0, m);
            n1 -= m;
          }
        return;
      } else syserr("Add sp to bad reg %d", (int)r1);
    }
    add_integer0(r1, r2, n, 0);
}

static int load_integer0(RealRegister r, int32 n, int len_only)
{
    int32 m, shift;
    int32 i;

    if (!(disable_opt)) {
      if (register_holds_value(r, n))
          return 0;
    }
    if (n >= 0 && n < 256) {
      if (!len_only) outop(F_MOV8, r, 0, n);
      return 1;
    }
    if (!(disable_opt)) {
      for (m = 0; m < 8; m++) {
        if (value_is_constant(m)) {
          int32 k = reg_values[m].value;
          if (k == n) {
            if (!len_only) outop(F_ADDI3, r, m, 0);
            return 1;
          }
          if (k == -n) {
            if (!len_only) outop(F_NEG, 0, r, m);
            return 1;
          }
          if (k == ~n) {
            if (!len_only) outop(F_MVN, 0, r, m);
            return 1;
          }
          if (r == m && k >= n-255 && k <= n-255) {
            if (!len_only) {
                if (n-k >= 0)
                    outop(F_ADDI8, r, 0, n-k);
                else
                    outop(F_SUBI8, r, 0, k-n);
            }
            return 1;
          }
          if ((k >= n-7 && k <= n+7)) {
            if (!len_only) {
                if (n-k >= 0)
                    outop(F_ADDI3, r, m, n-k);
                else
                    outop(F_SUBI3, r, m, k-n);
            }
            return 1;
          }
          for (i = 1; i <= 31; i++) {
            if ((k << i) == n) {
              if (!len_only) outop(F_LSLK, r, m, i);
              return 1;
            }
            if (((uint32)k >> i) == (uint32)n) {
              if (!len_only) outop(F_LSRK, r, m, i);
              return 1;
            }
            if (signed_rightshift_(k, i) == n) {
              if (!len_only) outop(F_ASRK, r, m, i);
              return 1;
            }
          }
        }
      }
    }
    if (!(config & CONFIG_OPTIMISE_TIME)) {
      if ((i = lit_findwordaux(n, LIT_NUMBER, 0, LITF_INCODE|LITF_FIRST|LITF_LAST|LITF_PEEK)) >=0) {
        if (!len_only) load_lit(r, n);
        return 1;
      }
    }
    if (n < 0 && n >= -256) {
      if (!len_only) {
        outop(F_MOV8, r, 0, ~n);
        outop(F_MVN, 0, r, r);
      }
      return 2;
    }
    if (n >= 0 && n <= 255 * 2) {
      if (!len_only) {
        outop(F_MOV8, r, 0, 255);
        outop(F_ADDI8, r, 0, n - 255);
      }
      return 2;
    }
    m = n, shift = 0;
    while (!(m & 1)) m >>= 1, shift++;
    if (!(m & ~0xff)) {
      if (!len_only) {
        outop(F_MOV8, r, 0, m);
        outop(F_LSLK, r, r, shift);
      }
      return 2;
    }
    if (!len_only) load_lit(r, n);
    return 3;
}

/* Set register r to the integer n, setting condition codes on scc       */
static void load_integer(RealRegister r, int32 n)
{
    load_integer0(r, n, 0);
    if (!(pending_regs & (1L << r))) {
      reg_values[r].typ = REGV_CONSTANT;
      reg_values[r].value = n;
    }
}

static void and_integer(RealRegister r1, RealRegister r2, int32 n, int32 peep)
{
    int len;
    unsigned m;
    int32 s, t;
    RealRegister r_ip;
    int32 dead_r1;

    dead_r1 = nspareregs & (1 << r1);
    if (n == 0)
    {
        outop(F_MOV8, r1, 0, 0);
        return;
    }
    if (!disable_opt && (peep & P_CMPZ) && dead_r1) {
        if ((s = power_of_two(n)) >= 0) {
            outop(F_LSRK, r1, r2, (s+1) & 0x1f);
            andk_flag = n;
            return;
        } else {
            m = (unsigned)n;
            s = 0;
            while (!(m & 1)) m = m / 2, s++;
            t = 0;
            while (m & 1) m = m / 2, t++;
            if (m == 0) {
                if (s) {
                    outop(F_LSRK, r1, r2, s);
                    r2 = r1;
                }
                if (s+t < 32) {
                    outop(F_LSLK, r1, r2, 32 - t);
                }
                return;
            }
        }
    }
    if ((s = constant_available(n)) >= 0) {
        if (r1 == s) {
            outop(F_AND, 0, r1, r2);
        } else {
            if (nspareregs & (1L << r2)) {
                outop(F_AND, 0, r2, s);
                if (!dead_r1) move_register(r1, r2);
            } else {
                move_register(r1, r2);
                outop(F_AND, 0, r1, s);
            }
        }
        return;
    } else if ((s = constant_available(~n)) >= 0) {
        if (r1 != s) {
            move_register(r1, r2);
            outop(F_BIC, 0, r1, s);
            return;
        }
    }
    if (power_of_two(n+1) >=0 || power_of_two(-n) >= 0) {
        m = (unsigned)n;
        s = 0;
        while (m & 1) m = m / 2, s++;
        if (!m) {
          outop(F_LSLK, r1, r2, 32 - s);
          outop(F_LSRK, r1, r1, 32 - s);
          return;
        }
        m = (unsigned)n;
        s = 0;
        while (m & 0x80000000) m = m * 2, s++;
        if (!m) {
          outop(F_LSRK, r1, r2, 32 - s);
          outop(F_LSLK, r1, r1, 32 - s);
          return;
        }
    }
    r_ip = R_IP;
    if (r2 == R_IP)
        syserr("and_integer: IP clash @ %.8lx", codebase+codep);
    len = load_integer0(R_IP, n, 1);
    if ((nspareregs & (1L << r2)) && load_integer0(R_IP, ~n, 1) < len) {
      load_integer(r_ip, ~n);
      outop(F_BIC, 0, r2, r_ip);
      if (!dead_r1) move_register(r1, r2);
      uses_IP = YES;
    } else {
      if (r1 == r2) {
        load_integer(r_ip, n);
        outop(F_AND, 0, r1, r_ip);
        uses_IP = YES;
      } else {
        load_integer(r1, n);
        outop(F_AND, 0, r1, r2);
      }
    }
}

static void multiply_integer(RealRegister r1, RealRegister r2, int32 n)
{
    int32 s, k;
    RealRegister workreg;

    if (r2 == R_IP) syserr("multiply_integer: IP clash @ %.8lx", codebase+codep);
/* Generate code for r1 = r2 * n. */
#if 0
    printf("Multiply integer: R%d = R%d * %d\n", r1, r2, n);
#endif
    workreg = r1;
    if (r1 == r2) workreg = R_IP;
    if (n==0)
        load_integer(r1, 0);
    else if (n==1)
        move_register(r1, r2);
    else if (n==-1)
        outop(F_NEG, 0, r1, r2);
    else if ((s = power_of_two(n)) >= 0)
        outop(F_LSLK, r1, r2, s);
    else if ((s = power_of_two(-n)) >= 0) {
        outop(F_LSLK, r1, r2, s);
        outop(F_NEG, 0, r1, r1);
    } else if ((s = power_of_two(n-1)) >= 0) {
        outop(F_LSLK, workreg, r2, s);
        outop(F_ADD3R, r1, workreg, r2);
    } else if ((s = power_of_two(n+1)) >= 0) {
        outop(F_LSLK, workreg, r2, s);
        outop(F_SUB3R, r1, workreg, r2);
    } else if ((s = power_of_two(1-n)) >= 0) {
        outop(F_LSLK, workreg, r2, s);
        outop(F_SUB3R, r1, r2, workreg);
    } else {
        if ((s = constant_available(n)) >= 0 && ((r1 != s) || (r2 != s))) {
            if (r1 == s && s != r2)
                outop(F_MUL, 0, s, r2);
            else {
                if ((nspareregs & (1L << r2)) && s != r2) {
                    /* This may allow a subsequent elimination of the move */
                    outop(F_MUL, 0, r2, s);
                    move_register(r1, r2);
                } else {
                    move_register(r1, r2);
                    outop(F_MUL, 0, r1, s);
                }
            }
            return;
        }
        /* ECN: not sure this is sensible */
        if ((n < 0 || n > 255) || !(config & CONFIG_OPTIMISE_SPACE)) {
            k = 0;
            while (!(n & 1)) n /= 2, k++;
            if ((s = power_of_two(n-1)) >= 0) {
                outop(F_LSLK, workreg, r2, s);
                outop(F_ADD3R, r1, workreg, r2);
                outop(F_LSLK, r1, r1, k);
                return;
            } else if ((s = power_of_two(n+1)) >= 0) {
                outop(F_LSLK, workreg, r2, s);
                outop(F_SUB3R, r1, workreg, r2);
                outop(F_LSLK, r1, r1, k);
                return;
            }
            n <<= k;
        }
        load_integer(workreg, n);
        if (r1 == r2)
            outop(F_MUL, 0, r1, R_IP);
        else
            outop(F_MUL, 0, r1, r2);
    }
}

/* Fix up correctly a big displacement by using R_IP which has been   */
/* reserved by regalloc.c                                             */
static int32 bigindex(RealRegister r, int32 m)
{
    if ((m & 3) == 0 && m >= 0 && m < 128) return -1;
    uses_IP = YES;
    add_integer(R_IP, r, m & ~(0x1f << 2));
    return m & (0x1f << 2);
}

static int32 bigindexshort(RealRegister r, int32 m)
{
    if ((m & 1) == 0 && m >= 0 && m < 64) return -1;
    uses_IP = YES;
    add_integer(R_IP, r, m & ~(0x1f << 1));
    return m & (0x1f << 1);
}

static int32 bigindexbyte(RealRegister r, int32 m)
{
    if (m >= 0 && m < 32) return -1;
    uses_IP = YES;
    add_integer(R_IP, r, m & ~0x1f);
    return m & 0x1f;
}

#define M_VARREGS (regbit(R_V1+NVARREGS)-regbit(R_V1))

#ifdef DEBUG_THUMB_CPLUSPLUS
extern int sanity_check_has_callr;
#endif

static void routine_entry(int32 m)
{
    int32 mask = (regmask & M_VARREGS);
    int32 n;
    int32 sp_offset;
    int32 res_regs;
    int32 i;

    if (procauxflags & bitoffnaux_(s_irq))
        cc_err(gen_err_irq, compiler_name());

    current_procnum++;
    label_values = label_references = NULL;
    fp_minus_sp = 0;
    available_branches = 0;
    reg_flush();
    pushed_args = 0;
    firstargoff = -16;
    stack_args_split = 0;
    res_regs = currentfunction.nresultregs;
    nspareregs = (regmask & M_VARREGS) & ((1 << 4) | (1 << 5) | (1 << 6) | (1 << 7));
    if (R_IP >= R_V1) mask |= regbit(R_IP);
    r_fr = R_IP;
    m = k_argwords_(m);
#ifdef DEBUG_THUMB_CPLUSPLUS
    if (sanity_check_has_callr && !(mask & regbit(R_FR)))
        syserr("function at %08x has CALLR but R7 not saved", codebase);
    sanity_check_has_callr = 0;
#endif
    if ((0 && usrdbg(DBG_PROC)) ||
            ((procflags & STACKCHECK) && !no_stack_checks &&
                !(pcs_flags & PCS_NOSTACKCHECK) && greatest_stackdepth > 256) ||
            ((procflags & BLK0EXIT) && m >= NARGREGS)) {
        r_fr = R_FR;
        mask |= regbit(R_FR);
    }
    n = (m <= NARGREGS) ? m : NARGREGS;
    if (procflags & BLK0EXIT && m >= NARGREGS) {
        r_fr = R_FR;
        mask |= regbit(R_FR);
    }
    for (i = n; i < 4; i++) nspareregs |= 1L << i;
    if (procflags & ARGS2STACK) {
        BindList *bl;
        Binder *b;
        int32 p;

        bl = currentfunction.argbindlist;
        p = 0;
        while (bl && p < 16) {
            b = bl->bindlistcar;
            p = bindaddr_(b);
            if ((p & BINDADDR_MASK) != BINDADDR_ARG) syserr("Binder not BINDADDR_ARG in argbindlist");
            p = p & ~BINDADDR_MASK;
            p += bindmcrep_(b) & MCR_SIZE_MASK;
            bl = bl->bindlistcdr;
        }
        if (n != 0) {
          if (!IS_VARIADIC(m) && !(p > 16)) {
            mask |= regbit(R_A1+n) - regbit(R_A1);
            argwordsbelowfp = n;
            realargwordsbelowfp = n;
            stack_args_split = 1;
          } else {
            if (res_regs >= 4 || (procflags & BLK0EXIT)) {
                r_fr = R_FR;
                mask |= regbit(R_FR);
            }
            fpdesc_setinitoffset(-4-n*4);
            outop(F_PUSH, 0, 0, regbit(R_A1+n) - regbit(R_A1));
          }
        }
        pushed_args = n;
        firstargoff = 0;
    } else
        argwordsbelowfp = n;
    pushed_lr = 0;
    procmask = mask;
    sp_offset = 4*bitcount(mask);
    fpdesc_enterproc();
    if (0 && usrdbg(DBG_PROC)) {
      outop(F_SUBSP, 0, 0, 16 >> 2);
      outop(F_PUSH, 0, 0, mask);
      outop(F_MOVHL, 0, R_FR, R_PC-8);
      outop(F_ADDI8, R_FR, 0, 6);
      outop(F_STRSP, R_FR, 0, (sp_offset+3*4) >> 2);
      outop(F_MOVHL, 0, R_FR, R_LR-8);
      outop(F_STRSP, R_FR, 0, (sp_offset+2*4) >> 2);
      outop(F_ADDRSP, R_FR, 0, (sp_offset+4*4+pushed_args*4) >> 2);
      outop(F_STRSP, R_FR, 0, (sp_offset+1*4) >> 2);
      outop(F_MOVHL, 0, R_FR, R_FP-8);
      outop(F_STRSP, R_FR, 0, (sp_offset+0*4) >> 2);
      outop(F_ADDRSP, R_FR, 0, (sp_offset+3*4) >> 2);
      outop(F_MOVLH, 0, R_FP-8, R_FR);
      firstargoff += 4*4;
    } else {
      if ((regmask & (1<<R_LR)) || procflags & NONLEAF || ((config & CONFIG_OPTIMISE_SPACE) && mask && !(pcs_flags & PCS_INTERWORK))) {
        if ((procflags & BLK0EXIT) || ((pcs_flags & PCS_INTERWORK) && res_regs >= 4)) {
            r_fr = R_FR;
            mask |= regbit(R_FR);
        }
        procmask = mask;
        sp_offset = 4*bitcount(mask);
        pushed_lr = 1;
        outop(F_PUSH, 0, 0, 0x100 | mask);
        intsavewordsbelowfp = bitcount((0x100 | mask) & ~M_ARGREGS);
        firstargoff += 4;
      } else {
        if (mask) outop(F_PUSH, 0, 0, mask);
        intsavewordsbelowfp = bitcount(mask & ~M_ARGREGS);
      }
    }
    firstargoff += sp_offset;;

    if ((procflags & STACKCHECK) && !no_stack_checks && !(pcs_flags & PCS_NOSTACKCHECK)) {
        Symstr *name = stackoverflow;
        LabelNumber *ll;

        n = greatest_stackdepth;
        if (n <= 256) {
            outop(F_CMPHH, 0, R_SP-8, R_SL-8);
        } else {
            name = stack1overflow;
            outop(F_MOVHH, 0, ARM_R_IP-8, R_SP-8);
            load_integer(R_FR, -n);
            outop(F_ADDLH, 0, ARM_R_IP-8, R_FR);
            outop(F_CMPHH, 0, ARM_R_IP-8, R_SL-8);
        }
        ll = nextlabel();
        AddLabelReference(codep, ll);
        addfref_(ll, codep | LABREF_BC);
        outop(F_BC, 0, C_of_Q(Q_GE), 0);
        call_k(name);
        setlabel(ll);
    }
    setlabel(entrylab);

    if (target_stack_moves_once) {
        add_integer(R_SP, R_SP, -greatest_stackdepth);
        fp_minus_sp += greatest_stackdepth;
    }
}

static void add_to_sp(int32 diff)
{
    add_integer(R_SP, R_SP, diff * 4);
}

static void routine_exit(int to_pc)
{
    int32 mask = procmask;
    int32 i, n;
    int32 sp_offset;
    int32 res_regs;

    res_regs = currentfunction.nresultregs;
    if (!res_regs) res_regs = 1;
    sp_offset = 4*bitcount(mask);
    if (0 && usrdbg(DBG_PROC)) {
      add_to_sp(fp_minus_sp/4);
      outop(F_LDRSP, R_IP, 0, (sp_offset+0*4) >> 2);
      outop(F_MOVLH, 0, R_FP-8, R_IP);
      if (to_pc && res_regs < 4) {
        if (mask) outop(F_POP, 0, 0, mask);
        outop(F_LDRSP, R_A1+3, 0, (2*4) >> 2);
        add_to_sp(4 + pushed_args);
        flush_pending(1 << R_SP);
        if (pcs_flags & PCS_INTERWORK)
            outop(F_BX_L, 0, R_A1+3, 0);
        else
            outop(F_MOVLH, 0, R_PC-8, R_A1+3);
      } else {
        /* Ugh */
        outop(F_LDRSP, r_fr, 0, (sp_offset+2*4) >> 2);
        outop(F_MOVLH, 0, R_LR-8, r_fr);
        if (mask) outop(F_POP, 0, 0, mask);
        add_to_sp(4 + pushed_args);
        flush_pending(1 << R_SP);
        if (to_pc) {
            if (pcs_flags & PCS_INTERWORK)
                outop(F_BX_H, 0, R_LR-8, 0);
            else
                outop(F_MOVHH, 0, R_PC-8, R_LR-8);
        }
      }
    } else {
      if (pending_regs & (1 << R_SP)) {
          assert(reg_values[R_SP].typ == REGV_BASE);
          assert(reg_values[R_SP].reg == R_SP);
          fp_minus_sp += reg_values[R_SP].value;
          pending_regs &= ~(1 << R_SP);
      }
      fp_minus_sp /= 4;
      assert(fp_minus_sp >= 0);
      mask &= ~0x0f;
      if (procflags & ARGS2STACK && pushed_args != 0 && stack_args_split == 0) {
          if (fp_minus_sp <= 4 - res_regs && (config & CONFIG_OPTIMISE_SPACE)) {
              for (i = 0; i < fp_minus_sp; i++)
                mask |= 1L << (3-i);
          } else
            add_to_sp(fp_minus_sp);
          if (to_pc && res_regs < 4) {
            if (mask) outop(F_POP, 0, 0, mask);
            outop(F_POP, 0, 0, regbit(R_A1+3));
            add_to_sp(pushed_args);
            flush_pending(1 << R_SP);
            if (pcs_flags & PCS_INTERWORK)
                outop(F_BX_L, 0, R_A1+3, 0);
            else
                outop(F_MOVLH, 0, R_PC-8, R_A1+3);
          } else {
            /* Ugh */
            outop(F_LDRSP, r_fr, 0, sp_offset >> 2);
            outop(F_MOVLH, 0, R_LR-8, r_fr);
            if (mask) outop(F_POP, 0, 0, mask);
            add_to_sp(1 + pushed_args);
            flush_pending(1 << R_SP);
            if (to_pc) {
                if (pcs_flags & PCS_INTERWORK)
                    outop(F_BX_H, 0, R_LR-8, 0);
                else
                    outop(F_MOVHH, 0, R_PC-8, R_LR-8);
            }
          }
      } else {
          n = pushed_args + fp_minus_sp;
          /* This optimisation is really horrible. Consider removing? */
          if (to_pc && n <= 4 - res_regs && (config & CONFIG_OPTIMISE_SPACE)) {
              for (i = 0; i < n; i++)
                  mask |= 1L << (3-i);
          } else
            add_to_sp(n);
          if (pushed_lr) {
            if (!to_pc || (pcs_flags & PCS_INTERWORK)) {
                if (to_pc && res_regs < 4) {
                    if (mask) outop(F_POP, 0, 0, mask);
                    outop(F_POP, 0, 0, regbit(R_A1+3));
                    outop(F_BX_L, 0, R_A1+3, 0);
                } else {
                    outop(F_LDRSP, r_fr, 0, sp_offset >> 2);
                    outop(F_MOVLH, 0, R_LR-8, r_fr);
                    if (mask) outop(F_POP, 0, 0, mask);
                    add_to_sp(1);
                    flush_pending(1 << R_SP);
                    if (to_pc)
                        outop(F_BX_H, 0, R_LR-8, 0);
                }
            } else {
                outop(F_POP, 0, 0, 0x100 | mask);
            }
          } else {
            if (mask) outop(F_POP, 0, 0, mask);
            if (to_pc) {
                if (pcs_flags & PCS_INTERWORK)
                    outop(F_BX_H, 0, R_LR-8, 0);
                else
                    outop(F_MOVHH, 0, R_PC-8, R_LR-8);
            }
          }
      }
    }
}

static int simple_routine_exit(void)
{
    if (fp_minus_sp) return 0;
    return (!(procflags & ARGS2STACK) || pushed_args == 0) && !usrdbg(DBG_PROC);
}

static int32 pcref(int32 dest, int32 size)
{
    int32 d;

    d = (dest - codep - PC_OFFSET) / 2;
    if (d < -size || d >= size) syserr(syserr_displacement, d);
    return d & (size - 1);
}

typedef struct Backwards_Branch {
    struct Backwards_Branch *cdr;
    LabelNumber *real_dest;
    LabelNumber *faked_dest;
} Backwards_Branch;

Backwards_Branch *backwards_branches;

static void add_casebranch(LabelNumber *destination)
{
    if (lab_isset_(destination)) {
        if (destination == returnlab && !(config & CONFIG_OPTIMISE_SPACE)) {
            destination = returnlab = nextlabel();
        } else {
            Backwards_Branch *b = NewSyn(Backwards_Branch);
            cdr_(b) = backwards_branches;
            b->real_dest = destination;
            b->faked_dest = destination = nextlabel();
            backwards_branches = b;
        }
    }
    {   LabelNumber *ll = NULL;
        int32 max_dest = casebranch_codep + branch_range((use_dcw ? FREF_DCW : FREF_DCB) | Q_AL);
        FRef_Branch *new_fref, *fref;
        FRef_Branch **fref_p = &fref_branches;
        for (; (fref = *fref_p) != NULL; fref_p = &cdr_(fref)) {
            if (destination == fref->real_dest && FREF_CONDITION(fref->flags) == Q_AL) {
                if (max_dest < fref->pcref + branch_range(fref->flags)) {
                    *fref_p = cdr_(fref);
                    if (cdr_(fref) == NULL) fref_branches_head = fref_p;
                    fref_p = &fref_branches;
                    new_fref = fref;
                    for (; (fref = *fref_p) != NULL; fref_p = &cdr_(fref)) {
                        if (max_dest <= fref->pcref + branch_range(fref->flags))
                            break;
                    }
                    cdr_(new_fref) = fref;
                    new_fref->pcref = casebranch_codep;
                    new_fref->codep = codep;
                    new_fref->flags = Q_AL | (use_dcw ? FREF_DCW : FREF_DCB);
                    *fref_p = new_fref;
                    if (fref == NULL) fref_branches_head = &cdr_(new_fref);
                    fref = new_fref;
                }
                ll = fref->chained_dest;
                break;
            }
        }
        if (fref == NULL) {
            ll = nextlabel();
            fref_p = &fref_branches;
            for (; (fref = *fref_p) != NULL; fref_p = &cdr_(fref))
                if (max_dest <= fref->pcref + branch_range(fref->flags))
                    break;
            new_fref = NewSyn(FRef_Branch);
            cdr_(new_fref) = fref;
            new_fref->pcref = casebranch_codep;
            new_fref->codep = codep;
            new_fref->flags = Q_AL | (use_dcw ? FREF_DCW : FREF_DCB);
            new_fref->real_dest = destination;
            new_fref->chained_dest = ll;
            *fref_p = new_fref;
            if (fref == NULL) fref_branches_head = &cdr_(new_fref);
            branchpoolsize += 2;
        }
        if (use_dcw)
        {
            AddLabelReference(codep, ll);
            addfref_(ll, codep| LABREF_BXX_16);
            outDCW(codep - casebranch_codep);
        }
        else
        {
            AddLabelReference(codep, ll);
            addfref_(ll, codep | LABREF_BXX_8);
            outDCB((codep - casebranch_codep) >> 1);
        }
    }
}

static LabelNumber *add_fref_branch(LabelNumber *destination, int32 codep, uint32 condition)
{
    LabelNumber *ll;
    FRef_Branch *new_fref, *fref, **fref_p;
    int32 max_dest;
    int32 span;

#if 0
    fprintf(stderr, "%.8x: (add_fref_branch) F%dL%d\n", codebase + codep, current_procnum, lab_name_(destination) & 0xfffff);
#endif
    span = branch_range(FREF_BRANCH | condition);
    max_dest = codep + span;
    fref_p = &fref_branches;
    for (; (fref = *fref_p) != NULL; fref_p = &cdr_(fref)) {
        if (destination == fref->real_dest &&
                (FREF_CONDITION(fref->flags) == Q_AL ||
                        FREF_CONDITION(fref->flags) == condition)) {
            if (condition == Q_AL &&
                    codep - fref->pcref > (FREF_TYPE(fref->flags) == FREF_BRANCH ? 1024 : 256)) {
                *fref_branches_head = fref;
                *fref_p = cdr_(fref);
                cdr_(fref) = NULL;
                fref_branches_head = &cdr_(fref);
                setlabel1(fref->chained_dest);
                fref->chained_dest = nextlabel();
                fref->pcref = codep;
                fref->codep = codep;
                fref->flags = condition | FREF_BRANCH;
            } else {
                if (max_dest < fref->pcref + branch_range(fref->flags)) {
                    *fref_p = cdr_(fref);
                    if (cdr_(fref) == NULL) fref_branches_head = fref_p;
                    fref_p = &fref_branches;
                    new_fref = fref;
                    for (; (fref = *fref_p) != NULL; fref_p = &cdr_(fref)) {
                        if (max_dest <= fref->pcref + branch_range(fref->flags))
                            break;
                    }
                    cdr_(new_fref) = fref;
                    new_fref->pcref = codep;
                    new_fref->codep = codep;
                    new_fref->flags = condition | FREF_BRANCH;
                    *fref_p = new_fref;
                    if (!fref) fref_branches_head = &cdr_(new_fref);
                    fref = new_fref;
                }
            }
            AddLabelReference(codep, fref->chained_dest);
            recalc_mustbranchlitby();
            return fref->chained_dest;
        }
    }
    ll = nextlabel();
    fref_p = &fref_branches;
    for (; (fref = *fref_p) != NULL; fref_p = &cdr_(fref)) {
        if (max_dest <= fref->pcref + branch_range(fref->flags))
            break;
    }
    new_fref = NewSyn(FRef_Branch);
    cdr_(new_fref) = fref;
    new_fref->pcref = codep;
    new_fref->codep = codep;
    new_fref->flags = condition | FREF_BRANCH;
    new_fref->real_dest = destination;
    new_fref->chained_dest = ll;
    *fref_p = new_fref;
    if (fref == NULL) fref_branches_head = &cdr_(new_fref);
    branchpoolsize += 2;
    AddLabelReference(codep, ll);
    recalc_mustbranchlitby();
    return new_fref->chained_dest;
}

static void add_branch(LabelNumber *dest, int32 condition, int32 codep)
{
    Branch *b = NewSyn(Branch);
    cdr_(b) = available_branches;
    available_branches = b;
    b->codep = codep;
    b->condition = condition;
    b->dest = dest;
}

static Branch *branch_available(LabelNumber *dest, int32 condition)
{
    int32 span = condition == Q_AL ? 2036 : 244;
    int32 max_dest = codep - span;
    Branch *b = available_branches;
    Branch *use_b = NULL;
    for (; b != NULL && b->codep >= max_dest; b = cdr_(b)) {
        if (b->dest == dest &&
            (b->condition == Q_AL ||
                (b->condition == condition && (!use_b || use_b->condition != Q_AL))))
            use_b = b;
    }
    return use_b;
}

static void conditional_branch_to(int32 condition, LabelNumber *destination, int use_bl)
{
    LabelNumber *ll;
    Branch *b;
    int32 inst_codep;

    if (destination == RETLAB) {
        /* Only the result registers matter on function exit */
        int32 i = 0;
        int32 regs = 0;
        do {
          regs |= 1L << i;
          i++;
        } while (i < currentfunction.nresultregs);
        if (condition == Q_AL) spareregs |= procmask & ~regs;
        ldm_flush();
        /* Ensure final values of result registers + any V registers not
         * in procmask. These must be assignments to global registers so
         * need to be flushed here
         */
        flush_pending(regs | (0xf0 & ~procmask));
        destination = returnlab;
        if (condition == Q_AL) {
            /* if get an unconditional return expand it inline */
            /* and save its address if it was the first            */
            pending_regs &= (1 << R_SP);
            return_pending = 0;
            if (simple_routine_exit() || !lab_isset_(destination)) {
              flush_pending(1 << R_SP);
              if (!lab_isset_(destination)) {
                setlabel(destination);
              }
              dbg_return(codebase+codep);
              routine_exit(1);
              return;
            }
        } else {
            if (flags_reg != NoRegister) flush_pending(1L << flags_reg);
            if (!lab_isset_(destination)) return_pending = 1;
        }
    } else {
      ldm_flush();
      flush_pending(0xff);
    }
    flush_pending(1 << R_SP);
    if ((condition & ~Q_UBIT) == Q_NE && cmp_reg != NoRegister) {
      reg_values[cmp_reg].typ = REGV_CONSTANT;
      reg_values[cmp_reg].value = cmp_value;
    }
/*
 * Unconditional branches can reach MUCH further than conditional ones...
 */
    inst_codep = codep;
    if (condition == Q_AL) {
        if (lab_isset_(destination) || use_bl) {
            /* u.defn shares with u.frefs */
            int32 dest = destination->u.defn & 0xffffff;
            int32 span = dest - (codep + PC_OFFSET);
            ll = destination;
            if (use_bl || span < -2048 || span >= 2048) {
              if (!pushed_lr) syserr(syserr_leaf_fn, symname_(currentfunction.symstr));
              if (!use_bl && (b = branch_available(destination, condition)) != 0) {
                ll = nextlabel();
                AddLabelReference(inst_codep, ll);
                outop(F_B, 0, 0, pcref(b->codep, 0x800));
                setlabel2(ll, b->codep);
              } else {
                int32 d;

                AddLabelReference(inst_codep, ll);
                d = 0;
                if (!lab_isset_(destination))
                    addfref_(destination, codep | LABREF_BL);
                else
                    d = pcref(dest, 0x400000);
                outop(F_CALL1, 0, 0, (d >> 11) & 0x7ff);
                outop(F_CALL, 0, 0, d & 0x7ff);
              }
            } else {
              AddLabelReference(inst_codep, ll);
              outop(F_B, 0, 0, pcref(dest, 0x800));
            }
            add_branch(destination, condition, inst_codep);
        } else {
            ll = add_fref_branch(destination, codep, Q_AL);
            addfref_(ll, codep | LABREF_B);
            outop(F_B, 0, 0, 0);
        }
    } else {
        if (lab_isset_(destination)) {
          /* u.defn shares with u.frefs */
          int32 span = (destination->u.defn & 0x00ffffff) - (codep+PC_OFFSET);
          if (span >= -256 && span < 256) {
              ll = destination;
              AddLabelReference(inst_codep, ll);
              outop(F_BC, 0, C_of_Q(condition),
                                pcref(destination->u.defn & 0x00ffffff, 0x100));
              add_branch(destination, condition, inst_codep);
          } else {
              ll = nextlabel();
              if ((b = branch_available(destination, codep)) != 0) {
                  AddLabelReference(inst_codep, ll);
                  outop(F_BC, 0, C_of_Q(condition), pcref(b->codep, 0x100));
                  setlabel2(ll, b->codep);
              } else {
                  AddLabelReference(inst_codep, ll);
                  addfref_(ll, codep | LABREF_BC);
                  outop(F_BC, 0, C_of_Q(Q_NEGATE(condition)), 0);
                  conditional_branch_to(Q_AL, destination, 0);
                  setlabel(ll);
              }
          }
        } else {
          ll = add_fref_branch(destination, codep, condition);
          addfref_(ll, codep | LABREF_BC);
          outop(F_BC, 0, C_of_Q(condition), 0);
        }
    }
}

static void dump_backwards_branches(void)
{
    Backwards_Branch *b;
    for (b = backwards_branches; b != NULL; b = cdr_(b)) {
        setlabel(b->faked_dest);
        conditional_branch_to(Q_AL, b->real_dest, 0);
    }
    backwards_branches = NULL;
}

static int is_commutative(int32 op)
{
    return op == F_AND || op == F_EOR || op == F_OR || op == F_MUL;
}

static void rk_op(int32 op, int32 r1, int32 r2, int32 m)
{
    int32 r;
    int32 dead_r1 = nspareregs & (1 << r1);
    if (r2 == R_IP) syserr("op = %x: IP clash @ %.8lx", (int)op, codebase+codep);
    r = constant_available(m);
    if (r >= 0) {
        if (r == r1) {
            if (is_commutative(op)) {
                outop(op, 0, r1, r2);
                return;
            }
        } else {
            if (nspareregs & (1L << r2)) {
                outop(op, 0, r2, r);
                if (!dead_r1) move_register(r1, r2);
            } else {
                move_register(r1, r2);
                outop(op, 0, r1, r);
            }
            return;
        }
    }
    if (r1 == r2) {
        load_integer(R_IP, m);
        outop(op, 0, r1, R_IP);
    } else if (is_commutative(op)) {
        load_integer(r1, m);
        outop(op, 0, r1, r2);
    } else {
        load_integer(R_IP, m);
        if (nspareregs & (1L << r2)) {
            /* Better this way ...
             * MOV may be eliminated later
             */
            outop(op, 0, r2, R_IP);
            if (!dead_r1) move_register(r1, r2);
        } else {
            move_register(r1, r2);
            outop(op, 0, r1, R_IP);
        }
    }
}

static void rr_op(int32 op, int32 r1, int32 r2, int32 m)
{
    int32 r_ip;
    int32 dead_r1 = nspareregs & (1 << r1);
    if (r1 == r2) {
        outop(op, 0, r1, m);
    } else if (r1 == m) {
        switch (op) {
          case F_AND:
          case F_OR:
          case F_EOR:
          case F_MUL:
#ifdef THUMB_INLINE_ASSEMBLER
          case F_ADC:
#endif
            outop(op, 0, r1, r2);
            break;
          case F_BIC:
            outop(F_MVN, 0, r1, r1);
            outop(F_AND, 0, r1, r2);
            break;
          case F_LSL:
          case F_LSR:
          case F_ASR:
          case F_ROR:
#ifdef THUMB_INLINE_ASSEMBLER
          case F_SBC:
#endif
            if (r2 == R_IP) syserr("F_LSL/F_LSR/F_ASR/F_ROR: IP clash @ %.8lx", codebase+codep);
            r_ip = R_IP;
            if (nspareregs & (1L << r2)) r_ip = r2;
            move_register(r_ip, r2);
            outop(op, 0, r_ip, r1);
            if (!dead_r1) move_register(r1, r_ip);
            break;
        }
    } else {
        if ((nspareregs & (1L << r2)) && !(op == F_MUL && r2 == m)) {
            outop(op, 0, r2, m);
            if (!dead_r1) move_register(r1, r2);
        } else {
            move_register(r1, r2);
            outop(op, 0, r1, m);
        }
    }
}

static int32 pending_op = -1;
static int32 pending_r1, pending_r2;
static int32 saved_spareregs;

static void debug_putc(char c)
{
    cc_msg("%c", c);
}

#if 0
static char *nameof_cond(int32 condition)
{
    switch (condition & ~Q_UBIT) {
      case Q_EQ & ~Q_UBIT: return "EQ";
      case Q_NE & ~Q_UBIT: return "NE";
      case Q_HS & ~Q_UBIT: return "CS";
      case Q_LO & ~Q_UBIT: return "CC";
      case Q_PL & ~Q_UBIT: return "PL";
      case Q_MI & ~Q_UBIT: return "MI";
      case Q_HI & ~Q_UBIT: return "HI";
      case Q_LS & ~Q_UBIT: return "LS";
      case Q_GE & ~Q_UBIT: return "GE";
      case Q_LT & ~Q_UBIT: return "LT";
      case Q_GT & ~Q_UBIT: return "GT";
      case Q_LE & ~Q_UBIT: return "LE";
      case Q_AL & ~Q_UBIT: return "AL";
      default:
        syserr("unknown condition %x\n", condition);
        return "??";
    }
}
#endif

#define BaseIsWordAligned(op, base, peep) (((op) & J_BASEALIGN4) || (base) == R_SP || ((peep) & P_BASEALIGNED))

void show_inst_direct(PendingOp *p)
{
    J_OPCODE op = p->ic.op;
    RealRegister r1 = p->ic.r1.rr, r2 = p->ic.r2.rr, m = p->ic.r3.i;
    int32 peep = p->peep, deadbits = p->dataflow;
    int32 illbits;
    int32 w;
    RealRegister r1r = NoRegister, r2r = NoRegister, mr = NoRegister;
    int len;
    J_OPCODE op1;
    int32 i, n;

    CheckJopcodeP(p, JCHK_MEM | JCHK_REGS | JCHK_SYSERR);
#if 0
    {
        FRef_Branch *fref;
        cc_msg("mustbranchlitby = %.8x (branchpoolsize = %.8x)\n",
               codebase + mustbranchlitby, branchpoolsize);
        for (fref = fref_branches; fref != NULL; fref = cdr_(fref)) {
            if (FREF_TYPE(fref->flags) == FREF_DCB)
                cc_msg("@%.8x, DCB F%dL%d (F%dL%d) (pcref = %.8x)\n",
                       codebase + fref->codep, current_procnum,
                       lab_name_(fref->chained_dest) & 0xfffff,
                       current_procnum, lab_name_(fref->real_dest) & 0xfffff, fref->pcref);
            else
                cc_msg("@%.8x, B%s F%dL%d (F%dL%d) (pcref = %.8x)\n",
                       codebase + fref->codep, nameof_cond(FREF_CONDITION(fref->flags)),
                       current_procnum, lab_name_(fref->chained_dest) & 0xfffff,
                       current_procnum, lab_name_(fref->real_dest) & 0xfffff, fref->pcref);
        }
    }
#endif
    nspareregs = spareregs;
    op1 = op & J_TABLE_BITS;
    if (op1 == J_CALLK || op1 == J_OPSYSK || op1 == J_CALLR) {
#if 0
/* /* ECN - Need to rethink this. This set is wrong if the usage of caller
 * save registers is precisely known.
 */
        nspareregs |= 0x0f;
#endif
        n = k_resultregs_(r2);
        for (i = 0; i < n; i++) nspareregs &= ~(1L << i);
    }

    if (debugging(DEBUG_LOCALCG)) {
        cc_msg("%.8lx ", codebase+codep);
        if (a_uses_r1(p) && (deadbits & J_DEAD_R1)) debug_putc('*'); else debug_putc('-');
        if (a_uses_r2(p) && (deadbits & J_DEAD_R2)) debug_putc('*'); else debug_putc('-');
        if (a_uses_r3(p) && (deadbits & J_DEAD_R3)) debug_putc('*'); else debug_putc('-');
        if (a_loads_r1(p)) debug_putc('!'); else debug_putc('-');
        if (a_loads_r2(p)) debug_putc('!'); else debug_putc('-');
        if (peep & P_CMPZ) debug_putc('#'); else debug_putc(' ');
        if (peep & P_BASEALIGNED) debug_putc('%'); else debug_putc(' ');
        if (op & J_BASEALIGN4) debug_putc('^'); else debug_putc(' ');
    }
    if (peep & P_CMPZ) {
        ldm_flush();
        flush_pending(0xff | (1 << R_SP));
    }
    if (a_uses_r1(p)) {
        r1r = r1;
/* Fails on inline assembler...
        if (r1r >= 8 && op1 != J_MOVR  && op1 != J_ADDR && !(r1r == R_SP && op1 == J_ADDK)
            syserr("r1 = %d, op = %d", (int)r1, (int)op1);
*/
        if (deadbits & J_DEAD_R1) nspareregs |= 1L << r1;
    }
    if (a_uses_r2(p)) {
        r2r = r2;
        if (r2r >= 8 && op1 != J_MOVR && op1 != J_ADDR && r2r != R_SP)
            syserr("r2 = %d, op = %d", (int)r2, (int)op1);
        if (deadbits & J_DEAD_R2) nspareregs |= 1L << r2;
    }
    if (a_uses_r3(p)) {
        mr = m;
        if (mr >= 8 && op1 != J_MOVR && op1 != J_ADDR && !(mr == R_SP && (op1 == J_SUBR || op1 == J_CMPR)))
            syserr("mr = %d, op = %d", (int)mr, (int)op1);
        if (deadbits & J_DEAD_R3) nspareregs |= 1L << m;
    }
    if (a_loads_r1(p) && !(deadbits & J_DEAD_R1)) nspareregs &= ~(1L << r1);
    if (a_loads_r2(p) && !(deadbits & J_DEAD_R2)) nspareregs &= ~(1L << r2);
    if (debugging(DEBUG_LOCALCG)) {
        for (i = 0; i < 8; i++)
            debug_putc((int)((nspareregs & (1L << i)) ? '0' + i : '-'));
        if ((op & J_TABLE_BITS) > J_LAST_JOPCODE)
            cc_msg("                %-3ld     %ld, %ld, %ld\n", (op & J_TABLE_BITS), p->ic.r1.rr, p->ic.r2.rr, p->ic.r3.rr);
        else
            print_jopcode (&p->ic);
    }

    op &= ~J_DEADBITS;

    if (op1 != J_BXX) {
        casebranch_pending = -1;
        if (codep & 1) outDCB(0);
        if (casebranch_litpool) {
            char b[32];
            sprintf(b, "x$litpool$%d", literal_pool_number);
            obj_symref(sym_insert_id(b), xr_code+xr_defloc+xr_dataincode, (casebranch_litpool+3) & ~3);
            sprintf(b, "x$litpool_e$%d", literal_pool_number++);
            obj_symref(sym_insert_id(b), xr_code+xr_defloc+xr_dataincode, codebase+codep-1);
            casebranch_litpool = 0;
        }
        if (backwards_branches)
            dump_backwards_branches();
    }

    if (deadcode) {
        if (op1 != J_LABEL && op1 != J_ENDPROC) {
            goto windup;
        } else {
            if (!(op1 == J_LABEL && deadcode == (LabelNumber *)m)) {
                conditional_branch_to(Q_AL, deadcode, 0);
                dump_branch_lits(0, 0);
            }
            deadcode = 0;
        }
    }
    if (pending_op >= 0) {
        int32 tmp_spareregs;
        if (op1 == J_ADDK && !(peep & P_CMPZ) && m == 4 && r1r == r2r && r1r == pending_r2) {
            w = F_LDM;
            if (pending_op == F_STRI5) w = F_STM;
            spareregs = saved_spareregs;
            outop(w, pending_r2, 0, 1L << pending_r1);
            pending_op = -1;
            goto windup;
        }
        tmp_spareregs = spareregs;
        spareregs = saved_spareregs;
        outop(pending_op, pending_r2, pending_r1, 0);
        spareregs = tmp_spareregs;
        pending_op = -1;
    }
    /* Don't dump literals just before an ENDPROC as otherwise the
     * 'branch round literals' will never be resolved.
     */
    if (op1 != J_ENDPROC) {
      if (codep >= mustlitby - branchpoolsize) {
        dumplits(1);
      }
      if (codep >= mustbranchlitby)
        dump_branch_lits(1, 0);
    }
    illbits = op & (Q_MASK | J_SIGNED | J_UNSIGNED);
    switch(op & ~(Q_MASK | J_SIGNED | J_UNSIGNED | J_BASEALIGN4))
    {
#define rkop(inst) rk_op(inst, r1r, r2r, m)

#define rrop(inst) rr_op(inst, r1r, r2r, mr)

#ifdef THUMB_CPLUSPLUS
case J_WORD_ADCON:
        cnop();
        obj_symref((Symstr *)m, xr_code, 0);
        AddCodeXref4(X_absreloc | codebase+codep, (Symstr *)m, 0);
        outcodeword(0, LIT_ADCON);
        break;

case J_WORD_LABEL:
        cnop();
        addfref_((LabelNumber *)m, codep | LABREF_WORD32);
        outcodeword(0, LIT_ADCON);
        break;
#endif

case J_WORD:
        flush_pending(0xff | (1 << R_SP));
        ldm_flush();
        outHW(m);
        break;

case J_ADCONF:
case J_ADCOND:
        load_fp_adcon(r1r, op, (FloatCon *)m);
        break;
case J_ADCONLL:
        load_ll_adcon(r1r, op, (Int64Con *)m);
        break;
case J_CMPR:
        if (r2r == R_SP)
            outop(F_CMPLH, 0, R_SP-8, mr);
        else if (mr == R_SP)
            outop(F_CMPHL, 0, r2r, R_SP-8);
        else
            outop(F_CMP, 0, r2r, mr);
        illbits &= ~Q_MASK;
        peep &= ~P_CMPZ;
        break;
#ifdef THUMB_INLINE_ASSEMBLER
case J_CMNR:
        outop(F_CMN, 0, r2r, mr);
        illbits &= ~Q_MASK;
        peep &= ~P_CMPZ;
        break;
#endif
case J_MOVR:
        move_register(r1r, mr);
        if (peep & P_CMPZ) {
            if (r1r >= 8 && mr >= 8) syserr("peep & P_CMPZ && r1 >= 8 && mr >= 8");
            if (r1r >= 8) outop(F_CMP8, mr, 0, 0);
            if (mr >= 8) outop(F_CMP8, r1r, 0, 0);
        }
        peep &= ~P_CMPZ;
        break;
case J_NEGR:
        outop(F_NEG, 0, r1r, mr);
        peep &= ~P_CMPZ;
        break;
case J_NOTR:
        outop(F_MVN, 0, r1r, mr);
        peep &= ~P_CMPZ;
        break;
case J_MOVK:
        load_integer(r1r, m);
        break;

case J_CALLK:
        call_k((Symstr *)m);
        break;

case J_TAILCALLK: {
            int32 d;
            int32 dest;
            int32 n;

            ldm_flush();
            if ((Symstr *)m == currentfunction.symstr) {
                dest = entrylab->u.defn & 0xffffff;
                if ((n = pushed_args) != 0) {
                    outop(F_ADDSP, 0, 0, n*4);
                    outop(F_PUSH, 0, 0, regbit(R_A1+n) - regbit(R_A1));
                }
                flush_pending(0xff | (1 << R_SP));
                d = (dest - codep - PC_OFFSET) / 2;
                if (d >= -0x400) {
                    AddLabelReference(codep, entrylab);
                    outop(F_B, 0, 0, d & 0x7ff);
                } else {
                    load_adcon(r_fr, (Symstr *)m, dest);
                    outop(F_MOVLH, 0, R_PC-8, r_fr);
                }
                break;
            }
#ifdef THUMB_CPLUSPLUS
            flush_pending(0xff | (1<<R_SP));
            arm_tailcall_k((Symstr *)m);
#else
            syserr("Non recursive tailcall to $r in $r", (Symstr *)m, currentfunction.symstr);
#endif
            break;
        }

case J_TAILCALLR:
            /* Pending rethink about J_TAILCALLR */
            syserr("Thumb cannot handle J_TAILCALLR");
            ldm_flush();
            flush_pending(0xff);
            if ((procmask & M_VARREGS & regbit(mr)) || mr == R_IP) {
                outop(F_MOVLH, 0, ARM_R_IP-8, mr);
                routine_exit(0);
                outop(F_BX_H, 0, ARM_R_IP-8, 0);
            } else {
                routine_exit(0);
                outop(F_BX_L, 0, mr, 0);
            }
            break;

case J_OPSYSK: {
            RealRegister i;

            if (p->ic.r2.i & K_SPECIAL_ARG)
                outop(F_MOVLH, 0, ARM_R_IP-8, TARGET_SPECIAL_ARG_REG);
            ldm_flush();
            flush_pending(0xff | (1 << R_SP));
            for (i = 0; i < 4; i++)
              reg_values[i].typ = REGV_UNKNOWN;
            outop(F_SWI, 0, 0, m);
            flags_reg = NoRegister;
            andk_flag = 0;
            cmp_reg = NoRegister;
        }
        break;

case J_CALLR:
#if 0
        if (pcs_flags & PCS_INTERWORK) {
            call_k(call_via[mr]);
        } else {
          RealRegister i;

          ldm_flush();
          flush_pending(0xff | (1 << R_SP));
          for (i = 0; i < 4; i++)
            reg_values[i].typ = REGV_UNKNOWN;
          outop(F_MOVHH, 0, R_LR-8, R_PC-8);
          outop(F_MOVLH, 0, R_PC-8, mr);
          flags_reg = NoRegister;
          andk_flag = 0;
          cmp_reg = NoRegister;
        }
#else
        call_k(call_via[mr]);
#endif
        break;

case J_ADCON:
        {   Symstr *name = (Symstr *)m;
            int32 offset = (int32)r2;
            load_adcon(r1r, name, offset);
        }
        break;

case J_INFOLINE:
        ldm_flush();
        flush_pending(ALL_REGS);
        dbg_addcodep((VoidStar)r1, codebase+codep);
        break;
case J_INFOSCOPE:
        ldm_flush();
        flush_pending(ALL_REGS);
        dbg_addcodep(NULL, codebase+codep);
        break;
case J_INFOBODY:
        dbg_bodyproc();
        break;
case J_STRING: {
            StringSegList *s;
            int32 disp;

            s = (StringSegList *)m;
            ldm_flush();
            flush_pending(0xff | (1 << R_SP));
            w = 0;
            if (r2 >= 0) w = r2 & ~3;
            disp = lit_findstringincurpool(s);
            if (disp >= 0) {
                addfref_(litlab, codep | LABREF_WORD8);
                AddLitPoolReference(codep, disp);
                outop(F_ADDRPC, r1r, 0, (disp + w) / 4);
            } else {
                disp = lit_findstringinprevpools(s, codebase+codep+PC_OFFSET-252+w);
                if (disp >= 0) {
                    disp = codebase+codep+PC_OFFSET-disp+w;
                    outop(F_MOVHL, 0, r1r, R_PC-8);
                    outop(F_SUBI8, r1r, 0, disp);
                } else {
                    if (stringlength(s) > 8 && (disp = lit_findstringinprevpools(s, 0)) >= 0) {
                        load_adcon(r1r, bindsym_(codesegment), disp+r2);
                    } else {
                        addressability(1024 - r2);
                        addfref_(litlab, codep | LABREF_WORD8);
                        AddLitPoolReference(codep, litpoolp << 2);
                        outop(F_ADDRPC, r1r, 0, litpoolp + w / 4);
                        codeseg_stringsegs(s, 1);
                    }
                }
            }
            if (w ^ r2) add_integer(r1r, r1r, w ^ r2);
        }
        break;

case J_B: {
          int32 condition;

          condition = check_cmp(op & Q_MASK);
          if (condition == Q_AL && !disable_opt)
            deadcode = (LabelNumber *)m;
          else if (condition != Q_NOT)
            conditional_branch_to(condition, (LabelNumber *)m, 0);
          illbits &= ~Q_MASK;
        }
        break;

case J_BXX: {            /* Used with case tables */
        LabelNumber *l, *ll;
        LabelNumber *table;

        l = (LabelNumber *)m;
        /* expand RETLAB so that we always generate a branch of 2 bytes */
        if (l == RETLAB) l = returnlab;
        m = casebranch_pending_m;
        r1r = casebranch_pending;
        casebranch_pending = -1;
        uses_IP = YES;
/*
 * The first BXX in any branch table is to the default label
 */
        if (r1r >= 0) {
            if (m >= USE_DCB_FOR_CASEBRANCH && m < USE_DCW_FOR_CASEBRANCH) {
                /* If this is a big switch statement then a conditional */
                /* branch might not reach from here to the default     */
                /* label so do it by a conditional branch to an        */
                /* unconditional branch at the head of the cases       */
                ll = nextlabel();
                AddLabelReference(codep, ll);
                conditional_branch_to(Q_HS, ll, 0);
                outop(F_LSLK, R_IP, r1r, use_bl ? 2 : 1);
                outop(F_ADDLH, 0, R_PC-8, R_IP);
                setlabel(ll);
                conditional_branch_to(Q_AL, l, 0);
            } else {
                table = nextlabel();
                if (use_dcw) {
                    ll = nextlabel();
                    AddLabelReference(codep, ll);
                    conditional_branch_to(Q_HS, ll, 0);
                    addfref_(table, codep | LABREF_WORD8);
                    AddLabelReference(codep, table);
                    outop(F_ADDRPC, R_IP, 0, 0);
                    outop(F_ADD3R, R_IP, R_IP, r1r);
                    outop(F_LDRHADDR, R_IP, R_IP, r1r);
                    casebranch_codep = codep;
                    outop(F_ADDLH, 0, R_PC-8, R_IP);
                    setlabel(ll);
                    conditional_branch_to(Q_AL, l, 0);
                } else {
                    conditional_branch_to(Q_HS, l, 0);
                    addfref_(table, codep | LABREF_WORD8);
                    AddLabelReference(codep, table);
                    outop(F_ADDRPC, R_IP, 0, 0);
                    outop(F_LDRBADDR, R_IP, R_IP, r1r);
                    outop(F_LSLK, R_IP, R_IP, 1);
                    casebranch_codep = codep;
                    outop(F_ADDLH, 0, R_PC-8, R_IP);
                }
                cnop();
                setlabel(table);
                casebranch_litpool = codebase+codep;
            }
        } else {
            if (m >= USE_DCB_FOR_CASEBRANCH && m < USE_DCW_FOR_CASEBRANCH)
                conditional_branch_to(Q_AL, l, use_bl);
            else
                add_casebranch(l);
        }
        break;
    }

case J_CASEBRANCH: {
        int32 b_size;
/*
 * I will not want any danger of the branch table being disrupted by
 * an attempt to dump out a literal pool, so if needbe I dump out the
 * pool right now...
 */
        if (m >= USE_DCB_FOR_CASEBRANCH && m < USE_DCW_FOR_CASEBRANCH) {
            use_bl = 0;
            b_size = 2+2;       /* 2 for B, 2 for branchpool */
        } else {
            use_dcw = (m >= USE_DCW_FOR_CASEBRANCH);
            b_size = 1+2;       /* 1 for DCB, 2 for branchpool */
            if (use_dcw) b_size = 2+2;  /* 2 for DCW, 2 for branchpool */
        }
        b_size = b_size * m + 2 * 6;
        if (codep+b_size >= mustlitby - branchpoolsize)
          dumplits(1);
        if (codep+b_size >= mustbranchlitby)
          dump_branch_lits(1, b_size);
        r2r = r1r;   /* So I can use rrop() */
        casebranch_pending_m = m;
        if (m >= 0 && m <= 0xff) {
            outop(F_CMP8, r2r, 0, (m-1));
        } else {
            m -= 1;
            rkop(F_CMP);
        }
        casebranch_pending = r1r;  /* Let BXX finish this bit of code off */
        break;
      }
case J_SHRK:
        if (m == 0) syserr("Shift right of 0");
        outop(op & J_UNSIGNED ? F_LSRK : F_ASRK, r1r, r2r, m & 0x1f);
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        peep &= ~P_CMPZ;
        break;
case J_SHLK:
        outop(F_LSLK, r1r, r2r, m & 0x1f);
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        peep &= ~P_CMPZ;
        break;

case J_SHLR:
        rrop(F_LSL);
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        peep &= ~P_CMPZ;
        break;
case J_SHRR:
        rrop(op & J_UNSIGNED ? F_LSR : F_ASR);
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        peep &= ~P_CMPZ;
        break;

case J_RORR:
        rrop(F_ROR);
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        peep &= ~P_CMPZ;
        break;

case J_RORK:
        rkop(F_ROR);
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        peep &= ~P_CMPZ;
        break;

#ifdef THUMB_CPLUSPLUS
case J_THIS_ADJUST:
          {   int32 v[4]; int32 *ve, *p;
              if (m & 3) syserr("Pointer adjustment %d not a multiple of 4", m);
              ve = arm_add_integer(R_A1, R_A1, m, 0, NULL, v);
              for (p = &v[0]; p != ve; p++)
                  outcodeword(ARM_AL | *p, LIT_OPCODE_32);
              break;
          }
#endif
#ifdef THUMB_INLINE_ASSEMBLER
case J_SBCK:
        rkop(F_SBC);
        peep &= ~P_CMPZ;
        break;
case J_ADCK:
        rkop(F_ADC);
        peep &= ~P_CMPZ;
        break;
#endif
case J_ADDK:
        if ((peep & P_CMPZ) && (nspareregs & (1L << r1))) {
            if (r2r < 8 && -m >= 0 && -m <= 0xff)
                outop(F_CMP8, r2r, 0, -m);
            else {
                add_integer(r1r, r2r, m);
                flush_pending(1 << r1r);
            }
        } else
            add_integer(r1r, r2r, m);
        if (r2r >= 8 && (peep & P_CMPZ)) {
            if (r1r >= 8) syserr("P_CMPZ set with Rd >= 8 and Rn >=8 in J_ADDK");
            outop(F_CMP8, r1r, 0, 0);
        }
        peep &= ~P_CMPZ;
        break;
#ifdef THUMB_INLINE_ASSEMBLER
case J_CMNK:
    if (m == 0)
    {
        outop(F_MOV8, R_IP, 0, 0);
        outop(F_CMN, 0, r2r, R_IP);
        illbits &= ~Q_MASK;
        peep &= ~P_CMPZ;
        break;
    }
    else
        m = -m; /* and fallthrough CMPK case */
#endif
case J_CMPK:
        if (m >= 0 && m <= 0xff) outop(F_CMP8, r2r, 0, m);
        else {
            int r;

            if (r2r == R_IP) syserr("J_CMPK:IP clash @ %.8lx", codebase+codep);
            if ((r = constant_available(m)) >= 0) {
                outop(F_CMP, 0, r2r, r);
            } else if ((r = constant_available(-m)) >= 0) {
                outop(F_CMN, 0, r2r, r);
            } else {
                len = load_integer0(R_IP, m, 1);
                if (load_integer0(R_IP, -m, 1) < len) {
                  load_integer(R_IP, -m);
                  outop(F_CMN, 0, r2r, R_IP);
                } else {
                  load_integer(R_IP, m);
                  outop(F_CMP, 0, r2r, R_IP);
                }
            }
        }
        illbits &= ~Q_MASK;
        peep &= ~P_CMPZ;
        break;
case J_LABEL:
        ldm_flush();
        flush_pending(0xff | (1 << R_SP));
        reg_flush();
        nspareregs = 0;
        setlabel((LabelNumber *)m);
        break;
case J_MULK:
        multiply_integer(r1r, r2r, m);
        peep &= ~P_CMPZ;
        break;
case J_ANDK:
        and_integer(r1r, r2r, m, peep);
        peep &= ~P_CMPZ;
        break;
case J_ORRK:
        rkop(F_OR);
        peep &= ~P_CMPZ;
        break;
case J_EORK:
        rkop(F_EOR);
        peep &= ~P_CMPZ;
        break;
#ifdef THUMB_INLINE_ASSEMBLER
case J_TSTK:
        load_integer(R_IP, m);
        outop(F_TST, 0, r2r, R_IP);
        break;
case J_TSTR:
        outop(F_TST, 0, r2r, mr);
        break;
case J_ADCR:
        rrop(F_ADC);
        break;
case J_SBCR:
        rrop(F_SBC);
        break;
#endif
case J_ADDR:
        if (r1r < 8 && r2r < 8 && mr < 8) {
            outop(F_ADD3R, r1r, r2r, mr);
        } else {
            if (r1r == mr)
                mr = r2r;
            else if (r1r != r2r)
                move_register(r1r, r2r);
            if (r1r >= 8) {
                if (mr >= 8)
                    outop(F_ADDHH, 0, r1r-8, mr-8);
                else
                    outop(F_ADDLH, 0, r1r-8, mr);
            } else {
                if (mr >= 8)
                    outop(F_ADDHL, 0, r1r, mr-8);
                else
                    outop(F_ADD3R, r1r, r1r, mr);
            }
        }
        peep &= ~P_CMPZ;
        break;
case J_SUBR:
        if (r2r == R_SP) {
            outop(F_MOVHL, 0, R_IP, R_SP-8);
            r2r = R_IP;
            if (mr == R_IP) syserr("J_SUBR: IP clash @ %.8lx", codebase+codep);
        } else if (mr == R_SP) {
            outop(F_MOVHL, 0, R_IP, R_SP-8);
            mr = R_IP;
        }
        outop(F_SUB3R, r1r, r2r, mr);
        peep &= ~P_CMPZ;
        break;
case J_ANDR:
        rrop(F_AND);
        peep &= ~P_CMPZ;
        break;
case J_ORRR:
        rrop(F_OR);
        peep &= ~P_CMPZ;
        break;
case J_EORR:
        rrop(F_EOR);
        peep &= ~P_CMPZ;
        break;
case J_MULR:
        rrop(F_MUL);
        peep &= ~P_CMPZ;
        break;
case J_BICR:
        rrop(F_BIC);
        peep &= ~P_CMPZ;
        break;


/* load/store                                                              */
case J_LDRBK:
        if (r2r == R_SP) {
            /* r1r clashes with IP if signed - checked later */
            if (m >= 0 && m <= (1020 + 31)) {
                n = (m > 1020) ? 1020 : (m & ~3);
                outop(F_ADDRSP, r1r, 0, n/4);
            } else {
                if (op & J_SIGNED) {
                    n = 0;
                    if (m >= 0) {
                        n = m & (0xff << 2);
                        if (m & 3)
                            n = (m > 1020) ? 1020 : (m & ~3);
                    }
                    outop(F_ADDRSP, r1r, 0, n/4);
                } else {
                    n = m & ~0x1f;
                    load_integer(r1r, n);
                    outop(F_ADDHL, 0, r1r, R_SP-8);
                }
            }
            m -= n;
            r2r = r1r;
        }
        if (op & J_SIGNED) {
            if (r2r == R_IP) syserr("J_LDRBK: IP clash @ %.8lx", codebase+codep);
            uses_IP = YES;
            load_integer(R_IP, m);
            outop(F_LDSBADDR, r2r, r1r, R_IP);
        } else {
            if ((n = bigindexbyte(r2r, m)) >= 0) {
                if (r2r == R_IP) syserr("J_LDRBK: IP clash @ %.8lx", codebase+codep);
                r2r = R_IP, m = n;
            }
            outop(F_LDRBI5, r2r, r1r, m);
        }
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        break;
case J_LDRBR:
        if (r2r == R_SP) {
            uses_IP = YES;
            if (mr == R_IP) syserr("J_LDRBR: IP clash @ %.8lx", codebase+codep);
            outop(F_MOVHL, 0, R_IP, R_SP-8);
            r2r = R_IP;
        }
        outop((op & J_SIGNED) ? F_LDSBADDR : F_LDRBADDR, r2r, r1r, mr);
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        break;
case J_LDRWK+J_ALIGN1:
        if (!BaseIsWordAligned(op, r2r, peep) || (m & 1) != 0) {
            int32 inc;
            int32 n;
            RealRegister r_ip = R_IP;

            if (r2r == R_SP) {
                if (m >= 0 && (m+3) <= (1020+31)) {
                    n = (m > 1020) ? 1020 : (m & ~0x0f);
                    outop(F_ADDRSP, R_IP, 0, n/4);
                    m = m-n;
                } else {
                    /* ECN: 0x0f here instead of 0x1f in case m & 3 */
                    load_integer(R_IP, m & ~0x0f);
                    outop(F_ADDHL, 0, R_IP, R_SP-8);
                    m = m & 0x0f;
                }
                r2r = R_IP;
            } else if (bigindexbyte(r2r, m+1) >= 0) {
                syserr("Unaligned LDRWK index too big (%ld) @ %.8lx", m, codebase+codep);
                m = 0;
            }
            if (r1r == R_IP)
                syserr("Unaligned LDRWK: IP clash @ %.8lx", codebase+codep);
            /* r2r may be IP */
            inc = 1;
            if (!target_lsbytefirst) inc = -1, m += 1;
            if (r1r == r2r) {
                outop(F_LDRBI5, r2r, r_ip, m+inc);
                outop(F_LDRBI5, r2r, r1r, m);
            } else {
                outop(F_LDRBI5, r2r, r1r, m);
                outop(F_LDRBI5, r2r, r_ip, m+inc);
            }
            outop(F_LSLK, r_ip, r_ip, 8);
            outop(F_OR, 0, r1r, r_ip);
            if (op & J_SIGNED) {
                outop(F_LSLK, r1r, r1r, 16);
                outop(F_ASRK, r1r, r1r, 16);
            }
            illbits &= ~(J_SIGNED|J_UNSIGNED);
            break;
        }
case J_LDRWK+J_ALIGN2:
        if (r2r == R_SP) {
            if (!(m & 1) && m >= 0 && m <= (1020 + 62)) {
                n = (m > 1020) ? 1020 : (m & ~3);
                outop(F_ADDRSP, r1r, 0, n/4);
            } else {
                if (op & J_SIGNED) {
                    n = 0;
                    if (m >= 0) {
                        n = m & (0xff << 2);
                        if (m & 3)
                            n = (m > 1020) ? 1020 : (m & ~3);
                    }
                    outop(F_ADDRSP, r1r, 0, n/4);
                } else {
                    n = m & ~(0x1f << 1);
                    load_integer(r1r, n);
                    outop(F_ADDHL, 0, r1r, R_SP-8);
                }
            }
            m -= n;
            r2r = r1r;
        }
        if (op & J_SIGNED) {
            if (r2r == R_IP) syserr("J_LDRWK: IP clash @ %.8lx", codebase+codep);
            uses_IP = YES;
            load_integer(R_IP, m);
            outop(F_LDSHADDR, r2r, r1r, R_IP);
        } else {
            if ((n = bigindexshort(r2r, m)) >= 0) {
                if (r2r == R_IP) syserr("J_LDRWK: IP clash @ %.8lx", codebase+codep);
                r2r = R_IP, m = n;
            }
            outop(F_LDRHI5, r2r, r1r, m >> 1);
        }
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        break;
case J_LDRWR+J_ALIGN2:
        if (r2r == R_SP) {
            uses_IP = YES;
            if (mr == R_IP) syserr("J_LDRWR: IP clash @ %.8lx", codebase+codep);
            outop(F_MOVHL, 0, R_IP, R_SP-8);
            r2r = R_IP;
        }
        outop((op & J_SIGNED) ? F_LDSHADDR : F_LDRHADDR, r2r, r1r, mr);
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        break;
case J_LDRK+J_ALIGN1:
case J_STRK+J_ALIGN1:
        if (!BaseIsWordAligned(op, r2r, peep) || (m & 3) != 0) {
            int32 inc;
            int32 n;
            RealRegister r_ip = R_IP;
            if (r2r == R_SP) {
                if (m >= 0 && (m+3) <= (1020+31)) {
                    n = (m > 1020) ? 1020 : (m & ~0x0f);
                    outop(F_ADDRSP, R_IP, 0, n/4);
                    m = m-n;
                } else {
                    /* ECN: 0x0f here instead of 0x1f in case m & 3 */
                    load_integer(R_IP, m & ~0x0f);
                    outop(F_ADDHL, 0, R_IP, R_SP-8);
                    m = m & 0x0f;
                }
                r2r = R_IP;
                if (op1 == J_STRK)
                    r_ip = R_A1+2;
            } else if (bigindexbyte(r2r, m+3) >= 0) {
                syserr("Unaligned LDRK/STRK index too big (%ld) @ %.8lx", m, codebase+codep);
                m = 0;
            }
            if (r1r == R_IP)
                syserr("Unaligned LDRK/STRK: IP clash @ %.8lx", codebase+codep);
            inc = 1;
            if (!target_lsbytefirst) inc = -1;
            if (op1 == J_STRK) {
                /* r1r and r2r clash with IP */
                uint32 value = 0x01020304;      /* unknown value - all bytes different */
                uint32 lastval;
                uint32 storebits = 0x01010101;
                int32 shift;
                RealRegister valreg = r1r;
                if (inc < 0) m += 3;
                if (value_is_constant(r1r))
                     value = reg_values[r1r].value;
                lastval = value & 255;              /* skip the first LSR */
                while (storebits != 0)
                {
                    for (shift = 0; shift < 32; shift += 8)
                        if (storebits & (1 << shift) &&
                            lastval == ((value >> shift) & 255)) break;
                    if (shift == 32)                /* didn't find the same value */
                    {
                        for (shift = 0; !(storebits & (1 << shift)); shift += 8)
                           continue;
                        lastval = (value >> shift) & 255;
                        outop(F_LSRK, r_ip, r1r, shift);
                        valreg = r_ip;
                    }
                    outop(F_STRBI5, r2r, valreg, m + inc * (shift >> 3));
                    storebits ^= 1 << shift;
                 }
            } else {
                RealRegister lo, hi;

                lo = r_ip, hi = r1r;
                if (r2r == r_ip) lo = r1r, hi = r_ip;
                if (BaseIsWordAligned(op, r2r, peep)) {
                    /* A3 not used. r2r may be IP, but r1r clashes with IP */
                    n = m & 3;
                    switch (n) {
                      case 1:
                        outop(F_LDRI5, r2r, lo, m >> 2);
                        outop(F_LDRBI5, r2r, hi, m + 3);
                        if (inc > 0)
                          outop(F_LSRK, lo, lo, 8);
                        break;
                      case 2:
                        outop(F_LDRHI5, r2r, lo, m >> 1);
                        outop(F_LDRHI5, r2r, hi, (m>>1)+1);
                        break;
                      case 3:
                        outop(F_LDRBI5, r2r, lo, m);
                        outop(F_LDRI5, r2r, hi, (m>>2)+1);
                        if (inc < 0)
                          outop(F_LSRK, hi, hi, 8);
                        break;
                    }
                    if (inc > 0)
                      outop(F_LSLK, hi, hi, (4-n)*8);
                    else
                      outop(F_LSLK, lo, lo, n * 8);
                    outop(F_OR, 0, r1r, r_ip);
                } else {
                    /* r1r clashes with IP and A3, r2r clashes with A3 (may be IP) */
                    if (inc < 0) m += 3;
                    if (r1r == r2r) {   /* now r2r <> IP! */
                        outop(F_LDRBI5, r2r, R_A3, m);
                        outop(F_LDRBI5, r2r, r_ip, m+inc);
                        outop(F_LSLK, r_ip, r_ip, 8);
                        outop(F_OR, 0, R_A3, r_ip);
                        outop(F_LDRBI5, r2r, r_ip, m+inc*2);
                        outop(F_LSLK, r_ip, r_ip, 16);
                        outop(F_OR, 0, R_A3, r_ip);
                        outop(F_LDRBI5, r2r, r1r, m+inc*3);
                        outop(F_LSLK, r1r, r1r, 24);
                        outop(F_OR, 0, r1r, R_A3);
                    } else {
                        outop(F_LDRBI5, r2r, r1r, m);
                        outop(F_LDRBI5, r2r, R_A3, m+inc);
                        outop(F_LSLK, R_A3, R_A3, 8);
                        outop(F_OR, 0, r1r, R_A3);
                        outop(F_LDRBI5, r2r, R_A3, m+inc*2);
                        outop(F_LSLK, R_A3, R_A3, 16);
                        outop(F_OR, 0, r1r, R_A3);
                        outop(F_LDRBI5, r2r, R_A3, m+inc*3);
                        outop(F_LSLK, R_A3, R_A3, 24);
                        outop(F_OR, 0, r1r, R_A3);
                    }
                }
            }
            uses_IP = YES;
            illbits &= ~(J_SIGNED|J_UNSIGNED);
            break;
        }
case J_LDRK+J_ALIGN4:
case J_STRK+J_ALIGN4:
        w = loads_r1(op) ? F_LDRI5 : F_STRI5;
        if (r2r == R_SP) {
            if (m < 0 || m > 1020 || (m & 3)) {
                if (r1r == R_IP && w == F_STRI5) syserr("J_STRK: IP clash @ %.8lx", codebase+codep);
                uses_IP = YES;
                if (!(m & 3) && m >= 0 && m <= (1020 + 124)) {
                    outop(F_ADDRSP, R_IP, 0, 1020/4);
                    outop(w, R_IP, r1r, (m - 1020) >> 2);
                } else {
                    load_integer(R_IP, m & ~(0x1f << 2));
                    outop(F_ADDHL, 0, R_IP, R_SP-8);
                    outop(w, R_IP, r1r, (m >> 2) & 0x1f);
                }
            } else {
                w = loads_r1(op) ? F_LDRSP : F_STRSP;
                outop(w, r1r, 0, m >> 2);
            }
        } else {
            if (m == 0 && !(w == F_LDRI5 && r1r == r2r)) {
                pending_op = w;
                pending_r2 = r2r;
                pending_r1 = r1r;
                saved_spareregs = spareregs;
                spareregs = nspareregs;
                return;
            } else {
                if ((n = bigindex(r2r, m)) >= 0) {
                    if (r2r == R_IP) syserr("J_LDRK/J_STRK: IP clash @ %.8lx", codebase+codep);
                    if (r1r == R_IP && w == F_STRI5) syserr("J_STRK: IP clash @ %.8lx", codebase+codep);
                    r2r = R_IP, m = n;
                }
                outop(w, r2r, r1r, m >> 2);
            }
        }
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        break;
case J_LDRR+J_ALIGN4:
case J_STRR+J_ALIGN4:
        w = loads_r1(op) ? F_LDRADDR : F_STRADDR;
        if (r2r == R_SP) {
            uses_IP = YES;
            if (mr == R_IP || (w == F_STRADDR && r1r == R_IP))
                syserr("J_LDRR/J_STRR: IP clash @ %.8lx", codebase+codep);
            outop(F_MOVHL, 0, R_IP, R_SP-8);
            r2r = R_IP;
        }
        outop(w, r2r, r1r, mr);
        illbits &= ~(J_SIGNED|J_UNSIGNED);
        break;
case J_STRBK:
        if (r2r == R_SP) {
            uses_IP = YES;
            if (r1r == R_IP) syserr("J_STRBK: IP clash @ %.8lx", codebase+codep);
            if (m >= 0 && m <= (1020 + 31)) {
                n = (m > 1020) ? 1020 : (m & ~3);
                outop(F_ADDRSP, R_IP, 0, n/4);
                outop(F_STRBI5, R_IP, r1r, m - n);
            } else {
                load_integer(R_IP, m & ~0x1f);
                outop(F_ADDHL, 0, R_IP, R_SP-8);
                outop(F_STRBI5, R_IP, r1r, m & 0x1f);
            }
        } else {
            if ((n = bigindexbyte(r2r, m)) >= 0) {
                if (r2r == R_IP || r1r == R_IP) syserr("J_STRBK: IP clash @ %.8lx", codebase+codep);
                r2r = R_IP, m = n;
            }
            outop(F_STRBI5, r2r, r1r, m);
        }
        break;
case J_STRBR:
        if (r2r == R_SP) {
            if (r1r == R_IP || mr == R_SP) syserr("J_STRBR: IP clash @ %.8lx", codebase+codep);
            uses_IP = YES;
            outop(F_MOVHL, 0, R_IP, R_SP-8);
            r2r = R_IP;
        }
        outop(F_STRBADDR, r2r, r1r, mr);
        break;
case J_STRWK+J_ALIGN1:
        if (!BaseIsWordAligned(op, r2r, peep) || (m & 1) != 0) {
            int32 inc;
            int32 n;
            RealRegister r_ip = R_IP;
            bool bytesequal = NO;
            if (value_is_constant(r1r)) {
                int32 value = reg_values[r1r].value;
                int32 b0 = value & 0xff,
                      b1 = (value >> 8) & 0xff;
                if (b0 == b1) bytesequal = YES;
                /* Expected to be useful really only for 0 / -1 */
            }

            if (r2r == R_SP) {
                if (m >= 0 && (m+3) <= (1020+31)) {
                    n = (m > 1020) ? 1020 : (m & ~0x0f);
                    outop(F_ADDRSP, R_IP, 0, n/4);
                    m = m-n;
                } else {
                    /* ECN: 0x0f here instead of 0x1f in case m & 3 */
                    load_integer(R_IP, m & ~0x0f);
                    outop(F_ADDHL, 0, R_IP, R_SP-8);
                    m = m & 0x0f;
                }
                r2r = R_IP;
                r_ip = R_A1+2;
            } else if (bigindexbyte(r2r, m+1) >= 0) {
                syserr("Unaligned STRWK index too big (%ld) @ %.8lx", m, codebase+codep);
                m = 0;
            }
            if (r1r == r_ip || r2r == r_ip)
                syserr("Unaligned STRWK: IP clash @ %.8lx", codebase+codep);
            inc = 1;
            if (!target_lsbytefirst) inc = -1, m += 1;
            outop(F_STRBI5, r2r, r1r, m);
            if (bytesequal)
                r_ip = r1r;
            else
                outop(F_LSRK, r_ip, r1r, 8);
            outop(F_STRBI5, r2r, r_ip, m+inc);
            uses_IP = YES;
            break;
        }
case J_STRWK+J_ALIGN2:
        if (r2r == R_SP) {
            uses_IP = YES;
            if (r1r == R_IP) syserr("J_STRWK: IP clash @ %.8lx", codebase+codep);
            if (!(m & 1) && m >= 0 && m <= (1020 + 62)) {
                n = (m > 1020) ? 1020 : (m & ~3);
                outop(F_ADDRSP, R_IP, 0, n/4);
                outop(F_STRHI5, R_IP, r1r, (m - n) >> 1);
            } else {
                load_integer(R_IP, m & ~(0x1f << 1));
                outop(F_ADDHL, 0, R_IP, R_SP-8);
                outop(F_STRHI5, R_IP, r1r, (m >> 1) & 0x1f);
            }
        } else {
            if ((n = bigindexshort(r2r, m)) >= 0) {
                if (r2r == R_IP || r1r == R_IP) syserr("J_STRWK: IP clash @ %.8lx", codebase+codep);
                r2r = R_IP, m = n;
            }
            outop(F_STRHI5, r2r, r1r, m >> 1);
        }
        break;
case J_STRWR+J_ALIGN2:
        if (r2r == R_SP) {
            uses_IP = YES;
            if (r1r == R_IP || mr == R_IP) syserr("J_STRWR: IP clash @ %.8lx", codebase+codep);
            outop(F_MOVHL, 0, R_IP, R_SP-8);
            r2r = R_IP;
        }
        outop(F_STRHADDR, r2r, r1r, mr);
        break;
#ifdef THUMB_INLINE_ASSEMBLER
case J_LDMW:
    if (r1r == R_SP)
    {   if (m & 0x8000) m ^= 0x8100;
        outop(F_POP, 0, 0, m);
    }
    else
        outop(F_LDM, r1r, 0, m);
    break;
case J_STMW:
    if (r1r == R_SP)
    {   if (m & 0x4000) m ^= 0x4100;
        outop(F_PUSH, 0, 0, m);
    }
    else
        outop(F_STM, r1r, 0, m);
    break;
case J_SWI:
    outop(F_SWI, 0, 0, r1);
    break;
case J_BL:
    call_k(bindsym_((Binder *) r1));
    break;
case J_NULLOP:
    outop(F_MOVHH, 0, 0, 0);
    break;
#endif
case J_ENDPROC: {
          bool branches_left = fref_branches != 0;
          int32 old_codep = codep;
          int32 new_codep;
          if (branches_left || (!lab_isset_(returnlab) && return_pending))
              conditional_branch_to(Q_AL, RETLAB, 0);
          new_codep = codep;
          codep = old_codep;
          while (fref_branches)
              setlabel(fref_branches->real_dest);
          codep = new_codep;
          available_branches = NULL;
          return_pending = 0;
          deadcode = 0;
          literal_pool_start = codebase+codep;
          dumplits2(0);
#ifdef THUMB_CPLUSPLUS
          cnop();
#else
          if (codep & 1) outDCB(0);
#endif
          fpdesc_endproc();
/* ECN: Many Thumb jopcodes will modify registers which cg does not know about
 *      Therefore we must mark R0-R3 as being used.
 * HCM: this is a weak argument. Thumb/gen can augment regmask in a more exact
 *      way.
 */
          regmask |= 0x0f;
        }
        break;

case J_ENTER:
        if (m < 0) syserr("emit(J_ENTER %ld)", m);
        returnlab = nextlabel();
        entrylab = nextlabel();
        routine_entry(m);
        break;

case J_STACK:
        fpdesc_newsp(m);
        fp_minus_sp = m;
        break;

case J_PUSHM:
        if (m != 0) outop(F_PUSH, 0, 0, m);
        break;

case J_USE:
case J_VSTORE:
        ldm_flush();
        break;

case J_CLRC+J_ALIGN4:
case J_MOVC+J_ALIGN4: {
          int32 regs;
          bool useloop;
          bool ismove;
          int32 i, n;
          int32 count, rcount;
          LabelNumber *l;

          ismove = op1 == J_MOVC;
          regs = movc_workregs(p) | spareregs;
          if (ismove) regs &= ~regbit(r2);
          count = m;
          useloop = count > MOVC_LOOP_THRESHOLD;
          rcount = 4 * bitcount(regs);

#if 0
          printf("%s %d, %d, %d, @ %.8x\n", ismove ? "J_MOVC" : "J_CLRC", r1, r2, m, codebase+codep);
#endif
          nspareregs |= regbit(r1);
          if (ismove) nspareregs |= regbit(r2);
          if (useloop) {
            if ((ismove && count <= 3*rcount) || (count <= 4*rcount))
              useloop = NO;
            else
              rcount -= 4, regs &= ~regbit(R_IP);
          }
          {   /* Remove unneeded registers if the register count either
                 exeeds ldm_regs_max or rcount.
               */
                int i, num_instr;
                if (count < 4 * ldm_regs_max)
                    i = rcount - count;
                else
                    i = rcount - 4 * ldm_regs_max;
                if (i > 0)
                {   rcount -= i;
                    for (; i > 0; i -= 4)
                        regs ^= (regs & -regs);
                }
                regmask |= regs;
                /* Count the number of instructions required to be sure we dump the
                   literal pool before it overflows.
                   MOVC: 6 instructions for no loop max, loop max: 6 + load_integer.
                   CLRC: 3 + rcount instructions for no loop, with loop max:
                   4 + load_integer + rcount. Assume 4 for load_integer max.
                   But... we must also take any pending instructions into account,
                   and any instructions in the ldm peepholer. Since there is a safety
                   margin of 12 instructions, we don't care...
                */
                num_instr = ismove ? 10 : rcount + 8;
                if (codep+2*num_instr >= mustlitby - branchpoolsize)
                    dumplits(1);
                if (codep+2*num_instr >= mustbranchlitby)
                    dump_branch_lits(1, num_instr*2);
          }

          if (!ismove) {
            for (i = 0; i <= 7; i++)
              if (regs & regbit(i)) load_integer(i, 0);
          }
          if (!useloop) {
            while (count > rcount) {
              if (ismove && count == rcount+4 && (deadbits & J_DEAD_R2) && !(peep & P_POST)) {
                rcount += 4;
                regs |= regbit(r2);
              }
              if (ismove) outop(F_LDM, r2, 0, regs);
              outop(F_STM, r1, 0, regs);
              count -= rcount;
            }
          } else {
            l = nextlabel();
            n = count / rcount;
            count = count % rcount;
            load_integer(R_IP, n);
            ldm_flush();
            flush_pending(0xff | (1 << R_SP));
            reg_flush();
            setlabel(l);
            if (ismove) outop(F_LDM, r2, 0, regs);
            outop(F_STM, r1, 0, regs);
            add_integer(R_IP, R_IP, -1);
            conditional_branch_to(Q_NE, l, 0);
          }
          if (count > 0) {
            for (i = rcount-count; i != 0; i -= 4)
              regs ^= (regs & -regs);
            if (ismove) outop(F_LDM, r2, 0, regs);
            outop(F_STM, r1, 0, regs);
          }
          if (reg_values[r1].typ == REGV_BASE) reg_values[r1].value += m;
          if (ismove && reg_values[r2].typ == REGV_BASE) reg_values[r2].value += m;
        }
        break;

case J_TYPECASE:
        ldm_flush();
        break;

default:
        syserr("show_inst_direct(%#lx)", (long)op);
        outop(0, 0, 0, 0);           /* placeholder */
    }
    /* Check we've tidied up correctly */
    if ((peep & ~P_BASEALIGNED) | illbits)
      syserr("show_inst_direct: peep = %lx illbits = %lx", (long)peep, (long)illbits);
    /* ECN: If P_CMPZ and the result is not used we must ensure the
     *      opcode is actually emitted.
     */
    if ((p->peep & P_CMPZ) && a_uses_r1(p) && (deadbits & J_DEAD_R1))
        flush_pending(1 << r1);
windup:
    spareregs = nspareregs;
    if (spareregs & pending_regs) pending_regs &= ~spareregs;
}

void show_instruction(const Icode *const ic)
{
    J_OPCODE op = ic->op;
    VRegInt r1 = ic->r1;
    VRegInt r2 = ic->r2;
    VRegInt m = ic->r3;

        int32 dataflow = op & J_DEADBITS;
        static int32 cond = Q_AL;
        int32 newcond = 1;
        op &= ~J_DEADBITS;                  /* remove dataflow bits         */
        /* While code is still in flux, we assume all STRW's coming here have   */
        /* J_ALIGN4&J_ALIGNWR set...                                            */
        /* apparently, they don't have ALIGNWR...                               */
        {
                int32 op1 = op & (J_TABLE_BITS | J_ALIGNMENT);
                if (op1 == J_STRWK+J_ALIGN4 || op1 == J_STRWR+J_ALIGN4)
                        op = op - J_STRWK + J_STRK;
        }
        switch (op) {
        case J_SETSP:
                {
                        int32 oldstack = r2.i, newstack = m.i;
                        int32 diff = newstack - oldstack;
                        if (fp_minus_sp != oldstack)
                                syserr(syserr_setsp_confused,
                                    (long)fp_minus_sp, (long)oldstack, (long)newstack);
                        fp_minus_sp = newstack;
                        op = J_ADDK;
                        r1.rr = R_SP;
                        r2.rr = R_SP;
                        m.i = -diff;
                        dataflow = J_DEAD_R2;
                }
                break;
        case J_PUSHM:
                fp_minus_sp += (4 * bitcount(m.i));
                break;

        case J_SUBK:
            if (m.i != 0)
            {
                op = J_ADDK;
                m.i = -m.i;
            }
            break;
#ifdef THUMB_INLINE_ASSEMBLER
        case J_CMNK:
            if (m.i != 0)
            {
                op = J_CMPK;
                m.i = -m.i;
            }
            break;
        case J_BICK:
            op = J_ANDK;
            m.i = ~m.i;
            break;

#endif
        case J_SHLK+J_SIGNED:
        case J_SHLK+J_UNSIGNED:
                m.i &= 255;
                if (m.i >= 32) {
                        op = J_MOVK;
                        dataflow &= ~J_DEAD_R2;
                        m.i = 0;
                }
                break;
        case J_SHRK+J_UNSIGNED:
                m.i &= 255;
                if (m.i > 32) {             /* LSR #32 allowed */
                        op = J_MOVK;
                        dataflow &= ~J_DEAD_R2;
                        m.i = 0;
                }
                else if (m.i == 0)
                {
                    op = J_MOVR;
                    m = r2;
                    r2.rr = GAP;
                    if (dataflow & J_DEAD_R2)
                        dataflow ^= J_DEAD_R2+J_DEAD_R3;
                }
                break;
        case J_SHRK+J_SIGNED:
                m.i &= 255;
                if (m.i >= 32) m.i = 32;    /* ASR #32 allowed */
                else if (m.i == 0)
                {
                    op = J_MOVR;
                    m = r2;
                    r2.rr = GAP;
                    if (dataflow & J_DEAD_R2)
                        dataflow ^= J_DEAD_R2+J_DEAD_R3;
                }
                break;
        }
        {
                bool flush = NO;
                switch (op & ~Q_MASK) {
                case J_ENTER:
                case J_ENDPROC:
                case J_LABEL:
                        newcond = Q_AL;
                        flush = YES;
                        break;
                case J_STACK:
                case J_INFOLINE:
                case J_INFOBODY:
                case J_INFOSCOPE:
                case J_OPSYSK:
                case J_CALLK:
                case J_CALLR:
                case J_CASEBRANCH:
                case J_BXX:
                case J_B:
                case J_WORD:
                case J_USE:
                case J_VOLATILE:
                        flush = YES;
                        break;
                case J_PUSHD:
                case J_PUSHF:
                case J_ORG:
                case J_CONDEXEC:
                        /* Things the ARM peepholer handles but we don't */
                        syserr("show_instruction(%#lx)", (long)op);
                        break;

                }
                {
                        PendingOp cur;

                        if ((op & J_BASEALIGN4) && !j_is_adcon(op)) {
                            cur.ic.op = op & ~J_BASEALIGN4;
                            cur.peep = (op & J_ALIGNMENT) < J_ALIGN4 ? P_BASEALIGNED : 0;
                        } else {
                            cur.ic.op = op & ~J_BASEALIGN4;
                            cur.peep = 0;
                        }
                        cur.ic.r1 = r1;
                        cur.ic.r2 = r2;
                        cur.ic.r3 = m;
                        cur.ic.r4.rr = 0;
                        cur.dataflow = dataflow;
                        cur.cond = cond;
                        peephole_op(&cur, flush);
                        if (flush) ldm_flush();
                        if (newcond != 1) cond = newcond;
                }

        }
}

void branch_round_literals(LabelNumber *m)
{
    conditional_branch_to(Q_AL, (LabelNumber *)m, 0);
}

void mcdep_init()
{
    char cv_name[16];
    int i;

    codebuf_reinit2();        /* this should be in driver.c? */
    avoidallocating(R_LR);    /* not directly accessible on this machine */
    casebranch_pending = -1;
    mustlitby = 0x10000000;
    mustbranchlitby = 0x10000000;
    backwards_branches = 0;
    current_procnum = 0;
    adconpool_init();
    peephole_init();
    for (i = 0; i < 8; i++) {
        sprintf(cv_name, "__call_via_r%d", i);
        call_via[i] = sym_insert_id(cv_name);
    }
    fpdesc_init();
    t_sym = sym_insert_id("$T");
    label_values = NULL;
    label_references = NULL;
}

/* AM: the following two interface routines are temporarily needed.     */
void localcg_reinit()
{
  casebranch_pending = -1;
  deadcode = 0;
  mustlitby = 0x10000000;
  mustbranchlitby = 0x10000000;
  backwards_branches = 0;
  peephole_reinit();
  fpdesc_init();
}

void localcg_tidy()
{
  dbg_finalise();
  peephole_tidy();
}

void localcg_newliteralpool(void)
{
    if (in_code) {
        literal_pool_start = codebase+codep;
        in_code = 0;
    }
    mustlitby = 0x10000000;
    mustbranchlitby = 0x10000000;
}

void localcg_endcode(void)
{
    describe_literal_pool();
}

/* End of section thumb/gen.c */

