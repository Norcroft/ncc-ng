/*
 * C compiler file mcdpriv.h
 * (Private interfaces within machine-dependent back end).
 * Copyright (C) Acorn Computers Ltd., 1988
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#ifndef __mcdpriv_h
#define __mcdpriv_h 1

#include "mcdep.h"
#ifndef JOPCODEDEF_ONLY
#include "codebuf.h"
#endif

#define P_RET               1
#define P_CMPZ              2  /* update PSR flags NZC, not V */
#define P_PRE               4  /* Used for pre-auto-index                  */
#define P_POST              8  /* Used for post-auto-index                 */
#define P_LSL            0x10
#define P_ASR            0x20  /* Used to generate register-controlled shifts */
#define P_LSR            0x30
#define P_ROR            0x40
#define P_RSHIFT  (P_LSL | P_ASR | P_LSR | P_ROR)
#define SCC_of_PEEP(peep) ((peep) & (P_CMPZ|P_SETCC) ? \
        ((peep) & P_SETPSR ? F_SCC | F_RD(15) : F_SCC):0)  /* change bit no.? */

#define P_BASEALIGNED   0x800
#define P_MS           0x1000
#define P_ADJUSTSP     0x2000

/* These two are used internally to the peepholer to mark a change of      */
/* condition for a comparison and its associated branch / condexec         */
#define P_UNSIGNEDCOND 0x4000  /* signed changed to unsigned */
#define P_SWAPCOND     0x8000  /* operands swapped           */
#define P_SWAPPEDOPS  0x10000
#define P_ZONLY       0x20000  /* Z-flag only needed (in conjunction with P_CMPZ) */
#define P_SETCC       0x40000  /* update PSR flags NZCV */
#define P_SETPSR      0x80000  /* update all PSR flags, including processor mode */
#define P_TRANS      0x100000  /* Translate user mode option - LDRT/STRT */

#define _a_read_r1      0x1
#define _a_read_r2      0x2
#define _a_read_r3      0x4
#define _a_read_r4      0x8
#define _a_set_r1      0x10
#define _a_set_r2      0x20
#define _a_modify_mem  0x40
#define _a_call        0x80
#define _a_regmask_r1 0x100
#define _a_regmask_r3 0x200
#define _a_gap_r1     0x400
#define _a_gap_r2     0x800
#define _a_read_mem  0x1000
#define _a_uses_stack 0x2000
extern struct JopTable a_joptable[];

#ifdef DEFINE_A_JOPTABLE
#  if defined ENABLE_CG || defined ENABLE_REGS || defined ENABLE_CSE
#    define a_with_bits(n, b) {n, b},
#  else
#    define a_with_bits(n, b) { b },
#  endif
   struct JopTable a_joptable[] = {
#else
#  define a_with_bits(n, b)
#endif

#define a_attributes(op) (a_joptable[(op-J_LAST_JOPCODE-1) & J_TABLE_BITS].bits)

#define J_POPMB (J_LAST_JOPCODE+1L)
        a_with_bits("POPMB", _a_gap_r1+_a_read_r2+_a_regmask_r3+_a_read_mem)

#define J_PUSHC (J_LAST_JOPCODE+2L)
        a_with_bits("PUSHC", _a_read_r1+_a_read_r2+_a_set_r1+_a_modify_mem)

#define J_CALLI (J_LAST_JOPCODE+3L)
        a_with_bits("CALLI", _a_read_r4+_a_set_r1+_a_call)

#define J_CALLIR (J_LAST_JOPCODE+4L)
        a_with_bits("CALLIR", _a_read_r4+_a_read_r3+_a_set_r1+_a_call)

#define J_TAILCALLI (J_LAST_JOPCODE+5L)
        a_with_bits("TAILCALLI", _a_read_r4+_a_set_r1+_a_call)

#define J_TAILCALLIR (J_LAST_JOPCODE+6L)
        a_with_bits("TAILCALLIR", _a_read_r4+_a_read_r3+_a_set_r1+_a_call)

#define J_CALLX (J_LAST_JOPCODE+7L)
        a_with_bits("CALLX", _a_read_r4+_a_set_r1+_a_call)

#define J_CALLXR (J_LAST_JOPCODE+8L)
        a_with_bits("CALLXR", _a_read_r4+_a_read_r3+_a_set_r1+_a_call)

#define J_TAILCALLX (J_LAST_JOPCODE+9L)
        a_with_bits("TAILCALLX", _a_read_r4+_a_set_r1+_a_call)

#define J_TAILCALLXR (J_LAST_JOPCODE+10L)
        a_with_bits("TAILCALLXR", _a_read_r4+_a_read_r3+_a_set_r1+_a_call)

#define J_MOVDIM (J_LAST_JOPCODE+11L)
        a_with_bits("MOVDIM", _a_regmask_r1+_a_gap_r2+_a_regmask_r3)

#define J_MOVIDM (J_LAST_JOPCODE+12L)
        a_with_bits("MOVIDM", _a_regmask_r1+_a_gap_r2+_a_regmask_r3)

#define J_ADCK   (J_LAST_JOPCODE+13L)
        a_with_bits("ADCK", _a_read_r2+_a_set_r1)
#define J_ADCR   (J_LAST_JOPCODE+14L)
        a_with_bits("ADCR", _a_read_r2+_a_read_r3+_a_set_r1)
#define J_SBCK   (J_LAST_JOPCODE+15L)
        a_with_bits("SBCK", _a_read_r2+_a_set_r1)
#define J_SBCR   (J_LAST_JOPCODE+16L)
        a_with_bits("SBCR", _a_read_r2+_a_read_r3+_a_set_r1)
#define J_RSCK   (J_LAST_JOPCODE+17L)
        a_with_bits("RSCK", _a_read_r2+_a_set_r1)
#define J_RSCR   (J_LAST_JOPCODE+18L)
        a_with_bits("RSCR", _a_read_r2+_a_read_r3+_a_set_r1)
#define J_TSTK   (J_LAST_JOPCODE+19L)
        a_with_bits("TSTK", _a_read_r2)
#define J_TSTR   (J_LAST_JOPCODE+20L)
        a_with_bits("TSTR", _a_read_r2+_a_read_r3)
#define J_TEQK   (J_LAST_JOPCODE+21L)
        a_with_bits("TEQK", _a_read_r2)
#define J_TEQR   (J_LAST_JOPCODE+22L)
        a_with_bits("TEQR", _a_read_r2+_a_read_r3)
#define J_BICK   (J_LAST_JOPCODE+23L)
        a_with_bits("BICK", _a_read_r2+_a_set_r1)
#define J_BICR   (J_LAST_JOPCODE+24L)
        a_with_bits("BICR", _a_read_r2+_a_read_r3+_a_set_r1)
#define J_CMNK   (J_LAST_JOPCODE+25L)
        a_with_bits("CMNK", _a_read_r2)
#define J_CMNR   (J_LAST_JOPCODE+26L)
        a_with_bits("CMNR", _a_read_r2+_a_read_r3)
#define J_MVNK   (J_LAST_JOPCODE+27L)
        a_with_bits("MVNK", _a_read_r2)
#define J_MVNR   (J_LAST_JOPCODE+28L)
        a_with_bits("MVNR", _a_read_r2+_a_read_r3)


#define J_LAST_A_JOPCODE J_MVNR

#ifdef DEFINE_A_JOPTABLE
    0
};
#endif

#ifndef JOPCODEDEF_ONLY

typedef struct {    /* like struct Icode but with RealReg's and a peep field */
  Icode ic;
  int32 peep;       /* opcode extension */
  int32 dataflow;
  int32 cond;
} PendingOp;

void a_pr_jopcode(PendingOp *p);

#define localcg_debug(n) (debugging(DEBUG_LOCALCG) && (localcg_debugcount & (n)))

extern char frameregnames[(16-9)*2];
                             /* register number -> name for sb (or v6), ip, fp, sl, sp
                              * (variable because dependent on calling standard
                              * in force).  Also does lr and pc for simplicity.
                              */

extern void setcallingstandard(char);
                             /* One of 'A', 'R', 'U', 'M', default set by compiler
                              * build, value alterable by configuration option.
                              */

extern int32 pcs_flags;

/* Beware: these values are also written in the config tool */
#define PCS_CALLCHANGESPSR  1
#define PCS_FPE3            2
#define PCS_NOSTACKCHECK    4
#define PCS_REENTRANT       8
#define PCS_FPREGARGS       16 /* never in pcs_flags, only a pcs config value */
                               /* but mustn't overlap with pcs_flags bits     */
#define PCS_NOFP            32
#define PCS_SOFTFP          64
#define PCS_INTERWORK       128
#define PCS_ACCESS_CONSTDATA_WITH_ADR 256

#define PCS_ZH_MASK         0x7f  /* options passed from driver via -zh argument */
                                  /* excludes access_constdata_with_adr          */

#ifndef PCS_DEFAULTS
#  define PCS_DEFAULTS 0
#endif

#define NONLEAF (PROC_ARGPUSH | PROC_ARGADDR | PROC_BIGSTACK | BLKCALL)
/* STACKCHECK (NONLEAF subset) defines when stack check is REALLY needed */
#define STACKCHECK (PROC_BIGSTACK | BLKCALL)

#define MOVC_LOOP_THRESHOLD 24

extern int32 a_loads_r1(PendingOp const* const p);
extern int32 a_uses_r1(PendingOp const* const p);
extern int32 a_reads_r1(PendingOp const* const p);
extern int32 a_loads_r2(PendingOp const* const p);
extern int32 a_uses_r2(PendingOp const* const p);
extern int32 a_reads_r2(PendingOp const* const p);
extern int32 a_uses_r3(PendingOp const* const p);
extern int32 a_uses_r4(PendingOp const* const p);
extern int32 a_uses_mem(PendingOp const* const p);
extern int32 a_modifies_mem(PendingOp const* const p);
extern int32 a_uses_stack(PendingOp const* const p);

extern bool a_corrupts_r1(PendingOp const* p);
extern bool a_corrupts_r2(PendingOp const* p);

typedef struct
{
    uint32 use, def, corrupt, dead;
}   RegisterUsage;

#define regs_in(u)      ((u)->use)
#define regs_out(u)     ((u)->def)
#define regs_corrupt(u) ((u)->corrupt)
#define regs_dead(u)    ((u)->dead)

#define regs_read(u)    ((u)->use)
#define regs_written(u) ((u)->def | (u)->corrupt)
#define regs_free(u)    ((u)->corrupt | (u)->dead)
#define regs_used(u)    ((u)->use | (u)->def | (u)->corrupt)

/* returns the complete register usage of c */
extern bool GetRegisterUsage(const PendingOp *c, RegisterUsage *u);

extern char *CheckJopcodeP(const PendingOp *p, CheckJopcode_flags flags);

extern int32 power_of_two(int32 n);
extern int32 regofregbit(int32 m);

extern bool MultiplyNeedsWorkreg(int32 n);
extern uint32 movc_workregs(PendingOp const *p);
extern bool movc_preserving_r1r2(PendingOp const *p, bool dead_r2);

extern void show_inst_direct(PendingOp *p);

extern void peephole_op(PendingOp *p, bool flush);

extern void peephole_reinit(void);
extern void peephole_init(void);
extern void peephole_tidy(void);

#ifdef TARGET_HAS_AOF

#define  aof_fpreg   xr_objflg1     /* fn passes FP args in FP registers */
#define  aof_usessb  xr_objflg2     /* defined fn 'uses' sb */
#define  aof_leaf    xr_objflg3     /* defined fn is a leaf */

typedef struct CommonDef {
    struct CommonDef *next;
    DataDesc data;
    Symstr *name;
    int index;
    int32 refsize;
    int32 stringpos;
} CommonDef;

extern CommonDef *commondefs;

extern Symstr *data_sym, *bss_sym, *adcon_sym;

#else

#define  aof_fpreg   0                      /* fn passes FP args in FP registers */
#define  aof_usessb  0                      /* defined fn 'uses' sb */
#define  aof_leaf    0                      /* defined fn is a leaf */

#endif

extern DataDesc adconpool;
extern Symstr *adconpool_lab;

extern int adconpool_find(int32 w, int32 flavour, Symstr *sym);
extern void adconpool_flush(void);
extern void adconpool_init(void);

extern unsigned integer_load_max;
extern unsigned ldm_regs_max;

#define PROCESSOR_HAS_HALFWORDS         1
#define PROCESSOR_HAS_MULTIPLY          2  /* 32x32 => 64 */
#define PROCESSOR_HAS_26BIT_MODE        4
#define PROCESSOR_HAS_32BIT_MODE        8
#define PROCESSOR_HAS_THUMB            16

typedef struct
{   char name[16]; Uint flags; char arch[4];
    char mulbits, multime, mlatime;
} Processor;
Processor const *LookupProcessor(char const *name);
Processor const *LookupArchitecture(char const *name);

typedef int ProcessorEnumProc(void *, Processor const *);

int EnumerateProcessors(ProcessorEnumProc *f, void *arg);

void target_lib_variant(char *b);

typedef enum { fpu_fpa, fpu_amp } FPU_Type;
extern FPU_Type fpu_type;

#endif /* JOPCODEDEF_ONLY */

#endif

/* end of arm/mcdpriv.h */
