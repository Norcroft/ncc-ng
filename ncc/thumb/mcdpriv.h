/*
 * C compiler file mcdpriv.h,  version 1
 * (Private interfaces within machine-dependent back end).
 * Copyright (C) Acorn Computers Ltd., 1988, Codemist Ltd 1994
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

#define P_RET      1
#define P_CMPZ             2
#define P_PRE      4      /* Used for pre-auto-index                  */
#define P_POST             8      /* Used for post-auto-index                 */
/* $$$$$ things definitely inapplicable to thumb removed */
#define P_BASEALIGNED 0x800

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

#ifndef THUMB_INLINE_ASSEMBLER

#define J_BICR          (J_LAST_JOPCODE+1L)
        a_with_bits("BICR", _a_read_r3+_a_read_r2+_a_set_r1)

#define J_LAST_A_JOPCODE J_BICR

#else

#define J_LAST_A_JOPCODE J_LAST_JOPCODE

#endif


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

extern bool gen_pass;

extern int32 current_procnum;
extern List3 *label_values, *label_references;

void a_pr_jopcode(PendingOp *p);

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

#define PCS_ZH_MASK         0xff  /* options passed from driver via -zh argument */
                                  /* excludes access_constdata_with_adr          */

#ifndef PCS_DEFAULTS
#  define PCS_DEFAULTS 0
#endif

#define localcg_debug(n) (debugging(DEBUG_LOCALCG) && (localcg_debugcount & (n)))

#define NONLEAF (PROC_ARGPUSH | PROC_ARGADDR | PROC_BIGSTACK | BLKCALL)
/* STACKCHECK (NONLEAF subset) defines when stack check is REALLY needed */
#define STACKCHECK (PROC_BIGSTACK | BLKCALL)

#define MOVC_LOOP_THRESHOLD 24
extern int32 movc_workregs(const PendingOp *const p);
extern bool movc_preserving_r1r2(PendingOp *p, bool dead_r2);

extern int32 a_loads_r1(const PendingOp * const p);
extern int32 a_uses_r1(const PendingOp * const p);
extern int32 a_reads_r1(const PendingOp * const p);
extern int32 a_loads_r2(const PendingOp * const p);
extern int32 a_uses_r2(const PendingOp * const p);
extern int32 a_reads_r2(const PendingOp * const p);
extern int32 a_uses_r3(const PendingOp * const p);
extern int32 a_uses_r4(const PendingOp * const p);
extern int32 a_modifies_mem(const PendingOp * const p);
extern int32 a_uses_mem(const PendingOp * const p);

extern bool a_corrupts_r1(PendingOp const* p);
extern bool a_corrupts_r2(PendingOp const* p);

extern bool setspsr(const Icode * const ic);

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

extern void show_inst_direct(PendingOp *p);

extern void peephole_op(PendingOp *p, bool flush);

extern void peephole_reinit(void);
extern void peephole_init(void);
extern void peephole_tidy(void);

#ifdef TARGET_HAS_AOF

#define  aof_fpreg   xr_objflg1     /* fn passes FP args in FP registers */
#define  aof_usessb  xr_objflg2     /* defined fn 'uses' sb */
#define  aof_leaf    xr_objflg3     /* defined fn is a leaf */

extern Symstr *data_sym, *bss_sym, *adcon_sym;

typedef struct CommonDef {
    struct CommonDef *next;
    DataDesc data;
    Symstr *name;
    int index;
    int32 refsize;
    int32 stringpos;
} CommonDef;

extern CommonDef *commondefs;

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

void localcg_endcode(void);

extern int integer_load_max;
extern int ldm_regs_max;

void target_lib_variant(char *b);

#endif /* JOPCODEDEDEF_ONLY */

#endif

/* end of thumb/mcdpriv.h */
