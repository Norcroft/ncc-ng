/*
 * C compiler file mip/flowgraf.c
 * Copyright (C) Codemist Ltd., 1988.
 * Copyright (C) Acorn Computers Ltd., 1988.
 * Copyright (C) Advanced Risc Machines Ltd., 1991
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$ Codemist 74
 * Checkin $Date$
 * Revising $Author$
 */

/* AM hack in progress: fixup J_CMP to have the condition code which      */
/* matches the J_B which follows.                                         */
/* Moreover, this can now remove CMP's at end of basic blocks which       */
/* have been make redundant by cross-jumping.                             */

/* Memo: it may be that tail-recursion optimisation should be done AFTER  */
/* cross_jumping.  This would allow common tails to be zipped.  However   */
/* it could lead to branches to branches if the tailcall expanded to just */
/* one branch instruction.                                                */
/* Memo: move SETSP amalgamation here from armgen.c etc.                  */

#ifdef __STDC__
#include <string.h>
#else
#include <strings.h>
#include <stddef.h>
#endif

#include "globals.h"
#include "flowgraf.h"
#include "store.h"
#include "cg.h"
#include "codebuf.h"
#include "regalloc.h"
#include "regsets.h"
#include "aeops.h"
#include "util.h"
#include "jopcode.h"
#include "mcdep.h"
#include "builtin.h"
#include "simplify.h"   /* for mcrep fields/macros */
#include "xrefs.h"      /* for xr_code/data */
#include "errors.h"
#include "sr.h"
#include "inline.h"     /* Inline_RealUse */
#include "sem.h"

/* AM Sep 88: Use obj_symref before J_ADCON (may kill J_FNCON on day)    */
/* WGD  8- 3-88 Deadflag allowed for in expand_jop_macros */
/* WGD 26- 2-88 J_USEx passed to xxxgen as peepholer must also handle */
/*              volatiles carefully */
/* WGD 15- 2-88 Corrected treatement of deadflags for pseudo_reads_rx ops */
/* WGD 19-10-87 Tailcall conversion blocked for assembler_call */
/* WGD 16-10-87 J_FNCON now passes static/extern flag in r2 */
                /*@@@ AM:this shows that xr_xxx are not quite enough.    */
/* AM 26-may-87: redo CASEBRANCH tables                                  */

/* AM has changed RETURN so that it passes the xxxgen.c file a
   (possibly conditional) branch to RETLAB.  This works nicely.
   However, we now have 5 special labels - RETLAB, RetIntLab, RetVoidLab,
   RetFltLab, NOTALAB.  The last is notionally NULL, but changed for
   testing.  Tidy sometime?
*/

/* The peepholer now effects the ARM elision of J_SETSP before RETURN.      */
/* This means that remove_noops() & branch_chain() are not perfect. Think.  */

/* @@@ The following lines are in flux:  we need an environment of          */
/* *user-declared* vars for debug info.  This probably can be amalgamated   */
/* with blkstack_ (discuss).  There are some importance differences.        */

struct CGState cgstate;

#ifndef TARGET_IS_NULL

static BindListList *current_env2;

/* procedural interface to machine dependent code generator is via: */
/* show_instruction(), local_base(), local_address(), plus ...      */
static void show_inst(Icode *ic)
{
    if (uses_r1(ic->op))
    {   RealRegister r1r = register_number(ic->r1.r);
        if ((uint32)r1r >= (uint32)NMAGICREGS) syserr(syserr_r1r, (long)r1r);
        ic->r1.rr = r1r;
    }
    if (uses_r2(ic->op))
    {   RealRegister r2r = register_number(ic->r2.r);
        if ((uint32)r2r >= (uint32)NMAGICREGS) syserr(syserr_r2r, (long)r2r);
        ic->r2.rr = r2r;
    }
    if (uses_r3(ic->op))
    {   RealRegister r3r = register_number(ic->r3.r);
        if ((uint32)r3r >= (uint32)NMAGICREGS) syserr(syserr_r3r, (long)r3r);
        ic->r3.rr = r3r;
    }
    if (uses_r4(ic->op))
    {   RealRegister r4r = register_number(ic->r4.r);
        if ((uint32)r4r >= (uint32)NMAGICREGS) syserr(syserr_r4r, (long)r4r);
        ic->r4.rr = r4r;
    }
#ifdef TARGET_HAS_2ADDRESS_CODE
    if (jop_asymdiadr_(ic->op) && two_address_code(ic->op))
    {   /* code in regalloc has ensured that r1 & r3 clash if r1 != r2 */
        if (ic->r1.rr != ic->r2.rr && ic->r1.rr == ic->r3.rr) syserr(syserr_expand_jop);
    }
    /* Maybe turn all 3-address codes to 2-address + MOVR here, but    */
    /* think more w.r.t use of load-address target opcodes.            */
#endif
    show_instruction(ic);
}

static void show_mem_inst1(J_OPCODE op, VRegnum r1, Binder *b, int32 k)
{
    Icode ic;
    INIT_IC (ic, op);

    if (uses_r1(op))
    {   RealRegister r1r = register_number(r1);
        if ((uint32)r1r >= (uint32)NMAGICREGS) syserr(syserr_r1r, (long)r1r);
        ic.r1.rr = r1r;
    }
    else ic.r1.r = r1;
    ic.r2.rr = local_base(b);
    ic.r3.i = local_address(b) + k;
    ic.op &= ~J_DEAD_R3;
#ifdef TARGET_HAS_RISING_STACK
    if ((bindaddr_(b) & BINDADDR_MASK) == BINDADDR_LOC)
      ic.r3.i += sizeof_int - ((b->bindmcrep) & MCR_SIZE_MASK);
#endif
    if (op != J_ADDK && alignof_toplevel_auto >= 4) /* (ADCONV) */
        ic.op |= J_BASEALIGN4;
    show_instruction(&ic);
}

static void show_mem_inst(J_OPCODE op, VRegnum r1, Binder *b)
{   show_mem_inst1(op, r1, b, 0);
}


static void show_inst3(J_OPCODE op, VRegInt r1, VRegInt r2, VRegInt r3)
{
    Icode ic;
    INIT_IC3 (ic, op, r1, r2, r3);
    show_inst (&ic);
}

#endif /* TARGET_IS_NULL */

/* the next 4 private vars control start_basic_block() and emit() */
static Icode *icodetop, *currentblock;
static int32 icoden;
static bool deadcode;  /* says to lose code = no current block */

typedef struct FreeIcodeChunk {
    struct FreeIcodeChunk *next;
    int32 size;
} FreeIcodeChunk;

static FreeIcodeChunk *holes;

/* A list of the gaps at the top of Icode segments, for the use of CSE
 * and loop optimisations (NOT used while emitting code).  The chaining
 * is in the Icode blocks themselves.
 */

static BlockHead *block_header;
BlockHead *top_block, *bottom_block;   /* exported to cg/regalloc */
/* beware: way_out is used for two different purposes.                  */
static LabelNumber *way_out;

#define size_of_binders(l) sizeofbinders(l, NO)

int32 sizeofbinders(BindList *l, bool countall)
/* return total size of non-slaved binders in the given list             */
/* Note that the BindList is in 'most recently bound first' order.       */
/* Thus, if alignof_double>alignof_toplevel we must be careful to pad    */
/* appropriately (a la padsize).  But normal padding algorithms pad      */
/* from the zero origin end.  Hence the special one here.                */
{
    int32 m = 0, m1 = 0;
    bool dbleseen = 0;
    for (; l!=NULL; l = l->bindlistcdr)
    {   Binder *b = l->bindlistcar;
        if (!(bindstg_(b) & bitofstg_(s_auto)))
            syserr(syserr_nonauto_active);
        if (bindxx_(b) == GAP || countall)
/* It is important that Binders processed here have had mcrepofexpr()      */
/* called on them before so that a cached rep is present. This is because  */
/* the TypeExpr may have been thrown away.                                 */
        {   int32 rep = bindmcrep_(b);
            if (rep == NOMCREPCACHE) syserr(syserr_size_of_binder);
/* The next line fixes up the backward scan of offsets.                  */
            if (alignof_double > alignof_toplevel_auto &&
                  rep & MCR_ALIGN_DOUBLE && !dbleseen)
                (dbleseen = 1, m1 = m, m = 0);
            m = padtomcrep(m, rep) +
                padsize(rep & MCR_SIZE_MASK, alignof_toplevel_auto);
        }
    }
    if (dbleseen) m = padsize(m, alignof_double);
    return m+m1;
}

static BlockHead *newblock2(LabelNumber *lab, BindList *active_on_entry)
{   /* one day it may be nice to make the 2nd arg a union { int; BindList *} */
    BlockHead *p = (BlockHead *) BindAlloc(sizeof(BlockHead));
    cgstate.block_cur += sizeof(BlockHead);
    blkcode_(p) = (Icode *) DUFF_ADDR;
    blkusedfrom_(p) = NULL;
    blklab_(p)  = lab;
    blklength_(p) = 0;
    blknext_(p) = (LabelNumber *) DUFF_ADDR;
    blknext1_(p) = (LabelNumber *) DUFF_ADDR;
    blkflags_(p) = 0;
    blkuse_(p) = 0;
    blkstack_(p) = active_on_entry;
    blknest_(p) = 0;
    blkexenv_(p) = currentExceptionEnv;
    return(p);
}

static BlockHead *newblock(LabelNumber *lab, BindList *active_on_entry)
{
    BlockHead *p = newblock2(lab, active_on_entry);
    if (bottom_block!=0) blkdown_(bottom_block) = p;
    blkup_(p) = bottom_block;
    blkdown_(p) = NULL;
     blkdebenv_(p) = current_env;
    bottom_block = block_header = p;
    return(p);
}

BlockHead *insertblockbetween(BlockHead *before, BlockHead *after, bool insertingraph)
{
    LabelNumber *newlab = nextlabel();
    BlockHead *newbh = newblock2(newlab, blkstack_(after));
    newlab->block = newbh;
    blknext_(newbh) = blklab_(after);

    /* Insert the new block after <before> in the blkdown chain */
    /* Often, this will be between <before> and <after>         */
    {   BlockHead *afterbefore = blkdown_(before);
        blkdown_(before) = newbh;
        blkdown_(newbh) = afterbefore;
        blkup_(newbh) = before;
        if (afterbefore == NULL)
            bottom_block = newbh;
        else
            blkup_(afterbefore) = newbh;
    }
    blkdebenv_(newbh) = blkdebenv_(after);
    blkexenv_(newbh) = blkexenv_(after);
    if (insertingraph)
        changesuccessors(before, newlab, blklab_(after));
    return newbh;
}

void changesuccessors(BlockHead *b, LabelNumber *newl, LabelNumber *old)
{
    bool replaced = NO;
    if (blkflags_(b) & BLKSWITCH) {
        LabelNumber **table = blktable_(b);
        int32 i, n = blktabsize_(b);
        for (i=0; i<n; i++)
            if (table[i] == old)
                replaced = YES, table[i] = newl;
    } else {
        if (blknext_(b) == old)
            replaced = YES, blknext_(b) = newl;

        if ((blkflags_(b) & BLK2EXIT) &&
             blknext1_(b) == old)
            replaced = YES, blknext1_(b) = newl;
    }
    if (!replaced)
        syserr(syserr_insertblockbetween, (int32)lab_name_(blklab_(b)),
                                          (int32)lab_name_(old));
}

void finishblock(void)
{
    blkcode_(block_header) = currentblock;
    blklength_(block_header) = icoden;
    currentblock = &currentblock[icoden];
    icoden = 0;
}

void end_emit(void)
{
    if (currentblock < icodetop)
        freeicodeblock(currentblock, icodetop - currentblock);
}

Icode *newicodeblock(int32 size)
{
    FreeIcodeChunk *p = holes, *prev = NULL;
    while (p != NULL) {
        int32 left = p->size - size;
        if (left >= 0) {
            if (left == 0) {
                if (prev == NULL)
                    holes = p->next;
                else
                    prev->next = p->next;
                return (Icode *)p;
            } else {
                p->size = left;
                return &((Icode *)p)[left];
            }
        }
        prev = p; p = p->next;
    }
    return (Icode *) BindAlloc(size * sizeof(Icode));
}

void freeicodeblock(Icode *p, int32 size)
{
    FreeIcodeChunk *q = (FreeIcodeChunk *) p;
    q->next = holes; q->size = size;
    holes = q;
}

void reopen_block(BlockHead *p)
{
/* This is required during loop optimisation. *p is a block that has no  */
/* code in it but which is otherwise complete. Set it up so that I can   */
/* emit() code into the block.                                           */
/* Note that I will need to call finishblock() again when I am done.     */
    IGNORE(p);
    syserr(syserr_reopen_block);
}

BlockHead *start_basic_block_at_level(LabelNumber *l, BindList *active_on_entry)
{
    BlockHead *b;
    if (!deadcode) emitbranch(J_B, l);   /* round off the previous block    */
    l->block = b = newblock(l, active_on_entry);    /* set the label        */
    deadcode = 0;                        /* assume label will be referenced */
    if (debugging(DEBUG_CG)) {
        cc_msg("L%ld: ", (long)lab_name_(l));
        pr_bindlist(active_on_entry);
        cc_msg("\n");
    }
    return b;
}

bool is_exit_label(LabelNumber *ll)  /* exported to jopprint.c/cse.c. (lab_xname_)  */
{
    if (ll == RetIntLab || ll == RetFloatLab || ll == RetDbleLab ||
        ll == RetVoidLab || ll == RetImplLab ||
/* RETLAB is present here so that print_jopcode may safely be used on the
 * arguments to show_instruction (when all the above have turned into RETLAB).
 */
        ll == RETLAB) return YES;
    else return NO;
}

/* emit() really takes a union mode as its last arg, so I provide a      */
/* number of entrypoints here so that I can preserve some type security  */
/* despite this mess.                                                    */

void emitfl(J_OPCODE op, FileLine fl)
{
    Icode ic;
    INIT_IC(ic,op);
    ic.r1.p = fl.p;
    ic.r2.str = fl.f;
    ic.r3.i = fl.l;
    emitic(&ic);
}

void emitshift(J_OPCODE op, VRegnum r1, VRegnum r2, VRegnum r3, int32 m)
{
    Icode ic;
    INIT_IC(ic,op);
    ic.r1.r = r1;
    ic.r2.r = r2;
    ic.r3.r = r3;
    if (m == 0) emitic(&ic);
#if defined TARGET_HAS_SCALED_ADDRESSING || defined TARGET_HAS_SCALED_OPS || \
    defined TARGET_HAS_SCALED_ADD
    else { ic.op |= (m << J_SHIFTPOS); emitic(&ic); }
#else
    else syserr(syserr_scaled_address);
#endif
}

void emitstring(J_OPCODE op, VRegnum r1, StringSegList *m)
{
    Icode ic;
    INIT_IC(ic,op);
    ic.r1.r = r1;
    ic.r2.i = 0;
    ic.r3.s = m;
    emitic(&ic);
}

void emitbranch(J_OPCODE op, LabelNumber *m)
{
    Icode ic;
    INIT_IC(ic,op);
    ic.r3.l = m;
    emitic(&ic);
}

void emitbinder(J_OPCODE op, VRegnum r1, Binder *m)
{
    Icode ic;
    INIT_IC(ic,op);
    ic.r1.r = r1;
    ic.r2.r = GAP;
    ic.r3.b = m;
    emitic(&ic);
}

void emitvk(J_OPCODE op, VRegnum r1, int32 n, Binder *m)
{
    Icode ic;
    INIT_IC(ic,op);
    ic.r1.r = r1;
    ic.r2.i = n;
    ic.r3.b = m;
    emitic(&ic);
}

void emitreg(J_OPCODE op, VRegnum r1, VRegnum r2, VRegnum m)
{
    Icode ic;
    INIT_IC(ic,op);
    ic.r1.r = r1;
    ic.r2.r = r2;
    ic.r3.r = m;
    emitic(&ic);
}


void emitreg4(J_OPCODE op, int flags, VRegnum r1, VRegnum r2, VRegnum r3, VRegnum r4)
{
    Icode ic;
    INIT_IC(ic,op);
    ic.flags = flags;
    ic.r1.r = r1;
    ic.r2.r = r2;
    ic.r3.r = r3;
    ic.r4.r = r4;
    emitic(&ic);
}

void emitfloat(J_OPCODE op, VRegnum r1, VRegnum r2, FloatCon *m)
{
    Icode ic;
    INIT_IC(ic,op);
    ic.r1.r = r1;
    ic.r2.r = r2;
    ic.r3.f = m;
    emitic(&ic);
}

void emitint64(J_OPCODE op, VRegnum r1, VRegnum r2, Int64Con *m)
{
    Icode ic;
    INIT_IC(ic,op);
    ic.r1.r = r1;
    ic.r2.r = r2;
    ic.r3.i64 = m;
    emitic(&ic);
}

void emitsetsp(J_OPCODE op, BindList *b2)
{
/* Note optimization performed here.                                     */
    if (active_binders != b2)
    {   Icode ic;
        INIT_IC(ic,op);
        ic.r2.bl = active_binders;
        ic.r3.bl = b2;
        emitic(&ic);
        active_binders = b2;
    }
}

void emitsetspandjump(BindList *b2, LabelNumber *l)
{
/* Note optimization performed here.                                     */
    if (active_binders != b2)
    {   Icode ic;
        INIT_IC(ic, J_SETSPENV);
        ic.r2.bl = active_binders;
        ic.r3.bl = b2;
        emitic(&ic);
    }
    {
        Icode ic;
        INIT_IC(ic, J_B);
        ic.r3.l = l;
        emitic(&ic);
    }
}

void emitsetspenv(BindList *b1, BindList *b2)
{
    Icode ic;
    INIT_IC(ic, J_SETSPENV);
    ic.r2.p = b1;
    ic.r3.p = b2;
    emitic(&ic);
}

void emitsetspgoto(BindList *b1, LabelNumber *l)
{
    Icode ic;
    INIT_IC(ic, J_SETSPGOTO);
    ic.r2.p = b1;
    ic.r3.p = l;
    emitic(&ic);
}

void emitcall(J_OPCODE op, VRegnum resreg, int32 nargs, Binder *fn)
{
    Icode ic;
    INIT_IC(ic,op);
    ic.r1.r = resreg;
    ic.r2.i = nargs;
    ic.r3.p = fn;
    emitic(&ic);
}

void emitcallreg(J_OPCODE op, VRegnum resreg, int32 nargs, VRegnum fn)
{
    Icode ic;
    INIT_IC(ic,op);
    ic.r1.r = resreg;
    ic.r2.i = nargs;
    ic.r3.i = fn;
    emitic(&ic);
}

void emitcasebranch(J_OPCODE op, VRegnum r1, LabelNumber **tab, int32 size)
{
    /* op == J_CASEBRANCH or J_THUNKTABLE or J_TYPECASE */
    Icode ic;
    INIT_IC(ic,op);
    ic.r1.r = r1;
    ic.r2.p = tab;
    ic.r3.i = size;
    emitic(&ic);
}

void emit(J_OPCODE op, VRegnum r1, VRegnum r2, int32 m)
{
    Icode ic;
    INIT_IC(ic,op);
    ic.r1.r = r1;
    ic.r2.r = r2;
    ic.r3.i = m;
    emitic(&ic);
}

void emitic(const Icode *const ic)
{
    if (deadcode) {
        if (!usrdbg(DBG_LINE) || usrdbg(DBG_OPT_DEAD)) return;
        start_new_basic_block(nextlabel());
    }
    if (ic->op==J_B)
    {   deadcode = 1;
        if (debugging(DEBUG_CG)) print_jopcode(ic);
        finishblock();
        blknext_(block_header) = ic->r3.l;
        return;
    }
/* Conditional branches terminate a basic block, so force a new start    */
/* if one has just been appended to the block                            */
    if ((ic->op & ~Q_MASK)==J_B)
    {   blknext1_(block_header) = ic->r3.l;
        blkflags_(block_header) |= BLK2EXIT;
        blkflags_(block_header) |= ic->op & Q_MASK;
        if (debugging(DEBUG_CG)) print_jopcode(ic);
        start_new_basic_block(nextlabel());
        return;
    }
/* The next line fixes to recover when I fill up a segment of store      */
    if (&currentblock[icoden] >= icodetop)
    {   if (icoden >= ICODESEGSIZE/2)
        {   if (debugging(DEBUG_CG | DEBUG_STORE))
                cc_msg("Force new block (ICODE segment overflow)\n");
            blkflags_(block_header) |= BLKREXPORTED;   /* mark block as exporting! */
            start_new_basic_block(nextlabel());
        }
/* The above arranges that icoden will be zero (following the call to      */
/* start_new_basic_block() -> emitbranch() -> finishcode()) if it had      */
/* originally been huge, and thus that I will not attempt an embarassingly */
/* large copy up into the new segment allocated here.                      */
        {   Icode *p = (Icode *) BindAlloc(ICODESEGSIZE*sizeof(Icode));
            if (icoden != 0)
            {   memcpy(p, currentblock, (size_t)(icoden*sizeof(Icode)));
                freeicodeblock(currentblock, icoden);
            }
            currentblock = p;
            icodetop = &p[ICODESEGSIZE];
            if (debugging(DEBUG_CG))
                cc_msg("New ICODE segment allocated\n");
            cgstate.icode_cur += icoden * sizeof(Icode);   /* wasted */
        }
    }
    if (debugging(DEBUG_CG)) print_jopcode(ic);
    currentblock[icoden++] = *ic;
    cgstate.icode_cur += sizeof(Icode);
    if (isproccall_(ic->op) && ic->op != J_OPSYSK)
    {   if (blkflags_(block_header) & BLKCALL)
            blkflags_(block_header) |= BLK2CALL;
        blkflags_(block_header) |= BLKCALL;
        /* see tail recursion optimisation comment below */
        if ((ic->op == J_CALLR && (config & CONFIG_INDIRECT_SETJMP)) ||
            (ic->op == J_CALLK && bindsym_(ic->r3.b) == setjmpsym))
        {   blkflags_(block_header) |= BLKSETJMP;
            if (HasFeature(Feature_UnixStyleLongjmp))
            /* We need this information early (to be able to turn off CSE),
             * but can't do branch_chain (where it is otherwise set) before
             * loop_optimise, because that turns some empty blocks into
             * non-empty ones.
             */
                procflags |= BLKSETJMP;
        }

    }
    /* special ways to end a block */
    if (ic->op == J_CASEBRANCH || ic->op == J_THUNKTABLE || ic->op == J_TYPECASE)
    {   deadcode = 1;
        finishblock();
        blkflags_(block_header) |= BLKSWITCH;
        blktable_(block_header) = ic->r2.lnn;
        blktabsize_(block_header) = ic->r3.i;
    }
}

/* AM believes that remove_noops logically fits here now. */

#ifndef TARGET_IS_NULL

bool is_compare(J_OPCODE op)
{   J_OPCODE realop = op & J_TABLE_BITS;
    return (realop == J_CMPK || realop == J_CMPR ||
            realop == J_CMPFR || realop == J_CMPDR ||
            realop == J_CMPFK || realop == J_CMPDK ||
            j_is_check(realop));
}

static Icode fg_pending;

static void show_pending_push(void) {
  /* Already tested that fg_pending.op == J_PUSHM */
    show_inst (&fg_pending);
    fg_pending.op = J_NOOP, fg_pending.r3.i = 0;
}

static void expand_jop_macro(const Icode *const icode)
{
    Icode ic = *icode;
#ifdef TARGET_NOT_YET_J_ALIGNMENT       /* removed soon */
    ic.op &= ~J_ALIGNMENT;
#endif
        if (debugging(DEBUG_CG)) print_jopcode(&ic);

    if (target_stack_moves_once) {
/*
 * TARGET_STACK_MOVES_ONCE is believed to be OK when used in combination
 * with NARGREGS==0, and in that case it drops SP once at the start of a
 * procedure and lifts it on exit.  If NARGREGS>0 all goes well when only
 * integer and pointer args are used.  However double and structure args
 * are handled by temporarily pushing them onto the stack and then popping
 * them into the argument registers.  While this is going on SP is not
 * where the MOVES_ONCE code expects it to be.  Again these temporary
 * movements are normally local and can cause no hassle - but it seems
 * possible that CSE optimisation and cross-jumping might sometimes
 * rearrange code in a way that in effect distributes the local stack
 * movement across several basic blocks.  At present this would break
 * the compiler, so with MOVES_ONCE and NARGREGS>0 it is suggested that
 * CSE and crossjumping be disabled for the while.  Work is in hand to
 * fix this problem by moving the offending args into registers directly
 * rather than via the stack.  Meanwhile a warning is generated if any
 * such local stack motion gets generated, and if the warning is not seen
 * all is well.
 */
    /* @@@ BEWARE: assumption here that fg_pending==J_NOOP.             */
    /* Turn a PUSHx into a STRK, but only if the push did not           */
    /* involve dropping the stack when NARGREGS>0.                      */
    /* E.g. struct { double d[3]; } x; ... f(x) ... with NARGREGS=4.    */
    J_OPCODE newop;
    switch (ic.op & J_TABLE_BITS)
    {
    case J_PUSHR: newop = J_STRK+J_ALIGN4; goto converted;
    case J_PUSHD: newop = J_STRDK+J_ALIGN8; goto converted;
    case J_PUSHF: newop = J_STRFK+J_ALIGN4; goto converted;
    case J_PUSHL: newop = J_STRLK+J_ALIGN8; goto converted;
    converted:
        if ((unsigned32)ic.r3.i < 4*NARGREGS)
            cc_warn(warn_untrustable, currentfunction.symstr); /* syserr() */
        else
/* @@@ (AM) BEWARE: do not trust this code if NARGREGS>0 since          */
/* it makes assumptions easily invalidated by crossjump/cse.            */
/* NB PUSHx codes are only used in function calls.                      */
        {   /* Forge a Binder sufficient for local_base/address.        */
            static Binder forgery;
            bindaddr_(&forgery) = BINDADDR_LOC |
                                  (greatest_stackdepth - (ic.r3.i - 4*NARGREGS));
/* @@@ "op & ~J_DEADBITS" was innocent effect of old code.  Check?!!    */
/* Also (only TARGET_STACK_MOVES_ONCE) J_STRK gets no J_ALIGNMENT.      */

            show_mem_inst(newop | (ic.op&J_DEAD_R1), ic.r1.r, &forgery);
            return;
        }
/* @@@ (AM) BEWARE: do not trust this code if NARGREGS>0 since          */
/* it makes assumptions easily invalidated by crossjump/cse.            */
/* NB PUSHx codes are only used in function calls.                      */
    default:
        break;
    }
    }

#ifndef EXPERIMENTAL_68000
    if ((ic.op & J_TABLE_BITS) == J_PUSHR)
    {
        ic.op = J_PUSHM;
        ic.r3.i = regbit(register_number(ic.r1.r));
        ic.r1.r = ic.r2.r = GAP;
    }
#endif
/* Now, a (mini-)jopcode peepholer...   ************************        */
/* Currently this just amalgamates J_PUSHR's, but J_SETSP's are next.   */
/* See the BEWARE for TARGET_STACK_MOVES_ONCE above.                    */
    if (ic.op == J_PUSHM)  /* && (pending==J_NOOP || pending==J_PUSHM)     */
    {
#ifdef TARGET_HAS_RISING_STACK
        /* The following check is that regs are ascending (this         */
        /* relies on the current code in cg.c).                         */
        if (fg_pending.r3.i & -ic.r3.i) syserr(syserr_expand_pushr);
#else
        /* The following check is that regs are descending (this        */
        /* relies on the current code in cg.c).                         */
        if (ic.r3.i & -fg_pending.r3.i) syserr(syserr_expand_pushr);
#endif
        fg_pending.op = J_PUSHM, fg_pending.r3.i |= ic.r3.i;
        if (ic.r3.i ==
#ifdef TARGET_HAS_RISING_STACK
                   regbit(R_A1 + NARGREGS - 1)
#else
                   regbit(R_A1)
#endif
           )
          show_pending_push();

        return;
    }
    if (fg_pending.op == J_PUSHM)
        show_pending_push();

/* end of peepholer                     ************************        */

    switch (ic.op & J_TABLE_BITS)
    {
case J_SETSP:
        if (target_stack_moves_once)
            return; /* Ignore.  @@@ temporary placing here.          */
        break;
#ifndef TARGET_HAS_SIGN_EXTEND
case J_EXTEND:
#  ifdef TARGET_LACKS_SIGNED_SHIFT
/* This trick could also be useful for loading signed chars on machines */
/* (like ARM) with load-byte with zero-extend, since the ANDK could     */
/* be lost in the load-byte and the SUBK might fold with another const. */
        {   int32 msb = (ic.r3.i == 2 ? (int32)0x8000 : 0x80);
            ic.r3.i = (msb << 1) - 1;
            show_inst3(J_ANDK, ic.r1, ic.r2, ic.r3);
            ic.r3.i = msb;
            show_inst3(J_EORK, ic.r1, ic.r1, ic.r3);
            show_inst3(J_SUBK, ic.r1, ic.r1, ic.r3);
        }
#  else
        ic.r3.i = ic.r3.i == 2 ? 16: 24;
        show_inst3(J_SHLK, ic.r1, ic.r2, ic.r3);
        show_inst3(J_SHRK+J_SIGNED, ic.r1, ic.r1, ic.r3);
# endif
        return;
#endif
/* The rest of this 'switch' deals with JOPCODE operators which are  */
/* macro-expanded to others on every conceivable machine.            */
/* N.B. the code below is slowly moving into remove_noops()          */
/* The next few groups of cases should not be here - see remove_noops */
case J_LDRV: case J_STRV:  case J_LDRLV:case J_STRLV:
case J_LDRFV:case J_STRFV: case J_LDRDV:case J_STRDV:
        {   Binder *bb = ic.r3.b;
            if (bindxx_(bb) != GAP)
                syserr(syserr_remove_noop_failed);
            ic.op = loads_r1(ic.op) ?
                J_XtoY(ic.op&~J_DEADBITS, J_LDRV, J_LDRK) :
                J_XtoY(ic.op&~J_DEADBITS, J_STRV, J_STRK) | (ic.op&J_DEAD_R1),
            /* J_ALIGNMENT preserved */
            show_mem_inst(ic.op, ic.r1.r, bb);
        }
        return;
case J_LDRV1:case J_LDRLV1:case J_LDRFV1:case J_LDRDV1:
        {   Binder *bb = ic.r3.b;
            if (!isany_realreg_(register_number(ic.r1.r)))
                syserr(syserr_remove_noop_failed2);
            if ((bindaddr_(bb) & BINDADDR_MASK)!=BINDADDR_ARG) /* DEAD? */
                syserr(syserr_bad_bindaddr);
            ic.op = J_XtoY(ic.op&~J_DEADBITS, J_LDRV1, J_LDRK),
            /* J_ALIGNMENT preserved */
            show_mem_inst(ic.op, ic.r1.r, bb);
        }
        return;
case J_LDRBVK:case J_STRBVK:
case J_LDRWVK:case J_STRWVK:
case J_LDRVK: case J_STRVK:
case J_LDRFVK:case J_STRFVK:
case J_LDRDVK:case J_STRDVK:
case J_LDRLVK:case J_STRLVK:
        show_mem_inst1(J_subvk(ic.op), ic.r1.r, ic.r3.b, ic.r2.i);
        return;
case J_ADCONV:
        show_mem_inst(J_ADDK, ic.r1.r, ic.r3.b);
        return;

/* Here (in the case that string literals are to be writable, we remove  */
/* J_STRING opcodes in favour of J_ADCON.                                */
case J_STRING:
        if (HasFeature(Feature_WRStrLits))
          /*
           * Pcc-mode - string lits writable in the data segment.
           */
        {   int32 offset = data_size();   /* The literal's about to be */
                                        /* put at this offset ...  */
            vg_genstring(ic.r3.s, stringlength(ic.r3.s)+1, 0);
            /* The following call is unexpectedly important...            */
            /* vg_genstring() does not post-align, and other genXXX() fns */
            /* do not pre-align, so death is inevitable if we omit it.    */
/* It also plays its part in optimising string constants to word          */
/* boundaries which improves performance on many machines (not just RISC) */
            padstatic(alignof_toplevel_static);
            /* since datasegment is defined, it will have been obj_symref'd */
            ic.op = J_ADCON;
            ic.r2.i = offset;
            ic.r3.sym = bindsym_(datasegment);
            show_inst(&ic);
            return;
        }
        ic.r2.i = 0;
        break;

#ifdef TARGET_FP_LITS_FROM_MEMORY
/*
 * In this case I want floating point string literals to go in the data
 * segment.  Really I would still like equal constants to be able to share,
 * and also I would like CSE to be able to consolidate separate expressions
 * using constants (which might sometimes render the original constants
 * unnecessary.  I note that mapping ADCONF/D onto just ADCON here seems to
 * lose information (in the data seg) that the data assembled is floating
 * point.
 */
case J_ADCOND:
        {   int32 offset = data.size;
            gendcE(8, ic.r3.f);
            padstatic(alignof_toplevel_static);
            ic.op = J_ADCON;
            ic.r2.i = offset;
            ic.r3.sym = bindsym_(datasegment);
            show_inst(&ic);
            return;
        }
case J_ADCONF:
        {   int32 offset = data.size;
            gendcE(4, ic.r3.f);
            padstatic(alignof_toplevel_static);
            ic.op = J_ADCON;
            ic.r2.i = offset;
            ic.r3.sym = bindsym_(datasegment);
            show_inst(&ic);
            return;
        }
#endif

/* normalise some Binder's to Symstr's for xxxgen.c */
case J_ADCON:
        {   Binder *bb = ic.r3.b;
            Symstr *name = bindsym_(bb);
            int32 offset = 0;
            {
#ifdef TARGET_HAS_BSS
                if ((bindstg_(bb) & u_bss) && bindaddr_(bb) != BINDADDR_UNSET)
                {   name = bindsym_(bsssegment);
                    offset = bindaddr_(bb);
                } else
#endif
#ifdef CONST_DATA_IN_CODE
                if (bindstg_(bb) & u_constdata)
                {   name = bindsym_(constdatasegment);
                    offset = bindaddr_(bb);
                } else
#endif
                if ((bindstg_(bb) & b_fnconst+bitofstg_(s_static)+u_loctype)
                        == bitofstg_(s_static))
/* static variables get referenced relative to a static base             */
/* extdef variables can be referenced that way, but here it seems nicer  */
/* (and certainly it is no more expensive) to use the external symbol.   */
                {   name = bindsym_(datasegment);
                    offset = bindaddr_(bb);
                }
            }
/* Announce to the linker the flavour (code/data) of the symbol.         */
            (void)obj_symref(name, (bindstg_(bb) & b_fnconst ?
                                             xr_code : xr_data) |
                                   (bindstg_(bb) & bitofstg_(s_weak) ?
                                             xr_weak : 0),
                             0);
/* The next line of code is probably dying given the obj_symref() above. */
            {
#ifdef TARGET_CALL_USES_DESCRIPTOR
                if (bindstg_(bb) & b_fnconst)
                {
                    /* WGD: pass static/extern flag in r2 */
                    ic.r2.i = bindstg_(bb) & bitofstg_(s_static);
                    ic.r3.sym = name;
                    ic.op = J_FNCON;
                }
                else
#endif
                {   ic.r2.i = offset;
                    ic.r3.sym = name;
                }
            }
        }
        break;
#ifndef TARGET_FP_ARGS_IN_FP_REGS
case J_ENTER:
        ic.r3.i = k_argwords_(ic.r3.i);
        break;
#endif
case J_TAILCALLK:
case J_CALLK:
/* /* @@@ BUG here:  1. if m is a local static data binder, then it does   */
/* not get defined in cfe.c.vargen (to avoid clashes and make sure      */
/* store does not vanish under out feet).  Thus this code should        */
/* resolve to codesegment+nnn.  However, unlike the ADCON case above    */
/* there is no room for the nnn.                                        */
/* 2. Moreover, the current (Dec 88) a.out formatter does not treat     */
/* X_PCreloc branches to data segment correctly -- see AM comments.     */
/* (This explains acorn's curious code in arm/mcdep.c).                 */
/* One fix is just to syserr(), or to fix into a CALLR.  But beware     */
/* that back ends do not support TAILCALLR yet (ANSI/register use).     */
        {
            ic.r3.sym = bindsym_(ic.r3.b);
#if 0
/*
/* The following code should never be needed: open_compilable in cg.c should
   ensure there are no calls left to memcpyfn etc (translating to real... if
   necessary). If it is needed, open_compilable should be fixed.
*/
            if (ic.r3.sym == bindsym_(exb_(arg1_(sim.memcpyfn))))
                ic.r3.sym = bindsym_(exb_(arg1_(sim.realmemcpyfn)));
            if (ic.r3.sym == bindsym_(exb_(arg1_(sim.memsetfn))))
                ic.r3.sym = bindsym_(exb_(arg1_(sim.realmemsetfn)));
#endif
/* There used to be code here to do obj_symref() for the target, to     */
/* avoid the need for each backend to do it. It's been retired, because */
/* the backend may be able to optimise the call away (and so want to    */
/* avoid the reference)                                                 */
        }
        break;
#ifdef TARGET_HAS_DATA_VTABLES
case J_WORD_ADCON:
        ic.r3.sym = bindsym_(ic.r3.b);
        break;
#endif
#ifdef TARGET_LACKS_RIGHTSHIFT
/* then map constant right shifts here to leftright, expr ones done in cg.c */
case J_SHRK:
        ic.r3.i = -ic.r3.i;
        ic.op ^= J_SHRK^J_SHLK;
        break;
#endif /* TARGET_LACKS_RIGHTSHIFT */
case J_NOOP:
        syserr(syserr_remove_noop_failed);
        return;
    }
    show_inst(&ic);
}

static void show_branch_instruction(J_OPCODE op, LabelNumber *m)
{
    Icode ic;
    INIT_IC(ic,op);
    ic.r3.l = m;
    expand_jop_macro(&ic);
}

/* more of the debugger */
static void dbg_scope1(BindListList *newbl, BindListList *old)
{
    IGNORE(newbl); IGNORE(old); /* avoid warnings when dbg_scope is FALSE */
    if (dbg_scope(newbl, old))
    {   Icode ic;
        INIT_IC(ic, J_INFOSCOPE);
        ic.r3.i = 0;
        /* request code location where scope started or ended */
        expand_jop_macro(&ic);
    }
}

static BlockHead *prevblock;

static void show_basic_block(BlockHead *p, uint32 cond)
{
    Icode *b = blkcode_(p);
    int32 len = blklength_(p);
    int32 b1;
   if (usrdbg(DBG_VAR)) dbg_scope1(blkdebenv_(p), current_env2),
                         current_env2 = blkdebenv_(p);
/* The BLKCODED bit allows me to display blocks out of their natural order */
/* @@@ but it may later cause trouble when DBG_VAR is on.                  */
/* /* AM: fix to suppress the spurious J_LABEL/J_STACK before J_ENTRY.     */
    blkflags_(p) |= BLKCODED;
    if (prevblock == NULL ||
        blkusedfrom_(p) == NULL ||
        blkusedfrom_(p)->blklstcdr != NULL ||
        blkusedfrom_(p)->blklstcar != prevblock ||
        (blkflags_(prevblock) & BLKSWITCH))
    {
        Icode ic;
        INIT_IC (ic, J_LABEL);
        ic.r3.l = blklab_(p);
        expand_jop_macro(&ic);    /* label of block */
        if (!target_stack_moves_once) {
            ic.op = J_STACK;
            ic.r3.i = blkstacki_(p);
            expand_jop_macro(&ic);    /* env. of block  */
        }
    }
    for (b1=0; b1<len; b1++)
    {   Icode ic = b [b1];
        uint32 cmpcond;
        switch (ic.op & J_TABLE_BITS)
        {   case J_CMPK:  case J_CMPR:
            case J_CMPFK: case J_CMPFR:
            case J_CMPDK: case J_CMPDR:
                cmpcond = ic.op & Q_MASK;
                if (cmpcond != Q_UNDEF && (cmpcond & ~Q_UBIT) != Q_UKN)
                {
                    if (cond != Q_UKN)
                        ic.op = (ic.op & ~Q_MASK) | cond;
                    else
                        ic.op = (ic.op & ~(Q_MASK & ~Q_UBIT)) | cond;
                }
        }
        expand_jop_macro(&ic);
    }
    prevblock = p;
}

static bool same_instruction(Icode *c1, Icode *c2) {
    /*Two instructions are deemed   */
    /* to match if they are identical when virtual registers have been   */
    /* converted to real register numbers wherever they are needed. The  */
    /* instructions that use pseudo-virtual registers to cope with items */
    /* lifted out of loops etc have to match even more exactly, thus the */
    /* tests here are conservative (and hence safe!).                    */
    if (c1->op == c2->op && c1->flags == c2->flags)
    {
        int same = 0;
/* The next fragment of code scares me somewhat - I need to see if the  */
/* two instructions being considered will be treated identically after  */
/* macro-expansion, where macro-expansion includes the replacement of   */
/* virtual register identifiers by real register numbers.               */
/* As more code moves from expand_jop_macro() to remove_noops this      */
/* will ease.                                                           */
/* Note that remove_noops() has removed any possible loop invariant     */
/* suggestions either by smashing to a RR operation or by               */
/* removing the (pseudo_reads_r1/2) potential invariant register field. */
        if (uses_r1(c1->op))
            same += register_number(c1->r1.r) == register_number(c2->r1.r);
        else
            same += c1->r1.i == c2->r1.i;
        if (uses_r2(c1->op))
            same += register_number(c1->r2.r) == register_number(c2->r2.r);
        else
            same += c1->r2.i == c2->r2.i;
        if (uses_r3(c1->op))
            same += register_number(c1->r3.r) == register_number(c2->r3.r);
        else
            same += c1->r3.i == c2->r3.i;
        if (uses_r4(c1->op))
            same += register_number(c1->r4.r) == register_number(c2->r4.r);
        else
            same += c1->r4.i == c2->r4.i;
        return same == 4 ? YES : NO;
    }
    return NO;
}

#endif /* TARGET_IS_NULL */

#define is_empty_block(b) (blklength_(b) == 0) /* remove_noops tidied */

/* N.B. BLKEMPTY and BLKALIVE are disjoint.                             */
/* BLKEMPTY performs a similar role to BLKALIVE: it flags that the      */
/* block has been seen, BUT that it is not really alive.                */
/* Note that self referential empty blocks have BLKALIVE set instead.   */

static bool branch_chain_exit_label(LabelNumber *lab, int stage) {
    return is_exit_label(lab) || (stage == 2 && lab == way_out);
}

static LabelNumber *branch_emptychain(LabelNumber *lab, int stage)
/* When we get an empty block we must flag it so (BLKEMPTY)  */
/* and change its blknext_() pointer to where it ULTIMATELY  */
/* goes.  Note that empty blocks are never BLKALIVE except   */
/* when they have a tight cycle which BLKBUSY detects.       */
{   LabelNumber *lab2 = lab, *lab3;
    /* skip to end of branch chain of empty basic blocks     */
    if (usrdbg(DBG_VAR+DBG_LINE) && !usrdbg(DBG_OPT_DEAD)) return lab;
    while (!branch_chain_exit_label(lab2, stage))
    {   BlockHead *b = lab2->block;
        /* Treat a block as empty if it does not have a conditional  */
        /* exit & it has no code (not overkill: three-way-branches). */
        if (blkflags_(b) & BLK2EXIT || !is_empty_block(b) ||
            (blkflags_(b) & (BLKBUSY|BLKALIVE|BLKEMPTY))) break;
        blkflags_(b) |= BLKBUSY;
        lab2 = blknext_(b);
    }
    /* the next line deals with the case that two empty chains have  */
    /* a common tail:  lab3 is the real end of the branch chain.     */
    lab3 = lab2;
    if (!branch_chain_exit_label(lab3, stage))
    {   BlockHead *b = lab3->block;
        if (blkflags_(b) & BLKEMPTY) lab3 = blknext_(b);
    }
    /* now remove empty blocks (c.f. indirection nodes) */
    while (lab != lab2)
    {   BlockHead *b = lab->block;
        if (debugging(DEBUG_CG))
            cc_msg("empty block: L%ld -> L%ld\n", (long)lab_name_(lab),
                    (long)lab_xname_(lab3));
        blkflags_(b) |= BLKEMPTY;
        blkflags_(b) &= ~BLKBUSY;    /* only for tidyness       */
        lab = blknext_(b);
        blknext_(b) = lab3;          /* smash it in             */
    }
    return lab3;                     /* the real place to go to */
}

static LabelNumber *branch_chain(LabelNumber *lab, int stage)
/* scan the flowgraph (a) marking bit BLKALIVE in blkflags_ of blocks    */
/* that can be reached, and (b) converting any destination addresses in  */
/* block exits to avoid chains of branches.                              */
/* When called on label n, if label n references a branch instruction    */
/* this function returns the label number of the destination of the jump */
/*                                                                       */
/* This code now uses pointer-reversal since otherwise it can use up a   */
/* great deal of stack.                                                  */
{
    BlockHead *b, *back_pointer = NULL;
    for (;;)
    {   for (;;)  /* Here to descend via lab */
        {   lab = branch_emptychain(lab, stage);
            if (branch_chain_exit_label(lab, stage))
            {   if (lab == RetImplLab && !implicit_return_ok)
                    implicit_return_ok = 1,
                    cc_warn(flowgraf_warn_implicit_return);
                if (stage == 1) lab = way_out;
                break; /* exit: do not chain further */
            }
            b = lab->block;
            if (blkflags_(b) & BLKALIVE) break;       /* visited already */
            blkflags_(b) |= BLKALIVE;
#ifdef TARGET_HAS_TAILCALL
            /* set up the BLKSETJMP bit early enough for TAILCALL        */
            /* optimisation.  refblock() sets up the other bits.         */
            procflags |= blkflags_(b) & BLKSETJMP;
#endif
            if (blkflags_(b) & BLKSWITCH)
            {   LabelNumber **v = blktable_(b);
                int32 i, n = blktabsize_(b);
/* For the moment I will leave this next line as a recursive call        */
                for (i=0; i<n; i++) v[i] = branch_chain(v[i], stage);
                break;
            }
            blkflags_(b) = (blkflags_(b) & ~(BLKP2|BLKP3)) | BLKP2;
            lab = blknext_(b); blkbackp_(b) = back_pointer;     /* share */
            back_pointer = b;
        }
        for (;;)        /* here to ascend */
        {   if (back_pointer==NULL) return lab;
            b = back_pointer;
            switch (blkflags_(b) & (BLKP2|BLKP3))
            {
    default:    syserr(syserr_branch_backptr);
    case BLKP2: back_pointer = blkbackp_(b); blknext_(b) = lab;  /* share */
                if (blkflags_(b) & BLK2EXIT)
                {   lab = blknext1_(b); blkbackp1_(b) = back_pointer; /* share */
                    blkflags_(b) = (blkflags_(b) & ~(BLKP2|BLKP3)) | BLKP3;
                    back_pointer = b;
                    break;
                }
                lab = blklab_(b);
                continue;
    case BLKP3: back_pointer = blkbackp1_(b); blknext1_(b) = lab; /* share */
/* Optimise away the conditional exit if both exits from this block go   */
/* to the same place.                                                    */
                if (blknext_(b) == blknext1_(b) ||
                    (branch_chain_exit_label(blknext_(b), stage) &&
                     branch_chain_exit_label(blknext1_(b), stage) )) {
                    blkflags_(b) &= ~(BLK2EXIT|Q_MASK);
                    if (!(blkflags_(b) & BLKCCEXPORTED) &&
                        is_compare(blkcode_(b)[blklength_(b)-1].op))
                        if (--blklength_(b) == 0 && lab != blklab_(b)) {
                            BlockHead *b1 = top_block;
                            LabelNumber *l = blklab_(b);
                        /* Empty predecessors of b must have their successor
                           altered to blknext_(b), or a subsequent block with
                           successor one of them will get forwarded to b not
                           blknext_(b). This rewriting makes it safe to mark b
                           BLKEMPTY below.
                         */
                            for (; b1 != NULL; b1 = blkdown_(b1)) {
                                if (blknext_(b1) == l)
                                    blknext_(b1) = lab;
                                if ((blkflags_(b1) & BLK2EXIT) && blknext1_(b1) == l)
                                    blknext1_(b1) = lab;
                            }
                            blkflags_(b) = (blkflags_(b) & ~BLKALIVE) | BLKEMPTY;
                            continue;
                        }
                }
                lab = blklab_(b);
                continue;
            }
            break;  /* so that break inside the switch = break in for    */
        }
    }
}

/* shouldn't the next line have BLK0EXIT? or is that done elsewhere?    */
#define block_single_entryexit(b) \
        (block_single_exit(b) && block_single_entry(b))

#define block_single_entry(b) \
        (blkusedfrom_(b) == NULL || blkusedfrom_(b)->blklstcdr == NULL)

#define block_single_exit(b) \
        (!(blkflags_(b) & (BLK2EXIT | BLKSWITCH)))

#define block_coded(b) (blkflags_(b) & BLKCODED)

static int32 adjust_stack_size(int32 stack_size, Icode *code) {
    switch (code->op & J_TABLE_BITS) {
/* This code seems distinctly grotty... */
    case J_SETSP:
        if (stack_size != code->r2.i)
            syserr(syserr_zip_blocks, stack_size, code->r2.i);
        return code->r3.i;
    case J_PUSHD:
    case J_PUSHL:
        return stack_size + 8;
/* alignof_toplevel_auto==8 is a euphemism for TARGET_IS_ADENART, else 4.   */
    case J_PUSHR:
    case J_PUSHF:
        return stack_size + alignof_toplevel_auto;
/* AM: use 4 (or sizeof_long?) on next lines in case sizeof_int==2.     */
/* (Oct 89) the following lines' case is under re-organisation.         */
    default:
        return stack_size;
    }
}

static int32 adjusted_stack_size(int32 stack_size, Icode *code, int32 n) {
    int32 i;
    if (!target_stack_moves_once)
        for (i = 0; i < n; i++)
            stack_size = adjust_stack_size(stack_size, &code[i]);
    return stack_size;
}

#ifdef TARGET_HAS_COND_EXEC

#define set_cond_execution(cond)        \
 { Icode ic; INIT_IC(ic, (J_CONDEXEC|(cond))) \
   ic.r3.i = 0; expand_jop_macro(&ic); }

/* A block is not usable with conditional execution if if ends with a */
/* conditional branch (or switch), or if it is shared between the     */
/* path in the code where a condition code will be tested and any     */
/* other route through the code.                                      */
#define conditionalizable(b, fl, maxl) \
        (block_single_entryexit(b) ? block_preserves_cc(b, fl, maxl) : Bpcc_No)

#define cc_ignorecmp 1
#define cc_includelast 2

#define Bpcc_No 255

static int CondMax_Ordinary, CondMax_Loop;

static int block_preserves_cc(BlockHead *b, int fl, int maxl)
/* True if the block does not contain any instructions that would cause  */
/* trouble with conditional execution & if the block is also short       */
/* (Ignorecmp is set only if the block is known to be two-exit)          */
{
    int n = 0;
    Icode *c = blkcode_(b);
    int32 i, len = blklength_(b);
    if (fl & cc_ignorecmp)
    {
        len--;
        n++;
    }
    for (i = 0; i < len; i++)
    {   switch (c[i].op & J_TABLE_BITS)
        {
    case J_SAVE:
            return Bpcc_No;
    case J_VSTORE:
    case J_USE:
            continue;    /* these expand into nothing */
#ifdef TARGET_HAS_BLOCKMOVE
#ifdef TARGET_IS_ARM_OR_THUMB
    case J_MOVC:
    case J_CLRC:
    /* Some cases get expanded into a loop ...
       These I want to reject even as the last op in a block.
     */
            if (alterscc(&c[i])) return Bpcc_No;
            /* increment instruction count by 3 */
            n += 2;
            break;
#endif
#endif
    case J_NOOP:   /* remove_noops has normalised noops to J_NOOP */
            syserr(syserr_remove_noop_failed);
            continue;
    default:
            if (((fl & (cc_ignorecmp|cc_includelast)) || i+1 < len) &&
                alterscc(&c[i]))
              return Bpcc_No;
        }
        if (++n > maxl) return Bpcc_No;
    }
    return n;
}

static void show_conditional_block(int32 cond, BlockHead *p, bool showbranch)
{
/* Show a block with conditional execution enabled                       */
    set_cond_execution(cond);
    show_basic_block(p, Q_AL);
    if (!(blkflags_(p) & BLK0EXIT) && showbranch) {
        LabelNumber *l = blknext_(p);
        show_branch_instruction(J_B, l == way_out ? RETLAB : l);
    }
    prevblock = NULL;
    set_cond_execution(Q_AL);
}

#define EQ_COND(x) (((x) | Q_UBIT) == Q_UEQ || ((x) | Q_UBIT) == Q_UNE)

static void show_blockchain(BlockHead *b, BlockList *bl, int32 cond) {
    /* Two surprising things are done here to stop the ARM peepholer
       making incorrect transformations:
         the cond field in comparisons may be set to Q_UKN to prevent its
         being changed in one place (but not consistently)
         a CONDEXEC jopcode is output before each block to stop all but
         the last comparison being optimised out.
     */

    show_basic_block(b, Q_UKN);
    set_cond_execution(cond);
    for (; bl != NULL; bl = bl->blklstcdr)
    {   b = bl->blklstcar;
        cond = blkflags_(b) & Q_MASK;
        if (!EQ_COND(cond) || bl->blklstcdr != NULL)
            cond = Q_UKN;
        show_basic_block(bl->blklstcar, cond);
        if (bl->blklstcdr != NULL)
            set_cond_execution(Q_NEGATE(blkflags_(b) & Q_MASK));
    }
}

static void pr_blocklist(BlockList *bl) {
    for (; bl != NULL; bl = bl->blklstcdr)
        cc_msg(" %ld", lab_name_(blklab_(bl->blklstcar)));
}

typedef struct CommonInst CommonInst;
struct CommonInst {
    CommonInst *cdr;
    int32 n1, n2;
};

static CommonInst *common_insts(BlockHead *b1, BlockHead *b2) {
    CommonInst *c = NULL, **cp = &c;
    Icode *c1 = blkcode_(b1), *c2 = blkcode_(b2);
    int32 l1 = blklength_(b1), l2 = blklength_(b2);
    int32 n1, n2 = 0;
    for (n1 = 0; n1 < l1; n1++) {
        int32 p2;
        for (p2 = n2; p2 < l2; p2++)
            if (same_instruction(&c1[n1], &c2[p2]) &&
                !alterscc(&c1[n1]) && !is_compare(c1[n1].op)) {
                CommonInst *ci = (CommonInst *)SynAlloc(sizeof(*ci));
                cdr_(ci) = NULL; ci->n1 = n1; ci->n2 = p2;
                *cp = ci; cp = &cdr_(ci);
                n2 = p2+1;
                break;
            }
    }
    return c;
}

static void show_block_pair(int32 cond, BlockHead *b1, BlockHead *b2, CommonInst *c) {
    Icode *c1 = blkcode_(b1), *c2 = blkcode_(b2);
    int32 l1 = blklength_(b1), l2 = blklength_(b2);
    int32 s1 = blkstacki_(b1), s2 = blkstacki_(b2);
    int32 n1, n2;
    int32 p1 = 0, p2 = 0;
    do {
        if (c == NULL) {
            n1 = l1; n2 = l2;
        } else {
            n1 = c->n1; n2 = c->n2;
            c = cdr_(c);
        }
        if (p1 != n1) {
            set_cond_execution(cond);
            if (!target_stack_moves_once && s1 != s2)  {
                Icode ic;
                INIT_IC(ic, J_STACK);
                ic.r3.i = s1;
                expand_jop_macro(&ic);
            }
            for (; p1 < n1; p1++, c1++) {
                s1 = adjust_stack_size(s1, c1);
                expand_jop_macro(c1);
            }
        }
        if (p2 != n2) {
            set_cond_execution(Q_NEGATE(cond));
            if (!target_stack_moves_once && s1 != s2)  {
                Icode ic;
                INIT_IC(ic, J_STACK);
                ic.r3.i = s2;
                expand_jop_macro(&ic);
            }
            for (; p2 < n2; p2++, c2++) {
                s2 = adjust_stack_size(s2, c2);
                expand_jop_macro(c2);
            }
        }
        if (n1 < l1) {
            set_cond_execution(Q_AL+Q_UBIT);
            s1 = adjust_stack_size(s1, c1);
            s2 = adjust_stack_size(s2, c2);
            expand_jop_macro(c1);
            c1++; c2++;
            p1++, p2++;
        }
    } while (p1 < l1 || p2 < l2);
    blkflags_(b1) |= BLKCODED;
    blkflags_(b2) |= BLKCODED;
    set_cond_execution(Q_AL);
}

static bool successor_inline(BlockHead *b) {
    LabelNumber *next = blknext_(b);
    BlockHead *b1;
    BlockList *bl;
    if (next == way_out) return NO;
    b1 = next->block;
    if (block_coded(b1)) return NO;
    /* b1 will be coded inline after b if its only predecessors which    */
    /* have not yet been coded are b and b1 itself                       */
    for (bl = blkusedfrom_(b1); bl != NULL; bl = bl->blklstcdr) {
        BlockHead *b2 = bl->blklstcar;
        if (b2 != b && b2 != b1 && !block_coded(b2)) {
        /* or probably if it is the first non-empty successor of b */
            b2 = blkdown_(b);
            for (; b2 != NULL; b2 = blkdown_(b2))
                if (!(blkflags_(b2) & BLKEMPTY))
                    return b2 == b1;
        }
    }
    return YES;
}

#endif

#ifndef TARGET_IS_NULL

static void show_n(int32 n, Icode *c, int32 s) {
    int32 i;
    IGNORE(s);
    for (i = 0; i < n; i++, c++)
        expand_jop_macro(c);
}

#define BLKLIFTABLE BLKP2

static LabelNumber *use_cond_field(BlockHead *p)
{
/* Decide if I can afford to use conditional execution. To do so I need: */
/*                                                                       */
/*             A           A           A                 A               */
/*            / \         | \         | \               | \__(return)    */
/*           B   C        |  C        |  C              |                */
/*            \ /         | /         |   \__(return)   |                */
/*             D           D           D                 D               */
/*                                                                       */
/* where B and C are short blocks that do not disturb the condition      */
/* codes which are not reached from elsewhere.                           */

/* A  here may be a single block, or a sequence of 2-exit blocks with a  */
/* common successor (reached with the same condition code), with blocks  */
/* in the sequence single-entry and not disturbing condition codes       */
/* (except by the comparison at their end).                              */

/* If either successor block for A has been displayed already I do not   */
/* need to use conditional execution.                                    */
/* Block p has now not yet been displayed.                               */
    int32 cond = blkflags_(p) & Q_MASK,
          lifted = blkflags_(p) & BLKLIFTABLE;
    LabelNumber *next = blknext_(p), *next1 = blknext1_(p);
    BlockHead *b = 0, *b1 = 0;
    int32 next1_arcs = 1;

#ifdef TARGET_HAS_COND_EXEC
#  define show_head(p, cond) if (next1_arcs == 1) show_basic_block(p, cond)
#else
#  define show_head(p, cond) show_basic_block(p, cond)
#endif
    if (cond == Q_AL) syserr(syserr_no_main_exit);
    if (next != way_out) b = next->block;
    if (next1 != way_out) b1 = next1->block;
/*
    if (b == 0 && b1 == 0) syserr(syserr_two_returns);
*/
    blkflags_(p) |= BLKCODED;   /* a bit of a hack -- see show_basic_block */
#ifdef TARGET_HAS_COND_EXEC
    /* Look for a sequence of 2-exit blocks with a common successor */
    if (!usrdbg(DBG_VAR+DBG_LINE))
    {   int32 cond2 = 0;
        LabelNumber *commonexit = NULL;
        BlockHead *bh = NULL;
        if (b1 != NULL && !block_coded(b1) && block_single_entry(b1) && (blkflags_(b1) & BLK2EXIT) &&
                block_preserves_cc(b1, cc_ignorecmp, CondMax_Ordinary) != Bpcc_No) {
            if ((blknext_(b1) == next && Q_implies(blkflags_(b1), cond)) ||
                (blknext1_(b1) == next && Q_implies(Q_NEGATE(blkflags_(b1)), cond)))
            {   commonexit = next; bh = b1;
            }
        }
        if (b != NULL && !block_coded(b) && block_single_entry(b) && (blkflags_(b) & BLK2EXIT) &&
                block_preserves_cc(b, cc_ignorecmp, CondMax_Ordinary) != Bpcc_No) {
            if ((blknext1_(b) == next1 && Q_implies(Q_NEGATE(blkflags_(b)), Q_NEGATE(cond))) ||
                (blknext_(b) == next1 && Q_implies(blkflags_(b), Q_NEGATE(cond))))
            {   commonexit = next1; bh = b;
                cond = Q_NEGATE(cond);
            }
        }

        if (commonexit != NULL) {
            BlockList *blockchain = NULL;
            int total_instr = 0;
            if (blknext_(bh) == commonexit)
                cond2 = blkflags_(bh);
            else
                cond2 = Q_NEGATE(blkflags_(bh));
            for (;;) {
                int num_instr = block_preserves_cc(bh, cc_ignorecmp, CondMax_Ordinary);
                total_instr += num_instr;
                if (block_coded(bh) || !block_single_entry(bh) || num_instr == Bpcc_No ||
                    (blkflags_(bh) & BLKLIFTABLE) != lifted || total_instr > CondMax_Ordinary)
                    break;
                if (blknext1_(bh) == commonexit && Q_implies(Q_NEGATE(blkflags_(bh)), cond2))
                {   next = blknext_(bh);
                    cond2 = Q_NEGATE(blkflags_(bh));
                }
                else if (blknext_(bh) == commonexit && Q_implies(blkflags_(bh), cond2))
                {   LabelNumber *tmp = blknext1_(bh);
                    next = blknext1_(bh);
                    cond2 = blkflags_(bh);
                    /* Swap next and next1 in order to simplify showblockchain. This is OK
                     * since the condition is inverted too.
                     */
                    blknext1_(bh) = blknext_(bh);
                    blknext_(bh) = tmp;
                    blkflags_(bh) = Q_NEGATE(blkflags_(bh));
                }
                else
                    break;
                next1 = commonexit;
                blockchain = mkBlockList(blockchain, bh);
                if (next == way_out) break;
                bh = next->block;
            }
            blockchain = (BlockList *)dreverse((List *)blockchain);
            next1_arcs = length((List *)blockchain)+1;

            if (debugging(DEBUG_CG)) {
                cc_msg("Conditional chain %ld", lab_name_(blklab_(p)));
                pr_blocklist(blockchain);
                cc_msg(" cond1 %lx cond2 %lx common successor %ld other successor %ld\n",
                       cond, cond2, lab_name_(next1), lab_name_(next));
                if (next1 != way_out) {
                    cc_msg("Predecessors of common successor:");
                    pr_blocklist(blkusedfrom_(next1->block));
                    cc_msg("\n");
                }
            }
            show_blockchain(p, blockchain, cond & Q_MASK);
            set_cond_execution(Q_AL);

            cond = Q_NEGATE(cond2 & Q_MASK);    /* condition for next basic block */
            if (next == next1)    /* I think this should now never happen */
                return next;
            b = (next == way_out) ? 0 : next->block;
            b1 = (next1 == way_out) ? 0 : next1->block;
        }
    }
#endif
    {   Icode *commonp = NULL;
        int32 ncommon = 0;
        int32 s = 0;
        if (b != 0 && b1 != 0 && !block_coded(b) && !block_coded(b1) &&
            block_single_entry(b) &&
            length((List *)blkusedfrom_(b1)) == next1_arcs) {
            int32 l1 = blklength_(b), l2 = blklength_(b1);
            Icode *c1 = blkcode_(b), *c2 = blkcode_(b1);
            commonp = c1;
            if (l1 > l2) l1 = l2;
            if (!target_stack_moves_once) s = blkstacki_(b);
            if (target_stack_moves_once || s == blkstacki_(b1))
                for (ncommon = 0; ncommon < l1; ncommon++, c1++, c2++)
                    if (!same_instruction(c1, c2) || alterscc(c1) || is_compare(c1->op))
                        break;
            blklength_(b) -= ncommon; blklength_(b1) -= ncommon;
            blkcode_(b) += ncommon; blkcode_(b1) += ncommon;
            blkstacki_(b) = blkstacki_(b1) = adjusted_stack_size(s, commonp, ncommon);
        }
        /* backward branches have priority over conditional execution */
        if (b != 0 && block_coded(b))
        {   if (b1 == 0 || !block_coded(b1) || blknest_(b) > blknest_(b1)) {
                show_head(p, Q_NEGATE(cond));
                show_branch_instruction(J_B + Q_NEGATE(cond), next);
                return (next1 == way_out) ? RETLAB : next1;
            }
        }
        if (b1 != 0 && block_coded(b1))
        {   show_head(p, cond);
            show_branch_instruction(J_B + cond, next1);
            return (next == way_out) ? RETLAB : next;
        }
#ifdef TARGET_HAS_COND_EXEC
        if (!usrdbg(DBG_VAR+DBG_LINE))
        {   int condb = Bpcc_No, lcondb = Bpcc_No,
                condb1 = Bpcc_No, lcondb1 = Bpcc_No;
            if (b != 0 && !block_coded(b)) {
              condb = lcondb = conditionalizable(b, cc_includelast, CondMax_Loop);
              if (condb == Bpcc_No)
                lcondb = conditionalizable(b, 0, CondMax_Loop);
            }
            if (b1 != 0 && !block_coded(b1) && block_single_exit(b1) &&
                length((List *)blkusedfrom_(b1)) == next1_arcs) {
              condb1 = lcondb1 = block_preserves_cc(b1, cc_includelast, CondMax_Loop);
              if (condb1 == Bpcc_No)
                  lcondb1 = block_preserves_cc(b1, 0, CondMax_Loop);
            }
            if (debugging(DEBUG_CG))
                cc_msg("block %ld: next %ld (%d,%d) next1 %ld (%d,%d)\n",
                       lab_xname_(blklab_(p)),
                       lab_xname_(next), condb, lcondb,
                       lab_xname_(next1), condb1, lcondb1);
            if (condb <= CondMax_Ordinary && condb1 <= CondMax_Ordinary &&
                blknext_(b) == blknext_(b1))
            {   CommonInst *c = common_insts(b1, b);
                show_head(p, cond);
                show_n(ncommon, commonp, s);
                show_block_pair(cond, b1, b, c);
                return blknext_(b) != way_out ? blknext_(b) :
         (blkflags_(b) & blkflags_(b1) & BLK0EXIT) ? NOTALAB :
                                                     RETLAB;
            }
            {   bool show_b_cond = NO, show_b1_cond = NO,
                     include_branch = YES;

                if (lcondb <= CondMax_Ordinary && blknext_(b) == next1)
                    show_b_cond = YES, include_branch = NO;
                else if (lcondb1 <= CondMax_Ordinary && blknext_(b1) == next)
                    show_b1_cond = YES, include_branch = NO;
                else if (condb <= CondMax_Loop && condb1 <= CondMax_Loop &&
                         blknest_(b) != blknest_(b1)) {
                    if (debugging(DEBUG_CG))
                        cc_msg("nesting(b) %ld, nesting(b1) %ld\n",
                               blknest_(b), blknest_(b1));
                    if (blknest_(b) > blknest_(b1))
                        show_b_cond = YES;
                    else
                        show_b1_cond = YES;
                } else if (condb <= CondMax_Ordinary && !successor_inline(b))
                    show_b_cond = YES;
                else if (condb1 <= CondMax_Ordinary && !successor_inline(b1))
                    show_b1_cond = YES;

                if (show_b_cond)
                {   show_head(p, Q_NEGATE(cond));
                    show_n(ncommon, commonp, s);
                    show_conditional_block(Q_NEGATE(cond), b, include_branch);
                    return next1 == way_out ? RETLAB : next1;
                }
                if (show_b1_cond)
                {   show_head(p, cond);
                    show_n(ncommon, commonp, s);
                    show_conditional_block(cond, b1, include_branch);
                    return next == way_out ? RETLAB : next;
                }
            }
        }
#endif
        if (b == 0)
        {   show_head(p, Q_NEGATE(cond));
            show_branch_instruction(J_B + Q_NEGATE(cond), RETLAB);
            return (next1 == way_out) ? RETLAB : next1;
        }
        if (b1 == 0)
        {   show_head(p, cond);
            show_branch_instruction(J_B + cond, RETLAB);
            return (next == way_out) ? RETLAB : next;
        }
        if ((blkflags_(b) & BLKLIFTABLE) == lifted) {
          if ((blkflags_(b1) & BLKLIFTABLE) != lifted) {
            show_head(p, cond);
            show_n(ncommon, commonp, s);
            show_branch_instruction(J_B + cond, next1);
            return next;
          }
        } else if ((blkflags_(b1) & BLKLIFTABLE) == lifted) {
          show_head(p, Q_NEGATE(cond));
          show_n(ncommon, commonp, s);
          show_branch_instruction(J_B + Q_NEGATE(cond), next);
          return next1;
        }
#ifdef TARGET_HAS_SCCK
/* The following code checks for two blocks which each have a single    */
/* MOVK to the same register and the same successor block.              */
/* Possible wish list: 1. SCCR to set r1 to 0 or r3, or do this by      */
/* (SCCK -1; AND) if r1!=r3.  2. A macro for target_SCCK_able(n)?.      */
        if (block_single_entryexit(b) && block_single_entryexit(b1) &&
              blknext_(b) == blknext_(b1) &&
              blklength_(b) == 1 && blklength_(b1) == 1)
        {   Icode *c = blkcode_(b), *c1 = blkcode_(b1);
/* The next test: really remove_noops() should remove J_DEADBITS for    */
/* loopopt vars which are removed.  Also note that equality is that of  */
/* virtregs, not real regs, but this is OK since both vregs are live.   */
            if ((c->op & ~J_DEAD_R2) == J_MOVK &&
                (c1->op & ~J_DEAD_R2) == J_MOVK && c->r1.r == c1->r1.r)
            {   Icode ic;
                if (c->r3.i == 0)
                {   INIT_IC (ic, J_SCCK+cond);
                    ic.r1 = c->r1;
                    ic.r3 = c1->r3;
                    show_head(p, cond);
                    expand_jop_macro(&ic);
                }
                else if (c1->r3.i == 0)
                {   INIT_IC (ic, J_SCCK+Q_NEGATE(cond));
                    ic.r1 = c->r1;
                    ic.r3 = c->r3;
                    show_head(p, Q_NEGATE(cond));
                    expand_jop_macro(&ic);
                }
/* This hits cases like x?4:5. It probably saves space (BC;MOVK;B;MOVK) */
/* vs (SCC;ADDK) and often time too.                                    */
                else
                {   INIT_IC (ic, J_SCCK+cond);
                    show_head(p, cond);
                    ic.r1 = c->r1;
                    ic.r3 = c1->r3.i - c->r3.i;
                    expand_jop_macro(&ic);
                    ic.op = J_ADDK;
                    ic.r1 = ic.r2 = c->r1;
                    ic.r3 = c->r3;
                    expand_jop_macro(&ic);
                }
/* The next line is unfortunate: we have to do this to avoid the        */
/* block getting spuriously displayed again later.  It therefore        */
/* requires the block_single_entryexit() condition.                     */
                blkflags_(b) |= BLKCODED, blkflags_(b1) |= BLKCODED;
                return blknext_(b) == way_out ? RETLAB : blknext_(b);
            }
/* Other cases worth searching for?                                     */
        }
#endif
        /*
         * Hack by RCC 24/02/88.  If both the destinations are not yet coded,
         * and one of them is the block we would code next, it can pay to do
         * the unconditional branch to the earlier one.
         *
         * There ought to be a quicker way to find out which of the
         * destinations is likely to be coded first.
         */
        {   BlockHead *x = b; /* unconditional branch destination */
            do {
                x = blkdown_(x);
                if (x == NULL) /* conditional dest is after uncond dest: swap */
                {   show_head(p, Q_NEGATE(cond));
                    show_n(ncommon, commonp, s);
                    show_branch_instruction(J_B + Q_NEGATE(cond), next);
                    return (is_exit_label(next1)) ? RETLAB : next1;
                }
            } while (x != b1);
        }

/* Here we drop through to the ordinary simple case                      */
        if (blknext_(b1) == next && ncommon == 0)
        {   show_head(p, Q_NEGATE(cond));
            show_branch_instruction(J_B + Q_NEGATE(cond), next);
            return next1;
        }
        show_head(p, cond);
        show_n(ncommon, commonp, s);
        show_branch_instruction(J_B + cond, next1);
        return next;
    }
}
#endif /* TARGET_IS_NULL */

static void refblock(LabelNumber *ll, BlockHead *from, BlockList *reuse)
{
    if (!is_exit_label(ll))
    {   BlockList *bl;
        procflags |= blkflags_(ll->block);
/* I make, in the blkusedfrom_() entry in b, a list of all blocks that   */
/* reference it. This list will be used when cross-jump optimizing.      */
/* NB the top block gets a NULL in its used-from list. I will only allow */
/* an ancestor to appear once in blkusedfrom_() even if there are many   */
/* routes (e.g. because of switchon tables) from one block to another.   */
        for (bl = blkusedfrom_(ll->block); bl != NULL; bl = bl->blklstcdr)
            if (bl->blklstcar == from) return;
        if (reuse == NULL) reuse = (BlockList*) BindAlloc(sizeof(BlockList));
        reuse->blklstcar = from;
        reuse->blklstcdr = blkusedfrom_(ll->block);
        blkusedfrom_(ll->block) = reuse;
    }
/*     else syserr("refblock");  really happens  -- why? */
}

#ifndef TARGET_IS_NULL

static BlockList *unrefblock(BlockHead *ll, BlockHead *from)
/* At present block ll has from recorded as one of its ancestors - kill this */
/* Return the dead cell for refblock().                                      */
{
    BlockList **lvbl = &(blkusedfrom_(ll));
    BlockList *bl;
    while ((bl = *lvbl) != NULL)
        if (bl->blklstcar == from)
        {   *lvbl = bl->blklstcdr;
            return bl;
        }
        else lvbl = &(bl->blklstcdr);
    syserr(syserr_unrefblock);
    return 0;
}

#endif

static void setstackoffset(Binder *b)
{  /* real stack variable -- change scope to stack offset */
    bindstg_(b) &= ~b_bindaddrlist,
    bindaddr_(b) = BINDADDR_LOC | size_of_binders(bindbl_(b));
}

static int32 remove_noops(Icode *c, int32 len)
{ int32 i;
  /* besides normalising noops to J_NOOP, the following code also turns */
  /* J_SETSPGOTO into J_SETSP - essentially a 2nd pass for goto/labels. */
  /* It also turns the addresses of locals to 'stack' form from         */
  /* environment form, thus completing auto and register allocation.    */
  /* Ultimately we should remove all _STACKREF jopcodes here too. ???   */
  /* J_NOOP's are now completely removed.                               */

  for (i=0;i<len;i++)
  { J_OPCODE op = c[i].op;
    if (uses_stack(op))
    {   Binder *bb = c[i].r3.b;
        if (bindstg_(bb) & b_bindaddrlist)
            setstackoffset(bb);
        else if (bindstg_(bb) & b_pseudonym) {
            Binder *b = bindsuper_(bb)->binder;
            if (bindstg_(b) & b_bindaddrlist) setstackoffset(b);
            bindstg_(bb) &= ~b_pseudonym;
            bindaddr_(bb) = bindaddr_(b);
        }
        if (target_stack_moves_once &&
            (bindaddr_(bb) & BINDADDR_MASK) == BINDADDR_NEWARG)
        {   /* Convert an 'actual in new frame' address into a local.   */
            /* AM, Nov89: this code is somewhat in flux.                */
            unsigned32 m = bindaddr_(bb) & ~BINDADDR_MASK;
/* @@@ see health warning in expand_jop_macro() if NARGREGS != 0.       */
            if (m < 4*NARGREGS)
                cc_warn(warn_untrustable, currentfunction.symstr); /* syserr() */
            bindaddr_(bb) = BINDADDR_LOC |
                                  (greatest_stackdepth - (m - 4*NARGREGS));
        }
    }

    switch (op & J_TABLE_BITS)
    {
#if defined(ARM_INLINE_ASSEMBLER) || defined(THUMB_INLINE_ASSEMBLER)
case J_BL:
        Inline_RealUse(c[i].r1.b);
        break;
#endif
case J_CALLK:
        Inline_RealUse(c[i].r3.b);
        /* and fall through */
case J_OPSYSK:  /* The 'call can be optimised out' info has now passed its
                   'use by' date */

case J_CALLR: c[i].r2.i &= ~K_PURE; break;

case J_SETSPGOTO:
        c[i].r2.i = size_of_binders(c[i].r2.bl);
        { /* The block this branch is to may have disappeared (because it was
           * empty).  If so, the scan to turn bind lists to frame sizes won't
           * have processed it.  We COULD look for SETSPGOTOs in branch_chain,
           * but that seems like overkill.  Instead, blocks which have had
           * their bind lists converted to a frame size are marked.
           */
            BlockHead *b = (c[i].r3.l)->block;
            c[i].r3.i = (blkflags_(b) & BLKSTACKI) ?
                          blkstacki_(b) :
                          size_of_binders(blkstack_(b));
        }
        c[i].op = J_SETSP;
        i--; break;                                         /* retry */
/*case J_SETSPENV:*/     /* already removed */
case J_SETSP:
        if (c[i].r2.i == c[i].r3.i) c[i].op = J_NOOP;
        break;
case J_LDRV: case J_LDRLV: case J_LDRFV: case J_LDRDV:
case J_STRV: case J_STRLV: case J_STRFV: case J_STRDV:
        {   VRegnum r1 = c[i].r1.r;
            Binder *bb = c[i].r3.b;
            VRegnum r3 = bindxx_(bb);
            if (r3 != GAP && isany_realreg_(register_number(r3)))
            {
                if (register_number(r1) == register_number(r3))
                    c[i].op = J_NOOP;
                else if (loads_r1(op))
                {   /* LDRV can have J_DEAD_R3 set */
                    c[i].op = J_XtoY(op&~(J_ALIGNMENT|J_BASEALIGN4), J_LDRV, J_MOVR);
                    c[i].r1.r = r1;
                    c[i].r2.r = GAP;
                    c[i].r3.r = r3;
                }
                else
                {
                    c [i].op = J_XtoY(op&~(J_DEADBITS|J_ALIGNMENT|J_BASEALIGN4), J_STRV, J_MOVR) |
                               (op & J_DEAD_R1 ? J_DEAD_R3 : 0);
                    c[i].r1.r = r3;
                    c[i].r2.r = GAP;
                    c[i].r3.r = r1;
                    /* but STRxV may have J_DEAD_R1, which we need to take care
                       not to discard in turning it into a MOV.
                     */
                }
            }
            else bindxx_(bb) = GAP;
        }
        break;
case J_LDRV1: case J_LDRLV1: case J_LDRFV1:case J_LDRDV1:
        /* as LDRV but always uses the stack value. Used at head of fn   */
        /* Should only be used to load from +ve offset from FP.          */
        /* Except that leaf procedures may not have set up FP!           */
        {   VRegnum r1 = c[i].r1.r;
            if (!isany_realreg_(register_number(r1)))
                c[i].op = J_NOOP;  /* Ignore unless this var got a real reg */
        }
        break;
case J_CMPK:                       /* I.e. the pseudo_uses_r1() ops      */
/* Note that if the r1 field holds a real register then the opcode       */
/* should be treated as a comparison against that.                       */
        {   VRegnum r1 = c[i].r1.r;
            VRegnum r2 = c[i].r2.r;
            /* Fix up deadbits (WGD) */
            J_OPCODE newop = (op&~(J_DEAD_R1|J_DEAD_R3)) ^ (J_CMPK ^ J_CMPR);
            if (op&J_DEAD_R1) newop |= J_DEAD_R3;
            if (r1!=GAP && isany_realreg_(register_number(r1)))
            {   c[i].op = newop;
                c[i].r1.r = GAP;
                c[i].r2.r = r2;
                c[i].r3.r = r1;
            }
            else
            {
                c[i].r1.r = GAP;/* normalise for cross jumping */
                c[i].op &= ~J_DEAD_R1;
            }
        }
        break;
case J_STRING:
        if (HasFeature(Feature_WRStrLits))
            procflags |= PROC_USESADCONS;
        break;
case J_CASEBRANCH:
        procflags |= PROC_CASEBRANCH;
        break;
case J_ADCOND:
case J_ADCONF:
case J_ADCONLL:
#ifdef TARGET_FP_LITS_FROM_MEMORY
        procflags |= PROC_USESADCONS;
#endif
        goto MaybeLoopOptRef;
/* the next three cases deal with lifting adcons/constants out of loops */
case J_ADCON:
        {   Binder *b = c[i].r3.b;
            if (bindstg_(b) & b_fnconst) Inline_RealUse(b);
            if (!(bindstg_(b) & u_constdata)) procflags |= PROC_USESADCONS;
        }
        /* and fall through */
MaybeLoopOptRef:
case J_ADCONV:
case J_MOVK:                       /* I.e. the pseudo_uses_r2() ops      */
/* r1 may still be a virtual register (corresponding to an optimisation  */
/* that has been spilled because of lack of real registers). In that     */
/* case I can just ignore this instruction.                              */
        {   VRegnum r1 = c[i].r1.r;
            if (isany_realreg_(register_number(r1)))
            {    VRegnum r2 = c[i].r2.r;
                 J_OPCODE newop = (op&J_DEAD_R2) ? J_MOVR|J_DEAD_R3 : J_MOVR;
/* The following funny treatment of MOVK helps loop optimisation.        */
/* If the r2 field is a real register (neither GAP nor an unallocated    */
/* virtual register) I can turn this into a MOVR r1,r2 instruction.      */
/* AM: (because loopopt.c has inserted a real register)                  */
                if (r2!=GAP && isany_realreg_(register_number(r2)))
                {   if (register_number(r1) != register_number(r2))
                    {   c[i].op = newop;
                        c[i].r1.r = r1;
                        c[i].r2.r = GAP;
                        c[i].r3.r = r2;
                    }
                    else c[i].op = J_NOOP;
                }
                else c[i].r2.r = GAP;/* normalise for cross jumping */
            }
            else c[i].op = J_NOOP;
            c[i].op &= ~J_DEAD_R2;
        }
        break;
/* AM: there seems no rationale behind which insts have the realreg test! */
case J_MOVR:
case J_MOVDR:
case J_MOVFR:
#ifdef TARGET_IS_ARM                         /* see regalloc.c, armgen.c */
case J_MOVFDR:                               /* see regalloc.c, armgen.c */
#endif
        /* optimize away moves from a register to itself.                */
        /* Also lose moves into virtual registers (which may be a side-  */
        /* effect of the optimiser trying to allocate local vars to regs */
        if (!isany_realreg_(register_number(c[i].r1.r)) ||
            register_number(c[i].r1.r)==register_number(c[i].r3.r))
                c[i].op = J_NOOP;
        break;
case J_MOVIFR:
case J_MOVIDR:
        if (!isany_realreg_(register_number(c[i].r1.r)))
            c[i].op = J_NOOP;
        break;
case J_INIT:
case J_INITF:
case J_INITD:
/* These will be left if there is a potentially uninitialized variable   */
case J_NOOP:
/* Flatten condition mask if there was one */
#ifndef TARGET_GEN_NEEDS_VOLATILE_INFO
case J_USE:
case J_USEF:
case J_USED:
case J_VSTORE:/* @@@ AM thinks VSTORE is a bit in a JOP store, not an opcode */
#endif
/* These help ensure that references to volatile things are not          */
/* optimized out of existence                                            */
/* The local code generator needs them for similar reasons, so not       */
/* optimised out                                                         */
        c[i].op = J_NOOP;
        break;
default:
        break;
    }
  }
  { int32 n;
    for (n = i = 0; i < len; i++)
/*
 * The next line exhibits a degree of extreme (unreasonable) caution - it
 * tests i!=n to prevent a structure assignment between overlapping structs
 * even in the case thet the overlap is total.  ANSI would permit the test
 * to be missed out but we are super-conservative!
 */
        if (c[i].op != J_NOOP)
        {   if (i != n) c[n] = c[i];
            n++;
        }
    return n;
  }
}

#ifndef TARGET_IS_NULL

/* Cross jumping optimisation routines:  note that cross jumping is here   */
/* implemented as a rooted (in way_out) tree isomorphism problem.          */
/* The tree is the backward chains of blocks in blkusedfrom_().            */
/* J_TAILCALLKs (blocks marked with BLK0EXIT) are also predecessors of     */
/* way_out, so now handled properly.                                       */
/* This means that (inter alia) it can never identify loops.               */
/* The full graph isomorphism problem is much more expensive and probably  */
/* does not gain significantly more in real code.  We do not intend to     */
/* change this implementation in the near future!                          */
/* Note that handling conditional exits (i.e. DAG isomorphism) is          */
/* probably not much harder -- see comments below "only merge if..."       */

static bool identify_blocks(BlockHead *x1, BlockHead *x2, BlockHead *q)
{
/* blocks x1 and x2 have identical contents - redirect all references to   */
/* x2 so that they point to x1.  q is the only successor of both x1 and x2 */
/* x2 is not the top block (i.e. the place where the procedure will be     */
/* entered), and so that is all right, isn't it.                           */
    BlockList *x2src = blkusedfrom_(x2);
    LabelNumber *l1 = blklab_(x1), *l2 = blklab_(x2);
    bool maybenewemptyblock = YES;
    /* first delete x2 from the ancestors of q and kill x2 then swing the  */
    /* chain of ancestors of x2 to x1.                                     */
    unrefblock(q, x2);
    blkflags_(x2) &= ~BLKALIVE;
    blkusedfrom_(x2) = (BlockList*) DUFF_ADDR; /* checks! */
    blkcode_(x2) = (Icode*) DUFF_ADDR;         /* checks! */
    while (x2src != NULL)
    {   BlockList *rplac = x2src;
        BlockHead *p = x2src->blklstcar;
        x2src = x2src->blklstcdr;
        refblock(l1, p, rplac);           /* re-use cell rplac */
        if (blkflags_(p) & BLKSWITCH)
        {   int32 i;
            LabelNumber **tab = blktable_(p);
            for (i = 0; i < blktabsize_(p); i++)
                if (tab[i] == l2) tab[i] = l1;
        }
        else
        {   /* AM: blknext_() is only valid if !BLK0EXIT & !BLKSWITCH   */
            /* NB blkflags_(p) cannot have BLK0EXIT and be an ancestor! */
            if (blknext_(p) == l2)
                blknext_(p) = l1; /* redirect main exit */
            if (blkflags_(p) & BLK2EXIT) {
                if (blknext1_(p) == l2) blknext1_(p) = l1;
                if (blknext_(p) == blknext1_(p)) maybenewemptyblock = YES;
            }
        }
    }
    return maybenewemptyblock;
}

static void truncate_block(BlockHead *x2, int32 i2, BlockHead *x1, BlockHead *p)
{
/* Here block x2 must be truncated to have new length i2, and its exit     */
/* must be rewritten as going to x1.                                       */
/* Due to the calls to truncate_block, we know that x2 has a single        */
/* successor (p) and so we only have to swing one pointer x2-->p to x1-->p */
/* However, note that p may have multiple ancestors.                       */
    blklength_(x2) = i2;
    blknext_(x2) = blklab_(x1);
    blkflags_(x2) &= ~BLK0EXIT;
    refblock(blklab_(x1), x2, unrefblock(p, x2));
}

static void zip_blocks(BlockHead *x1, int32 i1, BlockHead *x2, int32 i2, BlockHead *p)
{
    BlockHead *newbh;
    LabelNumber *lab = nextlabel();
    lab->block = newbh = newblock(lab, NULL);
    blkstacki_(newbh) = adjusted_stack_size(blkstacki_(x1), blkcode_(x1), i1);
    blklength_(newbh) = blklength_(x1) - i1;
    blkcode_(newbh) = &(blkcode_(x1)[i1]);
    blknext_(newbh) = blklab_(p);
    blkdebenv_(newbh) = blkdebenv_(x1);    /* maybe */
/* The next line is a slight lie -- e.g. not BLKCALL but does not matter */
    blkflags_(newbh) = BLKALIVE | BLKSTACKI | (blkflags_(x1) & BLK0EXIT);
    blklength_(x1) = i1;
    blknext_(x1) = lab;
    blkflags_(x1) &= ~BLK0EXIT;
    blklength_(x2) = i2;
    blknext_(x2) = lab;
    blkflags_(x2) &= ~BLK0EXIT;
    refblock(lab, x1, unrefblock(p, x1));
    refblock(lab, x2, unrefblock(p, x2));
    refblock(blklab_(p), newbh, 0);
}

static bool cross_jump_optimize(void)
{
    BlockHead *p;
    bool another_pass_needed;
    bool maybenewemptyblocks = NO;
    if (!crossjump_enabled || usrdbg(DBG_LINE+DBG_VAR)) return NO;
    do
    {   another_pass_needed = NO;
        for (p = top_block; p != NULL; p = blkdown_(p))
          if (blkflags_(p) & BLKALIVE)
          { BlockList *predecessors;
            BlockList *p1, *p2;
    restart_scanning_block_p:
            predecessors = blkusedfrom_(p);
            for (p1 = predecessors; p1!=NULL; p1 = p1->blklstcdr)
              for (p2 = p1->blklstcdr; p2!=NULL; p2 = p2->blklstcdr)
              { BlockHead *x1 = p1->blklstcar,
                           *x2 = p2->blklstcar;
                if (x1 != x2 &&     /* probably never happens, but be careful */
                    x1 != NULL &&   /* null block has nothing in common ... */
                    x2 != NULL &&   /* ... with anything */
                                    /* (null block is ancestor of top_block) */
                    /* only merge if parents' exits were simple */
                    (blkflags_(x1) & (BLKSWITCH | BLK2EXIT)) == 0 &&
                    (blkflags_(x2) & (BLKSWITCH | BLK2EXIT)) == 0)
                {   int32 ncommon = 0;
                    int32 i1 = blklength_(x1), i2 = blklength_(x2);
                    Icode *c1 = blkcode_(x1), *c2 = blkcode_(x2);
    /* Here I scan two ancestors of p from the tail-end looking for      */
    /* equivalent instructions. I only do this if the ancestors both     */
    /* have just simple exits (no branch tables or conditional jumps).   */
    /* J_NOOP's have already been removed.                               */
                    for (; i1 > 0 && i2 > 0; i1--, i2--, ncommon++)
                        if (!same_instruction(&c1[i1-1], &c2[i2-1])) break;

                    if (ncommon != 0)
                    {
                        if (i1 == 0)
                        {   if (i2 == 0)
/* At present the top block can not be an exact match for any other block  */
/* because it (and it alone) as an ENTER opcode in it. However I act with  */
/* caution here in case things change in the future.                       */
                            {   maybenewemptyblocks = (x2 != top_block) ?
                                                        identify_blocks(x1, x2, p) :
                                                        identify_blocks(x2, x1, p);
                                another_pass_needed = YES;
                            }
                            else
                            {   truncate_block(x2, i2, x1, p);
                                another_pass_needed = YES;
                            }
                        }
                        else if (i2 == 0)
                        {   truncate_block(x1, i1, x2, p);
                            another_pass_needed = YES;
                        }
                        else
                        {   zip_blocks(x1, i1, x2, i2, p);
                            another_pass_needed = YES;  /* ????? needed in allcases? */
                        }
/* The above procedures may well alter the chaining in blkusedfrom_(p),    */
/* the ancestor list for p, so to                                          */
/* keep things as simple as I can (albeit with some loss of speed, but     */
/* that only when optimisations are actually being found), I leap right    */
/* out from the middle of a load of nested loops here and start scanning   */
/* the ancestors of p all over again. I think that pretty well any other   */
/* construction here will really be a stylistically ugly as the goto that  */
/* I use - maybe I could demand that identify_blocks() etc guaranteed not  */
/* to have bad interactions with the iteration over ancestor-pairs, but    */
/* that seems like the wilfull design of fragile code.                     */
                        goto restart_scanning_block_p;
                    }
                }
              }
          }
    } while (another_pass_needed);
    if (debugging(DEBUG_CG)) {
        cc_msg("After crossjump optimisation (branch-chain %srequested)",
               maybenewemptyblocks ? "" : "not ");
        flowgraf_print("", YES);
    }
    return maybenewemptyblocks;
}

#endif /* TARGET_IS_NULL */

static void kill_unreachable_blocks(void)
{
    BlockHead *b = top_block;
    blkflags_(b) &= ~BLKALIVE;  /* top_block MUST have been alive */
    while (b != bottom_block)
    {   BlockHead *next = blkdown_(b);
        int32 ff = blkflags_(next);     /* only bottom_block has empty down */
        if (ff & BLKALIVE)
        {   blkflags_(next) = ff & ~BLKALIVE;
            b = next;
        }
        else if (usrdbg(DBG_LINE+DBG_VAR) && !usrdbg(DBG_OPT_DEAD))
            b = next;
        else if (next == bottom_block)  /* bottom_block was unreachable */
        {   blkdown_(b) = NULL;
            bottom_block = b;
        }
        else                            /* patch out a dead block */
        {   next = blkdown_(next);
            blkdown_(b) = next;
            blkup_(next) = b;
        }
    }
}

/* exported ... */

void lose_dead_code(void)
{   /* exported to cg.c to call before register allocation   */
/* cf branch_chain in flowgraf.c, which will be needed later */
/* AM: think about amalgamating this with branch chain()     */
    (void)branch_chain(blklab_(top_block), 0);
    kill_unreachable_blocks(); /* (just to unset BLKALIVE if usrdbg(..)) */
}

#ifdef TARGET_HAS_SAVE

/* If the target local codegenerator has separable entry to function (J_ENTER)
 * and save callee-save registers & setup frame (J_SAVE) operations, try to
 * move the J_SAVE into the body of the function past conditional exits (to give
 * faster fast exit paths). This is done after register allocation, so it may
 * fail when better allocation would allow it to succeed.
 */

typedef struct RAList RAList;
struct RAList {
  RAList *cdr;
  /* RealRegister */ IPtr r1, r2;
  /* int32 */ IPtr argregdead;
};
#define mkRAList(cdr, r1, r2, dead) (RAList *)syn_list4(cdr, r1, r2, dead)

#define BlockList_NDelete(b, bl) ((BlockList *)generic_ndelete((IPtr)b, (List *)bl))

static BlockList *BlockList_Insert(BlockHead *b, BlockList *bl) {
  return (generic_member((IPtr)b, (List *)bl)) ? bl : mkBlockList(bl, b);
}

static BlockList *BlockList_Union(BlockList *bl1, BlockList *bl2) {
  for (; bl2 != NULL; bl2 = bl2->blklstcdr)
    bl1 = BlockList_Insert(bl2->blklstcar, bl1);
  return bl1;
}


static BlockList *BlockList_Difference(BlockList *bl1, BlockList *bl2) {
  for (; bl2 != NULL; bl2 = bl2->blklstcdr)
    bl1 = BlockList_NDelete(bl2->blklstcar, bl1);
  return bl1;
}

static RealRegister ArgRegister(RealRegister r, RAList *ra) {
  r = register_number(r);
  for (; ra != NULL; ra = cdr_(ra))
    if (r == ra->r1)
      return ra->r2;
  return r;
}

static RealRegister VarRegister(RealRegister r, RAList *ra) {
  r = register_number(r);
  for (; ra != NULL; ra = cdr_(ra))
    if (r == ra->r2)
      return ra->argregdead ? ra->r1 : r;
  return r;
}

static BlockHead *ts_blockbetween(BlockHead *before, BlockHead *after) {
/* Insert a block between <before> and <after>, copying information from
 * <before>. Keep blkusedfrom_ fields up to date (insertblockbetween doesn't
 * because it's also used from CSE before the fields are set up).
 */
  BlockHead *b = insertblockbetween(before, after, YES);
  blkstacki_(b) = blkstacki_(before);
  blkdebenv_(b) = blkdebenv_(before);
  blkexenv_(b) = blkexenv_(before);
  blkflags_(b) = blkflags_(before);
  refblock(blklab_(after), b, unrefblock(after, before));
  refblock(blklab_(b), before, NULL);
  return b;
}

static void try_shrinkwrap(void) {
  BlockHead *top = top_block,
            *next = blknext_(top)->block;
  BlockList *lifted = NULL;

  int32 argdesc;
  RAList *copies = NULL;
  bool changed = NO, oktolift = YES;
  BlockHead *saveblock = ts_blockbetween(top, next);
  { /* Introduce the SAVE jopcode, and set up a translation between argument
     * registers and the VRegisters to which they've been moved.
     */
    Icode *newic = (Icode *)BindAlloc(sizeof(Icode));
    Icode *ic = blkcode_(top);
    int32 n = blklength_(top);
    *newic = *ic;
    ic->op = J_SAVE;
    argdesc = ic->r3.i;
    blkcode_(saveblock) = ic; blklength_(saveblock) = n;
    blkcode_(top) = newic; blklength_(top) = 1;
    for (; --n >= 0; ic++)
      if ((ic->op & J_TABLE_BITS) == J_MOVR)
        copies = mkRAList(copies, register_number(ic->r1.r),
                                  register_number(ic->r3.r),
                                  ic->op & J_DEAD_R3);
  }
  if (!(procauxflags & bitoffnaux_(s_irq)) &&
      !(var_cc_private_flags & 262144) &&
      !usrdbg(DBG_ANY) &&
      block_single_entry(next)) {
    /* Attempt to find a set of blocks after <saveblock> which can be moved
     * before it. The set must contain at least one return (or there's no point
     * to the motion), may have predecessors only in the set plus <saveblock>,
     * and may have successors only in the set plus returns plus one other
     * block (which will become the successor of <saveblock>). Blocks in the set
     * may contain no calls, nor write any callee-save register nor read any
     * register set up in <saveblock> (except those which are copies of argument
     * registers). In addition, blocks which are not single-exit with successor
     * way_out may write no argument register.
     */
    BlockHead *p = top;
    RealRegSet maynotwrite, maynotread, argregset, resregset, calleesaveregset;
    Icode *ic = blkcode_(saveblock);
    int32 i, n = blklength_(saveblock);
    memclr(&maynotread, sizeof(RealRegSet));
    memclr(&calleesaveregset, sizeof(RealRegSet));
    memclr(&argregset, sizeof(RealRegSet));
    memclr(&resregset, sizeof(RealRegSet));
    for (i = 0; i < k_intregs_(argdesc); i++)
        augment_RealRegSet(&argregset, R_P1+i);
    for (i = 0; i < k_fltregs_(argdesc); i++)
      augment_RealRegSet(&argregset, R_FP1+i);
    for (i = 0; i < NVARREGS; i++)
      augment_RealRegSet(&calleesaveregset, R_V1+i);
    for (i = 0; i < NFLTVARREGS; i++)
      augment_RealRegSet(&calleesaveregset, R_FV1+i);
#ifdef TARGET_IS_ARM
    /* Not preserved by J_SAVE for some calling standards. Holds value on
       function entry for reentrant APCS. FixedRegisterUse should tell us
       this.
     */
    if (config & CONFIG_REENTRANT_CODE)
        augment_RealRegSet(&calleesaveregset, R_IP);
#endif
#ifndef TARGET_STACKS_LINK
    augment_RealRegSet(&calleesaveregset, R_LR);
#endif
    if (currentfunction.baseresultreg != GAP) {
      augment_RealRegSet(&resregset, currentfunction.baseresultreg);
      for (i = 1; i < currentfunction.nresultregs; i++)
        augment_RealRegSet(&resregset, currentfunction.baseresultreg+i);
    }
    for (; --n >= 0; ic++) {
    /* Registers set in <saveblock> won't be accessible to code moved before it.
     * I think these can actually only be registers to which arguments are
     * copied, so this is redundant (they'll be translated back to the argument
     * register numbers via the <copies> list), but this code is cautious in case
     * anything else gets appended to the block.
     */
      if (loads_r1(ic->op)) augment_RealRegSet(&maynotread, register_number(ic->r1.r));
      if (loads_r2(ic->op)) augment_RealRegSet(&maynotread, register_number(ic->r2.r));
      if (loads_r1(ic->op) && member_RealRegSet(&resregset, register_number(ic->r1.r))) {
        oktolift = NO;
        break;
      }
      if (loads_r2(ic->op) && member_RealRegSet(&resregset, register_number(ic->r2.r))) {
        oktolift = NO;
        break;
      }
    }

    for (; p != NULL; p = blkdown_(p))
      blkflags_(p) &= ~BLKLIFTABLE;

    if (oktolift) for (p = next; p != NULL; p = blkdown_(p)) {
      if (blkflags_(p) & (BLKCALL | BLKSWITCH)) {
        break;
      } else if (p != way_out->block && (blkflags_(p) & BLKALIVE)) {
      /* Ignore blocks removed by cross-jumping (not BLKALIVE). Cross-jumping
       * also may add blocks after the way_out block, hence the explicit test
       * for it (it is the only block for which blknext_() doesn't label a real
       * block).
       */
        bool terminal = !(blkflags_(p) & BLK2EXIT) && blknext_(p) == way_out;
        RealRegSet mnr = maynotread;
        if (terminal)
          maynotwrite = calleesaveregset;
        else
          union_RealRegSet(&maynotwrite, &argregset, &calleesaveregset);
        ic = blkcode_(p); n = blklength_(p);
        for (; --n >= 0; ic++) {
          J_OPCODE op = ic->op;
          VRegInt r1 = ic->r1, r2 = ic->r2, r3 = ic->r3, r4 = ic->r4;
          RealRegSet corrupt;
          RealRegUse reg;
          if ((op == J_TAILCALLK || op == J_TAILCALLR) &&
              k_argwords_(r2.i) > 0)
          /* The arguments may come either from code in blocks being considered
           * for lifting, or from copies performed on entry (which if the block
           * is lifted, won't be executed). To handle this properly, we need to
           * able to distinguish the two cases and in the latter replicate the
           * moves here. It's a lot of work to do this in general, so our first
           * attempt is not to bother.
           */
            break;
          RealRegisterUse(ic, &reg);
          union_RealRegSet(&corrupt, &reg.c_in, &reg.c_out);
          if (uses_r1(op)) r1.r = ArgRegister(r1.r, copies);
          if (uses_r2(op)) r2.r = ArgRegister(r2.r, copies);
          if (uses_r3(op)) r3.r = ArgRegister(r3.r, copies);
          if (uses_r4(op)) r4.r = ArgRegister(r4.r, copies);
          if (uses_stack(op) ||
              intersect_RealRegSet(&corrupt, &maynotwrite, &corrupt) ||
              (loads_r1(op) && member_RealRegSet(&maynotwrite, r1.r)) ||
              (loads_r2(op) && member_RealRegSet(&maynotwrite, r2.r)) ||
              (reads_r1(op) && member_RealRegSet(&mnr, r1.r)) ||
              (reads_r2(op) && member_RealRegSet(&mnr, r2.r)) ||
              (reads_r3(op) && member_RealRegSet(&mnr, r3.r)) ||
              (reads_r4(op) && member_RealRegSet(&mnr, r4.r)))
            break;

          if (terminal) {
          /* exit paths are allowed to write result registers, but once written
           * they may not be read (mechanism defect: I can't distinguish between
           * reading the VReg copy, which definitely isn't allowed, and reading
           * the value written here, which would be OK. I doubt it matters.
           */
            if (loads_r1(op) && member_RealRegSet(&argregset, r1.r))
              augment_RealRegSet(&mnr, r1.r);
            if (loads_r2(op) && member_RealRegSet(&argregset, r2.r))
              augment_RealRegSet(&mnr, r2.r);
          }
        }
        if (n >= 0) break;
        blkflags_(p) |= BLKLIFTABLE;
      }
    }

    if (p != NULL) {
    /* (p == NULL means the SAVE is going to have no effect, so there's no sense
     * trying to move code before it)
     */
      BlockList *successors = NULL,
                *predecessors = NULL,
                *liftable = NULL;
      bool atleastoneexit = NO;
      for (p = next; p != NULL; p = blkdown_(p))
        if (blkflags_(p) & BLKLIFTABLE) {
          liftable = BlockList_Insert(p, liftable);
          if (blknext_(p) == way_out)
            atleastoneexit = YES;
          else
            successors = BlockList_Insert(blknext_(p)->block, successors);
          if (blkflags_(p) & BLK2EXIT) {
            if (blknext1_(p) == way_out)
              atleastoneexit = YES;
            else
              successors = BlockList_Insert(blknext1_(p)->block, successors);
          }
          predecessors = BlockList_Union(predecessors, blkusedfrom_(p));
        }

      predecessors = BlockList_Difference(predecessors, liftable);
      successors = BlockList_Difference(successors, liftable);

      if (atleastoneexit &&
          predecessors != NULL && predecessors->blklstcdr == NULL &&
          predecessors->blklstcar == saveblock &&
          /* really, <predecessors> must include <saveblock>, so the checks
           * besides that its length is 1 are redundant
           */
          successors != NULL && successors->blklstcdr == NULL) {
        /* The set <liftable> can safely be moved before <saveblock>, with all
         * occurrences of callee-save registers replaced by the corresponding
         * argument register.
         */
        BlockList *bl;
        BlockHead *insertbefore = successors->blklstcar;
        LabelNumber *l_saveblock = blklab_(saveblock),
                    *l_insertbefore = blklab_(insertbefore),
                    *l_inserted = blklab_(next);
        int32 s1 = blkstacki_(next),
              s2 = blkstacki_(insertbefore);
        lifted = liftable;
        blknext_(top) = blklab_(next);
        refblock(l_inserted, top, unrefblock(saveblock, top));
        blknext_(saveblock) = l_insertbefore;
        refblock(l_insertbefore, saveblock, unrefblock(next, saveblock));
        for (bl = liftable; bl != NULL; bl = bl->blklstcdr) {
          BlockHead *b = bl->blklstcar;
          Icode *ic_in = blkcode_(b),
                *ic_out = ic_in;
          n = blklength_(b);
          blkstacki_(b) = 0;
          for (; --n >= 0; ic_in++)
          {
            J_OPCODE op = ic_in->op;
            if (ic_in != ic_out) *ic_out = *ic_in;
            if (reads_r1(op)) ic_out->r1.r = ArgRegister(ic_out->r1.r, copies);
            if (reads_r2(op)) ic_out->r2.r = ArgRegister(ic_out->r2.r, copies);
            if (reads_r3(op)) ic_out->r3.r = ArgRegister(ic_out->r3.r, copies);
            if (reads_r4(op)) ic_out->r4.r = ArgRegister(ic_out->r4.r, copies);
            if (op != J_SETSP) ic_out++;
            else
              blklength_(b)--;
          }
          if (blknext_(b) == l_insertbefore) {
            blknext_(b) = l_saveblock;
            refblock(l_saveblock, b, unrefblock(insertbefore, b));
          }
          if ((blkflags_(b) & BLK2EXIT) && blknext1_(b) == l_insertbefore) {
            blknext1_(b) = l_saveblock;
            refblock(l_saveblock, b, unrefblock(insertbefore, b));
          }
        }
        if (s1 != s2) {
          BlockHead *b = ts_blockbetween(saveblock, insertbefore);
          Icode *ic = (Icode *)BindAlloc(sizeof(Icode));
          INIT_IC(*ic, J_SETSP);
          ic->r2.i = s1; ic->r3.i = s2;
          blkstacki_(b) = s1; blklength_(b) = 1; blkcode_(b) = ic;
        }
        changed = YES;
      }
    }
    if (lifted == NULL)
    for (p = next; p != NULL; p = blkdown_(p))
      blkflags_(p) &= ~BLKLIFTABLE;
    else
      blkflags_(top_block) |= BLKLIFTABLE;

  }
  /* Now follows code to turn direct tail recursion into a loop. Of course, the
   * call has already turned into a tailcall, but we can do better by omitting
   * the need to restore saved registers from the frame here and by branching to
   * after the save instruction. We may be able to do better still by writing
   * arguments to VRegisters not the argument registers and skipping the copy
   * from argument to VRegister on entry. This could be done as source-to-source
   * translation, but this would miss calls which become tail recursive only by
   * dead code elimination, and would preclude shifting fast exit code before
   * the save.
   * Code moved before the save must be duplicated here, so we limit severely
   * what it can be (just one block permitted: a number of jopcodes might be
   * more sensible).
   */

  if (!(var_cc_private_flags & 524288) &&
#ifdef TARGET_FP_ARGS_IN_FP_REGS
      k_fltregs_(argdesc) == 0 &&
#endif
      length((List *)copies) == k_argwords_(argdesc) &&
      (lifted == NULL || lifted->blklstcdr == NULL)) {
    /* First create places for tail-recursion branches to go to: one just after
     * the SAVE jopcode, and one after all copying of argument registers to
     * VRegisters which leave the argument register dead. For the second case,
     * the copies need to be reordered in general. (The two destinations are
     * tailreclab_argsinaregs and tailreclab_argsinvregs; the second may be
     * null).
     */
    int32 nargs = k_argwords_(argdesc);
    BlockList *exits = blkusedfrom_(way_out->block);
    LabelNumber *tailreclab_argsinaregs = NULL,
                *tailreclab_argsinvregs = NULL;
    BlockHead *inserted = lifted == NULL ? NULL :
                                           lifted->blklstcar;
    BlockHead *next = blknext_(saveblock)->block;
    if (blklength_(saveblock) == 1)
      tailreclab_argsinaregs = blklab_(next);
    else {
      BlockHead *p = ts_blockbetween(saveblock, next);
      Icode *ic = blkcode_(saveblock); int32 n = blklength_(saveblock);
      tailreclab_argsinaregs = blklab_(p);
      blkcode_(p) = ++ic; blklength_(p) = --n;
      blklength_(saveblock) = 1;
      { int32 ndead = 0;
        RAList *cp = copies;
        for (; cp != NULL; cp = cdr_(cp))
          if (cp->argregdead) ndead++;
        if (ndead > 0) {
          if (ndead == n)
            tailreclab_argsinvregs = blklab_(next);
          else {
            BlockHead *q = ts_blockbetween(p, next);
            tailreclab_argsinvregs = blklab_(q);
            { int32 i, j;
              for (cp = copies, i = j = n; --i >= 0; ) {
                if ((ic[i].op & J_TABLE_BITS) == J_MOVR &&
                    register_number(ic[i].r1.r) == cp->r1 &&
                    ic[i].r3.r == cp->r2) {
                  if (!cp->argregdead) {
                    if (--j != i) ic[j] = ic[i];
                  }
                  cp = cdr_(cp);
                } else if (--j != i)
                  ic[j] = ic[i];
              }
              copies = (RAList *)dreverse((List *)copies);
              for (cp = copies, i = 0; cp != NULL; cp = cdr_(cp))
                if (cp->argregdead) {
                  ic[i].op = J_MOVR + J_DEAD_R3;
                  ic[i].r1.r = cp->r1; ic[i].r2.r = GAP; ic[i].r3.r = cp->r2;
                  i++;
                }
              blkcode_(q) = ic + ndead; blklength_(q) = n - ndead;
              blklength_(p) = ndead;
              nargs = ndead;
            }
          }
        }
      }
    }
    for (; exits != NULL; exits = exits->blklstcdr) {
      BlockHead *b = exits->blklstcar;
      Icode *ic = blkcode_(b);
      int32 i, n = blklength_(b);
      if (n > 0 &&
          (ic[n-1].op & J_TABLE_BITS) == J_TAILCALLK &&
          bindsym_(ic[n-1].r3.b) == currentfunction.symstr) {
        LabelNumber **nextp;
        LabelNumber *dest = tailreclab_argsinaregs;
        blklength_(b) = --n;
        unrefblock(way_out->block, b);
        blkflags_(b) &= ~BLK0EXIT;
        changed = YES;
        if (inserted == NULL)
          nextp = &blknext_(b);
        else {
          BlockHead *q = insertblockbetween(b, way_out->block, YES);
          size_t size = (size_t)blklength_(inserted) * sizeof(Icode);
          Icode *ic = (Icode *)BindAlloc(size);
          memcpy(ic, blkcode_(inserted), size);
          blklength_(q) = blklength_(inserted); blkcode_(q) = ic;
          blkflags_(q) = blkflags_(inserted);
          blkstacki_(q) = blkstacki_(inserted);
          blkdebenv_(q) = blkdebenv_(inserted);
          blkexenv_(q) = blkexenv_(inserted);
          if (blknext_(inserted) == way_out) {
            blknext_(q) = way_out;
            nextp = &blknext1_(q);
          } else {
            blknext1_(q) = way_out;
            nextp = &blknext_(q);
          }
          refblock(blklab_(q), b, NULL);
          refblock(way_out, q, NULL);
          b = q;
        }
        if (tailreclab_argsinvregs != NULL) {
          RealRegSet maynotread, mnr;
          RAList *ra;
          int32 na = nargs;
          memclr(&maynotread, sizeof(RealRegSet));
          for (ra = copies; ra != NULL; ra = cdr_(ra))
            if (ra->argregdead)
              augment_RealRegSet(&maynotread, ra->r1);
          mnr = maynotread;
          for (i = n; --i >= 0 && na > 0; ) {
            J_OPCODE op = ic[i].op & J_TABLE_BITS;
            VRegInt r1 = ic[i].r1, r2 = ic[i].r2, r3 = ic[i].r3, r4 = ic[i].r4;
            if (uses_r1(op)) r1.r = register_number(r1.r);
            if (uses_r2(op)) r2.r = register_number(r2.r);
            if (uses_r3(op)) r3.r = register_number(r3.r);
            if (uses_r4(op)) r4.r = register_number(r4.r);
            /* The code below only recognizes simple 2 and 3 opnd instructions.
             * This is mainly because RealRegisterUse & Corrupt are not used,
             * and in many cases substitution may not be legal (LDM with writeback,
             * MUL with clashes etc).
             * Anyway, it will be easier to do this before register allocation...
             */
            if (op == J_MOVR || op == J_ADDR || op == J_ADDK || op == J_SUBR) { /* loads_r1 = true */
              r1.r =  VarRegister(r1.r, copies);
              if (delete_RealRegSet(&maynotread, r1.r))
                na--;
            }
            else
                break; /* fix of bug - do not cross calls etc. */
            if ((reads_r1(op) && member_RealRegSet(&maynotread, r1.r)) ||
                (reads_r2(op) && member_RealRegSet(&maynotread, r2.r)) ||
                (reads_r3(op) && member_RealRegSet(&maynotread, r3.r)) ||
                (reads_r4(op) && member_RealRegSet(&maynotread, r4.r)))
              break;
          }
          if (na == 0) {
            for (; --n, nargs > 0; ) {
              J_OPCODE op = ic[n].op;
              VRegInt r1 = ic[n].r1, r2 = ic[n].r2, r3 = ic[n].r3, r4 = ic[n].r4;
              if (uses_r1(op)) r1.r = VarRegister(r1.r, copies);
              if (uses_r2(op)) r2.r = VarRegister(r2.r, copies);
              if (uses_r3(op)) r3.r = VarRegister(r3.r, copies);
              if (uses_r4(op)) r4.r = VarRegister(r4.r, copies);
              if (loads_r1(op) && delete_RealRegSet(&mnr, r1.r)) {
                ic[n].r1 = r1;
                nargs--;
              }
              if (loads_r2(op) && delete_RealRegSet(&mnr, r2.r)) {
                ic[n].r2 = r2;
                nargs--;
              }
              if (reads_r1(op) && member_RealRegSet(&mnr, r1.r)) ic[n].r1 = r1;
              if (reads_r2(op) && member_RealRegSet(&mnr, r2.r)) ic[n].r2 = r2;
              if (reads_r3(op) && member_RealRegSet(&mnr, r3.r)) ic[n].r3 = r3;
              if (reads_r4(op) && member_RealRegSet(&mnr, r4.r)) ic[n].r4 = r4;
            }
            dest = tailreclab_argsinvregs;
            if (inserted != NULL) {
              ic = blkcode_(b), n = blklength_(b);
              for (; --n >= 0; ) {
                J_OPCODE op = ic[n].op;
                if (uses_r1(op)) ic[n].r1.r = VarRegister(ic[n].r1.r, copies);
                if (uses_r2(op)) ic[n].r2.r = VarRegister(ic[n].r2.r, copies);
                if (uses_r3(op)) ic[n].r3.r = VarRegister(ic[n].r3.r, copies);
                if (uses_r4(op)) ic[n].r4.r = VarRegister(ic[n].r4.r, copies);
              }
            }
          }
        }
        *nextp = dest;
        refblock(dest, b, NULL);
      }
    }
  }
  if (debugging(DEBUG_CG) && changed)
    flowgraf_print("After shrinkwrap", YES);
}

#endif

/* These functions support generation of tables for exception handling: */
ExceptionEnv *last_exenv_started; /*only swing this mechanism into action when the exception environment changes*/
int prev_codep; /*records codep_at_exenv_start */
List* handler_entries; /*builds up a list of incompile exception handler entries */

static void add_exhandler_entry(int word)
{
  DataInit *newtail, *oldtail = get_exhandler_ht(NO);
  newtail = (DataInit *)global_list5(SU_Data, (DataInit *)0, 1,
                                     LIT_NUMBER, 4, word);
  if (oldtail == NULL)
        set_exhandler_ht(YES, newtail); /*initialise head*/
  else
      oldtail->datacdr = newtail;
  set_exhandler_ht(NO, newtail);
  set_exhandler_size(exhandler_size()+4);
}

static void add_extable_entry(int word)
{
  DataInit *newtail, *oldtail = get_extable_ht(NO);
  newtail = (DataInit *)global_list5(SU_Data, (DataInit *)0, 1,
                                     LIT_NUMBER, 4, word);
  if (oldtail == NULL)
        set_extable_ht(YES, newtail); /*initialise head*/
  else
      oldtail->datacdr = newtail;
  set_extable_ht(NO, newtail);
  set_extable_size(extable_size()+4);
}

static void localcg_startfn(void)
{
  last_exenv_started=NULL;
  prev_codep=0;/*doesn't need initialising*/
  handler_entries=NULL;
}

#define cons(car,cdr) (binder_cons2((cdr),(car)))

/* called at the end of each fn, to coalesce and flush
 * exception tables as necessary
 */
static void output_thisfn_handler_entries(List* h_entries, int lastone)
{
  if (h_entries==NULL) return;
  output_thisfn_handler_entries((List*) car_(h_entries), 0);
  /*recurse, filling up stack; would be better to reverse list explicitly*/
  {
    List* tl=(List*) cdr_(h_entries);
    int destru, offset, range_len, ensp_offset;
    IPtr handler;
    destru=car_(tl); tl=cdr_(tl);
    handler=car_(tl); tl=cdr_(tl);
    offset=car_(tl); tl=cdr_(tl);
    range_len=car_(tl);
    ensp_offset=(IPtr) cdr_(tl); /*dotted-list*/

    if (lastone) offset|= 0x80000000; /* high bit set to mark the end */

    if (debugging(DEBUG_CG))
      {
        if (destru==0)
          printf("Error: unresolved handlerblock offset to L%d\n",
                 0xffffL&((LabelNumber*)handler)->name);
        printf("Offset=%8X range-len=%8X %s=%8X %s=%8X\n",
               offset, range_len,
               (destru==1) ? "en/SP-OFFSET" : "EN/sp-offset", ensp_offset,
               (destru==1) ? "DEST/handler" : "dest/HANDLER", handler);
        if (ensp_offset!=0)
          printf("should en/sp_offset really be non-zero?\n"), ensp_offset=0;
      }
    if (destru==0) return;
    add_exhandler_entry(offset);
    add_exhandler_entry(range_len);
    add_exhandler_entry(ensp_offset);
    add_exhandler_entry(handler);
  }
}

static void add_handler_entry(int destru, IPtr handler, int prev_codep,
                              int range_len, int ensp_offset)
{
  if (range_len!=0)
    handler_entries= cons(handler_entries,
                          cons(destru,
                               cons(handler,
                                    cons(prev_codep,
                                         cons(range_len, ensp_offset)))));
}

static void output_exenv(ExceptionEnv *e)
{
  int ensp_offset, range_len = (int) codep - prev_codep;
  IPtr handler;
  if (e==NULL) return;
  if (e->type==ex_destructor)
    {
      Binder* b =e->handlers.destructee;
      /* if ( bindstg_(b) | onstack) ; give error about not being on stack*/
      ensp_offset = bindaddr_(b) & ~BINDADDR_LOC; /*offset of obj from SP. OK*/
      ensp_offset = - ensp_offset;
      handler=1; /* address of destructor function, can only determine it
                    symbolically at this time, needs fixing up by linker*/
      add_handler_entry(1, handler, prev_codep, range_len, ensp_offset);
    }
  else /* e->type must be ex_handler, ie this is a 'try' block. */
    {
      LabelNumber *l = e->handlers.henv.handlerblock;
      HandlerList *hl = e->handlers.henv.handlerlist;
      LabelNumber **table = blktable_(lab_block_(l));
      int i;
      for(i=0;i<blktabsize_(lab_block_(l));i++) /* multiple handler cases: iterate over hl */
        {
          if (debugging(DEBUG_CG)) printf("i=%d hl=%p\n", i, hl);
          handler = (IPtr)table[i];
          ensp_offset=hl->type; /*this is exception number, or 0 for "..." */
          hl=hl->cdr;
          add_handler_entry(0, handler, prev_codep, range_len, ensp_offset);
        }
    }
  if (e->cdr!=NULL) output_exenv (e->cdr);/* must do innermost ones first */
  prev_codep = codep;
}

/*called at start of each block, to see if current block is on list
 * of blocks of which we need to know codep
 */
static void walk_handler_entries(List* h_entries, BlockHead *bl)
{
  List* this_h_entry;
  if (h_entries==NULL) return;
  this_h_entry=(List*) cdr_(h_entries);
  /* printf ("this_h_entry=%X car_(this_h_entry)=%X\n", (int)this_h_entry, (int) car_(this_h_entry)); */
  if (car_(this_h_entry) == 0)/*destructor-p slot, 0=>unresolved handler*/
    {
      LabelNumber* handlerslot = (LabelNumber*) car_(cdr_(this_h_entry));

      if (handlerslot->block == bl)/*handler slot*/
        {
          car_(this_h_entry) = -1;/*destructor-p slot*/
#ifdef TARGET_IS_THUMB
          car_(cdr_(this_h_entry)) = codep;
#else
          car_(cdr_(this_h_entry)) = codep /*+4=hack*/+4;/*handler slot*/
#endif
          /* don't return; there may be more than one predecessor of this bl */
        }
    }
  walk_handler_entries((List*) car_(h_entries), bl);
}

static void localcg_startblock(BlockHead* bl)
{
  if (bl==NULL) return; /*does this ever happen?*/
  if (!(var_cc_private_flags & 128L)) return;
  walk_handler_entries(handler_entries, bl);
  if (blkexenv_(bl)==last_exenv_started)
    return; /* a single exception environment may encompass a range of addresses, so don't deal with it until it has finished */
  output_exenv(last_exenv_started);
  last_exenv_started = blkexenv_(bl);
  return;
}

static void localcg_endfn(void)
{
  if (codep == 0) return; /*a function of zero length is not interesting*/
  if (!(var_cc_private_flags & 128L)) return;

  if (exhandler_size()==0)
    add_exhandler_entry(0xdeadbeef); /*dummy first entry so that index offset
                                       is not 0 which looks like null.*/

  if (debugging(DEBUG_CG))
    printf("FunctionExceptionTable addr=%4X fn-length=%4X exhandler=%4X\n",
           codebase, codep, exhandler_size());
#ifdef TARGET_IS_THUMB
  add_extable_entry(1+(int)codebase);
#else
  add_extable_entry(codebase);
#endif
  add_extable_entry(codep);
  /*codep is the offset of last instruction in the function, which is
    4 (or 2 for thumb) less than the instruction length; but the return
    address of the function will never be right at the end, so this
    won't affect behaviour of stackwalking code. */
  if (handler_entries==NULL)
    add_extable_entry(0);
  else add_extable_entry(exhandler_size());

  output_exenv (last_exenv_started);
  output_thisfn_handler_entries(handler_entries, 1);
}


static LabelNumber *dump_flowgraph(LabelNumber *pending_branch, int32 lifted)
{ BlockHead *p1;

  localcg_startfn();
  for (p1 = top_block; p1 != NULL; p1 = blkdown_(p1))
  { BlockHead *p = p1;
    if ( ( (blkflags_(p) & BLKALIVE)
           || (usrdbg(DBG_LINE+DBG_VAR) && !usrdbg(DBG_OPT_DEAD)))
         && !(blkflags_(p) & BLKCODED)
         && (blkflags_(p) & BLKLIFTABLE) == lifted)
      for (;;)
      { LabelNumber *w = blklab_(p);
        localcg_startblock(p);
        if ( (blkflags_(p) & BLKEMPTY)
             && (!usrdbg(DBG_LINE+DBG_VAR) || usrdbg(DBG_OPT_DEAD)))
          syserr(syserr_live_empty_block, (long)lab_name_(w));
        if (pending_branch != NOTALAB && pending_branch != w)
          show_branch_instruction(J_B, pending_branch);
        if (blkflags_(p) & BLKSWITCH)
        { LabelNumber **v = blktable_(p);
          int32 i, n = blktabsize_(p);
          /* Normalise the entries in the switch table */
          /* This is done so that the r2 field of J_CASEBRANCH is OK */
          for (i=0; i<n; i++)
            if (v[i] == way_out) v[i] = RETLAB;
        }
        if (blkflags_(p) & BLKSWITCH && blklength_(p) == 1
                                     && (blkcode_(p)->op == J_THUNKTABLE))
        { LabelNumber **v = blktable_(p);
          int32 i, n = blktabsize_(p);
          pending_branch = NOTALAB;
          for (i=0; i<n; i++)
          { BlockHead *b = v[i]->block;
            if (blkcode_(b)[0].op == J_ORG) goto omit_casebranch;
          }
          for (i=0; i<n; i++)
          { BlockHead *b = v[i]->block;
            Icode *c0 = blkcode_(b), *c1 = c0 + 1;
            int ptr_adjust_zero;
            ptr_adjust_zero = (blklength_(b) == 2 &&
                (c0->op & J_TABLE_BITS) == J_ADDK &&
                 c0->r1.rr == 0 && c0->r2.rr == 0 && c0->r3.i == 0 &&
                 (c1->op & J_TABLE_BITS) == J_TAILCALLK);
            localcg_startblock(b);
#ifdef TARGET_HAS_DATA_VTABLES
            if (target_has_data_vtables) {
                Icode ic;
                if (ptr_adjust_zero)
                {   ic = *c1;
                    ic.op = J_WORD_ADCON;
                    expand_jop_macro(&ic);
                    blkflags_(b) |= BLKCODED;
                } else {
                    INIT_IC (ic, J_WORD_LABEL);
                    ic.r3.l = v[i];
#ifdef THUMB_CPLUSPLUS
                    c0->op = (c0->op & ~J_TABLE_BITS) | J_THIS_ADJUST;
#endif
                    expand_jop_macro(&ic);
                }
            } else
#endif
            {
                if (ptr_adjust_zero)
                {
                  expand_jop_macro(c1);
                  blkflags_(b) |= BLKCODED;
                } else
#ifdef TARGET_HAS_SWITCH_BRANCHTABLE
                if (i == (n-1))
                  pending_branch = v[n-1];
                else
#endif
                  show_branch_instruction(J_BXX, v[i]);
            }
          }
          blkflags_(p) |= BLKCODED;
omit_casebranch:;
        } else
          if (blkflags_(p) & BLK2EXIT && blknext_(p) != blknext1_(p))
/* The seemingly odd test for distinct destinations is present here since  */
/* cross-jump optimisations can reveal new cases of vacuous tests, and if  */
/* I pass such a case down to use_cond_field() the destination block gets  */
/* displayed twice (which would be sort of OK except for the fact that     */
/* setting its label twice causes trouble).                                */
            pending_branch = use_cond_field(p);
        else
        {
          localcg_startblock(p);
          show_basic_block(p, Q_AL);
          if (blkflags_(p) & BLKSWITCH)
          {   LabelNumber **v = blktable_(p);
            int32 i, n = blktabsize_(p);
#ifdef TARGET_HAS_SWITCH_BRANCHTABLE
            n--;
#endif
/* drop though to execute last case directly: only if target uses a branch */
/* table of branch instructions!!!!!!!!!                                   */
            for (i=0; i<n; i++)
              {
                if (v[i]!=RETLAB)
                  localcg_startblock(lab_block_(v[i]));
                show_branch_instruction(J_BXX, v[i]);
              }
#ifdef TARGET_HAS_SWITCH_BRANCHTABLE
            pending_branch = v[n];
#else
            pending_branch = NOTALAB;
#endif
          }

#ifdef TARGET_HAS_TAILCALL
          else if (blkflags_(p) & BLK0EXIT)
            pending_branch = NOTALAB;
#endif
          else if ( blknext_(p) == way_out ||
                    (!(blkflags_(p) & BLKALIVE) &&
                     is_exit_label(blknext_(p))) )
            pending_branch = RETLAB;
          else
            pending_branch = blknext_(p);
        }
        /*localcg_endblock(p);*/
        if (pending_branch == NOTALAB
            || pending_branch == RETLAB
/* @@@ LDS 21-Sep-89: the following line conspires with cg_loop and emits  */
/* better code for while/for loops, saving 1 br-not-taken/iteration.       */
            || ( (blkflags_(p) & BLKLOOP)
                 && (!usrdbg(DBG_LINE) || usrdbg(DBG_OPT_DEAD))))
          break;
        { BlockList *bl;
          int flag = 1;
          BlockHead *prev = p;
          p = pending_branch->block;
/* p is now the destination block for the one I have just displayed.       */
/* If it has not already been coded but all its ancestors have (except     */
/* itself, if it is its own ancestor) I will display it next.              */
          if ((blkflags_(p) & BLKCODED) || usrdbg(DBG_VAR))
            break;
          for (bl = blkusedfrom_(p); bl!=NULL; bl=bl->blklstcdr)
            if (bl->blklstcar != p &&
                !(blkflags_(bl->blklstcar) & BLKCODED))
            { flag = 0;
              break;
            }

          if (flag) continue; /* use block p next, do not advance p1 */
          if (p == blkdown_(prev)) continue;
        }
        break;                       /* go on to next sequential block */
      }
  }
  localcg_endfn();
  return pending_branch;
}

void linearize_code(void)
{  int no_crossjumping = 0;
/* before we can tidy up branches to branches we have to find out which  */
/* basic blocks are empty (this is non-trivial because e.g. register     */
/* allocation may have turned a STRV into a MOV r,r).  Ultimately we     */
/* should remove all _STACKREF jopcodes, but for now just test by        */
/* smashing to NOOPs where relevant.                                     */
    { BlockHead *p;
      unsigned32 n, max_stackdepth = 0;
      int32 total_code_length = 0;
      /* Now seems a convenient time to replace blkstack by blkstacki */
      /* Also, we now recompute greatest_stackdepth                   */
      for (p = top_block; p != NULL; p = blkdown_(p)) {
        if (usrdbg(DBG_VAR)) {
          BindList *bl = blkstack_(p);
          for ( ; bl!=NULL ; bl = bl->bindlistcdr ) {
            Binder *b = bl->bindlistcar;
            if (bindstg_(b) & b_bindaddrlist)
            { /* The following code extends similar code in   */
              /* remove_noops by ensuring all variables (not  */
              /* only referenced ones) are allocated stack    */
              /* when the debugging tables are produced.      */
              setstackoffset(b);
            }
          }
        }
        blkstacki_(p) = n = size_of_binders(blkstack_(p));
        if (n > max_stackdepth) max_stackdepth = n;
        blkflags_(p) |= BLKSTACKI;
        { int32 i, len = blklength_(p);
          Icode *c = blkcode_(p);
          for (i = 0; i < len; i++)
            if ((c[i].op & J_TABLE_BITS) == J_SETSPENV) {
              c[i].r2.i = n = size_of_binders(c[i].r2.bl);
              if (n > max_stackdepth) max_stackdepth = n;
              c[i].r3.i = n = size_of_binders(c[i].r3.bl);
              if (n > max_stackdepth) max_stackdepth = n;
              c[i].op = J_SETSP;
            }
        }
      }
      greatest_stackdepth = max_stackdepth;
      if (greatest_stackdepth > 256)
        procflags |= PROC_BIGSTACK;
      else
        procflags &= ~PROC_BIGSTACK;
      for (p = top_block; p != NULL; p = blkdown_(p))
      {
              /* NB lose_dead_code() means that all these blocks are   */
              /* really alive, however BLKALIVE has been cleared.      */
        blklength_(p) = remove_noops(blkcode_(p), blklength_(p));
        total_code_length += blklength_(p);
      }
#ifdef TARGET_IS_THUMB
    /* force LR to be stored for large functions, so that BL may be used for jumps */
    if (total_code_length > 1000) augment_RealRegSet(&regmaskvec, R_LR);
#endif
    }
/* Remove branches to branches and similar oddities.                     */
/* N.B. the top_block will never be empty since it contains an ENTER     */
/* Also collect list of parents for each block.                          */
/* Furthermore turn exit-branches into jumps to a single exit block so   */
/* that cross-jumping will be able to detect shared code leading thereto */
    {   BlockHead *b;
        way_out = nextlabel();
        way_out->block = b = newblock(way_out, NULL);
        blkstacki_(b) = 0;
        blknext_(b) = RetVoidLab;  /* Hmmm - all returns are alike here */
        blkflags_(b) |= BLKALIVE | BLKSTACKI;
    }
    (void)branch_chain(blklab_(top_block), 1);

#ifdef TARGET_HAS_TAILCALL
/* Now (after branch-chaining) insert J_TAILCALL instead of J_CALL ...   */
/* This transformation is valid if the CALL is immediately followed by a */
/* return, and no variables whose address are taken are in scope and     */
/* further no calls to 'setjmp' occur within the procedure at all.       */
/* (CONFIG_INDIRECT_SETJMP allows (ANSI-forbidden) J_CALLR to 'setjmp'.) */
/* This is implemented in rather a different way.  We can tell that no   */
/* non-register locals are present from the immediate return since       */
/* this can at worst have come from a squashed SETSP.  We need to check  */
/* whether any block had a 'setjmp' or an arg address taken too.         */

/* sample code that could give trouble if setjmp were called & tail-call */
/* conversion applied...                                                 */
/*   int f(int x)                                                        */
/*   {   <code that is complicated enough for x to be spilt>             */
/*       if (setjmp(buff)) p(buff);                                      */
/*       else q(x);                                                      */
/*   }                                                                   */
/* where p calls longjmp(). Then if x is in the stack-frame of f() the   */
/* call to p() can clobber it even though its value is needed for q(x).  */
/* Note that if x were a register variable its value would have been safe*/
/* in buff, and if &x were mentioned the tail call would be illegal      */
/* otherwise, so it is only if x is spilt for other reasons....          */

/* Note that the destination in a J_TAILCALLR ought not to be one in the */
/* callee-saved set (which will be restored before it is used), but      */
/* register allocation saw an ordinary J_CALLR with no such restriction. */
/* The problem is ignored here: backends with TAILCALLR must take        */
/* appropriate action themselves.                                        */

    if (!(procflags & (BLKSETJMP|PROC_ARGADDR))
        && !usrdbg(DBG_ANY) /* No tail call if debugging - too confusing */
        && !(var_cc_private_flags & 16L)
#ifdef PROFILE_DISABLES_TAILCALL
        && !profile_option
#endif
        && !(procauxflags & bitoffnaux_(s_irq))
       )
    {   BlockHead *p; int32 len;
        for (p = top_block; p != NULL; p = blkdown_(p))
            if (!(blkflags_(p) & (BLK2EXIT|BLKSWITCH)) &&
                blknext_(p) == way_out &&
                (len = blklength_(p)) > 0)
            {   Icode *b = blkcode_(p);
                Icode *bend = &b[len-1];
/* AM: note that we do not tailify() J_CALLK/R  with K_NOTAILCALL set. */
                if (!(bend->r2.i & K_NOTAILCALL) &&
                    ( ( (bend->op & J_TABLE_BITS) == J_CALLK
#ifdef TARGET_HAS_RECURSIVE_TAILCALL_ONLY
                        && bindsym_(bend->r3.b) == currentfunction.symstr
#endif
                      )
                     /* ECN: Any CALLK marked 'K_THUNK' must be converted to a
                      * TAILCALLK regardless of TARGET_HAS_RECURSIVE_TAILCALL_ONLY
                      */
                     || ((bend->op & J_TABLE_BITS) == J_CALLK && (bend->r2.i & K_THUNK))
#ifdef TARGET_HAS_TAILCALLR
                     || (bend->op & J_TABLE_BITS)== J_CALLR
#endif
                    ) )
                {   bend->op = tailify_(bend->op); /* J_TAILCALLK/R */
                    /* flag block as having no exit and 1 less call ...   */
                    blkflags_(p) |= BLK0EXIT;
                    if (!(blkflags_(p) & BLK2CALL)) blkflags_(p) &= ~BLKCALL;
                }
            }
    }
#endif

/* Now establish reference counts for blocks so that I can see which     */
/* ones have more than one entry.                                        */
/* @@@ move this code into branch_chain() now that it is tidied?         */
    {   BlockHead *p;
        refblock(blklab_(top_block), NULL, 0);  /* Reference from outside proc  */
        for (p = top_block; p != NULL; p = blkdown_(p))
            if (blkflags_(p) & BLKALIVE)
            {   if (blkflags_(p) & BLKSWITCH)
                {   LabelNumber **v = blktable_(p);
                    int32 i, n = blktabsize_(p);
                    for (i=0; i<n; i++) refblock(v[i], p, 0);

                    if (blklength_(p) == 1 && blkcode_(p)->op == J_THUNKTABLE)
                        no_crossjumping = 1;
                }
                else
                {   /* Blocks with BLK0EXIT (ending with tailcall)       */
                    /* included here (successor is way_out)              */
                    refblock(blknext_(p), p, 0);
                    if (blkflags_(p) & BLK2EXIT) refblock(blknext1_(p), p, 0);
                }
            }
    }

    blkflags_(top_block) |= BLKALIVE;

#ifndef TARGET_IS_NULL
    /* cross-jump-optimise uses used-from information */
    if (!no_crossjumping && cross_jump_optimize()) {
        BlockHead *p;
        for (p = top_block; p != NULL; p = blkdown_(p)) blkflags_(p) &= ~BLKALIVE;
        branch_chain(blklab_(top_block), 2);
        if (debugging(DEBUG_CG))
            flowgraf_print("After branch-chain", YES);
    }
#ifndef TARGET_STACKS_LINK
/* See comment in regalloc.c - mark R_LR as allocated if a non-tail call   */
/* appears.                                                                */
    if (procflags & BLKCALL) augment_RealRegSet(&regmaskvec, R_LR);
#endif


    {   BlockHead *p;
        for (p = top_block; p != NULL; p = blkdown_(p))
        blkflags_(p) &= ~BLKLIFTABLE;
    }
#ifdef TARGET_HAS_SAVE
    try_shrinkwrap();
#endif

/* Now dump out the flowgraph - note that J_ENTER implicitly               */
/* does a 'set_cond_execution(Q_AL)' if TARGET_HAS_COND_EXEC               */

/* ???Is doing the next line here what causes the syserr() in refblock()   */
    blkflags_(way_out->block) |= BLKCODED;    /* do not display this block */
/* strictly a lie, but harmless.  The more obvious &= ~BLKALIVE fails if   */
/* usrdbg(something)                                                       */

/* /* AM: The following interface is spurious: xxxgen.c can detect         */
/* the J_ENTER.  AM leaves it (under threat) until we can inhibit the      */
/* J_LABEL and J_STACK which preceed J_ENTER currently.                    */
    localcg_reinit();

  { LabelNumber *pending_branch_address;
    current_env2 = 0;
#ifndef TARGET_IS_ARM
    dbg_enterproc();
#else
    /* called from armgen (possibly after codeseg_function_name()) */
#endif
    if (debugging(DEBUG_CG))
        cc_msg("\n\nFlattened form:\n\n");

    pending_branch_address = dump_flowgraph(NOTALAB, BLKLIFTABLE);
    pending_branch_address = dump_flowgraph(pending_branch_address, 0);

    if (pending_branch_address != NOTALAB)
      show_branch_instruction(J_B, pending_branch_address);
    if (usrdbg(DBG_VAR)) dbg_scope1(0, current_env2);
  }
  { Icode ic;
    INIT_IC(ic, J_ENDPROC);
    expand_jop_macro(&ic);
  }
#endif /* TARGET_IS_NULL */
}

void flowgraph_reinit(void)
{
    currentblock = icodetop = (Icode *) DUFF_ADDR;
                                        /* NB. (currentblock >= icodetop) */
    cgstate.icode_cur = cgstate.block_cur = 0;
    icoden = 0;
    bottom_block = 0, block_header = (BlockHead*) DUFF_ADDR;
    deadcode = 1;
    current_env = 0;
    holes = NULL;
    prevblock = NULL;
    INIT_IC(fg_pending, J_NOOP);
    fg_pending.r3.i = 0;
#ifdef TARGET_HAS_COND_EXEC
    if (config & CONFIG_OPTIMISE_SPACE)
    {
        CondMax_Loop = 10;
        CondMax_Ordinary = 5;
    }
    else
    {
        CondMax_Loop = 6;
        CondMax_Ordinary = 3;
    }
#endif
}

/* end of mip/flowgraph.c */
