/*
 * C compiler file mip/regalloc.c.
 * Copyright (C) Codemist Ltd., 1988, 1991.
 * Copyright (C) Acorn Computers Ltd., 1988.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$ Codemist 73
 * Checkin $Date$
 * Revising $Author$
 */

/* AM, Sept 91: In this version of the code (67), I have arranged to    */
/* store local (within basic block) liveness info in 2 data structures. */
/* One, the traditional VRegSetP, and also a vector reg_lsbusetab[].    */
/* These are checked for consistency at all times.                      */
/* SOON I INTEND TO ELIMINATE VRegSetP FOR LOCAL INFO (BUT NOT GLOBAL). */
/* Vectors are converted to/from VRegSetP's at begining and end of      */
/* basic blocks.  The effect is to allow optimisation of char/short     */
/* assignment w.r.t masking/sign extension.                             */
/* The code propagates demand (i.e. how many bits are needed)           */
/* and currently uses this to turn LDRBs/u to plain LDRB &c and also    */
/* smashes redundant J_AND/J_EXTEND to J_MOV.                           */

/* AM memo: tidy up the use of 'curstats'.                              */

/* AM whinge: Recently I changed the type of RealRegSet to allow        */
/* machines with more than 32 registers.  I found this very hard to do  */
/* reliably due to the vast number of VoidStar formal parameters        */
/* meaning it is impossible to find all occurrences.  Please can we     */
/* try to get rid of some?  Unions would be MUCH safer.  My view is     */
/* that VoidStar should really only be used where it is essential       */
/* and not to reduce type-checking (which indirectly increases the cost */
/* of modifications and the chances of buggy releases.                  */
/* Key suspicion: mapping fns are defined VoidStar for pseudo-          */
/* polymorphism and then only used at one type.                         */

/* WGD,AM 7-1-88 Op deadbits bug corrected - when several live virtual regs
   are allocated to the same real register (this is encouraged by the
   voiding of copy instructions) - then only the final occurrence
   of the set should be recorded as dead, not the final occurrence of each
   member separately.  New routine update_deadflags handles this.
*/
/* The simplest code AM can produce to exhibit this is:             */
/*   extern int z; void f(x) { while (x) z=1; while (x) z=1; }      */

/* Experimental test of using SynAlloc/syn_list2 here wasted space.      */

/* Following Nov 87 comment referenced below.                            */
/* Nov 87: Dataflow determination of dead registers introduced to allow  */
/* store-to-store ops to be peepholed in (e.g. x = y; vs. x = y = z;)    */
/* and use of ibm 370 RX arithmetic operations.                          */
/* Dead regs are indicated by the J_DEAD_Rx bits.  Two points:           */
/* 1. We do not claim that *ALL* dead regs are detected -- it seems      */
/*    overkill to detect it for (e.g. CALLR).  However, we do guarantee  */
/*    that J_DEAD_Rx guarantees that Rx fields may be corrupted, but...  */
/* 2. A (real) register may be marked dead, but become alive again by    */
/*    being set in the R1 field.  As to why this is so, and why nothing  */
/*    can sensibly be done about it, observe that                        */
/*    f(int x) { register int a = x; ... } will produce something like   */
/*    MOVR rt, rx; MOVR ra, rt.  Note that (if x is not used further)    */
/*    then the first MOVR will mark R3 (rx) as dead and the second MOVR  */
/*    also R3 (now rt).  Now either or both of these MOVR's may be       */
/*    killed by the mapping of virt. regs to (possibly same) phys. regs. */

/* The use of RetImplLab is nasty here (equivalent to RetVoidLab).       */

/* move towards this code being machine independent apart from a few
   parameters, such as 'number of registers'.
*/

#define uint HIDE_HPs_uint
#include <limits.h>
#undef uint
#include <time.h>
#ifdef __STDC__
#  include <string.h>
#else
#  include <strings.h>
#endif
#include "globals.h"
#include "regalloc.h"
#include "errors.h"
#include "sem.h"      /* princtype -- @@@ yuk, lets use abstract interface */
#include "jopcode.h"
#include "regsets.h"
#include "store.h"
#include "cg.h"
#include "mcdep.h"    /* immed_cmp, usrdbg(xxxx) */
#include "flowgraf.h" /* top_block, bottom_block */
#include "builtin.h"  /* sim */
#include "aeops.h"    /* bitofstg_(), s_register - sigh */
#include "sr.h"
#include "armops.h"
#include "inlnasm.h"

static uint32 warn_corrupted_regs;

/* Only one (of size vregistername) of these is allocated, so array OK. */
static unsigned char *reg_lsbusetab;
#define ALLBITS 32

static int spaceofmask(unsigned32 m)
{   int k = 0;
    if (m & 0x80000000) return 32;  /* For sake of 64 bit machines */
    while (m) m>>=1, k++;
    return k==0 ? 1 : k;            /* treat 0 as 1 */
}

static int min(int a, int b)        /* max is in misc.c!! */
{   return a<=b ? a : b;
}

#define extend_bitsused(x) ((x)==0 || (x)==1 ? 8 : (x)==2 ? 16 : ALLBITS)

/* Return number of least sig bits in arg which contribute to result.   */
/* The case we really want for 'short' on the ARM is that SHRK 8; STRB  */
/* only uses the low 16 bits of the SHRK.                               */
/* Always return at least 1 (so far) so that result matches classical   */
/* dataflow analysis based on booleans.                                 */
/* BEWARE: otherwise 2 shifts could give 0 bits required, but liveness  */
/* would disagree, giving a syserr() in current code.                   */
/* Note that 'op' here has been masked with J_TABLE_BITS.               */
static int reg_bitsrefd(const Icode *const ic, int demand, int pos)
{   switch (ic->op & J_TABLE_BITS)
    {
/* can't optimise demand for CMP/DIV/SHRR etc. as all bits count.       */
/* cases J_MOVK, J_ADCON, J_ADCONV probably can't benefit anyway.       */
default: demand = ALLBITS; break;
case J_STRBK: case J_STRBR: case J_STRBV: case J_STRBVK:
                                       demand = pos==1 ? 8 : ALLBITS; break;
case J_STRWK: case J_STRWR: case J_STRWV: case J_STRWVK:
                                       demand = pos==1 ? 16 : ALLBITS; break;
case J_MOVR:                            break;
case J_ADDK: case J_SUBK: case J_MULK:  break;
case J_ORRK: case J_EORK:               break;
case J_ADDR: case J_SUBR: case J_MULR:  break;
case J_ANDR: case J_ORRR: case J_EORR:  break;
case J_RSBR:                            break;
case J_NOTR: case J_NEGR:               break;
case J_STRV: /* Propagate number of bits needed from variable to value  */
             /* stored into it                                          */
             break;
case J_LDRV: /* Propagate number of bits needed to variable from value  */
             /* value loaded from it                                    */
             break;
  /* Now some more fun cases...                                           */
case J_ANDK: demand = (int)min(demand,spaceofmask(ic->r3.i)); break;
/* For the next cautious test remember TARGET_LACKS_RIGHTSHIFT.         */
case J_SHLK: demand = 0<=ic->r3.i && ic->r3.i<32 ? (int)max(demand-(int)ic->r3.i,1) : ALLBITS; break;
case J_SHRK: demand = 0<=ic->r3.i && ic->r3.i<32 ? (int)min(demand+(int)ic->r3.i,32) : ALLBITS; break;
/* Why don't we change extend so that it takes a mask like ANDK?        */
case J_EXTEND: demand = extend_bitsused(ic->r3.i); break;
    }
#ifdef J_SHIFTPOS
    if (pos == 3 && (ic->op & J_SHIFTMASK) != 0)    /* shifted R3 */
    {   int32 shift = (ic->op >> J_SHIFTPOS) & SHIFT_MASK;
        switch((ic->op >> J_SHIFTPOS) & (SHIFT_ARITH | SHIFT_RIGHT))
        {
            case 0: /* ROR */
                if (shift == 0) shift = 1;  /* RRX!! */
            case SHIFT_RIGHT: /* LSR */
            case SHIFT_RIGHT | SHIFT_ARITH: /* ASR */
                demand += shift;
                if (demand > ALLBITS) demand = ALLBITS;
                break;
            case SHIFT_ARITH: /* LSL! */
                demand -= shift;
                if (demand < 0) demand = 0;
                break;
        }
    }
#endif
    return demand;
}

#define ClashAllocType AT_Syn
#define ListAllocType AT_Syn
#define CopyAllocType AT_Syn

/* extra value for the r->realreg field... */
#define R_UNSCHEDULED (-1L)   /* not scheduled for allocation yet         */
#define R_SCHEDULED   (-2L)   /* now scheduled for allocation             */
#define R_WILLFIT     (-3L)   /* allocatable, but not yet assigned        */
                              /* (now defunct: future spilling considered */
                              /*  harmful)                                */
#define R_SPILT       (-4L)   /* need to spill onto stack                 */
#define R_BOGUS       (-5L)   /* used transiently: != SPILT, != WILLFIT   */

typedef struct ValnRegList ValnRegList;
typedef struct VRegister
{
    VRegnum rname;
    VRegSetP clash2;        /* with registers earlier in allocation order */
    VRegSetP clashes;                                        /* and later */
    union { int32 nclashes; Binder *spillbinder;} u;
    RealRegister realreg;
    int32 heapaddr;                /* effectively the inverse permutation */
    struct VRegister *perm;
    int32 ncopies;
    int32 refcount;
    VRegnum slave;
    uint32 valnum;
    ValnRegList *valsource;
    uint32 valwritecount;
} VRegister;

#define vregname_(vr) ((vr)->rname & ~REGSORTMASK)
#define vregtype_(vr) ((vr)->rname & REGSORTMASK)
#define valnr_(vr)    (vreg_(vr)->valnum)
#define valsource_(vr) (vreg_(vr)->valsource)
#define valwritecount_(vr) (vreg_(vr)->valwritecount)
#define VALN_UNSET 0
#define VALN_MULTIPLE 0x80000000
#define VALN_SLAVE    0x40000000
#define VALN_DEAD     0x20000000
#define VALN_MASK     0x1fffffff
#define VALN_REAL 1
#define is_real_valn_(n) ((n)!=VALN_UNSET && !((n) & VALN_MULTIPLE))
#define val_(n) ((n) & VALN_MASK)
#define using_valnr (!(var_cc_private_flags & 0x08000000))

RealRegSet regmaskvec;    /* registers used or corrupted in this proc */
static RealRegSet m_intregs, m_notpreserved;
#ifndef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
static RealRegSet m_fltregs;
#endif
#ifdef ADDRESS_REG_STUFF
static RealRegSet m_addrregs;
#endif

static int32 n_real_spills, n_cse_spills,        /* these seem to be real.. */
             tot_real_spills, tot_cse_spills,    /* while these are just for. */
             spill_cost, tot_cost, choose_count; /* the trace option.   */

static Icode ic_noop;

/* The following routines take pointers to RealRegSets as args even     */
/* though conceptually RealRegSets should be passed by value.           */


#if (NMAGICREGS <= 32)

bool member_RealRegSet(RealRegSet const *a, unsigned32 r)
{   return ((a->map)[0] & regbit(r)) != 0;
}

void augment_RealRegSet(RealRegSet *a, unsigned32 r)
{   (a->map)[0] |= regbit(r);
}

unsigned32 delete_RealRegSet(RealRegSet *a, unsigned32 r)
{   unsigned32 oldval = (a->map)[0] & regbit(r);
    (a->map)[0] ^= oldval;
    return oldval;
}

bool intersect_RealRegSet(RealRegSet *a, RealRegSet const *b, RealRegSet const *c)
{   return ((a->map)[0] = (b->map)[0] & (c->map)[0]) != 0;
}

void union_RealRegSet(RealRegSet *a, RealRegSet const *b, RealRegSet const *c)
{   (a->map)[0] = (b->map)[0] | (c->map)[0];
}

void difference_RealRegSet(RealRegSet *a, const RealRegSet *b, const RealRegSet *c)
{   (a->map)[0] = (b->map)[0] & ~(c->map)[0];
}

void map_RealRegSet(RealRegSet const *a, RealRegSet_MapFn *f, RealRegSet_MapArg *arg)
{   unsigned32 m = ((a)->map)[0];
    int j;
    for (j = 0; m != 0; j++)
        if (m & regbit(j))
        {    f(j, arg);
             m ^= regbit(j);
        }
}

#else

bool member_RealRegSet(RealRegSet const *a, unsigned32 r)
{   return ((a->map)[r/32] & regbit(r % 32)) != 0;
}

void augment_RealRegSet(RealRegSet *a, unsigned32 r)
{   (a->map)[r/32] |= regbit(r % 32);
}

unsigned32 delete_RealRegSet(RealRegSet *a, unsigned32 r)
{   unsigned32 oldval = (a->map)[r/32] & regbit(r % 32);
    (a->map)[r/32] ^= oldval;
    return oldval;
}

bool intersect_RealRegSet(RealRegSet *a, const RealRegSet *b,
                                         const RealRegSet *c)
{   int i; bool res = 0;
    for (i = 0; i < (NMAGICREGS+31)/32; i++)
        if (((a->map)[i] = (b->map)[i] & (c->map)[i]) != 0) res = 1;
    return res;
}

void union_RealRegSet(RealRegSet *a, const RealRegSet *b, const RealRegSet *c)
{   int32 i;
    for (i = 0; i < (NMAGICREGS+31)/32; i++)
        (a->map)[i] = (b->map)[i] | (c->map)[i];
}

void difference_RealRegSet(RealRegSet *a, const RealRegSet *b, const RealRegSet *c)
{   int32 i;
    for (i = 0; i < (NMAGICREGS+31)/32; i++)
        (a->map)[i] = (b->map)[i] & ~(c->map)[i];
}

void map_RealRegSet(RealRegSet const *a, RealRegSet_MapFn *f, RealRegSet_MapArg *arg)
{   int32 i, j;
    for (i = 0; i < (NMAGICREGS+31)/32; i++)
    {   unsigned32 m = ((a)->map)[i];
        int j;
        for (j = 0; m != 0; j++)
            if (m & regbit(j))
            {    f(32*i + j, arg);
                 m ^= regbit(j);
            }
    }
}

#endif

static void print_RealRegSet_cb(RealRegister r, RealRegSet_MapArg *arg) {
    cc_msg("%s%ld", *(arg->s), (long)r);
    *(arg->s) = " ";
}

void print_RealRegSet(RealRegSet const *a) {
    char *s = "";
    RealRegSet_MapArg arg; arg.s = &s;
    map_RealRegSet(a, print_RealRegSet_cb, &arg);
}

#ifdef TARGET_SHARES_INTEGER_AND_FP_REGISTERS

#ifdef never
/* I demand an even/odd pair for float regs as well as double ones     */
/* because doing so (slightly) simplifies allocation and because float */
/* registers will not often arise in C anyway.  Fix up later maybe.    */
#define needsregpair_(rsort) ((rsort) == DBLREG || (rsort) == FLTREG)
#else
/* The aih324 wants it this way...                                      */
#define needsregpair_(rsort) ((rsort) == DBLREG)
#endif

#define other_halfreg(r) ((r)+1)   /* works on vregs and physical regs. */

static bool two_bits(unsigned32 w)
{   /* Used to test if an even/odd register pair is available */
    /* There is probably a fast trick involving w+0x55555555! */
    int i;
    for (i=0; i<31; i++)
    {   if ((w & 3) == 3) return YES;
        else w = w >> 2;
    }
    return NO;
}

static bool nonempty_RealRegSet(const RealRegSet *a, int32 rsort)
{   int32 i; bool res = 0;
    if (needsregpair_(rsort))
    {   for (i = 0; i < (NMAGICREGS+31)/32; i++)
            if (two_bits((a->map)[i])) res = 1;
    }
    else
    {   for (i = 0; i < (NMAGICREGS+31)/32; i++)
            if ((a->map)[i] != 0) res = 1;
    }
    return res;
}

#else /* TARGET_SHARES_INTEGER_AND_FP_REGISTERS */
#  if NMAGICREGS <= 32
#    define nonempty_RealRegSet_x(a) (((a)->map)[0] != 0)
#  else
static bool nonempty_RealRegSet_x(const RealRegSet *a)
{   int32 i; bool res = 0;
    for (i = 0; i < (NMAGICREGS+31)/32; i++)
        if ((a->map)[i] != 0) res = 1;
    return res;
}
#endif

#define nonempty_RealRegSet(a,sort) nonempty_RealRegSet_x(a)

#endif /* TARGET_SHARES_INTEGER_AND_FP_REGISTERS */
#ifdef ADDRESS_REG_STUFF
static bool spillpanic;     /* forced to demote A to D register? */
#endif

/* @@@ tidy up these two parallel representations...                    */
static VRegSetP globalregvarset;
static RealRegSet globalregvarvec;

static void regalloc_changephase(void);

typedef union vreg_type { VRegister *vreg; VRegnum type; } vreg_type;

static vreg_type (*(vregheap[REGHEAPSEGMAX]))[REGHEAPSEGSIZE];

static unsigned32 vregistername;
#define vregtypetab_(n) (*vregheap[(n)>>REGHEAPSEGBITS]) \
                                  [(n)&(REGHEAPSEGSIZE-1L)].type
#define vreg_(n)        (*vregheap[(n)>>REGHEAPSEGBITS]) \
                                  [(n)&(REGHEAPSEGSIZE-1L)].vreg
/* Note that vreg_() is set and then never updated -- permregheap_() is */
#define permregheap_(n) (vreg_((n)+NMAGICREGS)->perm)

/*
 * Statistics-gathering stuff.
 */

typedef struct RegStats {
    unsigned32  dataflow_iterations;
    unsigned32  ncopies;
    unsigned32  copysquares;
    unsigned32  copysquarebytes;
    unsigned32  nlists;
    unsigned32  newlists;
    unsigned32  listbytes;
    unsigned32  nvregs;
    unsigned32  vregbytes;
    unsigned32  nsquares;
    unsigned32  squarebytes;
    unsigned32  nregsets;
    unsigned32  newregsets;
    unsigned32  regsetbytes;
    unsigned32  clashbytes; /* total of clashmatrix/regset stuff */
} RegStats;

static RegStats curstats, maxstats;

static clock_t regalloc_clock1, regalloc_clock2, dataflow_clock;

/* register_number() returns the physical register corresponding to a   */
/* virtual register, else a number < 0 (like R_BOGUS, q.v.)             */
extern RealRegister register_number(VRegnum a)
{
   return vreg_(a)->realreg;
}

/* TARGET_IS_NULL is defined when the system being built is a Lint-like   */
/* checker or some source-to-source conversion utility. It is desirable   */
/* to keep enough of the register allocation code that data-flow oddities */
/* such as unused variables can be reported on, but much of the rest can  */
/* (and should) be skipped as unnecessary.                                */

#ifndef TARGET_IS_NULL

/* first routines to keep the register heap in order of number of clashes */
/* so allocation can proceed from the most(?) clashing register first.    */
/* Note that these permute the vregheap table.                            */

/* Comparison routine for deciding heap-orderedness property.             */
/* Use ->nclashes as primary key, but experimentally use number of real   */
/* register copies for secondary one in lexicographic order.              */
/* To achieve this in a way which does not change during allocation       */
/* (which would upset the ordering property (but not chaotically))        */
/* we eliminate registers, 1. by least clashes and then 2. by least       */
/* register copies, counting a physical (magic) register many times.      */

#define has_physical_copy_(r) ((r)->ncopies>=0x10000)

static int32 reg_cmp(VRegister *v, VRegister *w)
{   int32 d;
    if (v->u.nclashes == 0 && has_physical_copy_(v)) {
        if (w->u.nclashes == 0 && has_physical_copy_(w))
            return v->ncopies - w->ncopies;
        else
            return 1;
    }
    if (w->u.nclashes == 0 && has_physical_copy_(w)) return 0;
    if ((d = v->u.nclashes - w->u.nclashes) != 0) return d;
    return v->ncopies - w->ncopies;
}

static void downheap(int32 k, int32 n)
{
/* fix up heap property at position k in the register heap               */
/* see Sedgewick's book on algorithms for commentary on this.            */
    VRegister *v = permregheap_(k), *w;
    while (k <= (n/2L))
    {   int32 j = k + k;
        if (j < n)
        {   if (reg_cmp(permregheap_(j),permregheap_(j+1)) > 0) j++;
        }
        if (reg_cmp(v, permregheap_(j)) <= 0) break;
        w = permregheap_(k) = permregheap_(j);
        w->heapaddr = k;
        k = j;
    }
    permregheap_(k) = v;
    v->heapaddr = k;
}

static void upheap(int32 k)
{
    VRegister *v = permregheap_(k), *w;
    int32 k1;
/* NB that there is a sentinel register with nclashes=-1 in the 0        */
/* position of the heap - that simplifies the end-test here.             */
    while (k1 = k/2L, w = permregheap_(k1), reg_cmp(w,v) > 0)
    {   permregheap_(k) = w;
        w->heapaddr = k;
        k = k1;
    }
    permregheap_(k) = v;
    v->heapaddr = k;
}

#define printvregclash(a) print_clashes(a)
#define printvregclash2(a) vregset_print((a)->clash2)

static Relation clashmatrix;

static Relation copymatrix;

static RelationAllocRec clashrallocrec;
/* = {ClashAllocType, &curstats.nsquares, &curstats.squarebytes}; */

static RelationAllocRec copyallocrec;
/* = {CopyAllocType, &curstats.copysquares, &curstats.copysquarebytes}; */

static void clash_reinit(int32 nregs)
{
    curstats.nvregs = nregs;
    clashmatrix = relation_init(&clashrallocrec, nregs, &curstats.vregbytes);
    copymatrix = relation_init(&copyallocrec, nregs, &curstats.vregbytes);
    vregset_init();
}

static void add_copy(VRegnum a, VRegnum b);

static void add_clash(VRegnum a, VRegnum b)
{   /* a register can never clash with itself */
    if (a == b)
    {
        if (!(procflags & PROC_INLNASM))
            syserr(syserr_regalloc_clash, a);
        return;
    }
    /* registers with the same value number never clash */
    if (using_valnr) {
        uint32 vala = valnr_(a),
               valb = valnr_(b);
        if (   (is_real_valn_(vala) && is_real_valn_(valb) && val_(vala) == val_(valb))
            || (is_real_valn_(vala) && (vala & VALN_SLAVE)
                && RegList_Member(b, valsource_(a)))
            || (is_real_valn_(valb) && (valb & VALN_SLAVE)
                && RegList_Member(a, valsource_(b))) )
        {   if (debugging(DEBUG_REGS))
                cc_msg("Prevent clash %ld %ld - %ld%s%s\n",
                       (long)a, (long)b, (long)val_(vala),
                       vala & VALN_SLAVE ? "S" : "",
                       vala & VALN_DEAD ? "D" : "");
            add_copy(a, b);
            return;
        }
    }
#ifndef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
    {   RegSort atype = vregtype_(vreg_(a));
        RegSort btype = vregtype_(vreg_(b));
#  ifdef ADDRESS_REG_STUFF
        if (atype == ADDRREG) atype = INTREG;
        if (btype == ADDRREG) btype = INTREG;
#  endif
        if (atype != btype)
        {
           if ((atype == INTREG) || (btype == INTREG)) return;
        }
    }
#endif
    if (a < b) { VRegnum t = a; a = b; b = t; }
    if ((b < 0) || ((uint32)a >= vregistername))
        syserr(syserr_addclash, (long)a, (long)b);
    if (relation_add(a, b, clashmatrix, &clashrallocrec))
    {   vreg_(a)->u.nclashes++;
        vreg_(b)->u.nclashes++;
    }
}

static void clashkillbits_cb(IPtr k, VoidStar arg)
{   /* clashkillbits_cb is passed as parameter and so needs silly type. */
    RealRegSet *m = (RealRegSet *) arg;
    RealRegister r = register_number((VRegnum)k);
    if ((unsigned32)r<(unsigned32)NMAGICREGS)   /* @@@ isany_realreg()? */
#ifdef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
    {   /* I certainly need to do more here */
        delete_RealRegSet(m,r);
    }
#else
        delete_RealRegSet(m,r);
#endif
}

static void clashkillbits(RealRegSet *m, VRegister *reg)
{
    vregset_map(reg->clash2, clashkillbits_cb, (VoidStar)m);
}

static VRegSetAllocRec clashvallocrec;
/* = {
 *    ClashAllocType,
 *    &curstats.nregsets,
 *    &curstats.newregsets,
 *    &curstats.regsetbytes };
 */

static void removeclashes_rcb(IPtr vr, VoidStar arg)
{
    VRegSetP *residual = (VRegSetP *) arg;
    VRegister *clashee = vreg_(vr);
    clashee->u.nclashes--;
    *residual = vregset_insert(vr, *residual, NULL, &clashvallocrec);
    if (clashee->realreg == R_UNSCHEDULED)
        upheap(clashee->heapaddr);
}

static void removeclashes(VRegister *vreg)
{
    VRegnum reg = vregname_(vreg);
    VRegSetP residual = NULL;
    relation_mapanddelete(reg, clashmatrix, removeclashes_rcb,
                                            (VoidStar)&residual);
    vreg->clash2 = residual;
    vreg->clashes = vregset_difference(vreg->clashes, vreg->clash2);
    vreg->u.nclashes = 0;
}

static void printvreg(VRegnum vr)
{
    int c = 'g';
    if (vr != GAP)
    {   RegSort type = vregtype_(vreg_(vr));
        c = type == FLTREG ? 'f' :
            type == DBLREG ? 'd' :
#ifdef ADDRESS_REG_STUFF
            type == ADDRREG ? 'a' :
#endif
            'r';
    }
    cc_msg(" %c%ld", c, (long)vr);
}

static void print_clashes(VRegister *vreg)
{   /* print the set of VRegisters which clash with  vreg */
    VRegnum reg = vregname_(vreg);
    relation_map1(reg, clashmatrix, printvreg);
}

static void add_copy(VRegnum a, VRegnum b)
/* Somebody has issued a 'MOVR a,b' or maybe a 'MOV b,a'. Life will be  */
/* distinctly better if I can arrange that r1 and r2 get put in the     */
/* same real register. Make a table of associations to help me to       */
/* achieve this at least some of the time.                              */
{
    if (a == b) return;
#ifndef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
    {   RegSort atype = vregtype_(vreg_(a));
        RegSort btype = vregtype_(vreg_(b));
#ifdef ADDRESS_REG_STUFF
        if (atype == ADDRREG) atype = INTREG;
        if (btype == ADDRREG) btype = INTREG;
#endif
        if (atype != btype)
        {  /* AM believes that atype and btype will always be the same  */
           /* with the possible exception of MOVDFR.  Hence the RETURN  */
           /* below can never be executed.                              */
           if ((atype == INTREG) || (btype == INTREG)) return;
        }
    }
#endif

/* Corresponding code in add_clash() ensures a<b here.  Should we?      */
    if (relation_add(a, b, copymatrix, &copyallocrec))
    {   curstats.ncopies++;
        vreg_(a)->ncopies += b<NMAGICREGS ? 0x10000 : 1;
        vreg_(b)->ncopies += a<NMAGICREGS ? 0x10000 : 1;
    }
}

static void vregset_print(VRegSetP set)
{
    vregset_map1(set, printvreg);
}

/*
 * End of abstract data type for reg clash matrix.
 */

#else /* TARGET_IS_NULL */
static void add_clash(VRegnum r1n, VRegnum r2n)
{
    IGNORE(r1n); IGNORE(r2n);
}

static VRegSetP set_register_copy(VRegnum r, VRegSetP s, VRegnum rsource)
{
    IGNORE(r); IGNORE(s); IGNORE(rsource); return NULL;
}

static VRegSetP set_register_slave(VRegnum r, VRegSetP s, VRegnum rmaster)
{
    IGNORE(r); IGNORE(s); IGNORE(rmaster); return NULL;
}

#endif /* TARGET_IS_NULL */

static void stats_print(RegStats *p)
{
    cc_msg("-- passes %2li: copies =%4ld, lists = %4ld, vregs = %4ld\n",
           p->dataflow_iterations, p->ncopies, p->nlists, p->nvregs);
    cc_msg("%19s %6ld %13ld %13ld\n", "space",
           p->copysquarebytes, p->listbytes, p->vregbytes);
    cc_msg("--            squares =%4ld, regsets =%4ld, bytes =%6ld\n",
           p->nsquares, p->nregsets, p->clashbytes);
    cc_msg("%19s %6ld %13ld  total=%6ld\n", "space",
           p->squarebytes, p->regsetbytes, p->clashbytes);
}

static void stats_endproc(void)
{   unsigned32  x, j, *cur, *max;

    curstats.clashbytes = curstats.vregbytes +
                          curstats.squarebytes + curstats.regsetbytes;

    if (curstats.nvregs >= 128) {
        cc_msg("regalloc space stats for big procedure:\n");
        stats_print(&curstats);
    }

    cur = (unsigned32 *)&curstats;
    max = (unsigned32 *)&maxstats;
    for (j = 0; j < sizeof(curstats)/sizeof(unsigned32); ++j)
    {   x = *cur++; if (x > *max) *max = x;
        ++max;
    }
}

/* Consider (p() ? 0:1).  If we generate <test> ... MOVK v,0 ... MOVK v,1  */
/* and 0,1 are put in master regs i0,i1 then we find that v is a slave of  */
/* both i0 and i1. The code in regalloc then causes v not to clash with    */
/* either i0 nor i1 which can allow i0 to share with v in spite of the fact*/
/* that v can  be updated to 1 when i0 is still live.                      */
/* HACK.  Note that things are OK when slave_list is a (reverse) forest    */
/* Hence delete all entries (v,i0), (v,i1) when i0 != i1.                  */
/* Memo to AM: the idea of slave_list would better be replaced with a     */
/* general algorithm which stops x & y clashing in:                       */
/*  f(x) { int y = x; return x+y;}                                        */

#ifndef TARGET_IS_NULL

typedef struct ReadonlyCopy     /* loopopt.c and regalloc.c interface   */
{
  struct ReadonlyCopy *next;
  VRegnum r1;
  VRegnum r2;
} ReadonlyCopy;

static ReadonlyCopy *slave_list;

/* note_slave() and forget_slave() are exported for cse.c:              */
void note_slave(VRegnum slave, VRegnum master)
{   ReadonlyCopy *p;
    for (p = slave_list; p != NULL; p = p->next)
        if (p->r1 == slave)
        {   if (p->r2 != master) p->r2 = GAP;   /* see above note re trees */
            return;
        }
    /* allocate BindAlloc store to survive into regalloc.c */
    p = (ReadonlyCopy *) BindAlloc(sizeof(ReadonlyCopy));
    p->next = slave_list, p->r1 = slave, p->r2 = master;
    slave_list = p;
}

void forget_slave(VRegnum slave, VRegnum master)
{   ReadonlyCopy *p, **prev;
    for (prev = &slave_list; (p = *prev) != NULL; prev = &p->next)
        if (p->r1 == slave)
        {   if (p->r2 == master) *prev = p->next;
            else if (!isany_realreg_(slave) && p->r2 != GAP)
                syserr(syserr_forget_slave, slave, master, p->r2);
            return;
        }
}

static bool reg_overlord(VRegnum r1, VRegnum r2)
/* true iff (r1,r2) is in the transitive closure of slave_list */
{   for (;;)
    {   VRegnum r = vreg_(r1)->slave;
        if (r == r2) return YES;
        else if (r == GAP) return NO;
        r1 = r;
    }
}

#else
void note_slave(VRegnum slave, VRegnum master)
{
    IGNORE(slave);
    IGNORE(master);
}

#endif

#ifdef LSBUSE_CONSISTENCY_CHECK
static uint8 *lsbmap;
#define LSBQUANTUM 128
#define lsbmap_(r) (lsbmap[r/(8*LSBQUANTUM)] & (1<<((r/LSBQUANTUM)%8)))
#define setlsbmap_(r) (lsbmap[r/(8*LSBQUANTUM)] |= 1<<((r/LSBQUANTUM)%8))
#else
#define lsbmap_(r) 1
#define setlsbmap_(r)
#endif

static VRegSetAllocRec listallocrec;
/* = {ListAllocType, &curstats.nlists, &curstats.newlists,
 *                   &curstats.listbytes};
 */

/* Sept 91: define procs to hide vregset_xxx/reg_lsbusetab reps.        */
static int reg_demand(VRegnum r)
{   if ((unsigned32)r >= vregistername) syserr(syserr_regno, (long)r);
    return reg_lsbusetab[r];
}
static void live_print(char *s)
{   unsigned i;
    cc_msg("live(%s):", s);
    for (i = 0; i < vregistername; i++)
        if (reg_lsbusetab[i]) cc_msg(" r%d:%d", i, reg_lsbusetab[i]);
    cc_msg("\n");
}
static void live_union_anon(VRegnum r)
{   if ((unsigned32)r >= vregistername) syserr(syserr_regno, (long)r);
    setlsbmap_(r);
    reg_lsbusetab[r] = ALLBITS;
}
static VRegSetP live_union(VRegSetP s1, VRegSetP s2, VRegSetAllocRec *allocrec)
{   vregset_map1(s2, live_union_anon);
    return vregset_union(s1, s2, allocrec);
}
static bool live_member(VRegnum r, VRegSetP set)
{   return vregset_member((int32)r, set);
}
static VRegSetP live_delete(VRegnum r, VRegSetP set, bool *livep)
{   if ((unsigned32)r >= vregistername) syserr(syserr_regno, (long)r);
    setlsbmap_(r);
    reg_lsbusetab[r] = 0;
    return vregset_delete((int32)r, set, livep);
}

/* One can think of 'reference_register()' as 'live_insert()'...        */

static VRegSetP reference_register(
    VRegnum r, int demand, VRegSetP s, bool *alreadylive)
/* s is a list of registers whose value is needed. We have encountered   */
/* (in a backwards scan over a basic block) an instruction that uses the */
/* value of register r.  r gets added to the list of registers that need */
/* to be given a value.                                                  */
/* BEWARE: the result is compared with s to determine if s became live.  */
/* Sep 91: Is this still true?                                           */
{
    if ((unsigned32)r >= vregistername) /* includes 'GAP' */
        syserr(syserr_regno, (long)r);
    s = vregset_insert(r, s, alreadylive, &listallocrec);
    setlsbmap_(r);
    if (reg_lsbusetab[r] < demand) reg_lsbusetab[r] = demand;
    return s;
}

/* things for pass2 (the exact clash info) only ... */

static BindList *thisBlocksBindList;

static void makebindersclash(VRegnum r, BindList *bl, VRegnum rx)
{   BindList *ab = argument_bindlist;
    for ( ; ab!=NULL ; ab = ab->bindlistcdr ) {
        VRegnum r1 = bindxx_(ab->bindlistcar);
        if (r1!=GAP && r1!=rx && r1!=r) add_clash(r1, r);
    }

    for ( ; bl!=NULL ; bl = bl->bindlistcdr ) {
        VRegnum r1 = bindxx_(bl->bindlistcar);
        if (r1!=GAP && r1!=rx && r1!=r) add_clash(r1, r);
    }
}

static void setregister_cb(IPtr r, VoidStar r1)
{   /* the type of 'r1' is a lie for map-function vregset_map.          */
    add_clash((VRegnum)r, (VRegnum)(IPtr)r1);
}

static VRegSetP set_register1(VRegnum r, VRegSetP s)
{
    vregset_map(s, setregister_cb, (VoidStar)(IPtr)r);
#ifdef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
    if (is_physical_double_reg_(r))
        vregset_map(s, setregister_cb, (VoidStar)(IPtr)other_halfreg(r));
#endif
    if (usrdbg(DBG_VAR) && !usrdbg(DBG_OPT_REG))
        makebindersclash(r, thisBlocksBindList, GAP);
    return s;
}

static void corrupt_register(VRegnum r, VRegSetP s)
/* register r has its value altered by this instruction, but not in a    */
/* useful or predictable way. Ensure that r is not unified with any      */
/* other register currently active                                       */
{
/* AM has thought and sees no real difference between corrupt_register */
/* and set_register */
    if (vregset_member(r, s))
    {   if (procflags & PROC_INLNASM)
        {   if (!(warn_corrupted_regs & regbit(r)))
                cc_warn(asm_err_corrupted_reg, r);
            warn_corrupted_regs |= regbit(r);
            return;
        }
        else
            syserr(syserr_corrupt_register, (long)r, s);  /* insert to check */
    }
    set_register1(r, s);
}

static void corrupt_physical_register(VRegnum r, VRegSetP s)
{   /* 'r' must be a physical register, corrupt it and add it to        */
    /* regmaskvec.                                                      */
    if (!isany_realreg_(r)) syserr(syserr_regalloc);
    augment_RealRegSet(&regmaskvec, r);
#ifdef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
    if (is_physical_double_reg_(r))
        augment_RealRegSet(&regmaskvec, other_halfreg(r));
#endif
    corrupt_register(r, s);
}

static VRegSetP set_register(VRegnum r, VRegSetP s)
/* This is called when an instruction that sets r is found (and when the */
/* instruction is not a direct copy instruction, and when then value of  */
/* the register is (expected to be) needed.                              */
{
    if (isany_realreg_(r))      /* physical register used -> need to be saved */
        augment_RealRegSet(&regmaskvec, r);
    /* In the next line, if !member(r,s) we have the dataflow anomaly */
    /* 'register set but value not used'.  In general this will be    */
    /* optimised away, but it also occurs for calls to void functions */
    /* and so is better reported elsewhere (see J_STRV code below).   */
    s = live_delete(r, s, NULL);
#ifdef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
    if (is_physical_double_reg_(r))
        s = live_delete(other_halfreg(r), s, NULL);
#endif
    return set_register1(r, s);
}

#ifndef TARGET_IS_NULL

typedef struct {
    VRegnum r;
    VRegnum rsource;
    RegList *rlist;
} SRCRecord;

static void setregistercopy_cb(IPtr ar, VoidStar arg)
{
    SRCRecord *p = (SRCRecord *)arg;
    VRegnum r = (VRegnum)ar;
    if (r != p->rsource && r != p->r) add_clash(p->r, r);
}

static void setregistercopy_cb2(IPtr ar, VoidStar arg)
{
    SRCRecord *p = (SRCRecord *)arg;
    VRegnum r = (VRegnum)ar;
    if (val_(valnr_(r)) == val_(valnr_(p->r)))
        p->rlist = mkRegList(p->rlist, r);
}

static VRegSetP set_register_copy(VRegnum r, VRegSetP s, VRegnum rsource)
/* This is called when an instruction that copies rsource into r is seen */
{
    SRCRecord sc;
    bool debug_regs = usrdbg(DBG_VAR) && !usrdbg(DBG_OPT_REG);
    /* If r is a global register variable and r is dead, other vregs
     * may share the same register. Only when register optimizations
     * are disabled this is suppressed by not calling live_delete.
     */
    if (!debug_regs || !vregset_member(r, globalregvarset))
        s = live_delete(r, s, NULL);
    sc.r = r; sc.rsource = rsource;
    if (using_valnr && val_(valnr_(r)) == val_(valnr_(rsource))
        && is_real_valn_(valnr_(r))) {
        sc.rlist = NULL;
        relation_map(r, copymatrix, setregistercopy_cb2, &sc);
        while (sc.rlist != NULL) {
            add_copy(rsource, (VRegnum)sc.rlist->rlcar);
            sc.rlist = (RegList *)discard2(sc.rlist);
        }
    }
/* r conflicts with all live registers EXCEPT rsource.                   */
    vregset_map(s, setregistercopy_cb, (VoidStar) &sc);
    if (debug_regs)
        makebindersclash(r, thisBlocksBindList, rsource);
    if (debugging(DEBUG_REGS))
        cc_msg("Record copy %ld %ld\n", (long)r, (long)rsource);
    add_copy(r, rsource);
    return s;
}

static void setregisterslave_cb(IPtr r, VoidStar r1)
{   /* the type of 'r1' is a lie for map-function vregset_map.          */
    if (!reg_overlord((VRegnum)(IPtr)r1, (VRegnum)r))
        add_clash((VRegnum)r, (VRegnum)(IPtr)r1);
}

static VRegSetP set_register_slave(VRegnum r, VRegSetP s, VRegnum rmaster)
/* This is a re-working of slave_list.  Not yet final because it builds  */
/* in the knowledge that code in other parts of the compiler did it.     */
/* r is a slave target register being set.  Arrange that it clashes with */
/* all live registers except its masters.                                */
{
    s = live_delete(r, s, NULL);
/* r conflicts with all live registers EXCEPT its masters.               */
    vregset_map(s, setregisterslave_cb, (VoidStar)(IPtr)r);

    if (usrdbg(DBG_VAR) && !usrdbg(DBG_OPT_REG)) {
        BindList *bl = thisBlocksBindList;
        for ( ; bl!=NULL ; bl = bl->bindlistcdr ) {
            VRegnum r1 = bindxx_(bl->bindlistcar);
            if (r1 != GAP && !reg_overlord(r, r1)) add_clash(r1, r);
        }
    }

    if (debugging(DEBUG_REGS))
        cc_msg("Record slave copy %ld %ld\n", (long)r, (long)rmaster);
    add_copy(r, rmaster);
    return s;
}

#endif /* TARGET_IS_NULL */

/* Value numbering pass, called once per block before register clashes   */
/* are collected for the block. All registers are set to a distinguished */
/* 'UNSET' state, apart from those imported to the block (which are each */
/* allocated distinct value numbers). Writes to a destination register   */
/* are either                                                            */
/*   copies from a source register. The value number of the source       */
/*          register is written to the value number of the destination   */
/*   something else. A new value number, distinct from any other, is     */
/*          given to the destination register                            */
/* In either case, if the value number of the destination is not 'UNSET',*/
/* the destination receives a sticky 'WRITTEN TWICE' flag.               */
/* Then, during the collection of register clashes, if a call to         */
/* add_clash(a, b) is made but valnr_(a) == valnr_(b) (and neither has   */
/* the 'WRITTEN TWICE' flag) the clash is not added and moreover, a is   */
/* made a copy of b.                                                     */

/* This is still not perfect, even given its strictly local nature.      */
/* for example in k = i; j = f(k); (k now dead) i = new value            */
/* it cannot detect that k need not clash with i (indeed, k can be a     */
/* slave of i)                                                           */

static uint32 current_value_number;
static uint32 max_value_number;

struct ValnRegList {
  ValnRegList *cdr;
  VRegnum rno;
  size_t wc;
};
#define rno_(rl) ((rl)->rno)
#define wc_(rl) ((rl)->wc)
#define ValnRegList_DiscardOne(l) ((ValnRegList *)discard3(l))

#define VALNSEGBITS 9
#define VALNSEGSIZE (1<<VALNSEGBITS)
#define VALNSEGMAX  64
static ValnRegList **valn_index[VALNSEGMAX];
#define valn_list_(n) (valn_index[(n)>>VALNSEGBITS])[(n)&(VALNSEGSIZE-1)]

static void init_value_number(int n) {
  current_value_number = n;
}

static void init_valn_seg(uint32 n) {
  ValnRegList **newv = (ValnRegList **)SynAlloc(VALNSEGSIZE * sizeof(ValnRegList *));
  uint32 i;
  for (i = 0; i < VALNSEGSIZE; i++)
    newv[i] = NULL;
  valn_index[n>>VALNSEGBITS] = newv;
}

static void valn_reinit(void) {
  current_value_number = max_value_number = 0;
  init_valn_seg(0);
}

static uint32 new_valnr(void) {
  uint32 n = ++current_value_number;
  if (n > max_value_number) {
    max_value_number = n;
    if ((n & (VALNSEGSIZE-1)) == 0)
      init_valn_seg(n);
  }
  valn_list_(n) = NULL;
  return n;
}

static ValnRegList *MkValnRegList(ValnRegList *l, VRegnum r, uint32 wc) {
  ValnRegList *res = (ValnRegList *)SynAlloc(sizeof(ValnRegList));
  cdr_(res) = l; rno_(res) = r; wc_(res) = wc;
  return res;
}

static ValnRegList *ValnRegList_Discard(ValnRegList *p) {
  while (p != NULL)
    p = ValnRegList_DiscardOne(p);
  return NULL;
}

static ValnRegList *ValnRegList_Copy(ValnRegList *p) {
  ValnRegList *res = NULL;
  for (; p != NULL; p = cdr_(p))
    res = MkValnRegList(res, rno_(p), wc_(p));
  return res;
}

static ValnRegList *ValnRegList_NDelete(VRegnum a, ValnRegList *l)
{
    ValnRegList *r = l, *s;
    if (l == NULL)
        return l;
    else if (rno_(l) == a)
        return (ValnRegList *)discard3(l);
    do
    {   s = l;
        l = cdr_(l);
        if (l == NULL) return r;
    } while (rno_(l) != a);
    cdr_(s) = (ValnRegList *)discard3(l);
    return r;
}


static void write_valnr(VRegnum dst, uint32 newvaln) {
  uint32 oldvaln = val_(valnr_(dst));
  if (newvaln == VALN_UNSET) {
    /* This is unfortunately necessary because there's no way to mark */
    /* instructions which are going to be killed, but the registers   */
    /* they read won't be seen as imports to a block (so will still be*/
    /* marked unset).                                                 */
    newvaln = new_valnr();
  }
  if (oldvaln == VALN_UNSET) {
    valsource_(dst) = ValnRegList_Copy(valn_list_(val_(newvaln)));
  } else {
    valn_list_(oldvaln) = ValnRegList_NDelete(dst, valn_list_(oldvaln));
    valsource_(dst) = ValnRegList_Discard(valsource_(dst));
    newvaln |= VALN_MULTIPLE;
  }
  valn_list_(val_(newvaln)) = MkValnRegList(valn_list_(val_(newvaln)), dst, ++valwritecount_(dst));
  valnr_(dst) = newvaln;
  if (debugging(DEBUG_REGS))
    cc_msg("%ld - %ld%s\n", dst, newvaln & ~VALN_MULTIPLE, newvaln & VALN_MULTIPLE ? "!" : "");
}

#define copy_valnr(dst, src) write_valnr((dst), val_(valnr_(src)))
#define set_valnr(dst) write_valnr((dst), new_valnr())

static void check_valnr_slave(VRegnum r) {
  if (is_real_valn_(r)) {
    ValnRegList *p, **prevp = &valsource_(r);
    while ((p = *prevp) != NULL)
      if (val_(valnr_(r)) != val_(valnr_(rno_(p)))
          || (valnr_(rno_(p)) & VALN_DEAD)
          || wc_(p) != valwritecount_(rno_(p)))
        *prevp = ValnRegList_DiscardOne(p);
      else {
        if (debugging(DEBUG_REGS))
          cc_msg("valn_slave %ld %ld\n", r, rno_(p));
        valnr_(r) |= VALN_SLAVE;
        prevp = &cdr_(p);
      }
    valnr_(r) |= VALN_DEAD;
  }
}

static void set_valnr_f1(RealRegister r) {
  set_valnr(r);
}

static void set_valnr_f2(RealRegister r, RealRegSet_MapArg *a) {
  IGNORE(a);
  set_valnr(r);
}

static void init_value_numbers(BlockHead *b)
{   uint32 n, r;
    for (n = 0; n < max_value_number; n++)
        valn_list_(n) = ValnRegList_Discard(valn_list_(n));

    /* Mark all registers as 'not yet written' ...                       */
    init_value_number(VALN_REAL);
    for (r = 0; r < vregistername; r++) {
        valnr_(r) = VALN_UNSET;
        valsource_(r) = ValnRegList_Discard(valsource_(r));
        valwritecount_(r) = 0;
    }
    /* ... except those used by the block, which acquire new value       */
    /* numbers now ...                                                   */
    vregset_map1(blkuse_(b), set_valnr_f1);
}


static void instruction_copy_info(const Icode *ic)
{   const int32 op = ic->op & J_TABLE_BITS;
    switch (op)
    {
        case J_INIT:
        case J_INITF:
        case J_INITD:
            break;
        case J_MOVR:
        case J_MOVFR:
        case J_MOVDR:
#ifdef TARGET_IS_ARM
        case J_MOVFDR:
#endif
            copy_valnr(ic->r1.r, ic->r3.r);
            break;
        case J_LDRV:
        case J_LDRFV:
        case J_LDRDV:
            if (bindxx_(ic->r3.b) != GAP)
                copy_valnr(ic->r1.r, bindxx_(ic->r3.b));
            else
                set_valnr(ic->r1.r);
            break;
        case J_STRV:
        case J_STRFV:
        case J_STRDV:
            if (bindxx_(ic->r3.b) != GAP)
                copy_valnr(bindxx_(ic->r3.b), ic->r1.r);
            break;
        case J_ADCON:
        case J_ADCONV:
        case J_ADCONF:
        case J_ADCOND:
        case J_MOVK:
            if (ic->r2.r != GAP)
                copy_valnr(ic->r1.r, ic->r2.r);
            else
                set_valnr(ic->r1.r);
            break;
        default:
        {   RealRegUse reg;
            RealRegSet corrupt;

            RealRegisterUse(ic, &reg);
            map_RealRegSet(&reg.def, set_valnr_f2, NULL);
            difference_RealRegSet(&corrupt, &reg.c_in, &reg.def);
            union_RealRegSet(&corrupt, &reg.c_out, &corrupt);
            map_RealRegSet(&corrupt, set_valnr_f2, NULL);
            if (loads_r1(op) || corrupts_r1(ic)) set_valnr(ic->r1.r);
            if (loads_r2(op) || corrupts_r2(ic)) set_valnr(ic->r2.r);
        }
    }
    if (ic->op & J_DEAD_R1)
        check_valnr_slave(ic->r1.r);
    if (ic->op & J_DEAD_R2)
        check_valnr_slave(ic->r2.r);
    if (ic->op & J_DEAD_R3) {
        if (uses_stack(op))
            check_valnr_slave(bindxx_(ic->r3.b));
        else
            check_valnr_slave(ic->r3.r);
    }
    if (ic->op & J_DEAD_R4)
        check_valnr_slave(ic->r4.r);
}


static VRegSetP instruction_ref_info(VRegSetP s1, Icode const *const ic,
                                     UPtr *exact, int demand)
{
    const int32 op = ic->op & J_TABLE_BITS;
    int32 dataflow = 0;
/* 'exact' is non-0 for the final pass when exact dataflow info is required */
/* It is convenient to arrange it to be a pointer to where J_DEAD_Rx is put */
/* Note that 'op' here has been masked with J_TABLE_BITS.                   */

    if (isproccall_(op))    /* global register variables are live at any call */
        s1 = live_union(s1, globalregvarset, &listallocrec);
    if (reads_r2(op) ||
        (pseudo_reads_r2(op) && ic->r2.r!=GAP))    /* MOVK/ADCON loopopt */
    {   bool alreadylive;
        s1 = reference_register(ic->r2.r, reg_bitsrefd(ic,demand,2), s1, &alreadylive);
        if (exact && !alreadylive) dataflow |= J_DEAD_R2;
    }
    if (reads_r3(op))
    {   bool alreadylive;
        s1 = reference_register(ic->r3.r, reg_bitsrefd(ic, demand, 3), s1, &alreadylive);
        if (exact && !alreadylive) dataflow |= J_DEAD_R3;
    }
    else if (loads_r1(op) && uses_stack(op) && op != J_ADCONV)
    {   VRegnum r = bindxx_(ic->r3.b);
        if (r != GAP)
        {   bool alreadylive;
            s1 = reference_register(r, reg_bitsrefd(ic,demand,3), s1, &alreadylive);
            if (exact && !alreadylive) dataflow |= J_DEAD_R3;
        }
    }
    if (reads_r4(op))
    {   bool alreadylive;
        s1 = reference_register(ic->r4.r, reg_bitsrefd(ic,demand,4), s1, &alreadylive);
        if (exact && !alreadylive) dataflow |= J_DEAD_R4;
    }
    if (reads_r1(op)
        || (pseudo_reads_r1(op) && ic->r1.r!=GAP))    /* CMPK loopopt */
    {   bool alreadylive;
        s1 = reference_register(ic->r1.r, reg_bitsrefd(ic,demand,1), s1, &alreadylive);
        if (exact && !alreadylive) dataflow |= J_DEAD_R1;
    }
    if (reads_psr(ic))
    {   s1 = reference_register(R_PSR, ALLBITS, s1, NULL);
    }
    if (exact)
    {   *exact = (*exact & ~J_DEADBITS) | dataflow;
    }
    return s1;
}

VRegSetP exitregset(VRegnum result, VRegSetP s)
{   /* return registers which are alive on function exit */
    int32 n;
    s = live_union(s, globalregvarset, &listallocrec);
    if (result != GAP) {
        s = reference_register(result, ALLBITS, s, NULL);
        for (n = 1; n < currentfunction.nresultregs; n++)
            s = reference_register(result + n, ALLBITS, s, NULL);
    }
    if (pcs_flags & PCS_NOFP)
        s = reference_register(R_SP, ALLBITS, s, NULL); /* SP or FP alive on exit */
    else
        s = reference_register(R_FP, ALLBITS, s, NULL);
    if (!(pcs_flags & PCS_NOSTACKCHECK))
        s = reference_register(R_SL, ALLBITS, s, NULL); /* SL alive if stackchecking */
    if (pcs_flags & PCS_REENTRANT)
        s = reference_register(R_SB, ALLBITS, s, NULL); /* SB alive if reentrant */
    return s;
}

static VRegSetP extra_regs(VRegSetP s, LabelNumber *q)
/* update the list s to reflect things needed by the block with label q. */
/* Note that q can have one of the special values RetIntLab, RetFloatLab */
/* or RetVoidLab (for exit labels).   New RetImplLab.                    */
/* This procedure is applied repeatedly to all blocks in the flowgraph   */
/* to find definitive information about what registers are used by which */
/* blocks.                                                               */
{   /* local to successor_regs() */
    if (q == RetIntLab)
        return exitregset(V_Presultreg(INTREG), s);
    else if (q == RetDbleLab)
        return exitregset(V_Presultreg(DBLREG), s);
    else if (q == RetFloatLab)
        return exitregset(V_Presultreg(FLTREG), s);
    else if (q == RetVoidLab || q == RetImplLab)
        return exitregset(GAP, s);
    else
        return live_union(s, blkuse_(q->block), &listallocrec);
}

static VRegSetP successor_regs(BlockHead *p)
{   /* local to collect_register_clashes and update_block_use_info */
/* Produce a list of the registers required at the end of block p        */
/* This is done by merging the blkuse_() information from all succesor   */
/* blocks.                                                               */
    VRegSetP s1 = NULL;
    memclr(reg_lsbusetab, (size_t)vregistername);
#ifdef LSBUSE_CONSISTENCY_CHECK
    memclr(lsbmap, (size_t)(vregistername/(LSBQUANTUM*8))+1);
#endif
    if (blkflags_(p) & BLKSWITCH)
    {   LabelNumber **v = blktable_(p);
        int32 i, n = blktabsize_(p);
        for (i=0; i<n; i++) s1 = extra_regs(s1, v[i]);
    }
    else
    {   s1 = extra_regs(s1, blknext_(p));
        if (blkflags_(p) & BLK2EXIT) s1 = extra_regs(s1, blknext1_(p));
    }
    if (debugging(DEBUG_REGS)) live_print("succ regs");
    return s1;
}

static VRegSetP live_deleteresults(VRegInt r2, VRegSetP s1, bool *livep) {
    int32 n = k_resultregs_(r2.i);
    bool live = NO;
    for (; --n >= 0;) {
        bool live2;
        s1 = live_delete(R_A1+n, s1, &live2);
        live |= live2;
    }
    *livep = live;
    return s1;
}

static void use_f(RealRegister r, RealRegSet_MapArg * a)
{   a->vr = reference_register(r, ALLBITS, a->vr, NULL);
}

static void def_f(RealRegister r, RealRegSet_MapArg * a)
{   a->vr = live_delete(r, a->vr, NULL);
}


static VRegSetP add_instruction_info(VRegSetP s1, Icode *ic, UPtr *deadp, bool removed)
{
    bool live_r1, live_r2, live_psr = NO;
    J_OPCODE op = ic->op & J_TABLE_BITS;

    if (sets_psr(ic))
        s1 = live_delete(R_PSR, s1, &live_psr);
    if (loads_r2(op) && loads_r1(op) && !removed)
    {   /* more code needed for (1) 'removed' and (2) SHARES_INT_AND_FP */
        s1 = live_delete(ic->r2.r, s1, &live_r2);
        s1 = live_delete(ic->r1.r, s1, &live_r1);
        if (!live_r1 && !live_r2 && !live_psr && !has_side_effects(ic))
        {
            if (debugging(DEBUG_REGS)) print_xjopcode(ic, "-> NOOP loads r1&r2 (a)");
            ic = &ic_noop, op = J_NOOP;
        }
    }
    else if (loads_r2(op) && !removed)
    {
        s1 = live_delete(ic->r2.r, s1, &live_r2);
        if (!live_r2 && !live_psr && !has_side_effects(ic))
        {
            if (debugging(DEBUG_REGS)) print_xjopcode(ic, "-> NOOP loads r2 (a)");
            ic = &ic_noop, op = J_NOOP;
        }
    }
    else if (loads_r1(op) && !removed)
        {   bool live_results;
            if ( iscalln_(op, ic->r2.i) &&
                      (s1 = live_deleteresults(ic->r2, s1, &live_results),
                      live_results)) /*nothing*/;
            else
#ifdef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
                 if ((J_fltisdouble(op) && isany_realreg_(ic->r1.r) ?
                          s1 = live_delete(other_halfreg(ic->r1.r), s1, NULL) : NULL),
                     s1 = live_delete(ic->r1.r, s1, &live_r1),
                     live_r1) /*nothing*/;
#else
            if (s1 = live_delete(ic->r1.r, s1, &live_r1), live_r1) /*nothing*/;
#endif
            else if (usrdbg(DBG_VAR+DBG_LINE) && !usrdbg(DBG_OPT_REG)) /*nothing*/;
                 /* leave unused code alone if debugging */
            else if (op == J_CALLK)
               /* I suppose this should really be just calls with K_PURE */
            {   if (ic->r3.b == exb_(arg1_(sim.mulfn)))
                    /* ignore mult if result seems (so far) unwanted */
                    ic = &ic_noop, op = J_NOOP;
                else if (ic->r3.b == exb_(arg1_(sim.divfn)) ||
                         ic->r3.b == exb_(arg1_(sim.udivfn)) ||
                         ic->r3.b == exb_(arg1_(sim.remfn)) ||
                         ic->r3.b == exb_(arg1_(sim.uremfn)))
                {
                    /* a division where the result is not needed can be treated as a one-arg */
                    /* function call. */
                    Icode icnew = *ic;
                    icnew.r2.i = k_argdesc_(1, 0, 1,0,0,0);
                    ic = &icnew;
                }
            }
            else if (op == J_OPSYSK || op == J_CALLR) /*nothing*/;
            else if (!live_psr && !has_side_effects(ic))
            {   /* we had better not treat a voided fn as dead code */
                if (debugging(DEBUG_REGS))
                    print_xjopcode(ic, "-> NOOP loads r1 (a)");
                ic = &ic_noop, op = J_NOOP;
            }
        }
        if (uses_stack(op) && op!=J_ADCONV)
        {   VRegnum r3 = bindxx_(ic->r3.b);
/* usage information is accumulated for the virtual register that I will */
/* use if I manage to map this stack location onto a register.           */
            if (r3 != GAP)
            {   bool live_r3;
                if (loads_r1(op)) {
                     /* Now handled by instruction_ref_info() */
                /* this else case is really J_STRV/STRDV/STRFV */
                } else if (vregset_member(r3, globalregvarset) ||
                         (s1 = live_delete(r3, s1, &live_r3), live_r3))
                {    /* nothing */
                } else if ((bindstg_(ic->r3.b) & (b_addrof|b_spilt)) == 0 &&
                         (!usrdbg(DBG_VAR+DBG_LINE) || usrdbg(DBG_OPT_REG)))
                {
                    if (debugging(DEBUG_REGS))
                        print_xjopcode(ic, "-> NOOP store %ld (a)", (long)r3);
                    ic = &ic_noop, op = J_NOOP;
                }
            }
        }
#ifdef TARGET_IS_ARM_OR_THUMB
        {
            RealRegUse reg;
            RealRegSet_MapArg a; a.vr = s1;

            RealRegisterUse(ic, &reg);
            if (nonempty_RealRegSet(&reg.def, INTREG))
                map_RealRegSet(&reg.def, def_f, &a);
            if (nonempty_RealRegSet(&reg.use, INTREG))
                map_RealRegSet(&reg.use, use_f, &a);
            s1 = a.vr; /* copy altered set back! */
        }
#endif
        return instruction_ref_info(s1, ic, deadp, ALLBITS);
}

static bool update_block_use_info(BlockHead *p)
/* scan a basic block backwards recording information about which        */
/* virtual registers will be needed at the start of the block.           */
{
    VRegSetP s1 = successor_regs(p);
    Icode *const q = blkcode_(p);
    int32 w;
/* Now scan this block backwards to see what is needed at its head.      */
    if (blkflags_(p) & BLK2EXIT)
        s1 = reference_register(R_PSR, ALLBITS, s1, NULL);
    for (w=blklength_(p)-1; w>=0; w--)
        s1 = add_instruction_info(s1, &q[w], &q[w].op, 0);

    {   VRegSetP s2 = blkuse_(p);
        bool same = vregset_equal(s1, s2);
        vregset_discard(s2);
        blkuse_(p) = s1;
#ifndef TARGET_IS_NULL
        if (debugging(DEBUG_REGS))
        {   cc_msg("Block %ld uses: ", (long)lab_name_(blklab_(p)));
            vregset_print(s1);
            cc_msg("\n");
        }
#endif
#ifdef LSBUSE_CONSISTENCY_CHECK
        /* REGALLOC_CHAR_OPTIMISER */
        {   /* lets do a consistency check on the new code.             */
            uint32 i;
            if (debugging(DEBUG_REGS)) live_print("block regs");
            for (i = 0, s2 = NULL; i < vregistername; i += LSBQUANTUM)
              if (lsbmap_(i)) {
                int32 j, max = i+LSBQUANTUM < vregistername ? i+LSBQUANTUM : vregistername;
                for (j = i; j < max; j++)
                if (reg_lsbusetab[j])
                    s2 = vregset_insert(j, s2, NULL, &listallocrec);
              }
            if (!vregset_equal(s1, s2))
                syserr(syserr_liveness);
            vregset_discard(s2);
        }
#endif
        return !same;
    }
}

static void increment_refcount(VRegnum n, BlockHead *p)
{
    if (n != GAP) vreg_(n)->refcount += (8L << blknest_(p));
}

static bool liveresult(VRegnum r2, VRegSetP s1) {
    int32 n = k_resultregs_(r2);
    for (; --n >= 0;)
        if (live_member(R_A1result+n, s1)) return YES;
    return NO;
}

static VRegSetP set_result_registers(VRegnum r2, VRegSetP s1) {
    int32 n = k_resultregs_(r2);
    for (; --n >= 0;) s1 = set_register(R_A1+n, s1);
    return s1;
}

static void crc_f1(RealRegister r, RealRegSet_MapArg *a)
{   corrupt_physical_register(r, a->vr);
}

static void use_f_reg(RealRegister r, RealRegSet_MapArg * a)
{   a->vr = reference_register(r, ALLBITS, a->vr, NULL);
}

static void def_f_reg(RealRegister r, RealRegSet_MapArg *a)
{   a->vr = set_register(r, a->vr);
}

static void clash_f_reg(RealRegister r, RealRegSet_MapArg *a)
{
    if (r != a->r) add_clash(r, a->r);
}

static void collect_register_clashes(BlockHead *p)
/* Called after block register use info has converged. (!pass1)          */
/* scan a basic block backwards recording information about which        */
/* virtual registers clash with each other.                              */
/* Essentially a souped-up version of update_block_use_info  (merge?)    */
{
    VRegSetP s1 = successor_regs(p);
    Icode *const q = blkcode_(p);
    int32 w;
#ifdef TARGET_IS_ARM_OR_THUMB
    RealRegUse reg;
#endif
    thisBlocksBindList = blkstack_(p);

    if (usrdbg(DBG_VAR) && !usrdbg(DBG_OPT_REG)) {
/* if we are generating debug data, cause all binders with extent that   */
/* includes this block to clash with all others.                         */
        BindList *bl = blkstack_(p);
        for ( ; bl!=NULL ; bl = bl->bindlistcdr ) {
            Binder *b = bl->bindlistcar;
            VRegnum r = bindxx_(b);
            if (r!=GAP) makebindersclash(r, bl->bindlistcdr, GAP);
        }
    }
    if (blkflags_(p) & BLK2EXIT)
        s1 = reference_register(R_PSR, ALLBITS, s1, NULL);
    /* Do the value numbering pass - initialize all global registers */
    init_value_number(VALN_REAL);
    init_value_numbers(p);
    for (w = 0; w <blklength_(p); w++)
        instruction_copy_info(&q[w]);

    for (w=blklength_(p)-1; w>=0; w--)
    {   Icode *const ic = &q[w];
        int32 op = ic->op & J_TABLE_BITS;
        int demand = ALLBITS;
        bool live_psr = NO;
/* Obviously, if TARGET_SHARES_INTEGER_AND_FP_REGISTERS then J_MOVDIR   */
/* could make some optimisations...                                     */
#ifdef TARGET_IS_ARM_OR_THUMB
        RealRegisterUse(ic, &reg);
        if (nonempty_RealRegSet(&reg.c_out, INTREG)) {
            RealRegSet_MapArg a; a.vr = s1;
            map_RealRegSet(&reg.c_out, crc_f1, &a);
        }
#endif
        if (sets_psr(ic))
            s1 = live_delete(R_PSR, s1, &live_psr);
        if (updates_r2(op) && !live_member(ic->r2.r, s1))
            remove_writeback(ic);
        if (updates_r1(op) && !live_member(ic->r1.r, s1))
            remove_writeback(ic);
        op = ic->op & J_TABLE_BITS;
        if (loads_r2(op) && loads_r1(op))
        {   /* assumes 'loads_r2' ops demand ALLREGS...                 */
            if (!live_member(ic->r2.r, s1) && !live_member(ic->r1.r, s1) && !live_psr && !has_side_effects(ic))
            {   if (debugging(DEBUG_REGS)) print_xjopcode(ic, "-> NOOP loads r1&r2");
                INIT_IC (*ic, J_NOOP);
                op = J_NOOP;
            }
            else
            {
                s1 = set_register(ic->r2.r, s1);
                s1 = set_register(ic->r1.r, s1);
                add_clash(ic->r1.r, ic->r2.r);
            }
        }
        else if (loads_r2(op))
        {
            if (!live_member(ic->r2.r, s1) && !live_psr && !has_side_effects(ic))
            {   if (debugging(DEBUG_REGS)) print_xjopcode(ic, "-> NOOP loads r2");
                INIT_IC (*ic, J_NOOP);
                op = J_NOOP;
            }
            else
                s1 = set_register(ic->r2.r, s1);
        }
        else if (loads_r1(op))
/* /* Unreconstructed WRT sharing TARGET_SHARES_INTEGER_AND_FP_REGISTERS */
        {   if (live_member(ic->r1.r, s1))
            {   demand = reg_demand(ic->r1.r);
/* amazing things happen here because MOV r1, r2 does not want to cause  */
/* r1 and r2 to clash - indeed the very opposite is true.                */
                if (op==J_MOVR || op==J_MOVFR || op==J_MOVDR
#ifdef TARGET_IS_ARM
                   || op==J_MOVFDR
#endif
                   )
                    s1 = set_register_copy(ic->r1.r, s1, ic->r3.r);
                else if ((op==J_LDRV || op==J_LDRFV || op==J_LDRDV) &&
                         bindxx_(ic->r3.b) != GAP)
                {
                    s1 = set_register_copy(ic->r1.r, s1, bindxx_(ic->r3.b));
                }
                else if (pseudo_reads_r2(op)
                         && ic->r2.r!=GAP)
                    s1 = set_register_slave(ic->r1.r, s1, ic->r2.r);
#ifdef REGALLOC_CHAR_OPTIMISER
                else if ((uint32)ic->r1.r < vregistername &&
                         ( (op == J_EXTEND
                            && extend_bitsused(ic->r3.r) >= reg_lsbusetab[ic->r1.r])
                        || (op == J_ANDK
                            && spaceofmask(ic->r3.r) >= reg_lsbusetab[ic->r1.r]
                            && just32bits_(ic->r3.r) == (1L<<spaceofmask(ic->r3.r))-1)))
                {   ic->op = op = J_MOVR;
                    ic->r3.r = ic->r2.r;
                    ic->r2.r = GAP;
                    s1 = set_register_copy(ic->r1.r, s1, ic->r3.r);
if (debugging(DEBUG_REGS)) live_print("EXTEND/ANDK => MOVR");
                }
#endif
                else
                {   /* it is not clear that J_INIT should set_register(r1) */
                    if (op == J_INIT || op == J_INITF || op == J_INITD)
                      if (HasFeature(Feature_Anomoly) && ic->r3.b != 0 &&
                          /* For binders generated by range splitting, there
                             has already been a warning (with a sensible name)
                           */
                          !(bindstg_(ic->r3.b) & b_pseudonym))
                        cc_warn(regalloc_warn_use_before_set, ic->r3.b);
#ifdef REGALLOC_CHAR_OPTIMISER
                    if ((uint32)ic->r1.r < vregistername && reg_lsbusetab[ic->r1.r] <= 8)
                        switch (op)
                        {   case J_LDRBK: case J_LDRBR:
                            case J_LDRBV: case J_LDRBVK:
                                ic->op &= ~(J_SIGNED|J_UNSIGNED);
if (debugging(DEBUG_REGS)) live_print("plain LDRBx");
                        }
                    if ((uint32)ic->r1.r < vregistername && reg_lsbusetab[ic->r1.r] <= 16)
                        switch (op)
                        {   case J_LDRWK: case J_LDRWR:
                            case J_LDRWV: case J_LDRWVK:
                                ic->op &= ~(J_SIGNED|J_UNSIGNED);
if (debugging(DEBUG_REGS)) live_print("plain LDRWx");
                        }
#endif
                    if (iscalln_(op, ic->r2.r))
                        s1 = set_result_registers(ic->r2.r, s1);
                    else
                        s1 = set_register(ic->r1.r, s1);
                }

            } else if (usrdbg(DBG_VAR) && !usrdbg(DBG_OPT_REG))
                s1 = set_register(ic->r1.r, s1);

            else if (iscalln_(op, ic->r2.r) && liveresult(ic->r2.r, s1))
                        s1 = set_result_registers(ic->r2.r, s1);

            else {   /* This load seems to be unnecessary                */
/* NB loading of volatile values will be protected by the jopcodes J_USE */
/* and friends which make it seem that the value loaded is used even     */
/* if it isn't.                                                          */
                if (op == J_CALLK || op == J_OPSYSK)
                {   if ((ic->r2.i & K_PURE) && op != J_OPSYSK)
                    {   if (ic->r3.b == exb_(arg1_(sim.divfn)) ||
                            ic->r3.b == exb_(arg1_(sim.udivfn)) ||
                            ic->r3.b == exb_(arg1_(sim.remfn)) ||
                            ic->r3.b == exb_(arg1_(sim.uremfn)))
                        {   if (debugging(DEBUG_REGS)) cc_msg("void a divide\n");
                            ic->r2.i = k_argdesc_(1, 0, 1,0,0,0);
                                             /* Reduce to one arg  */
                            ic->r3.i = (IPtr)arg1_(sim.divtestfn);
                        }
                        else
                        {   if (debugging(DEBUG_REGS))
                                cc_msg("void call to $b\n", ic->r3.b);
                            INIT_IC (*ic, J_NOOP);
                            op = J_NOOP;
                        }
                    }
                    else s1 = set_register(ic->r1.r, s1); /* cannot remove a call */
                }
                else if (op == J_CALLR)
                    s1 = set_register(ic->r1.r, s1);   /* cannot remove this call */
                else if (!live_psr && !has_side_effects(ic))  /* cannot remove instr which alters a live PSR */
                {   if (debugging(DEBUG_REGS))
                        print_xjopcode(ic, "-> NOOP loads r1");
                    INIT_IC (*ic, J_NOOP);
                    op = J_NOOP;
                }
                else
                    s1 = set_register(ic->r1.r, s1);
            }
        }
        if (uses_stack(op) && op!=J_ADCONV)
        {   VRegnum r3 = bindxx_(ic->r3.b);
/* usage information is accumulated for the virtual register that I will */
/* use if I manage to map this stack location onto a register.           */
            if (r3 != GAP)
            {   if (loads_r1(op)) {
                    /* This case now handed by instruction_ref_info() */
                } else
                {   /* this else case is really J_STRV/STRDV/STRFV */
                    if (live_member(r3, s1)
                        || (usrdbg(DBG_VAR+DBG_LINE) && !usrdbg(DBG_OPT_REG)))
                    {   demand = reg_demand(r3);
                        s1 = set_register_copy(r3, s1, ic->r1.r);
                    }
                    else if (bindstg_(ic->r3.b) & (b_addrof|b_spilt))
                        syserr(syserr_dataflow);
                    else
                    {   /* spurious store -- var not live.  Kill to NOOP. */
#ifdef EXPERIMENTAL_DATAFLOW
/* The following code is foiled (generates warnings from sensible code)   */
/* by an action of the optimiser earlier.  (See 'justregister'). Consider */
/* f() { int x = 1; return x;}.  This generates JOPCODE like              */
/* MOVK r,1; STRV r,x; MOVR a1,r which reuses r instead of re-using x     */
/* Possible solution, use the LDRV r2 field to indicate plausible reg?    */
/* Note that I consider the warning required in f() { int x; return x=1;} */
                        if (HasFeature(Feature_Anomoly)
                            cc_warn(regalloc_warn_never_used, ic->r3.b);
#endif
                        if (debugging(DEBUG_REGS))
                            print_xjopcode(ic, "-> NOOP stored %ld", (long)r3);
                        INIT_IC (*ic, J_NOOP);
                        op = J_NOOP;
                    }
                }
            }
        }

        if (uses_r1(op)) increment_refcount(ic->r1.r, p);
        if (uses_r2(op)) increment_refcount(ic->r2.r, p);
        if (uses_stack(op))
        {   VRegnum n = bindxx_(ic->r3.b);
            increment_refcount(n, p);
            if (n != GAP)
                vreg_(n)->refcount |= 1L; /* mark as 'real', rather than  */
        }                                 /* as a re-evaluable CSE binder.*/
        else if (uses_r3(op))
            increment_refcount(ic->r3.r, p);
        if (uses_r4(op)) increment_refcount(ic->r4.r, p);

        if (corrupts_r1(ic))
            corrupt_register(ic->r1.r, s1);
        if (corrupts_r2(ic))
            corrupt_register(ic->r2.r, s1);
        if (corrupts_psr(ic))
            corrupt_register(R_PSR, s1);
/* let's rationalise the below someday.                                  */
#ifdef TARGET_IS_ARM_OR_THUMB
        if (op == J_MULR || op == J_MLAR)
            add_clash(ic->r1.r, ic->r3.r);
        if (op == J_MULL || op == J_MLAL)
        {
            add_clash(ic->r1.r, ic->r2.r);
            add_clash(ic->r1.r, ic->r3.r);
            add_clash(ic->r2.r, ic->r3.r);
        }
#ifdef ARM_INLINE_ASSEMBLER
        if (op == J_SWP || op == J_SWPB)
        {
            add_clash(ic->r1.r, ic->r3.r);
            add_clash(ic->r2.r, ic->r3.r);
        }
        else if (op == J_LDMW)
        {   /* all registers in the registerlist clash with the base */
            RealRegSet_MapArg a; a.r = ic->r1.r;
            map_RealRegSet(&reg.def, clash_f_reg, &a);
        }
#endif
#endif


#ifdef TARGET_HAS_2ADDRESS_CODE
#  ifdef AVOID_THE_ACN_ADJUSTMENT_MADE_HERE
        if (jop_asymdiadr_(op) && ic->r2.r != ic->r3.r) add_clash(ic->r1.r, ic->r3.r);
#  else
/* See the comment in flowgraf.c (line 99) for why I think this test
   wants to be like this and why the previous version was wrong.  Note also
   that any test on register equality here is pretty suspect since it tests
   virtual registers not real ones - thus (and especially given that SUBR
   seems to be used but rarely) I might prefer a test just on
   jop_asymdiadr(op). */
        if (ic->r1.r != ic->r2.r)
        {
            if (jop_asymdiadr_(op) && two_address_code(op) && ic->r1.r != ic->r3.r)
                add_clash(ic->r1.r, ic->r3.r);
#ifdef NEVER  /* WD: under investigation... */
            if ((j_is_diadr(op) || j_is_diadk(op)) &&
                (op != J_ADDR && op != J_SUBR && op != J_CMPR && op != J_CMPK)
                )   /* WD: diadr/k BROKEN - includes CMP MOV etc, which have GAPs */
                if (ic->r1.r != GAP && ic->r2.r != GAP)
                    add_copy(ic->r1.r, ic->r2.r);
#endif
        }
#  endif
#endif
#ifdef TARGET_IS_ARM_OR_THUMB
        {
            RealRegUse reg;
            RealRegSet_MapArg a; a.vr = s1;

            RealRegisterUse(ic, &reg);
            if (nonempty_RealRegSet(&reg.def, INTREG))
                map_RealRegSet(&reg.def, def_f_reg, &a);
            if (nonempty_RealRegSet(&reg.use, INTREG))
                map_RealRegSet(&reg.use, use_f_reg, &a);
            s1 = a.vr; /* copy altered set back! */
        }
#endif
        s1 = instruction_ref_info(s1, ic, NULL, demand);

/* The following things that allow for workspace registers MUST be done  */
/* here after other register-use info for the instruction has been dealt */
/* with.   Again, this needs parameterising instead of #ifdef.           */

#ifdef TARGET_IS_ARM_OR_THUMB
        if (op == J_CALLK || op == J_CALLR)
        {
        /* WD: Very nasty hack!!! This causes regmaskvec to be incorrect for
         * calls. The idea is that if a call gets turned into a tailcall
         * the tailcall doesn't seem to save LR.
         */
            reg.c_in.map[0] &= ~regbit(R_LR);
            corrupt_register(R_LR, s1);
        }
        if (nonempty_RealRegSet(&reg.c_in, INTREG))
        {   RealRegSet_MapArg a; a.vr = s1;
            map_RealRegSet(&reg.c_in, crc_f1, &a);
        }
#endif
    }
    vregset_discard(s1);
    if (debugging(DEBUG_REGS))
        cc_msg("Scanned block %ld\n", (long)lab_name_(blklab_(p)));
}
/* end of ban on vregset direct operations.                             */

#ifndef TARGET_IS_NULL

typedef struct {
    VRegnum vreg;
    RealRegister rreg;
    Icode *icode;
    int32 mask;
} UDFRec;

static void udf_cb(VRegnum r, VoidStar arg)
{
    UDFRec *udf = (UDFRec *) arg;
    if (r != udf->vreg && register_number(r) == udf->rreg)
        udf->icode->op &= udf->mask;
}

/* The reason for update_deadflags() is that the DEADBITS information    */
/* for virtual registers is a superset of that for physical registers -- */
/* consider examples like                                                */
/*   extern int z; void f(x) { while (x) z=1; while (x) z=1; }           */
/* Since the mapping from virtual register (with clashes) to physical    */
/* register graphs (with inequality) is a homomorphism one would expect  */
/* some nice theory to cover it.  Note that the property of deadness is  */
/* not preserved by the homomorphism, but it IS semi-preserved.          */
/* So the code removes the DEAD infomation from any register which       */
/* has a another live register mapped to the same physical register.     */
/* AM is not sure that the tests below of ->realreg!=0 are really        */
/* required, but they look harmless.                                     */
static void update_deadflags(BlockHead *p)
{   VRegSetP s = successor_regs(p);
    Icode *q = blkcode_(p);
    int32 w;
    UDFRec udf;
    for (w=blklength_(p)-1; w>=0; w--)
    {   Icode *const ic = &q[w];
        int32 op = ic->op & J_TABLE_BITS;
/* The following three lines take care of the fact that we really want   */
/*               ^^^^^ i.e. to the vregset_delete() call?                */
/* to execute this code half-way through add_instruction_info().         */
/* This code ensures that we do not remove deadflags from r2 for (say)   */
/*   LDRK r1,r2,0  if r1 and r2 map to the same physical register (and   */
/* of course r2 is dead at the virtual level).                           */
/* WGD's 32000 code depends on this as he was entitled to from the       */
/* Nov87 comment above.  Whether we ought to reconsider this is another  */
/* matter.  Discuss with WGD one day.                                    */
        bool removed = 0;
        if (debugging(DEBUG_LOOP))
        {   cc_msg("live");
            vregset_print(s),
            cc_msg("\n %c%c%c%c", (ic->op & J_DEAD_R1 ? '1': '-'),
                                  (ic->op & J_DEAD_R2 ? '2': '-'),
                                  (ic->op & J_DEAD_R3 ? '3': '-'),
                                  (ic->op & J_DEAD_R4 ? '4': '-'));
            print_jopcode(ic);
        }
        udf.icode = ic;
        if (loads_r1(op) || corrupts_r1(ic))
            s = vregset_delete(ic->r1.r, s, &removed);
        if (loads_r2(op) || corrupts_r2(ic))
        {   bool removed1 = 0;
            s = vregset_delete(ic->r2.r, s, &removed1);
            removed = removed || removed1;
        }
        if ((ic->op & J_DEAD_R2) && (reads_r2(op) ||
            (pseudo_reads_r2(op) && ic->r2.r!=GAP)))    /* MOVK/ADCON loopopt */
        {   RealRegister rr = register_number(ic->r2.r);
            if (debugging(DEBUG_LOOP))
                cc_msg("try remove dead_r2 %ld %ld", (long)ic->r2.r, (long)rr);
            if (rr >= 0)
            {   udf.vreg = ic->r2.r;
                udf.rreg = rr;
                udf.mask = ~J_DEAD_R2;
                vregset_map(s, udf_cb, (VoidStar)&udf);
            }
            if (debugging(DEBUG_LOOP))
                cc_msg("%s", udf.icode->op & J_DEAD_R2 ? "\n": ": removed\n");
        }
        if ((ic->op & J_DEAD_R3) && reads_r3(op) /* &&
             op != J_CALLR*/)     /* see above */
        {   RealRegister rr = register_number(ic->r3.r);
            if (debugging(DEBUG_LOOP))
                cc_msg("try remove dead_r3 %ld %ld ", (long)ic->r3.r, (long)rr);
            if (rr >= 0)
            {   udf.vreg = ic->r3.r;
                udf.rreg = rr;
                udf.mask = ~J_DEAD_R3;
                vregset_map(s, udf_cb, (VoidStar)&udf);
            }
            if (debugging(DEBUG_LOOP))
                cc_msg("%s", udf.icode->op & J_DEAD_R3 ? "\n": ": removed\n");
        }
        /* This can only be a LDRV or equivalent (STRV doesn't have DEAD_R3) */
        if ((ic->op & J_DEAD_R3) && uses_stack(op) && bindxx_(ic->r3.b) != GAP)
        {   VRegnum r = bindxx_(ic->r3.b);
            RealRegister rr = register_number(r);
            if (debugging(DEBUG_LOOP))
                cc_msg("try remove dead_r3 %ld %ld ", (long)r, (long)rr);
            if (rr >= 0)
            {   udf.vreg = bindxx_(ic->r3.b);
                udf.rreg = rr;
                udf.mask = ~J_DEAD_R3;
                vregset_map(s, udf_cb, (VoidStar)&udf);
            }
            if (debugging(DEBUG_LOOP))
                cc_msg("%s", udf.icode->op & J_DEAD_R3 ? "\n": ": removed\n");
        }
        if ((ic->op & J_DEAD_R4) && reads_r4(op))
        {   RealRegister rr = register_number(ic->r4.r);
            if (debugging(DEBUG_LOOP))
                cc_msg("try remove dead_r4 %ld %ld ", (long)ic->r4.r, (long)rr);
            if (rr >= 0)
            {   udf.vreg = ic->r4.r;
                udf.rreg = rr;
                udf.mask = ~J_DEAD_R4;
                vregset_map(s, udf_cb, (VoidStar)&udf);
            }
            if (debugging(DEBUG_LOOP))
                cc_msg("%s", udf.icode->op & J_DEAD_R4 ? "\n": ": removed\n");
        }
        if ((ic->op & J_DEAD_R1) && (reads_r1(op) ||
            (pseudo_reads_r1(op) && ic->r1.r!=GAP)))    /* CMPK loopopt */
        {   RealRegister rr = register_number(ic->r1.r);
            if (debugging(DEBUG_LOOP))
                cc_msg("try remove dead_r1 %ld %ld ", (long)ic->r1.r, (long)rr);
            if (rr >= 0)
            {   udf.vreg = ic->r1.r;
                udf.rreg = rr;
                udf.mask = ~J_DEAD_R1;
                vregset_map(s, udf_cb, (VoidStar)&udf);
            }
            if (debugging(DEBUG_LOOP))
                cc_msg("%s", udf.icode->op & J_DEAD_R1 ? "\n": ": removed\n");
        }
        s = add_instruction_info(s, ic, NULL, removed);
    }
    vregset_discard(s);
}

/*************************************************************************/
/*       Here comes the code that allocates and assigns registers        */
/*************************************************************************/

static void MaybePrefer(VRegnum vr, void *vprefer)
{
    RealRegSet *prefer = (RealRegSet *)vprefer;
    RealRegister r1 = register_number(vr);
    if (isany_realreg_(r1)) augment_RealRegSet(prefer,r1);
}

static void MaybePrefer2(VRegnum vr, void *vprefer)
{
    RealRegister r1 = register_number(vr);
    if (!isany_realreg_(r1)) {
        VRegister *r = vreg_(vr);
        relation_map(vregname_(r), copymatrix, MaybePrefer, vprefer);
    }
}

static void GetPhysicalCopies(VRegnum vr, RealRegSet *copies) {
  /* return in *copies the set of physical registers which are preferred   */
  /* allocations for vr (are copied from/to vr and don't clash with it)    */

    RealRegister r1 = register_number(vr);
    memclr((void *)copies, sizeof(RealRegSet));
    if (isany_realreg_(r1))
        augment_RealRegSet(copies, r1);
    else {
        VRegister *r = vreg_(vr);
        relation_map(vregname_(r), copymatrix, MaybePrefer, (void *)copies);
        vregset_map(r->clashes, clashkillbits_cb, (void *)copies);
    }
}

static void avoid_cb(VRegnum vr, void *arg)
{
    RealRegSet *possible = (RealRegSet *)arg;
    /* Remove from the set *possible the physical registers which we'd     */
    /* like to allocate to vr (which clashes with the register for which   */
    /* we're considering *possible for allocation)                         */
    RealRegSet avoid;
    GetPhysicalCopies(vr, &avoid);
    if (intersect_RealRegSet(&avoid, &avoid, possible)) {
        difference_RealRegSet(possible, possible, &avoid);
        if (debugging(DEBUG_REGS)) {
            cc_msg("%ld: available {", vr); print_RealRegSet(possible); cc_msg("}\n");
        }
    }
}

typedef struct {
    RealRegSet onecopy;
    RealRegSet *possible;
} AvoidRec;

static void avoid_cb2(VRegnum vr, void *arg) {
    AvoidRec *ar = (AvoidRec *)arg;
    RealRegSet avoid, rs;
    GetPhysicalCopies(vr, &avoid);
    intersect_RealRegSet(&avoid, &avoid, ar->possible);
    if (intersect_RealRegSet(&rs, &avoid, &ar->onecopy))
        difference_RealRegSet(ar->possible, ar->possible, &rs);
    union_RealRegSet(&ar->onecopy, &ar->onecopy, &avoid);
}

static bool choose_real_register(VRegister *r)
/* select a real register to put r into: return 1 on success, 0 on failure */
{
    RealRegSet m1, m2, prefer;
    RealRegister r1;
    RegSort rsort = vregtype_(r);

#ifdef ENABLE_SPILL
    ++choose_count;
#endif

    memclr((VoidStar)&prefer, sizeof(RealRegSet));
    relation_map(vregname_(r), copymatrix, MaybePrefer, (VoidStar)&prefer);

    m1    =         *(
#ifdef ADDRESS_REG_STUFF
                      rsort == ADDRREG ?
                          (!spillpanic ? &m_addrregs : &m_intregs) :
#endif
#ifndef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
                      rsort != INTREG ? &m_fltregs :
#endif
                      &m_intregs);
    clashkillbits(&m1, r);

/* Test if this register can be allocated at all.                        */
    if (!nonempty_RealRegSet(&m1, rsort))
    {   if (debugging(DEBUG_REGS) || debugging(DEBUG_SPILL))
        {   cc_msg("Unable to allocate v%ld(%ld):",
                   (long)vregname_(r), (long)r->heapaddr);
            if (debugging(DEBUG_REGS))
            {   cc_msg(" to miss ");
                printvregclash2(r);
                cc_msg("\n");
            }
        }
        r->realreg = R_BOGUS;
/* If I fail to allocate a real register to this binder I drop into the  */
/* code that spills things. This will choose a register to spill based   */
/* on a number of criteria. If possible it will spill either the binder  */
/* that failed to get allocated or one of the binders that clashes with  */
/* it directly (thus having the best chance of unblocking this particular*/
/* clash). Failing that it will spill some binder that has already been  */
/* allocated a real register (ones that have not yet been considered for */
/* allocation would not be sensible to spill, would they?). In this      */
/* context it is desirable that the binder that causes the clash should  */
/* seem to have a real register allocated to it so that it can be        */
/* selected for spilling under this heading. Priority within the above   */
/* categories is based on usage information (->refcount) and register    */
/* provided by the user. After spilling a binder all binders that have   */
/* been given registers so far get reset to a null state (thus undoing   */
/* the spurious allocation of R_BOGUS above) so that the entire process  */
/* of allocation can be restarted: with some binder marked as spilt it   */
/* will generally be possible to proceed further, until at last it       */
/* becomes possible to allocate all registers.                           */
        return NO;
    }
#ifdef ADDRESS_REG_STUFF
   spillpanic = 0;
#endif
/* If possible allocate r1 so as to remove a copy operation somewhere    */
    if (intersect_RealRegSet(&m2, &m1, &prefer) &&
        !(var_cc_private_flags & 2048L)) {
     /* This is somewhat experimental ...                                */
     /* It says: if a preferred allocation for r is also a preferred     */
     /* allocation for more than one (not-yet-allocated) register which  */
     /* clashes with r, don't use it for r (since we hope that way to    */
     /* remove more copies). Since we don't count copy multiplicity, the */
     /* code only approximates to the intent.                            */

        AvoidRec ar;
        memclr((void *)&ar.onecopy, sizeof(RealRegSet));
        ar.possible = &m2;
        vregset_map(r->clashes, avoid_cb2, (void *)&ar);
    }
    if (nonempty_RealRegSet(&m2, rsort)) {
        m1 = m2;
    } else {
        if (!(var_cc_private_flags & 4096L)) {
    /* we are about to make an essentially arbitrary allocation.  Try to */
    /* avoid doing so in a way that will interfere with an allocation we */
    /* know will later be a good idea.                                   */
            if (debugging(DEBUG_REGS))
                cc_msg("No preferred allocation for %ld\n", vregname_(r));
            m2 = m1;
            vregset_map(r->clashes, avoid_cb, (VoidStar)&m2);
            memclr((VoidStar)&prefer, sizeof(RealRegSet));
            relation_map(vregname_(r), copymatrix, MaybePrefer2,
                                       (void *)&prefer);
            if (intersect_RealRegSet(&prefer, &m2, &prefer))
                m1 = prefer;
            else if (nonempty_RealRegSet(&m2, rsort))
                m1 = m2;
        }
    }

/* Try to allocate avoiding V1 to V<n> (and any floating var regs).      */
/* AM (Dec 87) wonders how necessary this is in that ALLOCATION_ORDER    */
/* can do this equally as well!                                          */

/* /* The next line needs to ensure that the overlap is an even/odd      */
/* pair if TARGET_SHARES_INTEGER_AND_FP_REGISTERS.                       */
    if (intersect_RealRegSet(&m2, &m1, &m_notpreserved))
        m1 = m2;

/* Convert representation from bit-position to register number.          */
    {   int32 i = 0;
        for (;; i++)
        {
#ifdef ALLOCATION_ORDER
/* a prespecified allocation ordering:                                   */
            static unsigned char o[] = ALLOCATION_ORDER;
            r1 = o[i];
#else
/* else choose in a not particularly inspired order.                     */
            r1 = i;
#endif
            if ((uint32)r1 >= (uint32)NMAGICREGS)
            {   syserr(syserr_choose_real_reg, (long)((m1.map)[0]));
                break;
            }
            if (member_RealRegSet(&m1,r1)
#ifdef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
                && (!needsregpair_(rsort) ||
                    member_RealRegSet(&m1,other_halfreg(r1)))
#endif
                ) break;
        }
    }

    if (debugging(DEBUG_REGS))
    {   cc_msg("Now allocate %ld to %ld: miss ",
               (long)vregname_(r), (long)r1);
        printvregclash2(r);
        cc_msg("\n");
    }

/* Record the allocation.                                                */
    r->realreg = r1;
/* regmaskvec gets bits set to show what registers this procedure uses.  */
    if (!member_RealRegSet(&globalregvarvec,r1))
    {
        augment_RealRegSet(&regmaskvec,r1);     /* register used */
#ifdef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
        if (needsregpair_(rsort))
            augment_RealRegSet(&regmaskvec, other_halfreg(r1));
#endif
    }
    return YES;                                 /* success!      */
}

static int32 spill_binder(VRegister *rr, BindList *spill_order, VRegSetP *vr)
/* Here virtual register rr could not be allocated.  Try to pick the     */
/* best Binder in spill_order to either spill rr to the stack or to      */
/* help the process of allocating rr to a real register.                 */
{   BindList *candidates = NULL;
    {   BindList *lb;
        for (lb = spill_order; lb != NULL ; lb = lb->bindlistcdr)
        {   Binder *bb = lb->bindlistcar;
            VRegnum r1n = bindxx_(bb);
/* there is no joy in trying to spill a binder if either (a) it was not  */
/* a candidate for slaving in a register anyway or (b) the corresponding */
/* register has not yet been scheduled for allocation.                   */
            if (r1n != GAP)
            {   RealRegister r1r = register_number(r1n);
                if (r1r != R_SCHEDULED)
                {
#ifdef ADDRESS_REG_STUFF
/* If we require an address reg and this one is not and we are not */
/* panicking yet -> don't consider this one because it wouldn't do */
/* any good any way.                                               */
/* Maybe the next line should use member(m_addrregs), but AM is    */
/* is not sure enough that r1v->realreg is in range.               */
                    if (vregtype_(rr) == ADDRREG &&
                        !target_isaddrreg_(r1r) &&
                        !spillpanic) continue;
#endif
                    candidates = (BindList *) binder_cons2(candidates, bb);
                }
            }
        }
    }
    if (candidates==NULL)
#ifdef ADDRESS_REG_STUFF
    {   if( !spillpanic )
        {   spillpanic = 1;
            return 0;
        }
        else syserr(syserr_fail_to_spill, (long)vregname_(rr));
    }
#else
    syserr(syserr_fail_to_spill, (long)vregname_(rr));
#endif
/* Now find the best binder, with ones that clash directly with the      */
/* thing that could not be allocated taking precedence                   */
    {   Binder *bb = (Binder *) DUFF_ADDR;
        VRegister *r1 = (VRegister *) DUFF_ADDR;
        int32 leastspillcost = INT_MAX;
        bool foundgood = NO;
        for (; candidates != NULL;
               candidates = (BindList *)discard2((List *)candidates))
        {   Binder *bb2 = candidates->bindlistcar;
            VRegnum r2n = bindxx_(bb2);
/* Presumably we know that r2n != GAP...                                */
            VRegister *r2 = vreg_(r2n);
            int32 spillcost = r2->refcount;
/* This is a good candidate if it was involved in the clash that caused  */
/* me to decide that I needed to spill something, or if no such register */
/* was on the list of candidates and this is the one with fewest uses    */
            if (rr==r2 || vregset_member(r2n, rr->clash2))
            {   if (!foundgood || spillcost <= leastspillcost)
                {   bb = bb2, r1 = r2, leastspillcost = spillcost;
                    foundgood = YES;
                }
            }
            if (!foundgood && spillcost <= leastspillcost)
            {   bb = bb2, r1 = r2, leastspillcost = spillcost;
            }
        }
        if (debugging(DEBUG_REGS|DEBUG_SPILL))
            cc_msg("    spill: $b, v%lu(r%ld:%ld), cost = %lu\n",
                bb, (long)vregname_(r1), (long)r1->realreg,
                (long)r1->heapaddr, (long)leastspillcost);
        r1->realreg = R_SPILT;   /* marker for spilled register   */
        r1->u.spillbinder = bb;
        *vr = vregset_insert(vregname_(r1), *vr, NULL, &listallocrec);
        bindxx_(bb) = GAP;   /* this one has to stay on the stack */
        if (bindstg_(bb) & b_pseudonym)
            bindsuper_(bb)->spillcount++;
#ifdef ENABLE_SPILL
        if (r1->refcount & 1L)
            ++n_real_spills;
        else
            ++n_cse_spills;
        spill_cost += leastspillcost;
#endif
        return r1->heapaddr;
    }
}

#endif /* TARGET_IS_NULL */

/* exported... */

static void addclashes_rcb(VRegnum n, void *arg)
{   /* the type of 'r1' is a lie for map-function vregset_map.          */
    VRegister *v = vreg_(n);
    VRegnum m = (VRegnum)(IPtr)arg;
    v->clash2 = vregset_insert(m, v->clash2, NULL, &listallocrec);
}

static void flattenrelation_cb(VRegnum n, VoidStar arg)
{   VRegSetP *v = (VRegSetP *)arg;
    *v = vregset_insert(n, *v, NULL, &clashvallocrec);
}

void allocate_registers(BindList *spill_order)
/* spill_order is a list of all binders active in this function,         */
/* ordered with the first-mentioned register variables LAST so that they */
/* are the things least liable to be spilled out to the stack.           */
{
    clock_t t0 = clock();
    uint32 i, nn;
    VRegSetP spillset = NULL;

#ifndef TARGET_IS_NULL
    ReadonlyCopy *p;
    regalloc_changephase();
    clash_reinit(vregistername);

    /* weight the reference counts of register variables to avoid spills */
    {   BindList *l = spill_order;
        Binder *b;
        while (l != NULL)
        {   b = (Binder *)(l->bindlistcar);
            if (bindstg_(b) & bitofstg_(s_register))
            {   VRegnum r = bindxx_(b);
    /* register vars may be forced to memory by setjmp, leaving r == GAP */
                if (r != GAP) vreg_(r)->refcount += 1000000;
            }
            l = l->bindlistcdr;
        }
    }

    if (debugging(DEBUG_REGS)) cc_msg("Slave list:\n");
    /* transform slave_list into a more convenient form for our use */
    for (p = slave_list; p!=NULL; p = p->next) {
        vreg_(p->r1)->slave = p->r2;
        if (debugging(DEBUG_REGS)) {
            cc_msg("%ld : ", (long)p->r1);
            if (p->r2 == GAP)
                cc_msg("GAP\n");
            else
                cc_msg("%ld\n", (long)p->r2);
        }
    }
#endif  /* TARGET_IS_NULL */
/* First I iterate over the basic blocks to collect information about    */
/* which registers are needed at the head of each block. With structured */
/* control-flow this should cost at worst one scan of the flowgraph      */
/* (plus another to verify that there are no changes left over). With    */
/* very contorted flow of control (e.g. via goto or switch with case     */
/* labels inside embedded loops) it can take MANY iterations.            */
    phasename = "dataflow";
    {   bool changed;
        do
        {   BlockHead *p;
            changed = NO;
            curstats.dataflow_iterations++;
            if (debugging(DEBUG_REGS))
                cc_msg("Start a scan of register flow iteration\n");
            for (p=bottom_block; p!=NULL; p = blkup_(p))
                changed = changed | update_block_use_info(p);
        } while (changed);
    }
    if (debugging(DEBUG_REGS))
        cc_msg("Block by block register use analysis complete\n");

    dataflow_clock += clock() - t0; t0 = clock();

    phasename = "clashmap";
    {   BlockHead *p;
        valn_reinit();
        if (debugging(DEBUG_REGS))
            for (p=top_block; p!=NULL; p=blkdown_(p))
                flowgraf_printblock(p, YES);
        for (p=top_block; p!=NULL; p=blkdown_(p))
            collect_register_clashes(p);
    }

    regalloc_clock1 += clock() - t0; t0 = clock();

#ifndef TARGET_IS_NULL
    if (debugging(DEBUG_REGS))
    {   cc_msg("\nGlobal register clash information collected\n");
        for (i=0; i<NMAGICREGS; i++)
        {   VRegister *r = vreg_(i);
            if (r->u.nclashes != 0)
            {   cc_msg("r%ld clashes with:", (long)vregname_(r));  /* ==i */
                printvregclash(r);
                cc_msg("\n");
            }
        }
        for (i=1; i<vregistername-NMAGICREGS; i++)
        {   VRegister *r = permregheap_(i);
            if (r->u.nclashes != 0)
            {   if (r->realreg >= 0) cc_msg("[r%ld]: ", (long)r->realreg);
                cc_msg("v%ld clashes with:", (long)vregname_(r));
                printvregclash(r);
                cc_msg("\n");
            }
        }
    }

    for (i=1; i<vregistername-NMAGICREGS; i++)
    {   VRegister *r = permregheap_(i);
        relation_map(vregname_(r), clashmatrix,
                     flattenrelation_cb, (VoidStar)&r->clashes);
    }

/* Form the register vector into a priority queue (heap)                 */
    phasename = "regalloc";
    for (i = (vregistername-NMAGICREGS-1)/2; i>=1; i--)
        downheap(i, vregistername-NMAGICREGS-1);

    for (i = vregistername-NMAGICREGS-1; i>0; i--)
    {   VRegister *s = permregheap_(1), *t = permregheap_(i);
        if (debugging(DEBUG_REGS))
            cc_msg("Register %ld clashes with %ld others\n",
                   (long)vregname_(s), (long)s->u.nclashes);
        permregheap_(1) = t;
        t->heapaddr = 1;
        permregheap_(i) = s;
        s->heapaddr = i;
        downheap(1, i-1);
        s->realreg = R_SCHEDULED;
        removeclashes(s);

    }

/* Now I will try the registers in the order just selected.              */
    for (i = 1; i < vregistername-NMAGICREGS; i++)
    {   VRegister *rr = permregheap_(i);
        if (rr->realreg == R_SPILT) continue;    /* spilt register       */
        if (!choose_real_register(rr))
        {   /* Here it is necessary to spill something                   */
            uint32 spilt = spill_binder(rr, spill_order, &spillset);
#ifdef ADDRESS_REG_STUFF
            if ( spilt == 0 )
            { --i;         /* spillpanic is now 1 */
              continue;
            }
#endif
/* N.B. this loop modifies the main loop control variable!!!             */
/* N.B. also (LDS) that while this loop appears to introduce quadratic   */
/* complexity, experiment shows that the total number of re-tries is     */
/* LESS than one scan through the list, ALMOST ALWAYS. Does this follow  */
/* from ordering the list by most clashes first?                         */
            while (i >= spilt)
            {   VRegister *rr = permregheap_(i);
                if (rr->realreg != R_SPILT) rr->realreg = R_SCHEDULED;
                i--;
            }
        }
    }

#ifdef ENABLE_SPILL
    if (debugging(DEBUG_SPILL))
        cc_msg("%ld calls to choose_real_register() to allocate %ld vregs\n",
               (long)choose_count, (long)vregistername-NMAGICREGS);
#endif

    nn = 0;
    if ((n_real_spills + n_cse_spills)> 1 &&        /* retrying may help */
        (var_cc_private_flags & 4L) == 0)     /* cleaning not suppressed */
    {
/* Here, we do some cleaning up of the register colouring to trying to   */
/* the things that have already been spilt. Sometimes we'll succeed.     */
/* This heuristic reduces the number of spills in the compiler by 2%,    */
/* with significant savings in larger functions. First, then, we rebuild */
/* the complete clash lists for each spilt register.                     */
        VRegSetP x;
        clock_t us_t = clock();
        for (i = 1; i < vregistername-NMAGICREGS; ++i)
        {   VRegister *rr = permregheap_(i);
            if (rr->realreg != R_SPILT)
            {   /* the following destroys rr->clash2, saving store */
                x = vregset_intersection(rr->clash2, spillset);
                rr->clash2 = (VRegSetP)DUFF_ADDR;
            }
            else
                x = vregset_intersection(
                        vregset_copy(spillset, &listallocrec), rr->clash2);
            vregset_map(x, addclashes_rcb, (VoidStar)(IPtr)vregname_(rr));
        }

/* It isn't clear which way this loop should go - or even whether it's   */
/* best to use notional spill cost order. So far, experiments on the     */
/*compiler itself have been inconclusive.                                */
        for (i = 1; i < vregistername-NMAGICREGS;  ++i)
        {   VRegister *rr = permregheap_(i);
            if (rr->realreg != R_SPILT) continue;
            if (choose_real_register(rr))
            {   Binder *bb = rr->u.spillbinder;
                bindxx_(bb) = vregname_(rr);
                if (bindstg_(bb) & b_pseudonym)
                    bindsuper_(bb)->spillcount--;
                nn += 1;
                spill_cost -= rr->refcount;
                if (rr->refcount & 1L)
                    --n_real_spills;
                else
                    --n_cse_spills;
                if (debugging(DEBUG_SPILL))
                   cc_msg("    unspill: $b, v%lu = r%lu, saving = %lu\n",
                       bb, vregname_(rr), rr->realreg, rr->refcount);
            }
            else if (debugging(DEBUG_SPILL))
                cc_msg("\n");
        }
        if (debugging(DEBUG_SPILL))
            cc_msg("%lu vregs unspilt by cleaning pass in %ucs\n",
                   nn, clock() - us_t);
    }

/* WGD Now check for spurious deadbits arising from register copies */
    {   BlockHead *p;
        for (p=top_block; p!=NULL; p=blkdown_(p)) update_deadflags(p);
        for (p=top_block; p!=NULL; p=blkdown_(p))
            vregset_discard(blkuse_(p));
    }
#else
    IGNORE(i); IGNORE(spill_order);
#endif /* TARGET_IS_NULL */
    regalloc_clock2 += clock() - t0;
    if (debugging(DEBUG_STORE | DEBUG_REGS)) stats_endproc();
#ifdef ENABLE_SPILL
    if (debugging(DEBUG_SPILL) && (n_real_spills + n_cse_spills + nn) > 0)
    {
       cc_msg("fn $r %3lu + %lu spills, cost = %6lu\n\n",
              currentfunction.symstr,
              n_real_spills, n_cse_spills, spill_cost);
       tot_real_spills += n_real_spills;
       tot_cse_spills += n_cse_spills;
       tot_cost += spill_cost;
       n_real_spills = n_cse_spills = spill_cost = 0;
    }
#endif
    {   SuperBinder *p = superbinders;
        for (; p != NULL; p = cdr_(p))
            if (p->spillcount == 0)
                bindxx_(p->binder) = 0;
    }
}

#ifndef TARGET_IS_NULL
/* change the union member in vregtable -- expand VRegnum's for allocation */
static void regalloc_changephase(void)
{   uint32 i;
    for (i = 0; i < vregistername; i++)
    {   VRegnum rname = vregtypetab_(i);
        VRegister *v = (VRegister *) BindAlloc(sizeof(VRegister));
        if (((uint32)rname & ~REGSORTMASK) != i) syserr(syserr_regalloc_reinit2);
        v->heapaddr = i-NMAGICREGS;   /* -ve for real regs, 0 for sentinel */
        v->perm = v;
        v->realreg = R_UNSCHEDULED;   /* Not yet scheduled for allocation  */
        v->clash2 = (VRegSetP) DUFF_ADDR;
        v->u.nclashes = 0;
        v->rname = rname;
        v->ncopies = 0;
        v->refcount = 0;
        v->slave = GAP;
        v->clashes = NULL;
        v->valnum = VALN_UNSET;
        v->valsource = NULL;
        v->valwritecount = 0;
        vreg_(i) = v;
        if (i < NMAGICREGS) v->realreg = i;     /* real register */
        if (i == NMAGICREGS) v->u.nclashes = -1;  /* heap sentinel */
    }
    reg_lsbusetab = (unsigned char *)BindAlloc(vregistername);
#ifdef LSBUSE_CONSISTENCY_CHECK
    lsbmap = (uint8 *)BindAlloc((vregistername/(LSBQUANTUM*8))+1);
#endif
}
#endif /* TARGET_IS_NULL */

/* exported for cg.c and cse.c/csescan.c */
VRegnum vregister(RegSort rsort)
{   if ((vregistername&(REGHEAPSEGSIZE-1)) == 0)
    {   int32 p = vregistername >> REGHEAPSEGBITS;
        if (p >= REGHEAPSEGMAX) syserr(syserr_regheap);
        else vregheap[p] =
          (vreg_type (*)[REGHEAPSEGSIZE]) BindAlloc(sizeof(*vregheap[0]));
    }
    vregtypetab_(vregistername) = rsort | vregistername;
    return vregistername++;
}

/* ... and its inverse (for cg/cse only, due regalloc_changephase()).   */
RegSort vregsort(VRegnum r)
{   if ((unsigned32)r >= (unsigned32)vregistername)
        syserr(syserr_vregsort, (long)r);
    return vregtypetab_(r) & REGSORTMASK;
}

void globalregistervariable(VRegnum r)
{
    unsigned32 dummy;
    VRegSetAllocRec a;
    a.alloctype = AT_Glob;
    a.statsloc = a.statsloc1 = a.statsbytes = &dummy;
    augment_RealRegSet(&globalregvarvec, r);
    vregset_init();
    globalregvarset = vregset_insert(r, globalregvarset, NULL, &a);
}

RealRegSet const *globalregset(void) {
    return &globalregvarvec;
}

void avoidallocating(VRegnum r)
{
    delete_RealRegSet(&m_intregs, r);
#ifndef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
    delete_RealRegSet(&m_fltregs, r);
#endif
#ifdef ADDRESS_REG_STUFF
    delete_RealRegSet(&m_addrregs, r);
#endif
}

/* call before first use of vregister() */
void regalloc_reinit(void)
{   RealRegister i;   /* parallel to vregistername here */
    vregistername = 0;
    for (i = 0; i < NMAGICREGS; i++)
        (void)vregister(i < NINTREGS ? INTREG : DBLREG);
    (void)vregister(SENTINELREG);
    memclr((VoidStar)&curstats, sizeof(curstats));
    memclr((VoidStar)&regmaskvec, sizeof(RealRegSet));
#ifndef TARGET_IS_NULL
    slave_list = NULL;
#endif
#ifdef ENABLE_SPILL
    n_real_spills = n_cse_spills = spill_cost = 0;
#endif
    reg_lsbusetab = (unsigned char *)DUFF_ADDR;
#ifdef LSBUSE_CONSISTENCY_CHECK
    lsbmap = (uint8 *)DUFF_ADDR;
#endif
}

void regalloc_init(void)
{   VRegnum i;
    dataflow_clock = regalloc_clock1 = regalloc_clock2 = 0;
/*
 * Active initialisations so that the compiled image has a chance to
 * be absolutely relocatable (e.g. for a RISC-OS relocatable module)
 */
    clashrallocrec.alloctype = ClashAllocType;
    clashrallocrec.statsloc = &curstats.nsquares;
    clashrallocrec.statsbytes = &curstats.squarebytes;
    copyallocrec.alloctype = CopyAllocType;
    copyallocrec.statsloc = &curstats.copysquares;
    copyallocrec.statsbytes = &curstats.copysquarebytes;
    clashvallocrec.alloctype = ClashAllocType;
    clashvallocrec.statsloc = &curstats.nregsets;
    clashvallocrec.statsloc1 = &curstats.newregsets;
    clashvallocrec.statsbytes = &curstats.regsetbytes;
    listallocrec.alloctype = ListAllocType;
    listallocrec.statsloc = &curstats.nlists;
    listallocrec.statsloc1 = &curstats.newlists;
    listallocrec.statsbytes = &curstats.listbytes;
    memclr((VoidStar)(&maxstats), sizeof(maxstats));

    memclr((VoidStar)&m_notpreserved, sizeof(RealRegSet));
    for (i = 0; i<NMAGICREGS; i++)
#ifdef target_preserves                 /* better? */
        if (target_preserves(i))
#else
        if (!(R_V1 <= i && i < R_V1+NVARREGS
#ifndef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
              || R_FV1 <= i && i < R_FV1+NFLTVARREGS
#endif
           ))
#endif
            augment_RealRegSet(&m_notpreserved,i);

    memclr((VoidStar)&m_intregs, sizeof(RealRegSet));
    for (i = 0; i<NMAGICREGS; i++)
        if (R_A1 <= i && i < R_A1+NARGREGS
            || R_P1 <= i && i < R_P1+NARGREGS
            || R_V1 <= i && i < R_V1+NVARREGS
/* on many machines R_IP will be one of the NTEMPREGS, but to allow it  */
/* to be non-contiguous we treat it specially.                          */
            || i == R_IP
            || R_T1 <= i && i < R_T1+NTEMPREGS
#ifndef TARGET_STACKS_LINK
            || i == R_LR
#endif
           ) augment_RealRegSet(&m_intregs,i);

#ifndef TARGET_SHARES_INTEGER_AND_FP_REGISTERS
    memclr((VoidStar)&m_fltregs, sizeof(RealRegSet));
    for (i = 0; i<NMAGICREGS; i++)
        if (R_FA1 <= i && i < R_FA1+NFLTARGREGS ||
                R_FP1 <= i && i < R_FP1+NFLTARGREGS ||
                R_FT1 <= i && i < R_FT1+NFLTTEMPREGS ||
                R_FV1 <= i && i < R_FV1+NFLTVARREGS)
            augment_RealRegSet(&m_fltregs,i);
#endif

#ifdef ADDRESS_REG_STUFF
    memclr((VoidStar)&m_addrregs, sizeof(RealRegSet));
    for (i = 0; i<NMAGICREGS; i++)
        if (target_isaddrreg_(i))
            augment_RealRegSet(&m_addrregs,i);
#endif

    memclr((VoidStar)&globalregvarvec, sizeof(RealRegSet));
    globalregvarset = 0;

#ifdef ENABLE_SPILL
    tot_real_spills = tot_cse_spills = tot_cost = choose_count = 0;
#endif
    INIT_IC(ic_noop, J_NOOP);
    warn_corrupted_regs = 0;
}

void regalloc_tidy(void)
{
#ifdef ENABLE_SPILL
    if (debugging(DEBUG_SPILL))
        cc_msg("%lu binders spilt, %lu CSEs re-evaluated, total cost = %lu\n",
               tot_real_spills, tot_cse_spills, tot_cost);
#endif
    if (!debugging(DEBUG_STORE | DEBUG_REGS)) return;
    cc_msg("Regalloc max space stats:\n");
    stats_print(&maxstats);
    cc_msg("Dataflow time %ldcs, regalloc time %ld+%ldcs\n",
           (long)dataflow_clock, (long)regalloc_clock1, (long)regalloc_clock2);
}

/* The following routine should really be a 'const RealRegSet' extern   */
/* definition.  However, there seems to be no way to initialise it in   */
/* C.  Note that it gets called before regalloc_init() (e.g. builtin.c) */
/* and so the obvious initialisation fails.                             */

extern void reg_setallused(RealRegSet *s) { memset(s, 0xff, sizeof(*s)); }

/* end of regalloc.c */
