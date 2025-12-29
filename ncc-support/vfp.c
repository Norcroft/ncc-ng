//
//  vfp.c
//  ncc
//
//  Created by Piers Wombwell on 31/10/2025.
//

#include "globals.h"
#include "codebuf.h"
#include "cgdefs.h"
#include "store.h"
#include "armops.h"
#include "errors.h"
#include "regalloc.h"

#include "gen.h"
#include "vfp.h"
#include "vfpops.h"

// Also NOTE: This only uses registers D0-D7 and S0-S15 STEP 2.

// NOTE: My INVENTED AND NOT TO BE USED procedure call NOT-standard:
// It only uses a simple register counter so considers S0 the same as D0,
// S1 as D1. It converts the register size correctly, but is wasteful.

#include <stdint.h>
#include <string.h>

// Pi Zero/Pi1 have VFP2, which only has 8 D registers and no VEOR.
// Will become a command-line flag eventually.
int vfp_version = 3;

#define VFP_SAVEREG_LOW R_F0 + NFLTARGREGS
#define VFP_SAVEREG_TOP VFP_SAVEREG_LOW + NFLTVARREGS

struct InlineTable inlinetable_vfp[] = {
    {"__r_abs",  0, VFP_VABS_S},
    {"__d_abs",  0, VFP_VABS_D},
    {0,0,0}};

typedef enum { encode_fail, encode_zero, encode_minus_zero, encode_imm } EncodedResult;

// Encode passed in float, returning  on failure, otherwise bits suitable
// for ORing with a VMOV ... #<imm> instruction.
static inline EncodedResult vfp_encode_imm_f32(FloatBin fb, uint32_t *imm8) {
    // F32: abcd efgh = aBbbbbbc defgh000 00000000 00000000
    const uint32_t b_mask = 0x7e; // mask valid once bits is shifted right 24.

    uint32_t masked_b, abcd;
    uint32_t bits = fb.val;

    // Fast-path zeros so J_*FK can preserve -0.0f correctly.
    if (bits == 0x00000000u) { *imm8 = 0; return encode_zero; }
    if (bits == 0x80000000u) { *imm8 = 0; return encode_minus_zero; }

    // Check if value can fit in an 8-bit immediate.
    if ((bits & 0x7ffffu) != 0)
        return encode_fail;

    // Check 'b' is repeated correctly ("B" is NOT b)
    masked_b = (bits >> 24) & b_mask;
    if (!(masked_b == 0x3e || masked_b == 0x40))
        return encode_fail;

    // bit a is at bit 31. Shift right by 28 as we want it in bit 3.
    // bit b is at bits [29:25]. Shift right by 27 as we want it in bit 2.
    // bit c is at bit 24. Shift right by 23 as we want it in bit 1.
    // bit d is at bit 23. Shift right by 23 as we want it in bit 0.
    abcd = ((bits >> 28) & 0x8) | ((bits >> 27) & 0x4) |
           ((bits >> 23) & 0x2) | ((bits >> 23) & 0x1);

    // imm4H in [19:16], imm4L in [3:0].
    *imm8 = (abcd << 16) | ((bits >> 19) & 0xf);

    return encode_imm;
}

static inline EncodedResult vfp_encode_imm_f64(DbleBin db, uint32_t *imm8) {
    // F64: abcd efgh = aBbbbbbb bbcdefgh 00000000 ...  00000000
    // hi: aBbbbbbb bbcdefgh 00000000 00000000. lo : 0
    const uint32_t b_mask = 0x7fc0; // mask valid once bits is shifted right 16.
    uint32_t masked_b, abcd;

    uint32_t bits_hi = db.msd;
    uint32_t bits_lo = db.lsd;

    // Fast-path zeros so J_*DK can preserve -0.0 correctly.
    if (bits_lo == 0u) {
        if (bits_hi == 0x00000000u) { *imm8 = 0; return encode_zero; }
        if (bits_hi == 0x80000000u) { *imm8 = 0; return encode_minus_zero; }
    }

    // Check if value can fit in an 8-bit immediate.
    if (bits_lo != 0 || (bits_hi & 0xffff) != 0)
        return encode_fail;

    // Check 'b' is repeated correctly ("B" is NOT b)
    masked_b = (bits_hi >> 16) & b_mask;
    if (!(masked_b == 0x3fc0 || masked_b == 0x4000))
        return encode_fail;

    // bit a is at bit 31. Shift right by 28 as we want it in bit 3.
    // bit b is at bits [29:22]. Shift right by 24 as we want it in bit 2.
    // bit c is at bit 21. Shift right by 20 as we want it in bit 1.
    // bit d is at bit 20. Shift right by 20 as we want it in bit 0.
    abcd = ((bits_hi >> 28) & 0x8) | ((bits_hi >> 24) & 0x4) |
           ((bits_hi >> 20) & 0x2) | ((bits_hi >> 20) & 0x1);

    // imm4H in [19:16], imm4L in [3:0].
    *imm8 = (abcd << 16) | ((bits_hi >> 16) & 0xf);

    return encode_imm;
}

/* Materialise a FloatCon into a VFP S/D register using a literal pool VLDR. */
// Based on fpa_show() case J_ADCOND
static bool vfp_materialise_literal(FloatCon *fc, bool is_double,
                                    uint32_t *direction, unsigned *offB)
{
    int size_words = is_double ? 2 : 1;
    int32 disp;

    *direction = VFP_UP;   /* up=+offset, down=-offset */
    disp = lit_findwordsincurpool(fc->floatbin.irep, size_words, LIT_FPNUM);
    if (disp < 0) {
        disp = lit_findwordsinprevpools(fc->floatbin.irep, size_words, LIT_FPNUM, codebase+codep+8-1020);
        if (disp >= 0) {
            disp      = codebase+codep+8 - disp; /* bytes */
            *direction = 0;
        } else {
            arm_addressability(256);

            if (size_words == 1) {
                disp = lit_findwordaux(fc->floatbin.fb.val,
                                       LIT_FPNUM, fc->floatstr,
                                       LITF_INCODE|LITF_FIRST|LITF_LAST);
            } else {
                // DbleBin is set to FPA order. Swap.
                (void)lit_findwordaux(fc->floatbin.db.lsd,
                                      LIT_FPNUM1, fc->floatstr,
                                      LITF_INCODE|LITF_FIRST|LITF_DOUBLE);
                /* use the second address in case overflow */
                disp =  lit_findwordaux(fc->floatbin.db.msd,
                                        LIT_FPNUM2, fc->floatstr,
                                        LITF_INCODE|LITF_LAST) - 4;
            }
        }
    }

    if (*direction == VFP_UP)
        addfref_(litlab, codep | LABREF_W256);

    *offB = (unsigned)(disp & ~3);

    return true;
}

// For double precision, map R_F0 upwards to VFP D0 upwards
static inline unsigned vfp_checkfreg_d(RealRegister r) {
    if (r < R_F0 || r >= R_F0 + NFLTARGREGS + NFLTVARREGS)
        syserr(syserr_gen_freg, (long)r);

    return (((int)r) & 0xf);
}

// For single precision, map R_F0..R_F7 to VFP S0..S15 STEP 2.
// This is to temporarily re-use the FPA register allocator.
static inline unsigned vfp_checkfreg_s(RealRegister r) {
    if (r < R_F0 || r >= R_F0 + NFLTARGREGS + NFLTVARREGS)
        syserr(syserr_gen_freg, (long)r);

    return (((int)r) & 0xf) * 2;
}

static void vfp_show(const PendingOp *p);
static void vfp_saveregs(int32 mask);
static int32 vfp_restoresize(int32 mask);
static void vfp_restoreregs(int32 mask, int32 condition,
                            FP_RestoreBase base, int32 offset);
static void vfp_saveargs(int32 n);

FP_Gen const vfp_gen = {
    vfp_show,
    vfp_saveregs,
    vfp_restoresize,
    vfp_restoreregs,
    vfp_saveargs
};

#define outinstr(X) arm_outinstr(X)

static void vfp_show(const PendingOp *p)
{   struct DispDesc dispdesc;
    J_OPCODE op = p->ic.op;
    RealRegister r1 = p->ic.r1.i, r2 = p->ic.r2.i, r3 = p->ic.r3.i;
    int peep = p->peep;
    int32 w;
    UPtr illbits;

    /* For now we accept the same legality mask as FPA/AMP. */
    illbits = op & (Q_MASK | J_SIGNED | J_UNSIGNED | J_NEGINDEX | J_SHIFTMASK);

    switch (op & ~(Q_MASK | J_SIGNED | J_UNSIGNED | J_NEGINDEX | J_SHIFTMASK))
    {
        case J_PUSHF: {
            arm_ldm_flush();
            outinstr(VFP_VPUSH_S | VFP_Sd(vfp_checkfreg_s(r1)) | 1);
            arm_adjustipvalue(R_SP, R_SP, -4);
            break;
        }
        case J_PUSHD: {
            arm_ldm_flush();
            outinstr(VFP_VPUSH_D | VFP_Dd(vfp_checkfreg_d(r1)) | 2);
            arm_adjustipvalue(R_SP, R_SP, -8);
            break;
        }

        case J_MOVFK: { // move float literal into Sd
            FloatCon *fc = (FloatCon *)r3;
            const int dest = vfp_checkfreg_s(r1);
            uint32_t imm8;
            EncodedResult res = vfp_encode_imm_f32(fc->floatbin.fb, &imm8);
            if (res == encode_imm) {
                outinstr(VFP_VMOV_S_IMM | VFP_Sd(dest) | imm8);
            } else if (res == encode_zero || res == encode_minus_zero) {
                outinstr(OP_EORR | F_RD(R_IP) | F_RN(R_IP) | F_RM(R_IP)); // mov ip, #0
                outinstr(VFP_VMOV_S_R | VFP_Sn(dest) | VFP_Rt(R_IP));
                if (res == encode_minus_zero)
                    outinstr(VFP_VNEG_S | VFP_Sd(dest) | VFP_Sm(dest));
            } else {
                /* fall back to literal pool: VLDR Sd, [pc, #offB] via vfp_materialise_literal(...) */
                uint32_t direction, offB;
                int sd = vfp_checkfreg_s(r1);
                vfp_materialise_literal(fc, /*is_double=*/0, &direction, &offB);
                outinstr(VFP_VLDR_S(R_PC, sd, offB) | direction );
            }
            break;
        }

        /* J_MOVDK: move double literal into Dd */
        case J_MOVDK: {
            FloatCon *fc = (FloatCon *)r3;
            const int dest = vfp_checkfreg_d(r1);
            uint32_t imm8;
            EncodedResult res = vfp_encode_imm_f64(fc->floatbin.db, &imm8);
            if (res == encode_imm) {
                outinstr(VFP_VMOV_D_IMM | VFP_Dd(dest) | imm8);
            } else if (res == encode_zero || res == encode_minus_zero) {
                if (vfp_version >= 3 && is_condition_always())
                    outinstr_vfp_simd(VFP_VEOR_D | VFP_Dd(dest) | VFP_Dn(dest) | VFP_Dm(dest)); // #0
                else {
                    outinstr(OP_EORR | F_RD(R_IP) | F_RN(R_IP) | F_RM(R_IP)); // mov ip, #0
                    outinstr(VFP_VMOV_D_R_R | VFP_Dm(dest) | VFP_Rt(R_IP) | VFP_Rt2(R_IP));
                }
                if (res == encode_minus_zero)
                    outinstr(VFP_VNEG_D | VFP_Dd(dest) | VFP_Dm(dest));
            } else {
                uint32_t direction, offB;
                int dd = vfp_checkfreg_d(r1);
                vfp_materialise_literal(fc, /*is_double=*/1, &direction, &offB);
                outinstr( VFP_VLDR_D(R_PC, dd, offB) | direction );
            }
            break;
        }

        case J_ADCONF:
        case J_ADCOND: {
            // Address constant. Based on a comment in jopcode.h, it seems
            // they can never occur with an FPU. Implement them anyway as it's
            // the same code as MOVDK/MOVFK. No load should happen, as per
            // fpa_show() if opcode is ADCONF/ADCOND.

            FloatCon *fc = (FloatCon *)r3;
            const bool is_double = (op == J_ADCOND);
            uint32_t direction, offB;
            uint32 disp_words, adconop;

            vfp_materialise_literal(fc, /*is_double=*/is_double, &direction, &offB);

            // offB is a byte offset from PC, multiple of 4.
            disp_words = offB >> 2;
            adconop = (direction == VFP_UP) ? OP_ADDN : OP_SUBN;
            outinstr(adconop | F_RD(r1) | F_RN(R_PC) | disp_words | 0xf00);
            break;
        }

        case J_CMPFR: {
            outinstr(VFP_VCMP_S | VFP_Sd(vfp_checkfreg_s(r2)) | VFP_Sm(vfp_checkfreg_s(r3)) );
            outinstr(VFP_VMRS_APSR); // Move flags to ASPR
            illbits &= ~Q_MASK;
            break;
        }
        case J_CMPDR: { /* compare d(r2) vs d(r3) */
            outinstr(VFP_VCMP_D | VFP_Dd(vfp_checkfreg_d(r2)) | VFP_Dm(vfp_checkfreg_d(r3)) );
            outinstr(VFP_VMRS_APSR); // Move flags to ASPR
            illbits &= ~Q_MASK;
            break;
        }
        case J_CMPFK: {
            FloatCon *fc = (FloatCon *)r3;

            /* If constant is exactly 0.0f use VCMPZ, else VLDR into scratch and VCMP */
            if (fc->floatbin.fb.val == 0) {
                outinstr(VFP_VCMPZ_S | VFP_Sd(vfp_checkfreg_s(r2)));
            } else {
                uint32_t direction;
                unsigned offB;

                if (!vfp_materialise_literal(fc, /*is_double*/false, &direction, &offB)) {
                    syserr(syserr_show_inst_dir, (long)op);
                }

                outinstr(VFP_VLDR_S(R_PC, VFP_SCR_S, offB) | direction);
                outinstr(VFP_VCMP_S | VFP_Sd(vfp_checkfreg_s(r2)) | VFP_Sm(VFP_SCR_S));
            }

            outinstr(VFP_VMRS_APSR); // Move flags to ASPR
            illbits &= ~Q_MASK;
            break;
        }

        case J_CMPDK: {
            FloatCon *fc = (FloatCon *)r3;

            if (fc->floatbin.db.msd == 0 && fc->floatbin.db.lsd == 0) {
                outinstr(VFP_VCMPZ_D | VFP_Dd(vfp_checkfreg_d(r2)));
            } else {
                uint32_t direction;
                unsigned offB;

                if (!vfp_materialise_literal(fc, /*is_double*/true, &direction, &offB)) {
                    syserr(syserr_show_inst_dir, (long)op);
                }

                outinstr(VFP_VLDR_D(R_PC, VFP_SCR_D, offB) | direction);
                outinstr(VFP_VCMP_D | VFP_Dd(vfp_checkfreg_d(r2)) | VFP_Dm(VFP_SCR_D));
            }

            outinstr(VFP_VMRS_APSR); // Move flags to ASPR
            illbits &= ~Q_MASK;
            break;
        }

        case J_MOVFR: // mov.f32 between two fregs
            outinstr(VFP_VMOV_S_S | VFP_Sd(vfp_checkfreg_s(r1)) | VFP_Sm(vfp_checkfreg_s(r3)));
            break;

        case J_MOVDR: // mov.f64 between two fregs
            outinstr(VFP_VMOV_D_D | VFP_Dd(vfp_checkfreg_d(r1)) | VFP_Dm(vfp_checkfreg_d(r3)));
            break;

        case J_NEGFR:
            outinstr(VFP_VNEG_S | VFP_Sd(vfp_checkfreg_s(r1)) | VFP_Sm(vfp_checkfreg_s(r3)));
            break;

        case J_NEGDR:
            outinstr(VFP_VNEG_D | VFP_Dd(vfp_checkfreg_d(r1)) | VFP_Dm(vfp_checkfreg_d(r3)));
            break;

        case J_MOVFDR: // convert float to double
            outinstr(VFP_VCVT_F64_F32 | VFP_Dd(vfp_checkfreg_d(r1)) | VFP_Sm(vfp_checkfreg_s(r3)));
            break;

        case J_MOVDFR: // convert double to float
            outinstr(VFP_VCVT_F32_F64 | VFP_Sd(vfp_checkfreg_s(r1)) | VFP_Dm(vfp_checkfreg_d(r3)));
            break;

        case J_FIXFRM: { // signed fix towards minus infinity floor()
            outinstr(VFP_VCVT_S32_F32_FLOOR | VFP_Sd(VFP_SCR_S) | VFP_Sm(vfp_checkfreg_s(r3)));
            outinstr(VFP_VMOV_R_S | VFP_Rt(R_(r1)) | VFP_Sn(VFP_SCR_S));
            illbits ^= J_SIGNED;
            break;
        }

        case J_FIXDRM: { // signed fix towards minus infinity floor()
            outinstr(VFP_VCVT_S32_F64_FLOOR | VFP_Sd(VFP_SCR_S) | VFP_Dm(vfp_checkfreg_d(r3)));
            outinstr(VFP_VMOV_R_S | VFP_Rt(R_(r1)) | VFP_Sn(VFP_SCR_S));
            illbits ^= J_SIGNED;
            break;
        }

        case J_FIXFR: // FP to Int. C signed fix (truncate towards zero) - C cast
            outinstr(VFP_VCVT_S32_F32 | VFP_Sd(VFP_SCR_S) | VFP_Sm(vfp_checkfreg_s(r3)));
            outinstr(VFP_VMOV_R_S | VFP_Rt(R_(r1)) | VFP_Sn(VFP_SCR_S));
            illbits ^= J_SIGNED;
            break;

        case J_FIXDR: // FP to Int. C signed fix (truncate towards zero) - C cast
            outinstr(VFP_VCVT_S32_F64 | VFP_Sd(VFP_SCR_S) | VFP_Dm(vfp_checkfreg_d(r3)));
            outinstr(VFP_VMOV_R_S | VFP_Rt(R_(r1)) | VFP_Sn(VFP_SCR_S));
            illbits ^= J_SIGNED;
            break;

        case J_FLTFR: { // Int to FP.
            outinstr(VFP_VMOV_S_R | VFP_Sn(vfp_checkfreg_s(r1)) | VFP_Rt(R_(r3)));
            outinstr(VFP_VCVT_F32_S32 | VFP_Sd(vfp_checkfreg_s(r1)) | VFP_Sm(vfp_checkfreg_s(r1)));
            illbits ^= J_SIGNED;
            break;
        }

        case J_FLTDR: { // Int to FP. Scratch reg can be Dreg * 2 as it's the same.
            uint32_t d = vfp_checkfreg_d(r1);
            outinstr(VFP_VMOV_S_R | VFP_Sn(d*2) | VFP_Rt(R_(r3)));
            outinstr(VFP_VCVT_F64_S32 | VFP_Dd(d) | VFP_Sm(d*2));
            illbits ^= J_SIGNED;
            break;
        }

        case J_MOVIFR: // Load FP reg from int reg
            outinstr(VFP_VMOV_S_R | VFP_Sn(vfp_checkfreg_s(r1)) | VFP_Rt(R_(r3)));
            break;

        case J_MOVFIR:
            outinstr(VFP_VMOV_R_S | VFP_Rt(R_(r1)) | VFP_Sn(vfp_checkfreg_s(r3)));
            break;

        case J_MOVDIR: // Load integer register pair from fp register
            outinstr(VFP_VMOV_R_R_D | VFP_Rt(R_(r1)) | VFP_Rt2(R_(r2)) |
                     VFP_Dm(vfp_checkfreg_d(r3)));
            break;

        case J_MOVIDM: { /* Load n FP registers from 2n integer registers.
                           r3: bitmap of integer source registers (core regs)
                           r1: bitmap of destination FP registers (D-regs). */
            int32 fr;
            uint32_t intmask = R_(r3);
            uint32_t dmask   = R_(r1);
            int intcnt = bitcount(intmask);
            int dcnt   = bitcount(dmask);

            /* Require exactly two core regs per D-reg. */
            if (intcnt != 2 * dcnt) {
                syserr(syserr_show_inst_dir, (long)op);
                break;
            }

            // For each destination D-reg bit, take next two core regs.
            for (fr = R_F0; dmask != 0; ++fr) {
                int rt  = -1;
                int rt2 = -1;
                int idx;

                if (!(dmask & regbit(fr)))
                    continue;

                /* Find two lowest indices set in intmask. */
                for (idx = 0; idx < 32; ++idx) {
                    if (intmask & (1u << idx)) {
                        if (rt < 0) {
                            rt = idx;
                        } else {
                            rt2 = idx;
                            break;
                        }
                    }
                }

                if (rt < 0 || rt2 < 0) {
                    syserr(syserr_show_inst_dir, (long)op);
                    break;
                }

                /* VMOV Dd <- Rt,Rt2 */
                outinstr(VFP_VMOV_D_R_R | VFP_Dm(vfp_checkfreg_d(fr))
                         | VFP_Rt(rt) | VFP_Rt2(rt2));

                /* Consume used bits. */
                intmask &= ~(1u << rt);
                intmask &= ~(1u << rt2);
                dmask   &= ~regbit(fr);
            }
            break;
        }

        case J_MOVDIM: {
            // Load 2n integer registers from n FP registers.
            //   r3: bitmap of 'n' source FP D-registers
            //   r1: bitmap of destination core integer registers
            // There may be more than 2n entries in r1 map (see fpa_show()).
            uint32_t dmask   = R_(r3);
            uint32_t intmask = R_(r1);
            int dcnt   = bitcount(dmask);
            int intcnt = bitcount(intmask);
            uint32_t used_ints = 0;
            int32 fr;

            /* Must have at least two integer destinations per D-reg source. */
            if (intcnt < 2 * dcnt) {
                syserr(syserr_show_inst_dir, (long)op);
                break;
            }

            for (fr = R_F0; dmask != 0; ++fr) {
                int rt = -1, rt2 = -1;
                int idx;

                if (!(dmask & regbit(fr)))
                    continue;

                /* Find first two destination core regs. */
                for (idx = 0; idx < 32; ++idx) {
                    if (intmask & (1u << idx)) {
                        if (rt < 0) { rt = idx; }
                        else { rt2 = idx; break; }
                    }
                }
                if (rt < 0 || rt2 < 0) {
                    syserr(syserr_show_inst_dir, (long)op);
                    break;
                }

                /* Emit: VMOV Rt, Rt2, Dm (core pair from D-reg) */
                outinstr(VFP_VMOV_R_R_D
                         | VFP_Rt(rt) | VFP_Rt2(rt2)
                         | VFP_Dm(vfp_checkfreg_d(fr)));

                /* Consume and record these integer destinations; clear this D bit. */
                intmask   &= ~(1u << rt);
                intmask   &= ~(1u << rt2);
                used_ints |=  (1u << rt) | (1u << rt2);
                dmask     &= ~regbit(fr);
            }

            // Mark used integer registers as having unknown values.
            // This doesn't necessarily write out all of r1 as fpa_show() does.
            // It's currently unclear if this is necessary or if returning
            // an incomplete map will trigger it to be written elsewhere.
            arm_KillKnownRegisterValues(used_ints);
            break;
        }

        case J_MOVIDR: {
            /* Load FP register from 2 integer registers.  Only happens just after   */
            /* function entry, with the integer registers being argument registers.  */
            /* If arguments have been pushed on the stack, we can load the fp value  */
            /* directly.  (It would be nice to ensure that if anything had been      */
            /* pushed on entry, the argument registers of the MOVIDR had).           */
            outinstr(VFP_VMOV_D_R_R | VFP_Dm(vfp_checkfreg_d(r1)) |
                     VFP_Rt(R_(r3)) | VFP_Rt2(R_(r2)));
            break;
        }

        // Loads/stores from memory
        case J_LDRFK+J_ALIGN4:   // load  float,  align 4
        case J_LDRDK+J_ALIGN4:   // load  double, align 4 -- slow
        case J_LDRDK+J_ALIGN8:   // load  double, align 8
        case J_STRFK+J_ALIGN4:   // store float,  align 4
        case J_STRDK+J_ALIGN4:   // store double, align 4 -- slow
        case J_STRDK+J_ALIGN8: { // store double, align 8
            const bool is_load   = loads_r1(op) != 0;
            const bool is_double = ((op & J_TABLE_BITS) == J_LDRDK) || ((op & J_TABLE_BITS) == J_STRDK);
            const bool want_pre  = (peep & P_PRE)  != 0;
            const bool want_post = (peep & P_POST) != 0;
            const bool need_wb   = want_pre || want_post;

            uint32_t base, offB, offW, insn;
            bool dir_up;

            arm_ldm_flush();

            /* Compute base, direction and byte offset (multiple of 4). */
            arm_bigdisp(&dispdesc, R_(r3), 0x3fc, r2);      /* ±1020 with word scaling */
            base  = R_(dispdesc.r);
            offB  = dispdesc.m;              /* byte offset (multiple of 4) */
            dir_up    = (dispdesc.u_d == F_UP);

            offW = need_wb ? 0u : (offB >> 2);

            insn = VFP_Rn(base);
            if (is_load) {
                if (is_double)
                    insn |= VFP_VLDR_D_IMM | VFP_Dd(vfp_checkfreg_d(r1));
                else
                    insn |= VFP_VLDR_S_IMM | VFP_Sd(vfp_checkfreg_s(r1));
            } else {
                if (is_double)
                    insn |= VFP_VSTR_D_IMM | VFP_Dd(vfp_checkfreg_d(r1));
                else
                    insn |= VFP_VSTR_S_IMM | VFP_Sd(vfp_checkfreg_s(r1));
            }

            /* We cannot use writeback with VLDR/VSTR. If pre/post-indexing
             * was requested, we emulate it with an ADD/SUB around a zero-offset transfer. */
            if (need_wb && offB) {
                /* PRE: adjust base first, then zero-offset transfer. */
                if (want_pre) {
                    arm_gen_add_integer(base, base, dir_up ? (int32)offB : -(int32)offB, 0);
                    if (base == R_SP)
                        arm_fpdesc_notespchange(dir_up ? -(int32)offB : (int32)offB);
                }

                outinstr(insn | offW);

                /* POST: zero-offset transfer, then adjust base. */
                if (want_post) {
                    arm_gen_add_integer(base, base, dir_up ? (int32)offB : -(int32)offB, 0);
                    if (base == R_SP)
                        arm_fpdesc_notespchange(dir_up ? -(int32)offB : (int32)offB);
                }
            } else {
                /* No writeback requested: use the immediate offset encoding.
                 *
                 * IMPORTANT: For VFP VLDR/VSTR (immediate), the direction (add/sub)
                 * is selected by the U bit, NOT by the sign of the encoded offset.
                 * The offset field 'offW' is always an *unsigned* #words (0..255).
                 * We must therefore set/clear the U bit to match 'dir_up'.
                 */

                /* Prefer '+0' aesthetically in the disassembly, but still honour U for non-zero. */
                if (offW == 0) {
                    insn |= VFP_UP;            /* [Rn, #+0] */
                } else {
                    if (dir_up) insn |= VFP_UP; /* [Rn, #+off]  */
                    /* else U=0 => [Rn, #-off] */
                }

                outinstr(insn | offW);
            }

            /* Clear peep info we've just consumed. */
            peep &= ~(P_BASEALIGNED | P_PRE | P_POST);
            break;
        }

        case J_ADDFR:
            outinstr(VFP_VADD_S | VFP_Sd(vfp_checkfreg_s(r1)) |
                     VFP_Sn(vfp_checkfreg_s(r2)) | VFP_Sm(vfp_checkfreg_s(r3)));
            break;

        case J_ADDDR:
            outinstr(VFP_VADD_D | VFP_Dd(vfp_checkfreg_d(r1)) |
                     VFP_Dn(vfp_checkfreg_d(r2)) | VFP_Dm(vfp_checkfreg_d(r3)));

            break;

        case J_SUBFR:
            outinstr(VFP_VSUB_S | VFP_Sd(vfp_checkfreg_s(r1)) |
                     VFP_Sn(vfp_checkfreg_s(r2)) | VFP_Sm(vfp_checkfreg_s(r3)));
            break;

        case J_SUBDR: {
            outinstr(VFP_VSUB_D | VFP_Dd(vfp_checkfreg_d(r1)) |
                     VFP_Dn(vfp_checkfreg_d(r2)) | VFP_Dm(vfp_checkfreg_d(r3)));
            break;
        }
        case J_RSBFR:
            outinstr(VFP_VSUB_S | VFP_Sd(vfp_checkfreg_s(r1)) |
                     VFP_Sn(vfp_checkfreg_s(r3)) | VFP_Sm(vfp_checkfreg_s(r2)));
            break;

        case J_RSBDR:
            outinstr(VFP_VSUB_D | VFP_Dd(vfp_checkfreg_d(r1)) |
                     VFP_Dn(vfp_checkfreg_d(r3)) | VFP_Dm(vfp_checkfreg_d(r2)));
            break;

        case J_MULFR:
            outinstr(VFP_VMUL_S | VFP_Sd(vfp_checkfreg_s(r1)) |
                     VFP_Sn(vfp_checkfreg_s(r2)) | VFP_Sm(vfp_checkfreg_s(r3)));
            break;

        case J_MULDR:
            outinstr(VFP_VMUL_D | VFP_Dd(vfp_checkfreg_d(r1)) |
                     VFP_Dn(vfp_checkfreg_d(r2)) | VFP_Dm(vfp_checkfreg_d(r3)));
            break;

        case J_DIVFR:
            outinstr(VFP_VDIV_S | VFP_Sd(vfp_checkfreg_s(r1)) |
                     VFP_Sn(vfp_checkfreg_s(r2)) | VFP_Sm(vfp_checkfreg_s(r3)));
            break;

        case J_DIVDR:
            outinstr(VFP_VDIV_D | VFP_Dd(vfp_checkfreg_d(r1)) |
                     VFP_Dn(vfp_checkfreg_d(r2)) | VFP_Dm(vfp_checkfreg_d(r3)));
            break;

        case J_RDVFR:
            outinstr(VFP_VDIV_S | VFP_Sd(vfp_checkfreg_s(r1)) |
                     VFP_Sn(vfp_checkfreg_s(r3)) | VFP_Sm(vfp_checkfreg_s(r2)));
            break;

        case J_RDVDR:
            outinstr(VFP_VDIV_D | VFP_Dd(vfp_checkfreg_d(r1)) |
                     VFP_Dn(vfp_checkfreg_d(r3)) | VFP_Dm(vfp_checkfreg_d(r2)));
            break;

        case J_ADDFK:
        case J_SUBFK:
        case J_RSBFK:
        case J_MULFK:
        case J_DIVFK:
        case J_RDVFK: {
            unsigned dst = vfp_checkfreg_s(r1);
            unsigned lhs = vfp_checkfreg_s(r2);
            FloatCon *fc = (FloatCon *)r3;
            uint32_t imm8;

            EncodedResult res = vfp_encode_imm_f32(fc->floatbin.fb, &imm8);
            if (res == encode_imm) {
                outinstr(VFP_VMOV_S_IMM | VFP_Sd(VFP_SCR_S) | imm8);
            } else if (res == encode_zero || res == encode_minus_zero) {
                outinstr(OP_EORR | F_RD(R_IP) | F_RN(R_IP) | F_RM(R_IP)); // mov ip, #0
                outinstr(VFP_VMOV_S_R | VFP_Sn(VFP_SCR_S) | VFP_Rt(R_IP));
                if (res == encode_minus_zero)
                    outinstr(VFP_VNEG_S | VFP_Sd(VFP_SCR_S) | VFP_Sm(VFP_SCR_S));
            } else {
                uint32_t direction, offB;
                if (!vfp_materialise_literal(fc, false /*double*/, &direction, &offB))
                    syserr(syserr_show_inst_dir, (long)op);

                outinstr(VFP_VLDR_S(R_PC, VFP_SCR_S, offB) | direction);
            }

            switch (op & J_TABLE_BITS) {
                case J_ADDFK: outinstr(VFP_VADD_S | VFP_Sd(dst) | VFP_Sn(lhs) | VFP_Sm(VFP_SCR_S)); break; // dst = lhs + scr
                case J_SUBFK: outinstr(VFP_VSUB_S | VFP_Sd(dst) | VFP_Sn(lhs) | VFP_Sm(VFP_SCR_S)); break;
                case J_MULFK: outinstr(VFP_VMUL_S | VFP_Sd(dst) | VFP_Sn(lhs) | VFP_Sm(VFP_SCR_S)); break;
                case J_DIVFK: outinstr(VFP_VDIV_S | VFP_Sd(dst) | VFP_Sn(lhs) | VFP_Sm(VFP_SCR_S)); break;

                // Reverse subtract/divide.
                case J_RSBFK: outinstr(VFP_VSUB_S | VFP_Sd(dst) | VFP_Sn(VFP_SCR_S) | VFP_Sm(lhs)); break; // dst = scr - lhs
                case J_RDVFK: outinstr(VFP_VDIV_S | VFP_Sd(dst) | VFP_Sn(VFP_SCR_S) | VFP_Sm(lhs)); break;
            }
            break;
        }

        case J_ADDDK:
        case J_SUBDK:
        case J_RSBDK:
        case J_MULDK:
        case J_DIVDK:
        case J_RDVDK: {
            unsigned dst = vfp_checkfreg_d(r1);
            unsigned lhs = vfp_checkfreg_d(r2);
            FloatCon *fc = (FloatCon *)r3;
            uint32_t imm8;

            EncodedResult res = vfp_encode_imm_f64(fc->floatbin.db, &imm8);
            if (res == encode_imm) {
                outinstr(VFP_VMOV_D_IMM | VFP_Dd(VFP_SCR_D) | imm8);
            } else if (res == encode_zero || res == encode_minus_zero) {
                if (vfp_version >= 3 && is_condition_always())
                    outinstr_vfp_simd(VFP_VEOR_D | VFP_Dd(VFP_SCR_D) | VFP_Dn(VFP_SCR_D) | VFP_Dm(VFP_SCR_D)); // #0
                else {
                    outinstr(OP_EORR | F_RD(R_IP) | F_RN(R_IP) | F_RM(R_IP)); // mov ip, #0
                    outinstr(VFP_VMOV_D_R_R | VFP_Dn(VFP_SCR_D) | VFP_Rt(R_IP) | VFP_Rt2(R_IP));
                }
                if (res == encode_minus_zero)
                    outinstr(VFP_VNEG_D | VFP_Dd(VFP_SCR_D) | VFP_Dm(VFP_SCR_D));
            } else {
                uint32 direction; unsigned offB;
                if (!vfp_materialise_literal(fc, true /*double*/, &direction, &offB))
                    syserr(syserr_show_inst_dir, (long)op);

                outinstr(VFP_VLDR_D(R_PC, VFP_SCR_D, offB) | direction);
            }

            switch (op & J_TABLE_BITS) {
                case J_ADDDK: outinstr(VFP_VADD_D | VFP_Dd(dst) | VFP_Dn(lhs) | VFP_Dm(VFP_SCR_D)); break;
                case J_SUBDK: outinstr(VFP_VSUB_D | VFP_Dd(dst) | VFP_Dn(lhs) | VFP_Dm(VFP_SCR_D)); break;
                case J_MULDK: outinstr(VFP_VMUL_D | VFP_Dd(dst) | VFP_Dn(lhs) | VFP_Dm(VFP_SCR_D)); break;
                case J_DIVDK: outinstr(VFP_VDIV_D | VFP_Dd(dst) | VFP_Dn(lhs) | VFP_Dm(VFP_SCR_D)); break;

                // Reverse subtract/divide.
                case J_RSBDK: outinstr(VFP_VSUB_D | VFP_Dd(dst) | VFP_Dn(VFP_SCR_D) | VFP_Dm(lhs)); break;
                case J_RDVDK: outinstr(VFP_VDIV_D | VFP_Dd(dst) | VFP_Dn(VFP_SCR_D) | VFP_Dm(lhs)); break;
            }
            break;
        }

        case J_INLINE1F:
                outinstr(r3 | VFP_Sd(vfp_checkfreg_d(r1)) | VFP_Sd(vfp_checkfreg_d(r2)));
                break;

        case J_INLINE1D:
                outinstr(r3 | VFP_Dd(vfp_checkfreg_d(r1)) | VFP_Dd(vfp_checkfreg_d(r2)));
                break;

            /* --- Range checks (if enabled) --- */
#ifdef RANGECHECK_SUPPORTED
        case J_CHKNEFR: {  /* fault if float == 0.0 */
            arm_ldm_flush();
            int sd = vfp_checkfreg_s(r2);
            outinstr(VFP_VCMPZ_S | VFP_Sd(sd));
            outinstr(VFP_VMRS_APSR);
            outinstr3((OP_BL | F_COND(COND_EQ)), bindsym_(exb_(sim.valfault)), 0);
            illbits &= ~Q_MASK;
            break;            break;
        }
        case J_CHKNEDR: {  /* fault if double == 0.0 */
            arm_ldm_flush();
            int dd = vfp_checkfreg_d(r2);
            outinstr(VFP_VCMPZ_D(dd));
            outinstr(VFP_VMRS_APSR);
            outinstr3((OP_BL | F_COND(COND_EQ)), bindsym_(exb_(sim.valfault)), 0);
            illbits &= ~Q_MASK;
            break;
        }
#endif

        default:
            syserr(syserr_show_inst_dir, (long)op);
            illbits = 0;
            break;
    }

    if (illbits | peep)
        syserr(syserr_jop_mode, (long)op, (long)peep);
}

static void vfp_saveregs(int32 mask)
{
    RealRegister r = VFP_SAVEREG_LOW;

    while (r < VFP_SAVEREG_TOP) {
        RealRegister start;
        unsigned count = 0;

        /* find next run of set bits */
        if (!(mask & regbit(r))) {
            ++r;
            continue;
        }

        start = r;
        count = 0;

        while (r < VFP_SAVEREG_TOP && (mask & regbit(r))) {
            ++count;
            ++r;
        }

        // VPUSH stores a contiguous list starting at Dstart, unlike PUSH.
        // imm8 is in units of S-regs, so double it for D-regs.
        outinstr(VFP_VPUSH_D
                 | VFP_Dd(vfp_checkfreg_d(start))
                 | (count * 2));
        arm_fpdesc_notespchange(8 * (int)count);
    }
}

static int32 vfp_restoresize(int32 mask)
{
    // 8 bytes per saved D-reg (F4..F7 only)
    int32 n = 0;
    RealRegister r;
    for (r = VFP_SAVEREG_LOW; r < VFP_SAVEREG_TOP; ++r) {
        if (mask & regbit(r))
            n += 8;
    }

    return n;
}

static void vfp_restoreregs(int32 mask, int32 condition,
                            FP_RestoreBase base, int32 offset_bytes)
{
    if (base == UseSP_Adjust) {
        /* VPOP in contiguous runs from the lowest register upwards. */
        RealRegister r = VFP_SAVEREG_LOW;
        while (r < VFP_SAVEREG_TOP) {
            RealRegister start;
            unsigned count = 0;

            if (!(mask & regbit(r))) {
                ++r;
                continue;
            }

            start = r;
            while (r < VFP_SAVEREG_TOP && (mask & regbit(r))) {
                ++count;
                ++r;
            }

            outinstr(VFP_VPOP_D | condition |
                     VFP_Dd(vfp_checkfreg_d(start)) |
                     (count * 2));
            arm_fpdesc_notespchange(-8 * (int)count);
        }
    } else if (base == UseSP_NoAdjust) {
        // Restore from SP+offset without adjusting SP.
        // UseFP (below) has a better algorithm than this.
        RealRegister r = VFP_SAVEREG_LOW;
        while (r < VFP_SAVEREG_TOP) {
            RealRegister run_lo, run_hi;
            unsigned run_len = 0;

            if (!(mask & regbit(r))) {
                ++r;
                continue;
            }

            // Start of a run
            run_lo = r;
            while (r < VFP_SAVEREG_TOP && (mask & regbit(r))) {
                ++run_len;
                ++r;
            }

            run_hi = run_lo + (run_len - 1);

            if (run_len == 1) {
                outinstr(VFP_VLDR_D_IMM | condition |
                         VFP_Rn(R_SP) | VFP_Dd(vfp_checkfreg_d(run_lo)) |
                         (unsigned)(offset_bytes >> 2));
                offset_bytes += 8;
            } else {
                arm_gen_add_integer(R_IP, R_SP, offset_bytes, 0);

                outinstr(VFP_VLDMFD_D | condition |
                         VFP_Rn(R_IP) | VFP_Dd(vfp_checkfreg_d(run_lo)) |
                         (run_len * 2));

                offset_bytes += 8 * run_len;
            }
        }
    } else { // base == UseFP
        // FP-relative loads. Calculate words-below-FP once, then group
        // contiguous runs, using VLDR if the length is just one.
        // Must combine with UseSP_NoAdjust, and possibly Adjust.
        uint32_t num_regs = bitcount(regmask & M_FVARREGS);
        int32 n_words_below_fp = arm_intsavewordsbelowfp() +
                                 2 * num_regs +
                                 arm_realargwordsbelowfp();
        RealRegister r = VFP_SAVEREG_LOW;
        bool need_set_ip = true;

        if (num_regs == 0)
            return;

        while (r < VFP_SAVEREG_TOP) {
            RealRegister run_lo, run_hi;
            unsigned run_len = 0;

            if (!(mask & regbit(r))) {
                ++r;
                continue;
            }

            // Start a run
            run_lo = r;
            while (r < VFP_SAVEREG_TOP && (mask & regbit(r))) {
                ++run_len;
                ++r;
            }

            run_hi = run_lo + (run_len - 1);

            if (run_len == 1) {
                outinstr((VFP_VLDR_D_IMM | condition) |
                         VFP_Rn(R_FP) | VFP_Dd(vfp_checkfreg_d(run_lo)) |
                         (unsigned)n_words_below_fp);
                need_set_ip = true; // hasn't updated ip.
                n_words_below_fp -= 2;
            } else {
                if (need_set_ip) {
                    arm_gen_add_integer(R_IP, R_FP, -n_words_below_fp * 4, 0);
                    need_set_ip = false; // will be maintained by writeback
                }

                outinstr(VFP_VLDMFD_D | condition | VFP_WRITEBACK |
                         VFP_Rn(R_IP) | VFP_Dd(vfp_checkfreg_d(run_lo)) |
                         (run_len * 2));

                n_words_below_fp -= 2 * run_len;
            }
        }
    }
}

static void vfp_saveargs(int32 n)
{
    unsigned int list;
    unsigned dd;

    if (n == 0)
        return;

    list = ((1u << n) - 1) << 1;
    dd = vfp_checkfreg_d(R_F0);

    // Push incoming FP args D0..D{n-1}.
    outinstr(VFP_VPUSH_D | VFP_Dd(dd) | (n * 2));

    arm_fpdesc_notespchange(8 * n);
}
