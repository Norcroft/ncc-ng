/* Copyright 2025 Piers Wombwell
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#include "globals.h"
#include "disass-arm.h"
#include "disass-vfp.h"
#include "vfpops.h"

#include <stdio.h>
#include <string.h>

#define BITS(v,hi,lo) (((v) >> (lo)) & ((1u << ((hi)-(lo)+1)) - 1u))

/* Bits used to encode VFP D/S registers – used to mask off register fields
   when pattern-matching against opcodes from vfpops.h. */
#define VFP_REGMASK_DS   ((unsigned32)((1u<<22) | (0xFu<<12) | (1u<<7) | (0xFu<<16) | (1u<<5) | 0xFu))
#define VFP_CONDMASK     ((unsigned32)0xF0000000u)
#define VFP_LDST_REGMASK ((unsigned32)((1u<<23) | (1u<<22) | (0xFu<<12) | (0xFu<<16) | 0xFFu))
#define VFP_VCMP_REGMASK ((unsigned32)((1u<<22) | (0xFu<<12) | (1u<<5) | 0xFu))
#define VFP_SCALAR_REGMASK_DS ((unsigned32)((1u<<22) | (0xFu<<12) | (1u<<5) | 0xFu))

static unsigned vfp_decode_d_reg_from_D_Vd(unsigned32 instr)
{
    unsigned D  = (instr >> 22) & 1u;
    unsigned Vd = (instr >> 12) & 0xFu;
    return (D << 4) | Vd;
}

static unsigned vfp_decode_d_reg_from_N_Vn(unsigned32 instr)
{
    unsigned N  = (instr >> 7) & 1u;
    unsigned Vn = (instr >> 16) & 0xFu;
    return (N << 4) | Vn;
}

static unsigned vfp_decode_d_reg_from_M_Vm(unsigned32 instr)
{
    unsigned M  = (instr >> 5) & 1u;
    unsigned Vm = instr & 0xFu;
    return (M << 4) | Vm;
}

static unsigned vfp_decode_s_reg_from_D_Vd(unsigned32 instr)
{
    /* Sd is encoded like Dd but with an extra low bit. */
    unsigned D  = (instr >> 22) & 1u;
    unsigned Vd = (instr >> 12) & 0xFu;
    return (Vd << 1) | D;
}

static unsigned vfp_decode_s_reg_from_N_Vn(unsigned32 instr)
{
    unsigned N  = (instr >> 7) & 1u;
    unsigned Vn = (instr >> 16) & 0xFu;
    return (Vn << 1) | N;
}

static unsigned vfp_decode_s_reg_from_M_Vm(unsigned32 instr)
{
    unsigned M  = (instr >> 5) & 1u;
    unsigned Vm = instr & 0xFu;
    return (Vm << 1) | M;
}

static char *append_dreg(char *p, unsigned d)
{
    return append_reg(p, d, RegType_VFP_D);
}

static char *append_sreg(char *p, unsigned s)
{
    return append_reg(p, s, RegType_VFP_S);
}

static char *append_fp_literal(char *p, double v)
{
    char buf[32];
    int n = sprintf(buf, "%.15g", v);

    /* Ensure there is at least one decimal point for finite, non-exponential values. */
    if (strchr(buf, '.') == NULL &&
        strchr(buf, 'e') == NULL &&
        strchr(buf, 'E') == NULL)
    {
        if (n < (int)sizeof(buf) - 2) {
            buf[n++] = '.';
            buf[n++] = '0';
            buf[n] = '\0';
        }
    }

    memcpy(p, buf, (size_t)n);
    return p + n;
}

static char *append_comment_padding(char *start, char *p)
{
    const int comment_col = 32;  /* where the '@' should roughly land */
    int col = (int)(p - start);

    if (col < comment_col) {
        int pad = comment_col - col;
        memset(p, ' ', (size_t)pad);
        p += pad;
    } else {
        *p++ = ' ';
    }

    return p;
}

static DblePun vfp_decode_imm_f64(uint32_t imm8)
{
    // Implements the reverse of vfp_encode_imm_f64()
    // hi: aBbbbbbb bbcdefgh 00000000 00000000. lo : 0
    DblePun d;
    uint32_t bits = 0;
    uint32_t a, b;

    a = ((imm8 >> 7) & 0x1);
    b = ((imm8 >> 6) & 0x1);
    b = b ? 0x3fc00000u : (1u << 30);

    bits |= (a << 31) | b | ((imm8 & 0x3fu) << 16);

    d.b.msd = bits;
    d.b.lsd = 0;

    return d;
}

static FloatBin vfp_decode_imm_f32(uint32_t imm8)
{
    // Implements the reverse of vfp_encode_imm_f32()
    // F32: abcd efgh = aBbbbbbc defgh000 00000000 00000000
    FloatBin f;
    uint32_t a, b;

    a = ((imm8 >> 7) & 0x1);
    b = ((imm8 >> 6) & 0x1);
    b = b ? 0x3e000000u : (1u << 30);

    f.val = (a << 31) | b | ((imm8 & 0x3eu) << 19);

    return f;
}

bool disass_vfp(unsigned32 instr,
                unsigned32 pc,
                void *cb_arg,
                dis_cb_fn cb,
                char *out);

/* VFP / simple SIMD decoder for the subset of instructions Norcroft emits.
   We use the opcode constants from vfpops.h and mask off condition and
   register fields.  Returns YES if an instruction was recognised. */
bool disass_vfp(unsigned32 instr,
                unsigned32 pc,
                void *cb_arg,
                dis_cb_fn cb,
                char *out)
{
    unsigned cond = BITS(instr, 31, 28);
    unsigned32 core = instr & ~(VFP_CONDMASK | VFP_REGMASK_DS);
    char *p = out;

    if (cond == 0xFu) {
        /* Advanced SIMD / NEON encodings use cond = 0xF and should not be
           treated as classic VFP coprocessor instructions.  For now we only
           recognise VEOR between D registers, but we do so generically so
           the D/N/M register numbers can vary. */
        unsigned32 veor_core = 0xF3088118u & ~(VFP_CONDMASK | VFP_REGMASK_DS);
        unsigned32 core_neon = instr        & ~(VFP_CONDMASK | VFP_REGMASK_DS);

        if (core_neon == veor_core) {
            /* VEOR between D registers: VEOR Dd, Dn, Dm */
            char *p = out;
            unsigned d = vfp_decode_d_reg_from_D_Vd(instr);
            unsigned n = vfp_decode_d_reg_from_N_Vn(instr);
            unsigned m = vfp_decode_d_reg_from_M_Vm(instr);

            /* Use AL so we don't print a condition suffix. NEON integer ops
               are always executed even though cond == 0xF in the encoding. */
            p = emit_mnemonic(p, "VEOR", 0xEu);
            p = append_dreg(p, d);
            p = append_str(p, ", ");
            p = append_dreg(p, n);
            p = append_str(p, ", ");
            p = append_dreg(p, m);
            return YES;
        }

        /* Any other NEON encodings are left as DCD for now. */
        return NO;
    }

    /* Double-precision arithmetic: VADD.F64 / VSUB.F64 / VMUL.F64 / VDIV.F64 */
    {
        unsigned32 add_core = VFP_VADD_D & ~(VFP_CONDMASK | VFP_REGMASK_DS);
        unsigned32 sub_core = VFP_VSUB_D & ~(VFP_CONDMASK | VFP_REGMASK_DS);
        unsigned32 mul_core = VFP_VMUL_D & ~(VFP_CONDMASK | VFP_REGMASK_DS);
        unsigned32 div_core = VFP_VDIV_D & ~(VFP_CONDMASK | VFP_REGMASK_DS);
        const char *base = NULL;

        if (core == add_core) base = "VADD";
        else if (core == sub_core) base = "VSUB";
        else if (core == mul_core) base = "VMUL";
        else if (core == div_core) base = "VDIV";

        if (base != NULL) {
            unsigned d  = vfp_decode_d_reg_from_D_Vd(instr);
            unsigned n  = vfp_decode_d_reg_from_N_Vn(instr);
            unsigned m2 = vfp_decode_d_reg_from_M_Vm(instr);

            p = emit_mnemonic_with_suffix(p, base, ".F64", cond);
            p = append_dreg(p, d);
            p = append_str(p, ", ");
            p = append_dreg(p, n);
            p = append_str(p, ", ");
            p = append_dreg(p, m2);
            return YES;
        }
    }

    /* Single-precision arithmetic: VADD.F32 / VSUB.F32 / VMUL.F32 / VDIV.F32 */
    {
        unsigned32 add_core_s = VFP_VADD_S & ~(VFP_CONDMASK | VFP_REGMASK_DS);
        unsigned32 sub_core_s = VFP_VSUB_S & ~(VFP_CONDMASK | VFP_REGMASK_DS);
        unsigned32 mul_core_s = VFP_VMUL_S & ~(VFP_CONDMASK | VFP_REGMASK_DS);
        unsigned32 div_core_s = VFP_VDIV_S & ~(VFP_CONDMASK | VFP_REGMASK_DS);
        const char *base = NULL;
        if (core == add_core_s) base = "VADD";
        else if (core == sub_core_s) base = "VSUB";
        else if (core == mul_core_s) base = "VMUL";
        else if (core == div_core_s) base = "VDIV";

        if (base != NULL) {
            unsigned sd = vfp_decode_s_reg_from_D_Vd(instr);
            unsigned sn = vfp_decode_s_reg_from_N_Vn(instr);
            unsigned sm = vfp_decode_s_reg_from_M_Vm(instr);
            p = emit_mnemonic_with_suffix(p, base, ".F32", cond);
            p = append_sreg(p, sd);
            p = append_str(p, ", ");
            p = append_sreg(p, sn);
            p = append_str(p, ", ");
            p = append_sreg(p, sm);
            return YES;
        }
    }

    /* Double-precision compare: VCMP.F64 (including compare-with-zero form).
       Use a narrower mask than VFP_REGMASK_DS so that instructions like
       VCVT.F64.S32 do not alias to VCMPZ. */
    {
        unsigned32 vcmp_core  = VFP_VCMP_D  & ~(VFP_CONDMASK | VFP_VCMP_REGMASK);
        unsigned32 vcmpz_core = VFP_VCMPZ_D & ~(VFP_CONDMASK | VFP_VCMP_REGMASK);
        unsigned32 core_cmp   = instr & ~(VFP_CONDMASK | VFP_VCMP_REGMASK);

        if (core_cmp == vcmp_core || core_cmp == vcmpz_core) {
            bool is_zero = (core_cmp == vcmpz_core);
            const char *base = "VCMP";
            unsigned d  = vfp_decode_d_reg_from_D_Vd(instr);

            p = emit_mnemonic_with_suffix(p, base, ".F64", cond);
            p = append_dreg(p, d);

            if (!is_zero) {
                unsigned m2 = vfp_decode_d_reg_from_M_Vm(instr);
                p = append_str(p, ", ");
                p = append_dreg(p, m2);
            } else {
                p = append_str(p, ", ");
                p = append_str(p, "#0.0");
            }
            return YES;
        }
    }

    /* Single-precision compare: VCMP.F32 (including compare-with-zero form) */
    {
        unsigned32 vcmp_s_core  = VFP_VCMP_S  & ~(VFP_CONDMASK | VFP_VCMP_REGMASK);
        unsigned32 vcmpz_s_core = VFP_VCMPZ_S & ~(VFP_CONDMASK | VFP_VCMP_REGMASK);
        unsigned32 core_cmp = instr & ~(VFP_CONDMASK | VFP_VCMP_REGMASK);
        if (core_cmp == vcmp_s_core || core_cmp == vcmpz_s_core) {
            bool is_zero = (core_cmp == vcmpz_s_core);
            const char *base = "VCMP";
            unsigned sd = vfp_decode_s_reg_from_D_Vd(instr);
            p = emit_mnemonic_with_suffix(p, base, ".F32", cond);
            p = append_sreg(p, sd);
            if (!is_zero) {
                unsigned sm = vfp_decode_s_reg_from_M_Vm(instr);
                p = append_str(p, ", ");
                p = append_sreg(p, sm);
            } else {
                p = append_str(p, ", ");
                p = append_str(p, "#0.0");
            }
            return YES;
        }
    }

    /* Single- and double-precision unary: VNEG/VABS */
    {
        unsigned32 vneg_s_core = VFP_VNEG_S & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        unsigned32 vneg_d_core = VFP_VNEG_D & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        unsigned32 vabs_s_core = VFP_VABS_S & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        unsigned32 vabs_d_core = VFP_VABS_D & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        unsigned32 core_unary  = instr      & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        const char *base = NULL;
        bool single = false;

        if (core_unary == vneg_s_core) { base = "VNEG"; single = true; }
        else if (core_unary == vneg_d_core) { base = "VNEG"; single = false; }
        else if (core_unary == vabs_s_core) { base = "VABS"; single = true; }
        else if (core_unary == vabs_d_core) { base = "VABS"; single = false; }

        if (base != NULL) {
            if (single) {
                unsigned sd = vfp_decode_s_reg_from_D_Vd(instr);
                unsigned sm = vfp_decode_s_reg_from_M_Vm(instr);
                p = emit_mnemonic_with_suffix(p, base, ".F32", cond);
                p = append_sreg(p, sd);
                p = append_str(p, ", ");
                p = append_sreg(p, sm);
            } else {
                unsigned dd = vfp_decode_d_reg_from_D_Vd(instr);
                unsigned dm = vfp_decode_d_reg_from_M_Vm(instr);
                p = emit_mnemonic_with_suffix(p, base, ".F64", cond);
                p = append_dreg(p, dd);
                p = append_str(p, ", ");
                p = append_dreg(p, dm);
            }
            return YES;
        }
    }

    /* VMRS APSR_nzcv, FPSCR */
    {
        unsigned32 vmrs_core = VFP_VMRS_APSR & ~VFP_CONDMASK;
        if ((instr & ~VFP_CONDMASK) == vmrs_core) {
            p = emit_mnemonic(p, "VMRS", cond);
            p = append_str(p, "APSR_nzcv, fpscr");
            return YES;
        }
    }

    /* VCVT.S32.F64 (sD, dM) */
    {
        unsigned32 vcvt_s32_f64_core = VFP_VCVT_S32_F64 & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        unsigned32 core_vcvt         = instr            & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        if (core_vcvt == vcvt_s32_f64_core) {
            unsigned sd = vfp_decode_s_reg_from_D_Vd(instr);
            unsigned dm = vfp_decode_d_reg_from_M_Vm(instr);

            p = emit_mnemonic_with_suffix(p, "VCVT", ".S32.F64", cond);
            p = append_sreg(p, sd);
            p = append_str(p, ", ");
            p = append_dreg(p, dm);
            return YES;
        }
    }

    /* VCVT.F64.S32  (dD, sM) */
    {
        unsigned32 vcvt64_core = VFP_VCVT_F64_S32 & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        unsigned32 core_vcvt   = instr            & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        if (core_vcvt == vcvt64_core) {
            unsigned d  = vfp_decode_d_reg_from_D_Vd(instr);
            unsigned s  = vfp_decode_s_reg_from_M_Vm(instr);

            p = emit_mnemonic_with_suffix(p, "VCVT", ".F64.S32", cond);
            p = append_dreg(p, d);
            p = append_str(p, ", ");
            p = append_sreg(p, s);
            return YES;
        }
    }

    /* VCVT.F64.F32  (dD, sM) */
    {
        unsigned32 vcvt64f32_core = VFP_VCVT_F64_F32 & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        unsigned32 core_vcvt      = instr            & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        if (core_vcvt == vcvt64f32_core) {
            unsigned dd = vfp_decode_d_reg_from_D_Vd(instr);
            unsigned sm = vfp_decode_s_reg_from_M_Vm(instr);
            p = emit_mnemonic_with_suffix(p, "VCVT", ".F64.F32", cond);
            p = append_dreg(p, dd);
            p = append_str(p, ", ");
            p = append_sreg(p, sm);
            return YES;
        }
    }

    /* VCVT.F32.F64  (sD, dM) */
    {
        unsigned32 vcvt32f64_core = VFP_VCVT_F32_F64 & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        unsigned32 core_vcvt      = instr            & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        if (core_vcvt == vcvt32f64_core) {
            unsigned sd = vfp_decode_s_reg_from_D_Vd(instr);
            unsigned dm = vfp_decode_d_reg_from_M_Vm(instr);
            p = emit_mnemonic_with_suffix(p, "VCVT", ".F32.F64", cond);
            p = append_sreg(p, sd);
            p = append_str(p, ", ");
            p = append_dreg(p, dm);
            return YES;
        }
    }

    /* VCVT.S32.F32 (sD, sM) */
    {
        unsigned32 vcvt_s32_f32_core = VFP_VCVT_S32_F32 & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        unsigned32 core_vcvt         = instr            & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        if (core_vcvt == vcvt_s32_f32_core) {
            unsigned sd = vfp_decode_s_reg_from_D_Vd(instr);
            unsigned sm = vfp_decode_s_reg_from_M_Vm(instr);
            p = emit_mnemonic_with_suffix(p, "VCVT", ".S32.F32", cond);
            p = append_sreg(p, sd);
            p = append_str(p, ", ");
            p = append_sreg(p, sm);
            return YES;
        }
    }

    /* VCVT.F32.S32 (sD, sM) */
    {
        unsigned32 vcvt_f32_s32_core = VFP_VCVT_F32_S32 & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        unsigned32 core_vcvt         = instr            & ~(VFP_CONDMASK | VFP_SCALAR_REGMASK_DS);
        if (core_vcvt == vcvt_f32_s32_core) {
            unsigned sd = vfp_decode_s_reg_from_D_Vd(instr);
            unsigned sm = vfp_decode_s_reg_from_M_Vm(instr);
            p = emit_mnemonic_with_suffix(p, "VCVT", ".F32.S32", cond);
            p = append_sreg(p, sd);
            p = append_str(p, ", ");
            p = append_sreg(p, sm);
            return YES;
        }
    }

    /* VMOV between core and VFP registers.  We only handle the forms that
       Norcroft currently emits. */

    /* VMOV sN, Rt  (core -> scalar single) */
    {
        unsigned32 vmov_s_r_core = VFP_VMOV_S_R & ~(VFP_CONDMASK | VFP_REGMASK_DS);
        if (core == vmov_s_r_core) {
            const char *m = "VMOV";
            unsigned s = vfp_decode_s_reg_from_N_Vn(instr);
            unsigned rt = (instr >> 12) & 0xFu;   /* Rt in bits[15:12] */

            p = emit_mnemonic(p, m, cond);
            p = append_sreg(p, s);
            p = append_str(p, ", ");
            p = append_core_reg(p, rt);
            return YES;
        }
    }

    /* VMOV Rt, sN  (scalar single -> core) */
    {
        unsigned32 vmov_r_s_core = VFP_VMOV_R_S & ~(VFP_CONDMASK | VFP_REGMASK_DS);
        if (core == vmov_r_s_core) {
            const char *m = "VMOV";
            unsigned s  = vfp_decode_s_reg_from_N_Vn(instr);
            unsigned rt = (instr >> 12) & 0xFu;   /* Rt in bits[15:12] */

            p = emit_mnemonic(p, m, cond);
            p = append_core_reg(p, rt);
            p = append_str(p, ", ");
            p = append_sreg(p, s);
            return YES;
        }
    }

    /* VMOV Rt, Rt2, dM  (double -> two core registers) */
    {
        unsigned32 vmov_r_r_d_core = VFP_VMOV_R_R_D & ~(VFP_CONDMASK | VFP_REGMASK_DS);
        if (core == vmov_r_r_d_core) {
            const char *m = "VMOV";
            unsigned rt  = (instr >> 12) & 0xFu;
            unsigned rt2 = (instr >> 16) & 0xFu;
            unsigned d   = vfp_decode_d_reg_from_M_Vm(instr);

            p = emit_mnemonic(p, m, cond);
            p = append_core_reg(p, rt);
            p = append_str(p, ", ");
            p = append_core_reg(p, rt2);
            p = append_str(p, ", ");
            p = append_dreg(p, d);
            return YES;
        }
    }

    /* VMOV.F64 dD, Rt, Rt2  (two core registers -> double) */
    {
        unsigned32 vmov_d_r_r_core = VFP_VMOV_D_R_R & ~(VFP_CONDMASK | VFP_REGMASK_DS);
        if (core == vmov_d_r_r_core) {
            const char *base = "VMOV";
            unsigned d   = vfp_decode_d_reg_from_M_Vm(instr);
            unsigned rt  = (instr >> 12) & 0xFu;
            unsigned rt2 = (instr >> 16) & 0xFu;

            p = emit_mnemonic_with_suffix(p, base, ".F64", cond);
            p = append_dreg(p, d);
            p = append_str(p, ", ");
            p = append_core_reg(p, rt);
            p = append_str(p, ", ");
            p = append_core_reg(p, rt2);
            return YES;
        }
    }

    /* VMOV.S32 dS, #imm8  (immediate constant) */
    /* VMOV.F64 dD, #imm8  (immediate constant) */
    {
        unsigned32 vmov_s_imm_core = VFP_VMOV_S_IMM & ~(VFP_CONDMASK | VFP_REGMASK_DS);
        unsigned32 vmov_d_imm_core = VFP_VMOV_D_IMM & ~(VFP_CONDMASK | VFP_REGMASK_DS);

        if (core == vmov_s_imm_core || core == vmov_d_imm_core) {
            const bool single = core == vmov_s_imm_core;
            const char *base = "VMOV";
            unsigned dst;
            unsigned imm4H = (instr >> 16) & 0xFu;   /* bits[19:16] */
            unsigned imm4L = instr & 0xFu;           /* bits[3:0]   */
            unsigned imm8  = (imm4H << 4) | imm4L;
            double val;
            unsigned bits;

            if (single) {
                FloatBin f = vfp_decode_imm_f32(imm8);
                val = f.f; // printf will extend this anyway.
                bits = f.val;
                dst = vfp_decode_s_reg_from_D_Vd(instr);
                p = emit_mnemonic_with_suffix(p, base, ".F32", cond);
                p = append_sreg(p, dst);
            } else {
                DblePun d = vfp_decode_imm_f64(imm8);
                val = d.d;
                bits = d.b.msd;
                dst = vfp_decode_d_reg_from_D_Vd(instr);
                p = emit_mnemonic_with_suffix(p, base, ".F64", cond);
                p = append_dreg(p, dst);
            }

            p = append_str(p, ", #");
            p += sprintf(p, "%u", imm8);

            p = append_comment_padding(out, p);

            // Curiously, objdump dumps the hex of the type as a float, even,
            // for a VMOV.F64, which doesn't seem very useful.
            p += sprintf(p, "@ =");
            p = append_fp_literal(p, val);
            p += sprintf(p, " (0x%08x%s)", bits, single ? "" : "...0");

            return YES;
        }
    }

    /* VMOV.F64 dD, dM */
    {
        unsigned32 vmov_d_d_core = VFP_VMOV_D_D & ~(VFP_CONDMASK | VFP_REGMASK_DS);
        if (core == vmov_d_d_core) {
            const char *base = "VMOV";
            unsigned d  = vfp_decode_d_reg_from_D_Vd(instr);
            unsigned m2 = vfp_decode_d_reg_from_M_Vm(instr);

            p = emit_mnemonic_with_suffix(p, base, ".F64", cond);
            p = append_dreg(p, d);
            p = append_str(p, ", ");
            p = append_dreg(p, m2);
            return YES;
        }
    }

    /* VFP load/store (VLDR/VPUSH/VPOP) with double registers. */

    /* VLDR.F32 sD, [Rn, #imm] */
    {
        unsigned32 vldr_s_core = VFP_VLDR_S_IMM & ~(VFP_CONDMASK | VFP_LDST_REGMASK);
        unsigned32 core_ld = instr & ~(VFP_CONDMASK | VFP_LDST_REGMASK);
        if (core_ld == vldr_s_core) {
            const char *base = "VLDR";
            unsigned s   = vfp_decode_s_reg_from_D_Vd(instr);
            unsigned rn  = (instr >> 16) & 0xFu;
            unsigned ubit = (instr >> 23) & 1u;
            unsigned32 imm8 = instr & 0xFFu;
            int32 offset = (int32)(imm8 * 4u);
            if (!ubit) offset = -offset;

            p = emit_mnemonic(p, base, cond);
            p = append_sreg(p, s);
            p = append_str(p, ", ");

            if (rn == 15 && cb != NULL) {
                /* PC-relative literal load. */
                int32 target = (int32)pc + 8 + offset;
                p = cb(D_LOADPCREL,
                       offset,
                       (unsigned32)target,
                       (int)instr,
                       cb_arg,
                       p);
            } else if (cb != NULL) {
                /* Non-PC base with callback – mirror integer LDR behaviour. */
                p = append_str(p, "[");
                p = append_core_reg(p, rn);
                if (offset != 0) {
                    p = append_str(p, ", #");
                    p = cb(D_LOAD, offset, 0, (int)instr, cb_arg, p);
                }
                p = append_str(p, "]");
            } else {
                /* Plain numeric offset. */
                p = append_str(p, "[");
                p = append_core_reg(p, rn);
                if (offset != 0) {
                    p = append_str(p, ", ");
                    if (offset < 0) {
                        p = append_str(p, "-");
                        p = append_immediate(p, (unsigned32)(-offset));
                    } else {
                        p = append_immediate(p, (unsigned32)offset);
                    }
                }
                p = append_str(p, "]");
            }
            return YES;
        }
    }

    /* VLDR.F64 dD, [Rn, #imm] */
    {
        unsigned32 vldr_d_core = VFP_VLDR_D_IMM & ~(VFP_CONDMASK | VFP_LDST_REGMASK);
        unsigned32 core_ld = instr & ~(VFP_CONDMASK | VFP_LDST_REGMASK);
        if (core_ld == vldr_d_core) {
            const char *base = "VLDR";
            unsigned d   = vfp_decode_d_reg_from_D_Vd(instr);
            unsigned rn  = (instr >> 16) & 0xFu;
            unsigned ubit = (instr >> 23) & 1u;
            unsigned32 imm8 = instr & 0xFFu;
            int32 offset = (int32)(imm8 * 4u);
            if (!ubit) offset = -offset;

            p = emit_mnemonic(p, base, cond);
            p = append_dreg(p, d);
            p = append_str(p, ", ");

            if (rn == 15 && cb != NULL) {
                /* PC-relative literal load. */
                int32 target = (int32)pc + 8 + offset;
                p = cb(D_LOADPCREL,
                       offset,
                       (unsigned32)target,
                       (int)instr,
                       cb_arg,
                       p);
            } else if (cb != NULL) {
                /* Non-PC base with callback – mirror integer LDR behaviour. */
                p = append_str(p, "[");
                p = append_core_reg(p, rn);
                if (offset != 0) {
                    p = append_str(p, ", #");
                    p = cb(D_LOAD, offset, 0, (int)instr, cb_arg, p);
                }
                p = append_str(p, "]");
            } else {
                /* Plain numeric offset. */
                p = append_str(p, "[");
                p = append_core_reg(p, rn);
                if (offset != 0) {
                    p = append_str(p, ", ");
                    if (offset < 0) {
                        p = append_str(p, "-");
                        p = append_immediate(p, (unsigned32)(-offset));
                    } else {
                        p = append_immediate(p, (unsigned32)offset);
                    }
                }
                p = append_str(p, "]");
            }
            return YES;
        }
    }

    /* VSTR.F32 sD, [Rn, #imm] */
    {
        unsigned32 vstr_s_core = VFP_VSTR_S_IMM & ~(VFP_CONDMASK | VFP_LDST_REGMASK);
        unsigned32 core_st     = instr          & ~(VFP_CONDMASK | VFP_LDST_REGMASK);
        if (core_st == vstr_s_core) {
            const char *base = "VSTR";
            unsigned s   = vfp_decode_s_reg_from_D_Vd(instr);
            unsigned rn  = (instr >> 16) & 0xFu;
            unsigned ubit = (instr >> 23) & 1u;
            unsigned32 imm8 = instr & 0xFFu;
            int32 offset = (int32)(imm8 * 4u);
            if (!ubit) offset = -offset;

            p = emit_mnemonic(p, base, cond);
            p = append_sreg(p, s);
            p = append_str(p, ", ");

            if (rn == 15 && cb != NULL) {
                /* PC-relative literal store – unlikely in practice but keep
                   symmetry with the integer disassembler. */
                int32 target = (int32)pc + 8 + offset;
                p = cb(D_STOREPCREL,
                       offset,
                       (unsigned32)target,
                       (int)instr,
                       cb_arg,
                       p);
            } else if (cb != NULL) {
                /* Non-PC base with callback – mirror integer STR behaviour. */
                p = append_str(p, "[");
                p = append_core_reg(p, rn);
                if (offset != 0) {
                    p = append_str(p, ", #");
                    p = cb(D_STORE, offset, 0, (int)instr, cb_arg, p);
                }
                p = append_str(p, "]");
            } else {
                /* Plain numeric offset. */
                p = append_str(p, "[");
                p = append_core_reg(p, rn);
                if (offset != 0) {
                    p = append_str(p, ", ");
                    if (offset < 0) {
                        p = append_str(p, "-");
                        p = append_immediate(p, (unsigned32)(-offset));
                    } else {
                        p = append_immediate(p, (unsigned32)offset);
                    }
                }
                p = append_str(p, "]");
            }
            return YES;
        }
    }

    /* VSTR.F64 dD, [Rn, #imm] */
    {
        unsigned32 vstr_d_core = VFP_VSTR_D_IMM & ~(VFP_CONDMASK | VFP_LDST_REGMASK);
        unsigned32 core_st = instr & ~(VFP_CONDMASK | VFP_LDST_REGMASK);
        if (core_st == vstr_d_core) {
            const char *base = "VSTR";
            unsigned d   = vfp_decode_d_reg_from_D_Vd(instr);
            unsigned rn  = (instr >> 16) & 0xFu;
            unsigned ubit = (instr >> 23) & 1u;
            unsigned32 imm8 = instr & 0xFFu;
            int32 offset = (int32)(imm8 * 4u);
            if (!ubit) offset = -offset;

            p = emit_mnemonic(p, base, cond);
            p = append_dreg(p, d);
            p = append_str(p, ", ");

            if (rn == 15 && cb != NULL) {
                /* PC-relative literal store – unlikely in practice but keep
                   symmetry with the integer disassembler. */
                int32 target = (int32)pc + 8 + offset;
                p = cb(D_STOREPCREL,
                       offset,
                       (unsigned32)target,
                       (int)instr,
                       cb_arg,
                       p);
            } else if (cb != NULL) {
                /* Non-PC base with callback – mirror integer STR behaviour. */
                p = append_str(p, "[");
                p = append_core_reg(p, rn);
                if (offset != 0) {
                    p = append_str(p, ", #");
                    p = cb(D_STORE, offset, 0, (int)instr, cb_arg, p);
                }
                p = append_str(p, "]");
            } else {
                /* Plain numeric offset. */
                p = append_str(p, "[");
                p = append_core_reg(p, rn);
                if (offset != 0) {
                    p = append_str(p, ", ");
                    if (offset < 0) {
                        p = append_str(p, "-");
                        p = append_immediate(p, (unsigned32)(-offset));
                    } else {
                        p = append_immediate(p, (unsigned32)offset);
                    }
                }
                p = append_str(p, "]");
            }
            return YES;
        }
    }

    /* VPUSH {dD ...} */
    {
        unsigned32 vpush_d_core = VFP_VPUSH_D & ~(VFP_CONDMASK | VFP_LDST_REGMASK);
        unsigned32 core_ld = instr & ~(VFP_CONDMASK | VFP_LDST_REGMASK);
        if (core_ld == vpush_d_core) {
            const char *m = "VPUSH";
            unsigned d   = vfp_decode_d_reg_from_D_Vd(instr);
            unsigned32 imm8 = instr & 0xFFu;
            unsigned count = imm8 / 2u;    /* each D is 8 bytes => imm = 2 * count */
            if (count == 0) count = 1;

            p = emit_mnemonic(p, m, cond);
            *p++ = '{';
            p = append_dreg(p, d);
            if (count > 1) {
                *p++ = '-';
                p = append_dreg(p, d + count - 1);
            }
            *p++ = '}';
            *p = '\0';
            return YES;
        }
    }

    /* VPOP {dD ...} */
    {
        unsigned32 vpop_d_core = VFP_VPOP_D & ~(VFP_CONDMASK | VFP_LDST_REGMASK);
        unsigned32 core_ld = instr & ~(VFP_CONDMASK | VFP_LDST_REGMASK);
        if (core_ld == vpop_d_core) {
            const char *m = "VPOP";
            unsigned d   = vfp_decode_d_reg_from_D_Vd(instr);
            unsigned32 imm8 = instr & 0xFFu;
            unsigned count = imm8 / 2u;
            if (count == 0) count = 1;

            p = emit_mnemonic(p, m, cond);
            *p++ = '{';
            p = append_dreg(p, d);
            if (count > 1) {
                *p++ = '-';
                p = append_dreg(p, d + count - 1);
            }
            *p++ = '}';
            *p = '\0';
            return YES;
        }
    }

    /* Nothing recognised. */
    return NO;
}
