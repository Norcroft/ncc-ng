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
#include "armops.h"
#include "disass-fpa.h"
#include "disass-arm.h"
#include "ncc-types.h"

#include <stdarg.h>
#include <stdio.h>
#include <string.h>

#define FPA_CP_IS_VALID(cp) ((cp) == 1 || (cp) == 2)
#define BITS(v,hi,lo) (((v) >> (lo)) & ((1u << ((hi)-(lo)+1)) - 1u))

static char *append_freg(char *p, unsigned f)
{
    return append_reg(p, f, RegType_FPA);
}

// FPA has a small fixed table possible immediate constants.
static float fpa_literal_value(unsigned idx)
{
    switch (idx & 7u) {
        case 0: return 0.0f;
        case 1: return 1.0f;
        case 2: return 2.0f;
        case 3: return 3.0f;
        case 4: return 4.0f;
        case 5: return 5.0f;
        case 6: return 0.5f;
        default: return 10.0f;
    }
}

static char *append_fp_literal(char *p, float v)
{
    p += sprintf(p, "%.1f", v);
    return p;
}

/* Pad out to a comment column before writing an inline comment. */
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

/* Decode FPA CPDT (load/store) instructions. */
static bool fpa_decode_cpdt_single(unsigned32 instr,
                                   unsigned32 pc,
                                   void *cb_arg,
                                   dis_cb_fn cb,
                                   char *out)
{
    int cpnum = (instr >> 8) & 0x0f;

    const bool load      = (instr & F_LDR) != 0;
    const bool writeback = (instr & F_WRITEBACK) != 0;
    const bool pre       = (instr & F_PRE) != 0;
    const bool up        = (instr & F_UP) != 0;
    const char* prec;

    const unsigned cond = BITS(instr, 31, 28);
    const int rn  = (instr >> 16) & 0x0f;      /* base integer register */
    const int fd  = (instr >> 12) & 0x07;      /* FPA register number (0–7) */
    const unsigned offset_words = instr & 0xff;
    int offset_bytes = (int)offset_words * 4;
    int32 soff = up ? (int32)offset_bytes : -(int32)offset_bytes;
    const char *mnem = load ? "LDF" : "STF";

    if (!FPA_CP_IS_VALID(cpnum))
        return NO;

    /* Top-nibble class must be CPDT pre/post (OP_CPPRE/OP_CPPOST). */
    {
        unsigned32 top = instr & 0x0f000000u;
        if (top != (OP_CPPRE  & 0x0f000000u) &&
            top != (OP_CPPOST & 0x0f000000u))
            return NO;
    }

    switch (instr & F_PACKED) {
        case F_SINGLE:      prec = "S"; break;
        case F_DOUBLE:      prec = "D"; break;
        case F_EXTENDED:    prec = "E"; break;
        case F_PACKED:      prec = "P"; break;
    }

    out = emit_mnemonic_with_suffix(out, mnem, prec, cond);
    out = append_freg(out, fd);

    out = append_str(out, ", ");

    /* PC-relative literal load/store – let the callback resolve to a label. */
    if (rn == 15 && cb != NULL) {
        unsigned32 base = pc + 8u;
        unsigned32 addr = pre ? (unsigned32)((int32)base + soff) : base;
        dis_cb_type type = load ? D_LOADPCREL : D_STOREPCREL;
        cb(type, soff, addr, (int)instr, cb_arg, out);
        return true;
    }

    if (pre) {
        if (offset_bytes == 0 && !writeback) {
            /* Simple [Rn] */
            out = append_str(out, "[");
            out = append_core_reg(out, rn);
            out = append_str(out, "]");
            return true;
        }

        /* PC-relative literal load/store – let the callback resolve to a label. */
        if (rn == 15 && cb != NULL) {
            unsigned32 addr = (int32)pc + 8 + soff;

            dis_cb_type type = load ? D_LOADPCREL : D_STOREPCREL;
            cb(type, soff, 0, (int)instr, cb_arg, out);

            return true;
        }

        /* Pre-indexed with optional writeback. */
        out = append_str(out, "[");
        out = append_core_reg(out, rn);
        out = append_str(out, ", ");
        out = append_immediate_s(out, offset_bytes, up);

        out = append_str(out, writeback ? "]!" : "]");
        return true;
    } else {
        /* Post-indexed: [Rn], #imm */
        out = append_str(out, "[");
        out = append_core_reg(out, rn);
        out = append_str(out, "], ");

        if (cb != NULL) {
            dis_cb_type type = load ? D_LOAD : D_STORE;

            char *cb_start = out;
            out = cb(type, soff, 0, (int)instr, cb_arg, out);

            if (out != cb_start)
                return true;
        }

        // No cb function, or it refused to decorate.
        out = append_immediate_s(out, offset_bytes, up);

        return true;
    }
}

static char* append_fm(bool constop, unsigned fm, char* linestart, char* p)
{
    if (!constop) {
        /* Register form, eg. SQRD fd, fm */
        p = append_freg(p, (unsigned)fm);
    } else {
        /* Constant form, eg. SQRD fd, #imm_index [with value comment]. */
        unsigned idx = (unsigned)(fm & 7);
        float val = fpa_literal_value(idx);
        p = append_immediate(p, (unsigned32)idx);
        p = append_comment_padding(linestart, p);
        p = append_str(p, "@ =");
        p = append_fp_literal(p, val);
    }

    return p;
}

/* Decode FPA CPDT (load/store multiple) instructions. */
static bool fpa_decode_cpdt_multiple(unsigned32 instr,
                                     unsigned32 pc,
                                     void *cb_arg,
                                     dis_cb_fn cb,
                                     char *out)
{
    int cpnum = (instr >> 8) & 0x0f;

    const bool load      = (instr & F_LDR) != 0;
    const bool writeback = (instr & F_WRITEBACK) != 0;
    const bool pre       = (instr & F_PRE) != 0;
    const bool up        = (instr & F_UP) != 0;
    unsigned count;

    const unsigned cond = BITS(instr, 31, 28);
    const int rn  = (instr >> 16) & 0x0f;      /* base integer register */
    const int fd  = (instr >> 12) & 0x07;      /* base FPA register number (0–7) */
    const unsigned offset_words = instr & 0xff;
    int offset_bytes = (int)offset_words * 4;
    int32 soff = up ? (int32)offset_bytes : -(int32)offset_bytes;
    const char *mnem = load ? "LFM" : "SFM";

    if (!FPA_CP_IS_VALID(cpnum))
        return NO;

    /* Top-nibble class must be CPDT pre/post (OP_CPPRE/OP_CPPOST). */
    {
        unsigned32 top = instr & 0x0f000000u;
        if (top != (OP_CPPRE  & 0x0f000000u) &&
            top != (OP_CPPOST & 0x0f000000u))
            return NO;
    }

    /* Multiple transfer count is encoded by the F_FM_* selector bits. */
    switch (instr & (F_FM_1 | F_FM_2 | F_FM_3 | F_FM_4)) {
        case F_FM_1: count = 1; break;
        case F_FM_2: count = 2; break;
        case F_FM_3: count = 3; break;
        case F_FM_4: count = 4; break;
        default:
            return NO;
    }

    out = emit_mnemonic(out, mnem, cond);
    out = append_freg(out, (unsigned)fd);
    out = append_str(out, ", ");
    out += sprintf(out, "%u", count);
    out = append_str(out, ", ");

    /* PC-relative literal load/store – let the callback resolve to a label. */
    if (rn == 15 && cb != NULL) {
        unsigned32 base = pc + 8u;
        unsigned32 addr = pre ? (unsigned32)((int32)base + soff) : base;
        dis_cb_type type = load ? D_LOADPCREL : D_STOREPCREL;
        cb(type, soff, addr, (int)instr, cb_arg, out);
        return true;
    }

    if (pre) {
        if (offset_bytes == 0 && !writeback) {
            /* Simple [Rn] */
            out = append_str(out, "[");
            out = append_core_reg(out, rn);
            out = append_str(out, "]");
            return true;
        }

        /* Pre-indexed with optional writeback. */
        out = append_str(out, "[");
        out = append_core_reg(out, rn);
        out = append_str(out, ", ");
        out = append_immediate_s(out, offset_bytes, up);

        out = append_str(out, writeback ? "]!" : "]");
        return true;
    }

    /* Post-indexed: [Rn], #imm */
    out = append_str(out, "[");
    out = append_core_reg(out, rn);
    out = append_str(out, "], ");

    if (cb != NULL) {
        dis_cb_type type = load ? D_LOAD : D_STORE;

        char *cb_start = out;
        out = cb(type, soff, 0, (int)instr, cb_arg, out);

        if (out != cb_start)
            return true;
    }

    /* No cb function, or it refused to decorate. */
    out = append_immediate_s(out, offset_bytes, up);
    return true;
}

/* Decode FPA CDP (OP_CPOP) arithmetic and move instructions. */
static bool fpa_decode_cdp(unsigned32 instr,
                           unsigned32 pc,
                           void *cb_arg,
                           dis_cb_fn cb,
                           char *out)
{
    int cpnum = (instr >> 8) & 0x0f;
    const int fd = (instr >> 12) & 0x07;  /* destination F register or unused */
    const int fn = (instr >> 16) & 0x07;  /* first source F register */
    const int fm = instr & 0x07;          /* second source F register or imm index */
    const bool constop = (instr & F_CONSTOP) != 0;
    const char *prec = (instr & CPDO_DOUBLE) == CPDO_DOUBLE ? "D" : "S";
    const unsigned cond = (instr >> 28) & 0xFu;
    char *p;
    const char *mnem = NULL;
    const char *round = NULL; // round to nearest
    unsigned pat;

    if (!FPA_CP_IS_VALID(cpnum))
        return NO;

    /* Top-nibble class must be the CDP/CPOP group. */
    {
        unsigned32 top = instr & 0x0f000000u;
        if (top != (OP_CPOP & 0x0f000000u))
            return NO;
    }

    if ((instr & CPDO_RNDUP) == CPDO_RNDUP) round = "P";
    if ((instr & CPDO_RNDDN) == CPDO_RNDDN) round = "M";
    if ((instr & CPDO_RNDZ) == CPDO_RNDZ)   round = "Z";

    /* Compare family: CMF/CMFE/CNF/CNFE. */
    pat = instr & 0x00f0ff10u;
    switch (pat) {
        case F_CMF:  mnem = "CMF";  break;
        case F_CMFE: mnem = "CMFE"; break;
        case F_CNF:  mnem = "CNF";  break;
        case F_CNFE: mnem = "CNFE"; break;
        default:     break;
    }
    if (mnem != NULL) {
        p = out;
        p = emit_mnemonic(p, mnem, cond);
        p = append_freg(p, (unsigned)fn);
        p = append_str(p, ", ");
        p = append_fm(constop, fm, out, p);
        *p = '\0';
        return YES;
    }

    /* Conversions and FPSR/FPCR transfers: FLT/FIX/WFS/RFS/WFC/RFC.
     * These are encoded without the coprocessor number and rounding
     * mode bits in the armops.h macros, so we mask those out.
     */
    pat = instr & 0x00700110u;
    switch (pat) {
        case F_FIX: mnem = "FIX"; break;
        case F_FLT: mnem = "FLT"; break;
        case F_WFS: mnem = "WFS"; break;
        case F_RFS: mnem = "RFS"; break;
        case F_WFC: mnem = "WFC"; break;
        case F_RFC: mnem = "RFC"; break;
        default:    mnem = NULL;  break;
    }

    if (mnem != NULL) {
        int rd = (instr >> 12) & 0x0f;
        p = out;

        switch (pat) {
            case F_FIX:
                /* FIX Rd, Fn  ; integer dest in Rd, FP source in Fn */
                p = emit_mnemonic_with_suffix2(p, mnem, prec, round, cond);
                p = append_core_reg(p, rd);
                p = append_str(p, ", ");
                p = append_freg(p, (unsigned)fn);
                break;

            case F_FLT: {
                /* FLT Fn, Rd  ; FP dest in Fn, integer source in Rd */
                /* FLT Fn, #value form is not generated by Norcroft. */
                p = emit_mnemonic_with_suffix2(p, mnem, prec, round, cond);
                p = append_freg(p, (unsigned)fn);
                p = append_str(p, ", ");
                p = append_core_reg(p, rd);
                break;
            }

            case F_WFS:
            case F_RFS:
            case F_WFC:
            case F_RFC:
                /* Status/control register move: mnem Rd. */
                p = emit_mnemonic(p, mnem, cond);
                p = append_core_reg(p, rd);
                break;

            default:
                break;
        }

        *p = '\0';
        return YES;
    }

    /* Unary ops */
    switch (instr & 0x00f08000u) {
        case F_MVF: mnem = "MVF"; break;
        case F_MNF: mnem = "MNF"; break;
        case F_ABS: mnem = "ABS"; break;
        case F_RND: mnem = "RND"; break;
        case F_SQT: mnem = "SQT"; break;
        case F_LOG: mnem = "LOG"; break;
        case F_LGN: mnem = "LGN"; break;
        case F_EXP: mnem = "EXP"; break;
        case F_SIN: mnem = "SIN"; break;
        case F_COS: mnem = "COS"; break;
        case F_TAN: mnem = "TAN"; break;
        case F_ASN: mnem = "ASN"; break;
        case F_ACS: mnem = "ACS"; break;
        case F_ATN: mnem = "ATN"; break;
        default:
            break;
    }

    /* Shared path for simple unary register ops: mnem fd, fm. */
    if (mnem != NULL) {
        p = out;
        p = emit_mnemonic_with_suffix2(p, mnem, prec, round, cond);
        p = append_freg(p, (unsigned)fd);
        p = append_str(p, ", ");

        p = append_fm(constop, fm, out, p);
        *p = '\0';
        return YES;
    }

    /* Binary arithmetic family: ADF/SUF/RSF/MUF/DVF/RDF.
     * The operation is in bits 23:20 via F_ADF/F_SUF/... macros.
     */
    switch (instr & 0x00f00000u) {
        case F_ADF: mnem = "ADF"; break;
        case F_MUF: mnem = "MUF"; break;
        case F_SUF: mnem = "SUF"; break;
        case F_RSF: mnem = "RSF"; break;
        case F_DVF: mnem = "DVF"; break;
        case F_RDF: mnem = "RDF"; break;
        case F_POW: mnem = "POW"; break;
        case F_RPW: mnem = "RPW"; break;
        case F_RMF: mnem = "RMF"; break;
        case F_FML: mnem = "FML"; break;
        case F_FDV: mnem = "FDV"; break;
        case F_FRD: mnem = "FRD"; break;
        case F_POL: mnem = "POL"; break;
        default:    mnem = NULL;  break;
    }

    if (mnem != NULL) {
        if (!constop) {
            /* Register form: op fd, fn, fm */
            p = out;
            p = emit_mnemonic_with_suffix2(p, mnem, prec, round, cond);
            p = append_freg(p, (unsigned)fd);
            p = append_str(p, ", ");
            p = append_freg(p, (unsigned)fn);
            p = append_str(p, ", ");
            p = append_freg(p, (unsigned)fm);
            *p = '\0';
            return YES;
        } else {
            /* Literal form: op fd, fn, #imm_index with value comment. */
            unsigned idx = (unsigned)(fm & 7);
            double val = fpa_literal_value(idx);
            p = out;
            p = emit_mnemonic_with_suffix2(p, mnem, prec, round, cond);
            p = append_freg(p, (unsigned)fd);
            p = append_str(p, ", ");
            p = append_freg(p, (unsigned)fn);
            p = append_str(p, ", ");
            p = append_immediate(p, (unsigned32)idx);
            p = append_comment_padding(out, p);
            p = append_str(p, "@ =");
            p = append_fp_literal(p, val);
            *p = '\0';
            return YES;
        }
    }

    return NO;
}

bool disass_fpa(unsigned32 instr,
                unsigned32 pc,
                void *cb_arg,
                dis_cb_fn cb,
                char *out)
{
    /* Bits 27..25 must be 110 (CPDT) or 111 (CDP/MCR/MRC).
     *
     * Coprocessor 2 = load/store single, coprocessor 2 = load/store multiple.
     */
    switch ((instr >> 25) & 0x7u) {
        case 6: /* CPDT (LDC/STC / CPPRE/CPPOST) */
        {
            unsigned cp_field = (instr >> 8) & 0xf;
            if (cp_field == 1) {
                if (fpa_decode_cpdt_single(instr, pc, cb_arg, cb, out))
                    return YES;
            } else if (cp_field == 2) {
                if (fpa_decode_cpdt_multiple(instr, pc, cb_arg, cb, out))
                    return YES;
            }
        }
            break;
        case 7: /* CDP/MCR/MRC (CPOP) */
            if (fpa_decode_cdp(instr, pc, cb_arg, cb, out))
                return YES;
            break;
        default:
            break;
    }
    return NO;
}
