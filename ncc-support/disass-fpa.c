
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
static double fpa_literal_value(unsigned idx)
{
    switch (idx & 7u) {
        case 0: return 0.0;
        case 1: return 1.0;
        case 2: return 2.0;
        case 3: return 3.0;
        case 4: return 4.0;
        case 5: return 5.0;
        case 6: return 0.5;
        default: return 10.0;
    }
}

static char *append_fp_literal(char *p, double v)
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

/* Decode FPA CPDT (load/store) instructions generated via OP_CPPRE / OP_CPPOST. */
static bool fpa_decode_cpdt(unsigned32 instr,
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
    const bool is_double = (instr & F_DOUBLE) != 0;

    const unsigned cond = BITS(instr, 31, 28);
    const int rn  = (instr >> 16) & 0x0f;      /* base integer register */
    const int fd  = (instr >> 12) & 0x0f;      /* FPA register number (0–7) */
    const unsigned offset_words = instr & 0xff; /* FPE2 uses word offset */
    int offset_bytes = (int)offset_words * 4;
    const char *mnem;

    if (!FPA_CP_IS_VALID(cpnum))
        return NO;

    /* Top-nibble class must be CPDT pre/post (OP_CPPRE/OP_CPPOST). */
    {
        unsigned32 top = instr & 0x0f000000u;
        if (top != (OP_CPPRE  & 0x0f000000u) &&
            top != (OP_CPPOST & 0x0f000000u))
            return NO;
    }

    if (!up)
        offset_bytes = -offset_bytes;

    if (load)
        mnem = is_double ? "LDD" : "LDF";
    else
        mnem = is_double ? "STD" : "STF";

    out = emit_mnemonic(out, mnem, cond);
    out = append_freg(out, fd);

    if (pre) {
        if (offset_bytes == 0 && !writeback) {
            /* Simple [Rn] */
            out = append_str(out, ", [");
            out = append_core_reg(out, rn);
            out = append_str(out, "]");

            return true;
        } else {
            /* Pre-indexed with optional writeback. */
            out = append_str(out, ", [");
            out = append_core_reg(out, rn);
            out = append_str(out, ", ");
            out = append_immediate(out, offset_bytes);
            out = append_str(out, writeback ? "]!" : "]");

            return true;
        }
    } else {
        /* Post-indexed: [Rn], #imm */
        out = append_str(out, ", [");
        out = append_core_reg(out, rn);
        out = append_str(out, "], ");
        out = append_immediate(out, offset_bytes);

        return true;
    }
}

/* Decode FPA CDP (OP_CPOP) arithmetic and move instructions. */
static bool fpa_decode_cdp(unsigned32 instr,
                           unsigned32 pc,
                           void *cb_arg,
                           dis_cb_fn cb,
                           char *out)
{
    int cpnum = (instr >> 8) & 0x0f;
    const int fd = (instr >> 12) & 0x0f;  /* destination F register or unused */
    const int fn = (instr >> 16) & 0x0f;  /* first source F register */
    const int fm = instr & 0x0f;          /* second source F register or imm index */
    const bool constop = (instr & F_CONSTOP) != 0;
    const unsigned cond = (instr >> 28) & 0xFu;
    char *p;
    const char *mnem = NULL;

    if (!FPA_CP_IS_VALID(cpnum))
        return NO;

    /* Top-nibble class must be the CDP/CPOP group. */
    {
        unsigned32 top = instr & 0x0f000000u;
        if (top != (OP_CPOP & 0x0f000000u))
            return NO;
    }

    /* Unary move/negate family (MVF/MNF/ABS/RND).  These do not depend on
     * CPDO_SINGLE/CPDO_DOUBLE bits, so we can just match the opcode pattern.
     */
    switch (instr & 0x00f0f000u) {
        case F_MVF:
        case F_MNF: {
            const bool is_neg = (instr & 0x00f0f000u) == F_MNF;
            p = out;
            p = emit_mnemonic(p, is_neg ? "MNF" : "MVF", cond);
            p = append_freg(p, (unsigned)fd);
            p = append_str(p, ", ");
            if (!constop) {
                /* Register form: MVF/MNF fd, fm */
                p = append_freg(p, (unsigned)fm);
            } else {
                /* Literal form: MVF/MNF fd, #imm_index, with value comment. */
                unsigned idx = (unsigned)(fm & 7);
                double val = fpa_literal_value(idx);
                if (is_neg)
                    val = -val;
                p = append_immediate(p, (unsigned32)idx);
                p = append_comment_padding(out, p);
                p = append_str(p, "@ =");
                p = append_fp_literal(p, val);
            }
            *p = '\0';
            return YES;
        }

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

    /* Shared emission path for simple unary register ops: mnem fd, fm. */
    if (mnem != NULL) {
        p = out;
        p = emit_mnemonic(p, mnem, cond);
        p = append_freg(p, (unsigned)fd);
        p = append_str(p, ", ");
        p = append_freg(p, (unsigned)fm);
        *p = '\0';
        return YES;
    }

    /* First handle comparisons, conversions and FPSR/FPCR transfers, as these
     * share the same top opcode field as the arithmetic family but are
     * distinguished by additional low bits.
     */
    {
        unsigned pat;
        const char *mnem = NULL;

        /* Compare family: CMF/CMFE/CNF/CNFE.  These macros include the CP
         * number and all low bits, so we use a stricter mask.
         */
        pat = instr & 0x00f0fff0u;
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
            p = append_freg(p, (unsigned)fm);
            *p = '\0';
            return YES;
        }

        /* Conversions and FPSR/FPCR transfers: FLT/FIX/WFS/RFS/WFC/RFC.
         * These are encoded without the coprocessor number and rounding
         * mode bits in the armops.h macros, so we mask those out.
         */
        pat = instr & 0x00f00ff0u;
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
            p = emit_mnemonic(p, mnem, cond);

            switch (pat) {
            case F_FIX:
                /* FIX Rd, Fm  ; integer dest in Rd, FP source in Fm */
                p = append_core_reg(p, rd);
                p = append_str(p, ", ");
                p = append_freg(p, (unsigned)fm);
                break;

            case F_FLT: {
                /* FLT Fn, Rd  ; FP dest in Fn, integer source in Rd */
                int fn2 = (instr >> 16) & 0x0f;
                p = append_freg(p, (unsigned)fn2);
                p = append_str(p, ", ");
                p = append_core_reg(p, rd);
                break;
            }

            case F_WFS:
            case F_RFS:
            case F_WFC:
            case F_RFC:
                /* All the status/control register moves use a single
                 * core register operand: mnem Rd.
                 */
                p = append_core_reg(p, rd);
                break;

            default:
                break;
            }

            *p = '\0';
            return YES;
        }
    }

    /* Binary arithmetic family: ADF/SUF/RSF/MUF/DVF/RDF.
     * The operation is in bits 23:20 via F_ADF/F_SUF/... macros.
     * We do this after handling FLT/FIX so that conversion encodings
     * are not mis-decoded as ADF et al.
     */
    {
        const char *mnem = NULL;
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
                p = emit_mnemonic(p, mnem, cond);
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
                p = emit_mnemonic(p, mnem, cond);
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
    }

    return NO;
}

bool disass_fpa(unsigned32 instr,
                unsigned32 pc,
                void *cb_arg,
                dis_cb_fn cb,
                char *out)
{
    /* Fast reject on non-coprocessor opcodes.  Bits 27..25 must be 110
     * (CPDT) or 111 (CDP/MCR/MRC).
     */
    switch ((instr >> 25) & 0x7u) {
    case 6: /* CPDT (LDC/STC / CPPRE/CPPOST) */
        if (fpa_decode_cpdt(instr, pc, cb_arg, cb, out))
            return YES;
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
