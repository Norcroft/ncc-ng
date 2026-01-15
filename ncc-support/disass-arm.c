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

#include "ampdis.h"
#include "disass.h"
#include "disass-arm.h"
#include "disass-fpa.h"

#include <ctype.h>
#include <stdio.h>
#include <string.h>

static void disass_multiply(unsigned32 instr, char *out);
static void disass_long_multiply(unsigned32 instr, char *out);
static void disass_halfword_signed_transfer(unsigned32 instr, char *out);
static void disass_swp(unsigned32 instr, char *out);
static void disass_bx_blx_reg(unsigned32 instr, char *out);
static void disass_clz(unsigned32 instr, char *out);
static void disass_mrs(unsigned32 instr, char *out);
static void disass_msr(unsigned32 instr, char *out);

// This only covers classic ARM 32-bit instructions that Norcroft emits:
// data-processing, single data transfer, branches and SWI.

#define BITS(v,hi,lo) (((v) >> (lo)) & ((1u << ((hi)-(lo)+1)) - 1u))

static const char *const dp_opnames[16] = {
    "AND", "EOR", "SUB", "RSB",
    "ADD", "ADC", "SBC", "RSC",
    "TST", "TEQ", "CMP", "CMN",
    "ORR", "MOV", "BIC", "MVN"
};

/* Forward declaration for block data transfer helper. */
static char *append_core_reglist(char *p, unsigned list);

char *append_immediate(char *p, unsigned32 imm)
{
    return append_immediate_s(p, imm, true);
}

char *append_immediate_s(char *p, unsigned32 imm, bool sign)
{
    int n;

    /* Always print immediates in hex with the configured prefix. */
    if (sign)
        n = sprintf(p, "#%s%x", g_hexprefix, imm);
    else
        n = sprintf(p, "#-%s%x", g_hexprefix, imm);

    return p + n;
}

static char *append_offset_decimal_naked(char *p, int32 soff)
{
    unsigned abs = (soff < 0) ? (unsigned)(-soff) : (unsigned)soff;
    if (soff < 0) {
        int n = sprintf(p, "-%u", abs);
        p += n;
    } else {
        int n = sprintf(p, "%u", abs);
        p += n;
    }
    return p;
}

static char *append_hex_comment_for_offset(char *p, unsigned abs)
{
    int n;

    if (abs <= 9)
        return p;  /* No point showing hex for small values. */

    n = sprintf(p, "   @ %s%X", g_hexprefix, abs);
    return p + n;
}

static unsigned32 rotate_imm(unsigned32 imm8, unsigned rot)
{
    rot &= 31u;
    if (rot == 0) return imm8;
    return (imm8 >> rot) | (imm8 << (32u - rot));
}

static char *decode_shifted_reg(char *p, unsigned32 instr)
{
    unsigned rm = BITS(instr, 3, 0);
    unsigned shift_imm = BITS(instr, 11, 7);
    unsigned shift_type = BITS(instr, 6, 5);
    unsigned reg_shift = BITS(instr, 4, 4);

    p = append_core_reg(p, rm);

    if (reg_shift) {
        /* Rm, <shift> Rs form – keep simple for now. */
        unsigned rs = BITS(instr, 11, 8);
        const char *stype =
            (shift_type == 0) ? (disass_upper_mnemonics ? "LSL" : "lsl") :
            (shift_type == 1) ? (disass_upper_mnemonics ? "LSR" : "lsr") :
            (shift_type == 2) ? (disass_upper_mnemonics ? "ASR" : "asr") :
                                 (disass_upper_mnemonics ? "ROR" : "ror");
        p = append_str(p, ", ");
        p = append_str(p, stype);
        p = append_str(p, " ");
        p = append_core_reg(p, rs);
        return p;
    }

    if (shift_imm == 0) {
        /* LSL #0 is elided; ROR #0 is RRX; LSR/ASR #0 mean #32. */
        if (shift_type == 0) {
            return p; /* plain Rm */
        } else if (shift_type == 3) {
            p = append_str(p, disass_upper_mnemonics ? ", RRX" : ", rrx");
            return p;
        } else {
            /* LSR/ASR #32 */
            const char *stype =
                (shift_type == 1) ? (disass_upper_mnemonics ? "LSR" : "lsr") :
                                    (disass_upper_mnemonics ? "ASR" : "asr");
            p = append_str(p, ", ");
            p = append_str(p, stype);
            p = append_str(p, " #32");
            return p;
        }
    }

    {
        const char *stype =
            (shift_type == 0) ? (disass_upper_mnemonics ? "LSL" : "lsl") :
            (shift_type == 1) ? (disass_upper_mnemonics ? "LSR" : "lsr") :
            (shift_type == 2) ? (disass_upper_mnemonics ? "ASR" : "asr") :
                                 (disass_upper_mnemonics ? "ROR" : "ror");
        p = append_str(p, ", ");
        p = append_str(p, stype);
        {
            int n = sprintf(p, " #%u", shift_imm);
            p += n;
        }
        return p;
    }
}

static void disass_data_processing(unsigned32 instr,
                                   unsigned32 pc,
                                   void *cb_arg,
                                   dis_cb_fn cb,
                                   char *out)
{
    unsigned cond   = BITS(instr, 31, 28);
    unsigned opcode = BITS(instr, 24, 21);
    unsigned sbit   = BITS(instr, 20, 20);
    unsigned rn     = BITS(instr, 19, 16);
    unsigned rd     = BITS(instr, 15, 12);
    unsigned imm    = BITS(instr, 25, 25);
    char *p = out;

    const char *op = dp_opnames[opcode];
    char mnem[8];

    /* TST/TEQ/CMP/CMN ignore the S bit – they already update flags. */
    if (opcode >= 8 && opcode <= 11)
        sprintf(mnem, "%s", op);
    else if (sbit)
        sprintf(mnem, "%sS", op);
    else
        sprintf(mnem, "%s", op);

    p = emit_mnemonic(p, mnem, cond);

    if (opcode >= 8 && opcode <= 11) {
        /* TST/TEQ/CMP/CMN: op Rn, operand2 */
        p = append_core_reg(p, rn);
        p = append_str(p, ", ");
    } else if (opcode == 13 || opcode == 15) {
        /* MOV/MVN: op Rd, operand2 */
        p = append_core_reg(p, rd);
        p = append_str(p, ", ");
    } else {
        /* Normal: op Rd, Rn, operand2 */
        p = append_core_reg(p, rd);
        p = append_str(p, ", ");
        p = append_core_reg(p, rn);
        p = append_str(p, ", ");
    }

    if (imm) {
        unsigned imm8 = BITS(instr, 7, 0);
        unsigned rot  = BITS(instr, 11, 8) * 2u;
        unsigned32 val = rotate_imm(imm8, rot);

        /* PC-relative ADD/SUB (ADR) – let the callback supply the label. */
        if (cb != NULL && rn == 15 &&
            (opcode == 4 /* ADD */ || opcode == 2 /* SUB */)) {
            dis_cb_type type = (opcode == 4) ? D_ADDPCREL : D_SUBPCREL;
            p = cb(type, (int32)val, pc + 8u, (int)instr, cb_arg, p);
        } else {
            /* Normal immediate operand, printed in decimal. */
            int n = sprintf(p, "#%u", (unsigned)val);
            p += n;
        }
    } else {
        p = decode_shifted_reg(p, instr);
    }
}

static void disass_single_data_transfer(unsigned32 instr,
                                        unsigned32 pc,
                                        void *cb_arg,
                                        dis_cb_fn cb,
                                        char *out)
{
    unsigned cond  = BITS(instr, 31, 28);
    unsigned pbit  = BITS(instr, 24, 24);
    unsigned ubit  = BITS(instr, 23, 23);
    unsigned bbit  = BITS(instr, 22, 22);
    unsigned wbit  = BITS(instr, 21, 21);
    unsigned lbit  = BITS(instr, 20, 20);
    unsigned rn    = BITS(instr, 19, 16);
    unsigned rd    = BITS(instr, 15, 12);
    unsigned imm   = BITS(instr, 25, 25);
    unsigned32 off = BITS(instr, 11, 0);

    char *p = out;

    const char *base = lbit ? (bbit ? "LDRB" : "LDR")
                            : (bbit ? "STRB" : "STR");

    p = emit_mnemonic(p, base, cond);

    p = append_core_reg(p, rd);
    p = append_str(p, ", ");

    if (imm) {
        unsigned rm = BITS(instr, 3, 0);
        if (pbit) {
            p = append_str(p, "[");
            p = append_core_reg(p, rn);
            p = append_str(p, ", ");
            if (!ubit) p = append_str(p, "-");
            p = append_core_reg(p, rm);
            p = append_str(p, "]");
            if (wbit) p = append_str(p, "!");
        } else {
            p = append_str(p, "[");
            p = append_core_reg(p, rn);
            p = append_str(p, "], ");
            if (!ubit) p = append_str(p, "-");
            p = append_core_reg(p, rm);
        }
    } else {
        /* Immediate offset. */

        /* PC-relative literal load/store – let the callback resolve to a label. */
        if (rn == 15 && cb != NULL) {
            int32 soff = ubit ? (int32)off : -(int32)off;
            unsigned32 addr = (int32)pc + 8 + soff;

            dis_cb_type type = lbit ? D_LOADPCREL : D_STOREPCREL;
            cb(type, soff, addr, (int)instr, cb_arg, p);

            return;
        }

        /* Non-PC base with callback: use D_LOAD/D_STORE so caller can
           append a symbolic offset (e.g. "#4+sym") instead of a raw
           immediate.  This expects the callback to start writing at the
           point immediately after the '#' character. */
        if (cb != NULL) {
            dis_cb_type type = lbit ? D_LOAD : D_STORE;
            int32 soff = (int32)off;
            if (!ubit) soff = -soff;

            if (off == 0 && pbit && !wbit) {
                /* Simple [Rn] – no offset to decorate. */
                p = append_str(p, "[");
                p = append_core_reg(p, rn);
                p = append_str(p, "]");
            } else if (pbit) {
                /* Pre-indexed: [Rn, #offset] or [Rn, #-offset], with optional writeback. */
                p = append_str(p, "[");
                p = append_core_reg(p, rn);
                p = append_str(p, ", #");
                {
                    char *cb_start = p;
                    p = cb(type, soff, 0, (int)instr, cb_arg, p);
                    if (p == cb_start) {
                        /* Callback chose not to decorate – fall back to plain numeric (decimal). */
                        p = append_offset_decimal_naked(p, soff);
                        /* Close the bracket, then optionally add a hex comment. */
                        p = append_str(p, "]");
                        if (wbit) p = append_str(p, "!");
                        if (rn == 13 && off > 9) {
                            p = append_hex_comment_for_offset(p, off);
                        }
                    } else {
                        /* Callback emitted something (e.g. symbolic offset). Just close. */
                        p = append_str(p, "]");
                        if (wbit) p = append_str(p, "!");
                    }
                }
            } else {
                /* Post-indexed: [Rn], #offset */
                p = append_str(p, "[");
                p = append_core_reg(p, rn);
                p = append_str(p, "], #");
                {
                    char *cb_start = p;
                    p = cb(type, soff, 0, (int)instr, cb_arg, p);
                    if (p == cb_start) {
                        /* Callback chose not to decorate – fall back to plain numeric (decimal). */
                        int abs = (soff < 0) ? -soff : soff;
                        if (soff < 0)
                            p += sprintf(p, "-%d", abs);
                        else
                            p += sprintf(p, "%d", abs);
                        if (rn == 13 && off > 9) {
                            p += sprintf(p, "   @ %s%X", g_hexprefix, (unsigned)off);
                        }
                    }
                }
            }
            return;
        }

        /* No callback – print as a plain numeric immediate (decimal, with optional hex comment). */
        {
            int32 soff = !ubit ? (int32)off : -(int32)off;
            int abs = (soff < 0) ? -soff : soff;

            if (off == 0 && pbit && !wbit) {
                p = append_str(p, "[");
                p = append_core_reg(p, rn);
                p = append_str(p, "]");
            } else if (pbit) {
                /* Pre-indexed: [Rn, #+/-imm] */
                p = append_str(p, "[");
                p = append_core_reg(p, rn);
                p = append_str(p, ", #");
                if (soff < 0)
                    p += sprintf(p, "-%d", abs);
                else
                    p += sprintf(p, "%d", abs);
                p = append_str(p, "]");
                if (wbit) p = append_str(p, "!");
            } else {
                /* Post-indexed: [Rn], #+/-imm */
                p = append_str(p, "[");
                p = append_core_reg(p, rn);
                p = append_str(p, "], #");
                if (soff < 0)
                    p += sprintf(p, "-%d", abs);
                else
                    p += sprintf(p, "%d", abs);
            }

            /* For stack-relative offsets, add an objdump-style hex comment for larger immediates. */
            if (rn == 13 && off > 9) {
                p += sprintf(p, "   @ %s%X", g_hexprefix, (unsigned)off);
            }
        }
    }
}

static void disass_branch(unsigned32 instr, unsigned32 pc, void *cb_arg,
                          dis_cb_fn cb, char *out)
{
    unsigned cond = BITS(instr, 31, 28);
    unsigned link = BITS(instr, 24, 24);
    int32 imm24   = (int32)(instr & 0x00FFFFFFu);
    char *p = out;

    /* Sign-extend imm24 then multiply by 4 and add PC+8. */
    if (imm24 & 0x00800000) imm24 |= ~0x00FFFFFF;
    {
        unsigned32 target = pc + 8u + ((unsigned32)imm24 << 2);
        const char *base = link ? "BL" : "B";

        p = emit_mnemonic(p, base, cond);

        if (cb != NULL) {
            p = cb(D_BORBL, 0, target, (int)instr, cb_arg, p);
        } else {
            int n = sprintf(p, "%s%08lX", g_hexprefix, (unsigned long)target);
            p += n;
        }
        *p = '\0';
    }
}

static void disass_swi(unsigned32 instr, char *out)
{
    unsigned cond = BITS(instr, 31, 28);
    unsigned32 imm24 = instr & 0x00FFFFFFu;
    char *p = out;

    p = emit_mnemonic(p, "SWI", cond);

    {
        int n = sprintf(p, "%s%06lX", g_hexprefix, (unsigned long)imm24);
        p += n;
        *p = '\0';
    }
}

/* Helper: print ARM register list as {r0, r1, ...} with ranges. */
static char *append_core_reglist(char *p, unsigned list)
{
    int first = 1;
    int r = 0;

    *p++ = '{';

    while (r < 16) {
        if (list & (1u << r)) {
            int start = r;
            int end = r;
            while (end + 1 < 16 && (list & (1u << (end + 1))))
                ++end;

            if (!first) {
                *p++ = ',';
                *p++ = ' ';
            }
            p = append_core_reg(p, (unsigned)start);
            if (end > start) {
                *p++ = '-';
                p = append_core_reg(p, (unsigned)end);
            }
            first = 0;
            r = end + 1;
        } else {
            ++r;
        }
    }

    *p++ = '}';
    *p = '\0';
    return p;
}

/* ARM block data transfer (LDM/STM) decoder. */
static void disass_block_data_transfer(unsigned32 instr, char *out)
{
    unsigned cond = BITS(instr, 31, 28);
    unsigned pbit = BITS(instr, 24, 24);
    unsigned ubit = BITS(instr, 23, 23);
    unsigned sbit = BITS(instr, 22, 22);
    unsigned wbit = BITS(instr, 21, 21);
    unsigned lbit = BITS(instr, 20, 20);
    unsigned rn   = BITS(instr, 19, 16);
    unsigned regs = instr & 0xFFFFu;

    const char *base = lbit ? "LDM" : "STM";
    const char *mode;

    char mnem[8];
    char *p = out;

    /* Addressing mode suffix from P/U bits: IA, IB, DA, DB. */
    if (ubit) {
        mode = pbit ? "IB" : "IA";
    } else {
        mode = pbit ? "DB" : "DA";
    }

    sprintf(mnem, "%s%s", base, mode);
    p = emit_mnemonic(p, mnem, cond);

    p = append_core_reg(p, rn);
    if (wbit) {
        *p++ = '!';
        *p = '\0';
    }
    p = append_str(p, ", ");
    p = append_core_reglist(p, regs);
    if (sbit) {
        *p++ = '^';
        *p = '\0';
    }
}

void disass(uint64_t w, uint64_t oldq, const char* buf, void *cb_arg, dis_cb_fn cb)
{
    unsigned32 instr = (unsigned32)w;
    unsigned32 pc    = (unsigned32)oldq;  /* byte offset within current function */
    char *out = (char *)buf;

    /* Default: show raw word as data. */
    sprintf(out, "DCD      %s%.8lX", g_hexprefix, (unsigned long)instr);

#if TARGET_IS_ARM
    // Try obsolete FPA/FPE disassembler for CP1/CP2 encodings.
    if (disass_fpa(instr, pc, cb_arg, cb, out)) {
        return;
    }
#endif

    /* BLX (immediate) – shares the branch encoding space but is unconditional.
       For now, leave it as DCD instead of mis-decoding as BLNV. */
    if ((instr & 0xfe000000u) == 0xfa000000u) {
        return;
    }

    /* BX / BLX (register). */
    if ((instr & 0x0ffffff0u) == 0x012fff10u ||   /* BX */
        (instr & 0x0ffffff0u) == 0x012fff30u) {   /* BLX (register) */
        disass_bx_blx_reg(instr, out);
        return;
    }

    /* SWP / SWPB. */
    if ((instr & 0x0fb00ff0u) == 0x01000090u) {
        disass_swp(instr, out);
        return;
    }

    /* CLZ. */
    if ((instr & 0x0fff0ff0u) == 0x016f0f10u) {
        disass_clz(instr, out);
        return;
    }

    /* MRS / MSR (status register moves). */
    if ((instr & 0x0fbf0fffu) == 0x010f0000u) {
        disass_mrs(instr, out);
        return;
    }
    if ((instr & 0x0db0f000u) == 0x0120f000u) {
        disass_msr(instr, out);
        return;
    }

    /* Multiply / multiply-accumulate (MUL / MLA). */
    if ((instr & 0x0FC000F0u) == 0x00000090u ||   /* MUL{S} */
        (instr & 0x0FC000F0u) == 0x00200090u) {   /* MLA{S} */
        disass_multiply(instr, out);
        return;
    }

    /* 64-bit multiply family (UMULL/UMLAL/SMULL/SMLAL). */
    if ((instr & 0x0F8000F0u) == 0x00800090u) {
        disass_long_multiply(instr, out);
        return;
    }

    /* Halfword and signed data transfer (LDRH/STRH/LDRSB/LDRSH). */
    if ((instr & 0x0E0000F0u) == 0x000000B0u) {
        disass_halfword_signed_transfer(instr, out);
        return;
    }

    /* Branch / BL */
    if ((instr & 0x0E000000u) == 0x0A000000u) {
        disass_branch(instr, pc, cb_arg, cb, out);
        return;
    }

    /* SWI */
    if ((instr & 0x0F000000u) == 0x0F000000u) {
        disass_swi(instr, out);
        return;
    }

    /* Single data transfer (LDR/STR, LDRB/STRB) */
    if ((instr & 0x0C000000u) == 0x04000000u) {
        disass_single_data_transfer(instr, pc, cb_arg, cb, out);
        return;
    }

    /* Block data transfer (LDM/STM). */
    if ((instr & 0x0E000000u) == 0x08000000u) {
        disass_block_data_transfer(instr, out);
        return;
    }

    /* Data processing (AND/EOR/SUB/ADD/... MOV/MVN). */
    if ((instr & 0x0C000000u) == 0x00000000u) {
        disass_data_processing(instr, pc, cb_arg, cb, out);
        return;
    }

    /* Anything we don't understand is left as the DCD we printed at the top. */
}

/* ARM multiply / multiply-accumulate decoder (MUL / MLA). */
static void disass_multiply(unsigned32 instr, char *out)
{
    unsigned cond = BITS(instr, 31, 28);
    unsigned sbit = BITS(instr, 20, 20);
    unsigned acc  = BITS(instr, 21, 21);
    unsigned rn   = BITS(instr, 19, 16);   /* accumulate register for MLA */
    unsigned rd   = BITS(instr, 15, 12);
    unsigned rs   = BITS(instr, 11, 8);
    unsigned rm   = BITS(instr, 3, 0);
    char mnem[8];
    char *p = out;

    if (acc)
        sprintf(mnem, "MLA%s", sbit ? "S" : "");
    else
        sprintf(mnem, "MUL%s", sbit ? "S" : "");

    p = emit_mnemonic(p, mnem, cond);

    /* MUL{S} Rd, Rm, Rs
       MLA{S} Rd, Rm, Rs, Rn */
    p = append_core_reg(p, rd);
    p = append_str(p, ", ");
    p = append_core_reg(p, rm);
    p = append_str(p, ", ");
    p = append_core_reg(p, rs);
    if (acc) {
        p = append_str(p, ", ");
        p = append_core_reg(p, rn);
    }
}

/* ARM 64-bit multiply family decoder (UMULL/UMLAL/SMULL/SMLAL). */
static void disass_long_multiply(unsigned32 instr, char *out)
{
    unsigned cond = BITS(instr, 31, 28);
    unsigned ubit = BITS(instr, 22, 22);  /* 0 = unsigned, 1 = signed */
    unsigned abit = BITS(instr, 21, 21);  /* accumulate */
    unsigned sbit = BITS(instr, 20, 20);
    unsigned rdhi = BITS(instr, 19, 16);
    unsigned rdlo = BITS(instr, 15, 12);
    unsigned rs   = BITS(instr, 11, 8);
    unsigned rm   = BITS(instr, 3, 0);
    const char *base;
    char mnem[8];
    char *p = out;

    if (ubit == 0 && abit == 0) base = "UMULL";
    else if (ubit == 0 && abit == 1) base = "UMLAL";
    else if (ubit == 1 && abit == 0) base = "SMULL";
    else                              base = "SMLAL";

    sprintf(mnem, "%s%s", base, sbit ? "S" : "");
    p = emit_mnemonic(p, mnem, cond);

    /* xMULL{S} RdLo, RdHi, Rm, Rs */
    p = append_core_reg(p, rdlo);
    p = append_str(p, ", ");
    p = append_core_reg(p, rdhi);
    p = append_str(p, ", ");
    p = append_core_reg(p, rm);
    p = append_str(p, ", ");
    p = append_core_reg(p, rs);
}

/* ARM halfword & signed-data transfer decoder:
 * STRH, LDRH, LDRSB, LDRSH (immediate or register offset).
 */
static void disass_halfword_signed_transfer(unsigned32 instr, char *out)
{
    unsigned cond = BITS(instr, 31, 28);
    unsigned pbit = BITS(instr, 24, 24);
    unsigned ubit = BITS(instr, 23, 23);
    unsigned ibit = BITS(instr, 22, 22);
    unsigned wbit = BITS(instr, 21, 21);
    unsigned lbit = BITS(instr, 20, 20);
    unsigned rn   = BITS(instr, 19, 16);
    unsigned rd   = BITS(instr, 15, 12);
    unsigned high = BITS(instr, 11, 8);
    unsigned sh   = BITS(instr, 6, 5);
    unsigned low  = BITS(instr, 3, 0);

    const char *base;
    char *p = out;

    /* Determine base mnemonic from L bit and sh field. */
    if (!lbit && sh == 1) {
        base = "STRH";
    } else if (lbit && sh == 1) {
        base = "LDRH";
    } else if (lbit && sh == 2) {
        base = "LDRSB";
    } else if (lbit && sh == 3) {
        base = "LDRSH";
    } else {
        /* Undefined/unused combination – leave as DCD. */
        return;
    }

    p = emit_mnemonic(p, base, cond);

    p = append_core_reg(p, rd);
    p = append_str(p, ", ");

    if (ibit) {
        /* Immediate offset: high nibble in bits[11:8], low nibble in bits[3:0]. */
        unsigned32 off = (high << 4) | low;

        if (off == 0 && pbit && !wbit) {
            p = append_str(p, "[");
            p = append_core_reg(p, rn);
            p = append_str(p, "]");
        } else if (pbit) {
            p = append_str(p, "[");
            p = append_core_reg(p, rn);
            p = append_str(p, ", ");
            if (!ubit) p = append_str(p, "-");
            p = append_immediate(p, off);
            p = append_str(p, "]");
            if (wbit) p = append_str(p, "!");
        } else {
            p = append_str(p, "[");
            p = append_core_reg(p, rn);
            p = append_str(p, "], ");
            if (!ubit) p = append_str(p, "-");
            p = append_immediate(p, off);
        }
    } else {
        /* Register offset. */
        unsigned rm = low;

        if (pbit) {
            p = append_str(p, "[");
            p = append_core_reg(p, rn);
            p = append_str(p, ", ");
            if (!ubit) p = append_str(p, "-");
            p = append_core_reg(p, rm);
            p = append_str(p, "]");
            if (wbit) p = append_str(p, "!");
        } else {
            p = append_str(p, "[");
            p = append_core_reg(p, rn);
            p = append_str(p, "], ");
            if (!ubit) p = append_str(p, "-");
            p = append_core_reg(p, rm);
        }
    }
}

/* ARM single data swap: SWP / SWPB. */
static void disass_swp(unsigned32 instr, char *out)
{
    unsigned cond = BITS(instr, 31, 28);
    unsigned rn   = BITS(instr, 19, 16);
    unsigned rd   = BITS(instr, 15, 12);
    unsigned rm   = BITS(instr, 3, 0);
    bool byte     = (instr & (1u << 22)) != 0;
    const char *base = byte ? "SWPB" : "SWP";
    char mnem[8];
    char *p = out;

    sprintf(mnem, "%s", base);
    p = emit_mnemonic(p, mnem, cond);

    /* SWP{B} Rd, Rm, [Rn] */
    p = append_core_reg(p, rd);
    p = append_str(p, ", ");
    p = append_core_reg(p, rm);
    p = append_str(p, ", [");
    p = append_core_reg(p, rn);
    p = append_str(p, "]");
}

/* ARM branch and exchange: BX / BLX (register form). */
static void disass_bx_blx_reg(unsigned32 instr, char *out)
{
    unsigned cond = BITS(instr, 31, 28);
    unsigned rm   = BITS(instr, 3, 0);
    /* Bit 5 distinguishes BX vs BLX in this encoding. */
    bool link = (instr & 0x20u) != 0;
    const char *base = link ? "BLX" : "BX";
    char mnem[8];
    char *p = out;

    sprintf(mnem, "%s", base);
    p = emit_mnemonic(p, mnem, cond);
    p = append_core_reg(p, rm);
}

/* ARM count-leading-zeros instruction: CLZ. */
static void disass_clz(unsigned32 instr, char *out)
{
    unsigned cond = BITS(instr, 31, 28);
    unsigned rd   = BITS(instr, 15, 12);
    unsigned rm   = BITS(instr, 3, 0);
    char *p = out;

    p = emit_mnemonic(p, "CLZ", cond);
    p = append_core_reg(p, rd);
    p = append_str(p, ", ");
    p = append_core_reg(p, rm);
}

/* ARM status register to general-purpose register: MRS. */
static void disass_mrs(unsigned32 instr, char *out)
{
    unsigned cond = BITS(instr, 31, 28);
    unsigned rd   = BITS(instr, 15, 12);
    unsigned psr  = BITS(instr, 22, 22);  /* 0 = CPSR, 1 = SPSR */
    const char *psr_name = psr ? "SPSR" : "CPSR";
    char *p = out;

    p = emit_mnemonic(p, "MRS", cond);
    p = append_core_reg(p, rd);
    p = append_str(p, ", ");
    p = append_str(p, psr_name);
}

/* ARM general-purpose register or immediate to status register: MSR. */
static void disass_msr(unsigned32 instr, char *out)
{
    unsigned cond = BITS(instr, 31, 28);
    unsigned psr  = BITS(instr, 22, 22);  /* 0 = CPSR, 1 = SPSR */
    const char *psr_name = psr ? "SPSR" : "CPSR";
    unsigned imm  = BITS(instr, 25, 25);
    char *p = out;

    p = emit_mnemonic(p, "MSR", cond);
    p = append_str(p, psr_name);
    p = append_str(p, ", ");

    if (imm) {
        /* Immediate form uses the same rotated-imm encoding as data-processing. */
        unsigned imm8  = BITS(instr, 7, 0);
        unsigned rot   = BITS(instr, 11, 8) * 2u;
        unsigned32 val = rotate_imm(imm8, rot);
        p = append_immediate(p, val);
    } else {
        unsigned rm = BITS(instr, 3, 0);
        p = append_core_reg(p, rm);
    }
}

