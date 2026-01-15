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

#include "disass.h"
#include "disass-arm.h"   /* reuse mnemonic/operand helpers */
#include "ops.h"          /* Thumb opcode #defines (F_*) */

#include <stdio.h>
#include <string.h>

#define BITS(v,hi,lo) (((v) >> (lo)) & ((1u << ((hi)-(lo)+1)) - 1u))

/* Thumb condition codes for conditional branches. */
static const char *const tcond_codes[16] = {
    "EQ", "NE", "CS", "CC",
    "MI", "PL", "VS", "VC",
    "HI", "LS", "GE", "LT",
    "GT", "LE", "AL", "NV"
};

static char *append_core_reglist_thumb(char *p, unsigned list)
{
    int first = 1;
    int r;

    *p++ = '{';
    for (r = 0; r < 16; ++r) {
        if (list & (1u << r)) {
            if (!first) {
                *p++ = ',';
                *p++ = ' ';
            }
            p = append_core_reg(p, (unsigned)r);
            first = 0;
        }
    }
    *p++ = '}';
    *p = '\0';
    return p;
}

static int32 sign_extend(int32 v, unsigned bits)
{
    /* bits is number of value bits in v (excluding sign extension). */
    int32 m = (int32)(1u << (bits - 1));
    return (v ^ m) - m;
}

static unsigned32 thumb_pc_base(unsigned32 pc)
{
    /* Thumb PC for literals/ADR is (address of current insn + 4) with low 2 bits cleared. */
    return (pc + 4u) & ~3u;
}

static void print_thumb_dcd(uint16_t h1, char *out)
{
    sprintf(out, "DCW      0x%04X", (unsigned)h1);
}

/*
 * Disassemble Thumb (Thumb-1) instructions used by Norcroft.
 * Returns instruction length in bytes (2 or 4).
 */
int32 disass_16(uint16_t h1, uint16_t h2, uint64_t oldq,
                const char* buf, void *cb_arg, dis_cb_fn cb)
{
    unsigned32 pc = (unsigned32)oldq; /* byte offset within current function */
    unsigned32 instr16 = (unsigned32)h1;
    char *out = (char *)buf;
    char *p;

    /* Default: show raw halfword. */
    print_thumb_dcd(h1, out);

    /* --- 32-bit Thumb BL (Thumb-1 long branch with link): 11110 + 11111 --- */
    if ((h1 & 0xF800u) == 0xF000u && (h2 & 0xF800u) == 0xF800u) {
        /*
         * Encoding:
         *   first:  11110 S imm10
         *   second: 11111 J1 J2 imm11
         * For classic Thumb-1 BL, treat as signed 23-bit offset (<<1).
         */
        unsigned s    = (h1 >> 10) & 1u;
        unsigned imm10 = h1 & 0x03FFu;
        unsigned j1   = (h2 >> 13) & 1u;
        unsigned j2   = (h2 >> 11) & 1u;
        unsigned imm11 = h2 & 0x07FFu;

        /* Reconstruct I1/I2 per ARM ARM style (for Thumb-2); this also works for the classic pattern. */
        unsigned i1 = (~(j1 ^ s)) & 1u;
        unsigned i2 = (~(j2 ^ s)) & 1u;

        unsigned32 imm23 = (s << 22) | (i1 << 21) | (i2 << 20) | (imm10 << 10) | imm11;
        int32 soff = sign_extend((int32)imm23, 23) << 1;
        unsigned32 target = pc + 4u + (unsigned32)soff;

        p = emit_mnemonic(out, "BL", 0xE /* always */);
        if (cb != NULL) {
            (void)cb(D_BORBL, 0, target, (int)((h2 << 16) | h1), cb_arg, p);
        } else {
            sprintf(p, "0x%08lX", (unsigned long)target);
        }
        return 4;
    }

    /* --- 16-bit unconditional branch: 11100 imm11 --- */
    if ((h1 & 0xF800u) == (uint16_t)F_B) {
        int32 imm11 = (int32)(h1 & 0x07FFu);
        int32 soff = sign_extend(imm11, 11) << 1;
        unsigned32 target = pc + 4u + (unsigned32)soff;

        p = emit_mnemonic(out, "B", 0xE);
        if (cb != NULL) {
            (void)cb(D_BORBL, 0, target, (int)instr16, cb_arg, p);
        } else {
            sprintf(p, "0x%08lX", (unsigned long)target);
        }
        return 2;
    }

    /* --- 16-bit conditional branch: 1101 cond imm8 (cond != 1111) --- */
    if ((h1 & 0xF000u) == (uint16_t)F_BC) {
        unsigned cond = (h1 >> 8) & 0xFu;
        unsigned imm8 = h1 & 0x00FFu;

        if (cond == 0xF) {
            /* SWI in this space (see below). */
        } else {
            int32 soff = sign_extend((int32)imm8, 8) << 1;
            unsigned32 target = pc + 4u + (unsigned32)soff;

            /* Emit as B<cond>. */
            {
                char mnem[8];
                sprintf(mnem, "B%s", tcond_codes[cond]);
                p = emit_mnemonic(out, mnem, 0xE);
            }
            if (cb != NULL) {
                (void)cb(D_BORBL, 0, target, (int)instr16, cb_arg, p);
            } else {
                sprintf(p, "0x%08lX", (unsigned long)target);
            }
            return 2;
        }
    }

    /* --- SWI: 1101 1111 imm8 --- */
    if ((h1 & 0xFF00u) == (uint16_t)F_SWI) {
        unsigned imm8 = h1 & 0x00FFu;
        p = emit_mnemonic(out, "SWI", 0xE);
        sprintf(p, "#0x%02X", imm8);
        return 2;
    }

    /* --- PC-relative LDR literal: 01001 Rt imm8 (addr = Align(PC+4,4) + imm8*4) --- */
    if ((h1 & 0xF800u) == (uint16_t)F_LDRLIT) {
        unsigned rt = (h1 >> 8) & 0x7u;
        unsigned imm8 = h1 & 0x00FFu;
        unsigned32 base = thumb_pc_base(pc);
        int32 soff = (int32)(imm8 * 4u);
        unsigned32 addr = base + (unsigned32)soff;

        p = emit_mnemonic(out, "LDR", 0xE);
        p = append_core_reg(p, rt);
        p = append_str(p, ", ");

        if (cb != NULL) {
            (void)cb(D_LOADPCREL, soff, addr, (int)instr16, cb_arg, p);
        } else {
            sprintf(p, "[pc, #0x%X]", imm8 * 4u);
        }
        return 2;
    }

    /* --- ADD (ADR): 10100 Rd imm8  => Rd = Align(PC+4,4) + imm8*4 --- */
    if ((h1 & 0xF800u) == (uint16_t)F_ADDRPC) {
        unsigned rd = (h1 >> 8) & 0x7u;
        unsigned imm8 = h1 & 0x00FFu;
        unsigned32 base = thumb_pc_base(pc);
        unsigned32 off = (unsigned32)imm8 * 4u;

        /* Prefer the ADR pseudo-instruction syntax: ADR Rd, #imm */
        p = emit_mnemonic(out, "ADR", 0xE);
        p = append_core_reg(p, rd);
        p = append_str(p, ", ");

        if (cb != NULL) {
            (void)cb(D_ADDPCREL, (int32)off, base, (int)instr16, cb_arg, p);
        } else {
            sprintf(p, "#0x%lX", (unsigned long)off);
        }
        return 2;
    }

    /* --- ADD Rd, SP, #imm: 10101 Rd imm8 (imm8*4) --- */
    if ((h1 & 0xF800u) == (uint16_t)F_ADDRSP) {
        unsigned rd = (h1 >> 8) & 0x7u;
        unsigned imm8 = h1 & 0x00FFu;
        unsigned32 off = (unsigned32)imm8 * 4u;

        p = emit_mnemonic(out, "ADD", 0xE);
        p = append_core_reg(p, rd);
        p = append_str(p, ", ");
        p = append_core_reg(p, 13);
        p = append_str(p, ", ");
        sprintf(p, "#0x%lX", (unsigned long)off);
        return 2;
    }

    /* --- PUSH/POP: 1011 L 10 R list --- */
    if ((h1 & 0xF600u) == (uint16_t)F_PUSH) {
        unsigned lbit = (h1 >> 11) & 1u; /* 0 push, 1 pop */
        unsigned rbit = (h1 >> 8) & 1u;  /* include LR/PC */
        unsigned list = h1 & 0x00FFu;
        unsigned full_list = list;

        if (!lbit) {
            /* PUSH includes LR when rbit set. */
            if (rbit) full_list |= (1u << 14);
            p = emit_mnemonic(out, "PUSH", 0xE);
        } else {
            /* POP includes PC when rbit set. */
            if (rbit) full_list |= (1u << 15);
            p = emit_mnemonic(out, "POP", 0xE);
        }

        p = append_core_reglist_thumb(p, full_list);
        return 2;
    }

    /* --- LDMIA/STMIA: 1100 L Rn list --- */
    if ((h1 & 0xF000u) == (uint16_t)F_STM) {
        unsigned lbit = (h1 >> 11) & 1u;
        unsigned rn = (h1 >> 8) & 0x7u;
        unsigned list = h1 & 0x00FFu;
        p = emit_mnemonic(out, lbit ? "LDMIA" : "STMIA", 0xE);
        p = append_core_reg(p, rn);
        if ((list & (1u << rn)) == 0) {
            /* Only show writeback when base register is not also being transferred. */
            p = append_str(p, "!, ");
        } else {
            p = append_str(p, ", ");
        }
        p = append_core_reglist_thumb(p, list);
        return 2;
    }

    /* --- High register ops / BX / BLX: 010001 op H1 H2 Rs --- */
    if ((h1 & 0xFC00u) == 0x4400u) {
        unsigned op = (h1 >> 8) & 0x3u;
        unsigned h1b = (h1 >> 7) & 1u;
        unsigned h2b = (h1 >> 6) & 1u;
        /* Low bits of Rm/Rs are bits[5:3] (3 bits). Bit6 (H2) extends it to r8-r15. */
        unsigned rm3 = (h1 >> 3) & 0x7u;
        unsigned rd = (h1 & 0x7u) | (h1b ? 8u : 0u);
        unsigned rhs = rm3 | (h2b ? 8u : 0u);

        if (op == 3) {
            /* BX/BLX. rd field is ignored; rhs selects register. */
            p = emit_mnemonic(out, h1b ? "BLX" : "BX", 0xE);
            p = append_core_reg(p, rhs);
            return 2;
        }

        p = emit_mnemonic(out,
                          (op == 0) ? "ADD" : (op == 1) ? "CMP" : "MOV",
                          0xE);
        p = append_core_reg(p, rd);
        p = append_str(p, ", ");
        p = append_core_reg(p, rhs);
        return 2;
    }

    /* --- ALU ops: 010000 op Rs Rd --- */
    if ((h1 & 0xFC00u) == 0x4000u) {
        unsigned op = (h1 >> 6) & 0xFu;
        unsigned rs = (h1 >> 3) & 0x7u;
        unsigned rd = h1 & 0x7u;
        const char *m = NULL;

        switch (op) {
            case 0x0: m = "AND"; break;
            case 0x1: m = "EOR"; break;
            case 0x2: m = "LSL"; break;
            case 0x3: m = "LSR"; break;
            case 0x4: m = "ASR"; break;
            case 0x5: m = "ADC"; break;
            case 0x6: m = "SBC"; break;
            case 0x7: m = "ROR"; break;
            case 0x8: m = "TST"; break;
            case 0x9: m = "NEG"; break;
            case 0xA: m = "CMP"; break;
            case 0xB: m = "CMN"; break;
            case 0xC: m = "ORR"; break;
            case 0xD: m = "MUL"; break;
            case 0xE: m = "BIC"; break;
            case 0xF: m = "MVN"; break;
            default:  m = NULL;  break;
        }

        if (m != NULL) {
            p = emit_mnemonic(out, m, 0xE);
            p = append_core_reg(p, rd);
            p = append_str(p, ", ");
            p = append_core_reg(p, rs);
            return 2;
        }
    }

    /* --- MOV/CMP/ADD/SUB (immediate): 001 op Rd imm8 --- */
    if ((h1 & 0xE000u) == 0x2000u) {
        unsigned op = (h1 >> 11) & 0x3u;
        unsigned rd = (h1 >> 8) & 0x7u;
        unsigned imm8 = h1 & 0x00FFu;
        /* Thumb-1 immediate MOV/ADD/SUB are flag-setting (MOVS/ADDS/SUBS). */
        const char *m = (op == 0) ? "MOVS" : (op == 1) ? "CMP" : (op == 2) ? "ADDS" : "SUBS";

        p = emit_mnemonic(out, m, 0xE);
        p = append_core_reg(p, rd);
        p = append_str(p, ", ");
        sprintf(p, "#0x%X", imm8);
        return 2;
    }

    /* --- Shift by immediate: 000 op imm5 Rm Rd --- */
    if ((h1 & 0xE000u) == 0x0000u) {
        unsigned op = (h1 >> 11) & 0x3u;
        unsigned imm5 = (h1 >> 6) & 0x1Fu;
        unsigned rm = (h1 >> 3) & 0x7u;
        unsigned rd = h1 & 0x7u;
        const char *m = (op == 0) ? "LSL" : (op == 1) ? "LSR" : "ASR";

        if (op != 3) {
            /* LSL with imm5==0 is the MOVS (register) alias in Thumb-1. */
            if (op == 0 && imm5 == 0) {
                p = emit_mnemonic(out, "MOVS", 0xE);
                p = append_core_reg(p, rd);
                p = append_str(p, ", ");
                p = append_core_reg(p, rm);
                return 2;
            }

            p = emit_mnemonic(out, m, 0xE);
            p = append_core_reg(p, rd);
            p = append_str(p, ", ");
            p = append_core_reg(p, rm);
            p = append_str(p, ", ");
            sprintf(p, "#%u", imm5);
            return 2;
        }
        /* op==3: ADD/SUB (register or immediate3): 00011 I op imm3/Rm Rn Rd */
        {
            unsigned i = (h1 >> 10) & 1u;          /* 0=register, 1=immediate3 */
            unsigned sub = (h1 >> 9) & 1u;        /* 0=ADD, 1=SUB */
            unsigned imm3_or_rm = (h1 >> 6) & 0x7u;
            unsigned rn = (h1 >> 3) & 0x7u;
            unsigned rd = h1 & 0x7u;

            /* Thumb-1 ADD/SUB in this format are flag-setting (ADDS/SUBS). */
            p = emit_mnemonic(out, sub ? "SUBS" : "ADDS", 0xE);
            p = append_core_reg(p, rd);
            p = append_str(p, ", ");
            p = append_core_reg(p, rn);
            p = append_str(p, ", ");

            if (i) {
                /* immediate3 */
                sprintf(p, "#%u", imm3_or_rm);
            } else {
                /* register */
                p = append_core_reg(p, imm3_or_rm);
            }
            return 2;
        }
    }

    /* --- Load/store with immediate offset: 011x imm5 Rn Rt --- */
    if ((h1 & 0xE000u) == (uint16_t)F_STRI5) {
        unsigned top = h1 & 0xF800u;
        unsigned imm5 = (h1 >> 6) & 0x1Fu;
        unsigned rn = (h1 >> 3) & 0x7u;
        unsigned rt = h1 & 0x7u;
        const char *m;
        unsigned off;

        if (top == (uint16_t)F_STRI5) {
            m = "STR";
            off = imm5 << 2; /* word offsets are scaled */
        } else if (top == (uint16_t)F_LDRI5) {
            m = "LDR";
            off = imm5 << 2;
        } else if (top == (uint16_t)F_STRBI5) {
            m = "STRB";
            off = imm5;
        } else if (top == (uint16_t)F_LDRBI5) {
            m = "LDRB";
            off = imm5;
        } else {
            /* Not one of the i5 forms. */
            m = NULL;
            off = 0;
        }

        if (m != NULL) {
            p = emit_mnemonic(out, m, 0xE);
            p = append_core_reg(p, rt);
            p = append_str(p, ", [");
            p = append_core_reg(p, rn);
            if (off != 0) {
                p = append_str(p, ", #");
                sprintf(p, "%u", off);
                p += strlen(p);
            }
            p = append_str(p, "]");
            return 2;
        }
    }

    /* Unknown/unhandled: leave as DCW. */
    return 2;
}
