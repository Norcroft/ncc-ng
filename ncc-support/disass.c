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

#include <ctype.h>
#include <stdio.h>
#include <string.h>

const char *g_hexprefix = "0x";   // default if not set
static const char *g_regnames[16];       // kept only to satisfy API
static const char *g_fregnames[8];

void disass_addcopro(disass_addcopro_type copro)
{
    // No support for AMP. Never will be.
}

void disass_sethexprefix(const char* prefix)
{
    g_hexprefix = (prefix && *prefix) ? prefix : "0x";
}

void disass_setregnames(const char* regnames[16], const char* fregnames[8])
{
    if (regnames)
        memcpy((void*)g_regnames,  regnames,  sizeof g_regnames);

    if (fregnames)
        memcpy((void*)g_fregnames, fregnames, sizeof g_fregnames);
}

const char *const cond_codes[16] = {
    "EQ", "NE", "CS", "CC",
    "MI", "PL", "VS", "VC",
    "HI", "LS", "GE", "LT",
    "GT", "LE", "AL", "NV"
};

static const int mnemonic_field_width = 16;

char *emit_mnemonic_with_suffix(char *p,
                                const char *base,
                                const char *suffix,
                                unsigned cond)
{
    return emit_mnemonic_with_suffix2(p, base, suffix, NULL, cond);
}

char *emit_mnemonic_with_suffix2(char *p,
                                 const char *base,
                                 const char *suffix1,
                                 const char *suffix2,
                                 unsigned cond)
{
    int len = 0;
    const char *s;

    /* Base mnemonic (no suffix yet). */
    for (s = base; *s != '\0'; ++s) {
        char ch = *s;
        if (!disass_upper_mnemonics)
            ch = (char)tolower((unsigned char)ch);
        *p++ = ch;
        ++len;
    }

    /* Condition code, unless AL (always). */
    if (cond != 0xE) {
        const char *cc = cond_codes[cond];
        while (*cc != '\0') {
            char ch = *cc++;
            if (!disass_upper_mnemonics)
                ch = (char)tolower((unsigned char)ch);
            *p++ = ch;
            ++len;
        }
    }

    /* Optional suffix, e.g. ".F64" or ".F64.S32". */
    if (suffix1 && *suffix1) {
        for (s = suffix1; *s != '\0'; ++s) {
            char ch = *s;
            if (!disass_upper_mnemonics)
                ch = (char)tolower((unsigned char)ch);
            *p++ = ch;
            ++len;
        }
    }

    if (suffix2 && *suffix2) {
        for (s = suffix2; *s != '\0'; ++s) {
            char ch = *s;
            if (!disass_upper_mnemonics)
                ch = (char)tolower((unsigned char)ch);
            *p++ = ch;
            ++len;
        }
    }

    /* Always add at least one space between mnemonic and operands. */
    *p++ = ' ';
    ++len;

    /* Pad out to the configured field width. */
    while (len < mnemonic_field_width) {
        *p++ = ' ';
        ++len;
    }

    *p = '\0';
    return p;
}

/* Emit mnemonic (including S bit if present) plus condition, padded to a fixed field. */
char *emit_mnemonic(char *p, const char *mnem, unsigned cond)
{
    return emit_mnemonic_with_suffix(p, mnem, NULL, cond);
}

static const char *regname(unsigned r, RegType type)
{
    // Old Norcroft would always output lowercase register names.

    // Most registers are a prefix followed by the number.
    // Return a short static buffer containing the value.
    static char buf[8];

    char prefix = 'r';

    if (type == RegType_Core) {
        if (disass_apcs_reg_names && g_regnames[r])
            return g_regnames[r];

        // else use 'r<num>' except for 'fp', 'ip', 'sp', 'lr' and 'pc'.
        if (r == 11)
            return "fp";
        else if (r == 12)
            return "ip";
        else if (r == 13)
            return "sp";
        else if (r == 14)
            return "lr";
        else if (r == 15)
            return "pc";

        prefix = 'r';
    }

    if (type == RegType_FPA)
        prefix = 'f';

    // no snprintf in old C libs.
    sprintf(buf, "%c%u", prefix, r);

    return buf;
}

char *append_str(char *p, const char *s)
{
    while (*s)
        *p++ = *s++;

    *p = '\0';
    return p;
}

char *append_reg(char *p, unsigned r, RegType type)
{
    const char *name = regname(r, type);

    return append_str(p, name);
}

char *append_core_reg(char *p, unsigned r)
{
    return append_reg(p, r, RegType_Core);
}
