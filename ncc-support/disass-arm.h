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

extern char *append_str(char *p, const char *s);

typedef enum { RegType_Core, RegType_FPA } RegType;
extern char *append_reg(char *p, unsigned r, RegType type);
extern char *append_core_reg(char *p, unsigned r);
extern char *append_immediate(char *p, unsigned32 imm);
extern char *append_immediate_s(char *p, unsigned32 imm, bool sign);

extern char *emit_mnemonic(char *p, const char *mnem, unsigned cond);
extern char *emit_mnemonic_with_suffix(char *p,
                                       const char *base,
                                       const char *suffix,
                                       unsigned cond);

extern char *emit_mnemonic_with_suffix2(char *p,
                                        const char *base,
                                        const char *suffix1,
                                        const char *suffix2,
                                        unsigned cond);

#ifndef PRETTY_DISASSEMBLY
# define disass_upper_mnemonics true
# define disass_apcs_reg_names true
#else
# define disass_upper_mnemonics false
# define disass_apcs_reg_names false
#endif

extern const char *g_hexprefix;
