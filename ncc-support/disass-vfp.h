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

#pragma once

#include "globals.h"
#include "disass.h"

/* Returns YES if the instruction was recognised as a VFP/NEON op and
   disassembly was written into 'out'. */
extern bool disass_vfp(unsigned32 instr,
                       unsigned32 pc,
                       void *cb_arg,
                       dis_cb_fn cb,
                       char *out);

extern char *emit_mnemonic_with_suffix(char *p,
                                       const char *base,
                                       const char *suffix,
                                       unsigned cond);
