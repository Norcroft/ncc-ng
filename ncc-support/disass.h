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

// Used for symbolising the disassembly output.
typedef enum {
    D_BORBL,        // Branch
    D_ADDPCREL,     // add r1, pc, #offset
    D_SUBPCREL,     // sub r1, pc, #offset
    D_LOADPCREL,    // ldr a1, [pc, #offset]
    D_STOREPCREL,   // str a1, [pc, #offset]
    D_LOAD,         // ldr a1, [v1, #offset] / ldr a1, [v1], #offset
    D_STORE,        // str a1, [v1, #offset] / str a1, [v1], #offset
    D_SWI           // swi
} dis_cb_type;

// Callback used to print labels on branches, ADR, etc.
typedef char *(*dis_cb_fn)(dis_cb_type type,
                           int32 offset,
                           unsigned32 address,
                           int w,
                           void *cb_arg,
                           char *buf);

extern void disass(uint64_t w, uint64_t oldq, const char* buf,
                   void *cb_arg, dis_cb_fn cb);

// Returns instruction length in bytes (so 2 or 4).
extern int32 disass_16(uint16_t h1, uint16_t h2, uint64_t oldq,
                       const char* buf, void *cb_arg, dis_cb_fn cb);

extern void disass_sethexprefix(const char* prefix);
extern void disass_setregnames(const char* regnames[16],
                               const char* fregnames[8]);
