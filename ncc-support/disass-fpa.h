
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

// FPA/FPE disassembler. RISC OS and ARM7500FE-era.
bool disass_fpa(unsigned32 instr,
                unsigned32 pc,
                void *cb_arg,
                dis_cb_fn cb,
                char *out);

