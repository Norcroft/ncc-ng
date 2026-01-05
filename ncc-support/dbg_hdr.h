/* Copyright 2026 Piers Wombwell
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

#include <string.h>

struct Dbg_Result {
    int32 intres;
};

struct Dbg_MCStateCall{
    struct Dbg_Result res;
};

typedef struct {
    struct Dbg_MCStateCall call;
} Dbg_MCState;

typedef struct Dbg_Proc {
    ItemProc *item;
    struct { ItemSection *section; } n;
} Dbg_Proc;

typedef struct {
    void *fp;
} Dbg_Frame;

typedef struct {
    void *st;
    Dbg_Proc *proc;
    Dbg_Frame frame;
} Dbg_Environment;

typedef enum { Error_OK, Error_NOK } Dbg_Error;

typedef struct VarDef {
    struct { ItemSection *section; } n;
    Item *item;
} VarDef;

typedef uint32_t ARMword;
typedef uint16_t ARMhword;
typedef uint8_t Dbg_Byte;

typedef size_t ARMaddress;

Dbg_Error dbg_WriteWord(Dbg_MCState *state, ARMaddress addr, ARMword word);
Dbg_Error Dbg_ReadHalf(Dbg_MCState *state, ARMhword *hword, ARMaddress addr);
Dbg_Error dbg_ReadWord(Dbg_MCState *state, ARMword *word, ARMaddress addr);
Dbg_Error Dbg_WriteHalf(Dbg_MCState *state, ARMaddress addr, ARMhword hword);
Dbg_Error dbg_ReadByte(Dbg_MCState *state, Dbg_Byte *byte, ARMaddress addr);
Dbg_Error dbg_WriteByte(Dbg_MCState *state, ARMaddress addr, Dbg_Byte byte);

Dbg_Error dbg_StringToVarDef(Dbg_MCState *state,
                             const char *name,
                             Dbg_Environment *current_env,
                             char **varname,
                             VarDef **var,
                             Dbg_Environment *out_env);

Dbg_Error dbg_StringToPath(Dbg_MCState *state,
                           const char *start,
                           const char *end,
                           Dbg_Environment *env,
                           void *unused,
                           void *st,
                           Dbg_Proc *proc);

Dbg_Error dbg_FindActivation(Dbg_MCState *state, Dbg_Environment *env);

ARMaddress FPOffset(int32_t offset, Dbg_Environment *env);

typedef enum { ps_callreturned, ps_callfailed } ResultFrom_CallNaturalSize;

ResultFrom_CallNaturalSize Dbg_CallNaturalSize(Dbg_MCState* cc_dbg_state,
                                               ARMaddress addr, int argw,
                                               ARMword args[32]);

typedef enum { B } Dbg_LLSymType;

void* dbg_LLSymVal(Dbg_MCState* cc_dbg_state,
                   void* cc_dbg_env_st,
                   const char* symname,
                   Dbg_LLSymType* junk,
                   unsigned32* val);
