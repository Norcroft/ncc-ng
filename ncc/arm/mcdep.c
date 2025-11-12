/*
 * mcdep.c - miscellaneous target-dependent things.
 * Copyright (C) Acorn Computers Ltd., 1988.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#include <ctype.h>
#include <string.h>
#include <stdlib.h>

#include "globals.h"
#include "mcdep.h"
#include "mcdpriv.h"
#include "errors.h"
#include "pp.h"
#include "compiler.h"
#include "arminst.h"

#include "toolenv.h"
#include "toolenv2.h"
#include "tooledit.h"

int arthur_module;
int32 config;
int32 pcs_flags;
FPU_Type fpu_type;

static int config_mulbits;          /* number of bits per cycle */
static int config_multime;          /* minimum cycles for MUL */
static int config_mlatime;          /* minimum cycles for MLA */

typedef struct {
  char const *name;
  char const *val;
} EnvItem;

#define str(s) #s
#define xstr(s) str(s)

static EnvItem const builtin_defaults[] = {
#if (PCS_DEFAULTS & PCS_CALLCHANGESPSR)
  { "-apcs.32bit", "#/32"},
#else
  { "-apcs.32bit", "#/26"},
#endif
#if (PCS_DEFAULTS & PCS_NOSTACKCHECK)
  { "-apcs.swst", "#/noswst"},
#else
  { "-apcs.swst", "#/swst"},
#endif
#if (PCS_DEFAULTS & PCS_REENTRANT)
  { "-apcs.reent", "#/reent"},
#else
  { "-apcs.reent", "#/noreent"},
#endif
#if (PCS_DEFAULTS & PCS_SOFTFP)
  { "-apcs.softfp", "#/softfp"},
#else
  { "-apcs.softfp", "#/hardfp"},
#endif
#if (PCS_DEFAULTS & PCS_FPE3)
  { "-apcs.fpis", "#/fpe3"},
#else
  { "-apcs.fpis", "#/fpe2"},
#endif
#if (PCS_DEFAULTS & PCS_NOFP)
  { "-apcs.fp", "#/nofp"},
#else
  { "-apcs.fp", "#/fp"},
#endif
#if (PCS_DEFAULTS & PCS_FPREGARGS)
  { "-apcs.fpr", "#/fpregargs"},
#else
  { "-apcs.fpr", "#/nofpregargs"},
#endif
#if (PCS_DEFAULTS & PCS_INTERWORK)
  { "-apcs.inter", "#/interwork"},
  { "-cpu", "#ARM7TM"},  /* Which automagically sets -arch */
#else
  { "-apcs.inter", "#/nointerwork"},
  { "-cpu", "#ARM6"},    /* Which automagically sets -arch */
#endif
#if (PCS_DEFAULTS & PCS_UNWIDENED_NARROW_ARGS)
  { "-apcs.wide", "#/narrow"},
#else
  { "-apcs.wide", "#/wide"},
#endif

  { "-zr",  "=" xstr(LDM_REGCOUNT_MAX_DEFAULT) },
  { "-zi",  "=" xstr(INTEGER_LOAD_MAX_DEFAULT) },
  { "-zap", "=" xstr(STRUCT_PTR_ALIGN_DEFAULT) },
  { "-zas", "=4" },

#ifdef NO_UNALIGNED_LOADS
  { "-za",  "=1"},
#else
  { "-za",  "=0"},
#endif

  { ".areaperfn", "=-z+o" },

#ifdef CPLUSPLUS
  { ".debugtable", "=-dwarf" },
#else
  { ".debugtable", "=-asd" },
#endif
  { "-fpu",       "#fpa"},
  {NULL, NULL}
};

int mcdep_toolenv_insertdefaults(ToolEnv *t) {
  EnvItem const *p = builtin_defaults;
  for (; p->name != NULL; p++) {
    ToolEdit_InsertStatus rc = tooledit_insert(t, p->name, p->val);
    if (rc == TE_Failed) return 1;
  }
  return 0;
}

#define MULSPD(bits, mul, mla) bits, mul, mla

#define ARCH_2  PROCESSOR_HAS_26BIT_MODE
#define ARCH_3  PROCESSOR_HAS_26BIT_MODE|PROCESSOR_HAS_32BIT_MODE
#define ARCH_3G PROCESSOR_HAS_32BIT_MODE
#define ARCH_3M ARCH_3|PROCESSOR_HAS_MULTIPLY
#define ARCH_4  ARCH_3|(PROCESSOR_HAS_MULTIPLY|PROCESSOR_HAS_HALFWORDS)
#define ARCH_4T ARCH_3|(PROCESSOR_HAS_MULTIPLY|PROCESSOR_HAS_HALFWORDS)|PROCESSOR_HAS_THUMB

static Processor const p_arm6      = {"#ARM6",       ARCH_3,  "#3", MULSPD(2,2,2) };
static Processor const p_arm7      = {"#ARM7",       ARCH_3,  "#3", MULSPD(2,2,2) };
static Processor const p_arm7M     = {"#ARM7M",      ARCH_3M, "#3M",MULSPD(8,2,3) };
static Processor const p_arm7TM    = {"#ARM7TM",     ARCH_4T, "#4T",MULSPD(8,2,3) };
static Processor const p_arm8      = {"#ARM8",       ARCH_4,  "#4", MULSPD(8,3,3) };
static Processor const p_strongarm = {"#StrongARM1", ARCH_4,  "#4", MULSPD(12,1,1)};
static Processor const p_sa1500    = {"#SA1500",     ARCH_4,  "#4", MULSPD(12,1,1)};
static Processor const p_arm2      = {"#ARM2",       ARCH_2,  "#2", MULSPD(2,2,2) };
static Processor const p_arm3      = {"#ARM3",       ARCH_2,  "#2", MULSPD(2,2,2) };

static Processor const *const processors[] = {
  &p_arm6,  /* default: must come first */
  &p_arm7,
  &p_arm7M,
  &p_arm7TM,
  &p_arm8,
  &p_strongarm,
  &p_sa1500,
  &p_arm2,
  &p_arm3,
};

static const char *cistrchr(const char *s, int ch)
{   char c1 = (char)safe_tolower(ch);
    for (;;)
    {   char c = safe_tolower(*s++);
        if (c == c1) return s - 1;
        if (c == 0) return 0;
    }
}

int EnumerateProcessors(ProcessorEnumProc *f, void *arg) {
    Uint i;
    for (i = 0; i < sizeof processors / sizeof processors[0]; i++) {
        int rc = f(arg, processors[i]);
        if (rc != 0) return rc;
    }
    return 0;
}

static Processor const *LookupProcessor_i(char const *key, size_t keylen) {
    Uint i;
    const char *keyopts = strpbrk(key, "0123456789");
    const Processor *best = NULL;
    int bestval = 0;
    if (keyopts == NULL)
        keyopts = key + keylen;
    else
        keyopts = keyopts + strspn(keyopts, "0123456789");
    for (i = 0; i < sizeof processors / sizeof processors[0]; i++)
    {   /* match things like ARM700TDMI with ARM7TM */
        const char *matchend =
            strpbrk(processors[i]->name, "0123456789");
        size_t matchlen;
        if (matchend == NULL)
            matchlen = strlen(&processors[i]->name[1]);
        else
            matchlen = matchend - processors[i]->name;
        if (cistrneq(key, &processors[i]->name[1], matchlen))
        {   if (keyopts[0] == '\0' || keyopts[0] == '/')
            {   best = processors[i];
                break;
            }
            else
            {   bool matches = YES;
                const char *p = keyopts;
                const char *opts = &processors[i]->name[1] + matchlen;
                int matchval = 0;
                for (; p < key + keylen; ++p)
                {   int ch = safe_tolower(*p);
                    if (ch == 'd' || ch == 'i')
                        continue;
                    if (cistrchr(opts, ch) != NULL)
                        ++matchval;
                    else
                    {   matches = NO;
                        break;
                    }
                }
                if (!matches)
                    continue;
                if (bestval < matchval)
                {   bestval = matchval;
                    best = processors[i];
                }
            }
        }
    }
    return best;
}

Processor const *LookupProcessor(char const *key) {
  return LookupProcessor_i(key, strlen(key));
}

Processor const *LookupArchitecture(char const *key) {
    Uint i;
    for (i = 0; i < sizeof processors / sizeof processors[0]; i++)
        if (cistreq(processors[i]->arch+1, key)) return processors[i];
    return NULL;
}

bool mcdep_config_option(char name, char const tail[], ToolEnv *t)
{   char b[64];
    switch (safe_tolower(name)) {
#ifndef TARGET_IS_UNIX
    case 'm':
        {   int m = 1;
            if (isdigit(tail[0])) m += (tail[0]-'0');
            sprintf(b, "=%d", m);
            tooledit_insert(t, "-zm", b);
            return YES;
        }
#endif
    case 'a':
        if (tail[0] == '\0' || isdigit(tail[0])) {
            tooledit_insert(t, "-za", tail[0] == '0' ? "=0" : "=1");
            return YES;
        }
        break;

    case 'd':
        tooledit_insert(t, "-zd", tail[0] == '0' ? "=0" : "=1");
        return YES;

    case 'i':
        return tooledit_insertwithjoin(t, "-zi", '=', tail) != TE_Failed;

    case 'r':
        return tooledit_insertwithjoin(t, "-zr", '=', tail) != TE_Failed;
    }
    return NO;
}

typedef struct { char const *opt; char const *name; char const *val; } kw;

static kw const pcs_keywords[] = {
    { "reentrant",      "-apcs.reent",  "#/reent" },
    { "nonreentrant",   "-apcs.reent",  "#/noreent"},
    { "noreentrant",    "-apcs.reent",  "#/noreent"},
    { "reent",          "-apcs.reent",  "#/reent" },
    { "nonreent",       "-apcs.reent",  "#/noreent"},
    { "noreent",        "-apcs.reent",  "#/noreent"},
    { "fpe3",           "-apcs.fpis",   "#/fpe3"},
    { "fpe2",           "-apcs.fpis",   "#/fpe2"},
    { "swstackcheck",   "-apcs.swst",   "#/swst"},
    { "noswstackcheck", "-apcs.swst",   "#/noswst"},
    { "swst",           "-apcs.swst",   "#/swst"},
    { "noswst",         "-apcs.swst",   "#/noswst"},
    { "26bit",          "-apcs.32bit",  "#/26"},
    { "32bit",          "-apcs.32bit",  "#/32"},
    { "26",             "-apcs.32bit",  "#/26"},
    { "32",             "-apcs.32bit",  "#/32"},
    { "fpregargs",      "-apcs.fpr",    "#/fpregargs"},
    { "nofpregargs",    "-apcs.fpr",    "#/nofpregargs"},
    { "fpr",            "-apcs.fpr",    "#/fpregargs"},
    { "nofpr",          "-apcs.fpr",    "#/nofpregargs"},
    { "fp",             "-apcs.fp",     "#/fp"},
    { "nofp",           "-apcs.fp",     "#/nofp"},
    { "softfp",         "-apcs.softfp", "#/softfp"},
    { "softdoubles",    "-apcs.softfp", "#/softdoubles"},
    { "softd",          "-apcs.softfp", "#/softdoubles"},
    { "hardfp",         "-apcs.softfp", "#/hardfp"},
    { "interwork",      "-apcs.inter",  "#/interwork"},
    { "nointerwork",    "-apcs.inter",  "#/nointerwork"},
    { "inter",          "-apcs.inter",  "#/interwork"},
    { "nointer",        "-apcs.inter",  "#/nointerwork"},
    { "wide",           "-apcs.wide",   "#/wide"},
    { "narrow",         "-apcs.wide",   "#/narrow"}
};

static char const * const debug_table_keywords[] = {
#ifdef TARGET_HAS_ASD
    "-asd",
    "-asd-old",
#endif
#ifdef TARGET_HAS_DWARF
    "-dwarf1",
    "-dwarf2",
    "-dwarf",
#endif
    ""
};

KW_Status mcdep_keyword(char const *key, char const *nextarg, ToolEnv *t) {
    char str[64];
    int ch;
    unsigned i;
    bool sawproc = NO;

    if (cistreq(key, "-apcs")) {
        Uint count = 0;
        if (nextarg == NULL) return KW_MISSINGARG;
        if (nextarg[0] == '3') nextarg++;
        for (;; count++) {
            ch = *nextarg;
            i = 0;
            if (ch == 0) return (count == 0) ? KW_BADNEXT: KW_OKNEXT;
            if (ch != '/') return KW_BADARG;
            for (; (ch = *++nextarg) != '/' && ch != 0; )
                str[i++] = safe_tolower(ch);
            str[i] = 0;
            for (i = 0; i < sizeof(pcs_keywords) / sizeof(pcs_keywords[0]); i++)
                if (StrEq(str, pcs_keywords[i].opt)) {
                    tooledit_insert(t, pcs_keywords[i].name, pcs_keywords[i].val);
                    break;
                }
            if (i == sizeof(pcs_keywords) / sizeof(pcs_keywords[0]))
                return KW_BADNEXT;
        }
    }

    for (i = 0; i < sizeof(debug_table_keywords) / sizeof(debug_table_keywords[0]); i++)
        if (cistreq(key, debug_table_keywords[i])) {
            tooledit_insertwithjoin(t, ".debugtable", '=', debug_table_keywords[i]);
            return KW_OK;
        }

    if (cistreq(key, "-fpu")) {
        if (nextarg == NULL) return KW_MISSINGARG;
        if (cistreq(nextarg, "fpa")) {
            tooledit_insert(t, "-fpu", "#fpa");
            return KW_OKNEXT;
        } else if (cistreq(nextarg, "amp")) {
            tooledit_insert(t, "-fpu", "#amp");
            return KW_OKNEXT;
        }
        return KW_BADNEXT;
    }
    /* The '-proc' form is preferred since '-armxxx' is passed to the linker
       without complaint. */
    if (cistreq(key, "-arch")) {
        Uint i;
        if (nextarg == NULL) return KW_MISSINGARG;
        for (i = 0; i < sizeof processors / sizeof processors[0]; i++)
            if (cistreq(nextarg, &processors[i]->arch[1])) {
                tooledit_insert(t, "-cpu", "#generic");
                tooledit_insert(t, "-arch", processors[i]->arch);
                return KW_OKNEXT;
            }
        return KW_BADNEXT;
    } else if (cistreq(key, "-proc") || cistreq(key, "-processor") || cistreq(key, "-cpu")) {
        if (nextarg == NULL) return KW_MISSINGARG;
        sawproc = YES;
        key = nextarg;
    }
    else if (key[0] == '-')
        key = key + 1;
    else
        return KW_NONE;

    {   char const *sfx = strchr(key, '/');
        size_t keylen = (sfx == NULL) ? strlen(key) : sfx - key;
        Processor const *cpu = LookupProcessor_i(key, keylen);

        if (cpu == NULL) return sawproc ? KW_BADNEXT : KW_NONE;

        if (cpu->flags & PROCESSOR_HAS_HALFWORDS && sfx != NULL)
        {   if (cistreq(sfx + 1, "nohalfwordstores"))
                tooledit_insert(t, ".nohalfwordstores", "?");
            else
                return sawproc ? KW_BADNEXT : KW_BADARG;
        }
        else if (sfx != NULL)
            return sawproc ? KW_BADNEXT : KW_BADARG;

        tooledit_insert(t, "-cpu", cpu->name);
        return sawproc ? KW_OKNEXT : KW_OK;
    }
}

static char lib_variant[16];

void target_lib_variant(char *b) {
    strcpy(b, lib_variant);
}

#ifndef COMPILING_ON_ARM
char const *target_lib_name(ToolEnv *t, char const *name) {
    static char namebuf[64];
    int len = strlen(name);
    IGNORE(t);
    if (name[len-2] == '.' && name[len-1] == 'o') {
        memcpy(namebuf, name, len-2);
        target_lib_variant(&namebuf[len-2]);
        return namebuf;
    }
    return name;
}
#endif

char *target_asm_options(ToolEnv *t) {
  int i;
  static char v[32];
  config_init(t);
  strcpy(v, (config & CONFIG_BIG_ENDIAN) ? "-bi" : "-li");
  i = 3;
  if (pcs_flags & (PCS_REENTRANT+PCS_FPE3+PCS_CALLCHANGESPSR)) {
    if (i != 0) v[i++] = ' ';
    strcpy(&v[i], "-apcs 3");
    if (pcs_flags & PCS_REENTRANT) strcat(&v[i], "/reent");
    strcat(&v[i], (pcs_flags & PCS_CALLCHANGESPSR) ? "/32bit" : "/26bit");
  }
  return v;
}

    /*************************************************************/
    /*                                                           */
    /*               Code to configure compiler for host system  */
    /*                                                           */
    /*************************************************************/

#if 0
#ifdef TARGET_HAS_DATA_VTABLES
bool mcdep_data_vtables(void)
{
    return !!(pcs_flags & PCS_INTERWORK);
}
#endif
#endif

typedef struct { char const *name; char const *val; uint32 flag; } Opt;

static Opt const config_opts[] = {
    {".bytesex",     "=-bi",        CONFIG_BIG_ENDIAN},
    {"-apcs.reent",  "#/reent",     CONFIG_REENTRANT_CODE},
    {"-apcs.softfp", "#/softfp",    CONFIG_SOFTWARE_FP},
    {"-apcs.softfp", "#/softdoubles", CONFIG_SOFTWARE_DOUBLES},
    {"-apcs.fpr",    "#/fpregargs", CONFIG_FPREGARGS},
    {"-apcs.wide",   "#/narrow",    CONFIG_UNWIDENED_NARROW_ARGS},
    {"-za",          "=1",          CONFIG_NO_UNALIGNED_LOADS},
    {"-zap",         "=1",          CONFIG_STRUCT_PTR_ALIGN},
    {NULL, NULL, 0}
};

static Opt const pcs_opts[] = {
    {"-apcs.32bit",  "#/32",        PCS_CALLCHANGESPSR},
    {"-apcs.swst",   "#/noswst",    PCS_NOSTACKCHECK},
    {"-apcs.reent",  "#/reent",     PCS_REENTRANT},
    {"-apcs.fpis",   "#/fpe3",      PCS_FPE3},
    {"-apcs.fp",     "#/nofp",      PCS_NOFP},
    {"-apcs.inter",  "#/interwork", PCS_INTERWORK},
    {"-zd",          "=1",          PCS_ACCESS_CONSTDATA_WITH_ADR},
    {NULL, NULL, 0}
};

void config_init(ToolEnv *t)
{
    Uint i;
    config = 0;
    if (TE_HasValue(t, "-apcs.softfp", "#/hardfp") &&
        TE_HasValue(t, "-fpu", "#amp"))
        config |= CONFIG_SOFTWARE_DOUBLES;

    for (i = 0; config_opts[i].name != NULL; i++)
        if (TE_HasValue(t, config_opts[i].name, config_opts[i].val))
            config |= config_opts[i].flag;

    arthur_module = 0;

    integer_load_max = TE_Integer(t, "-zi", INTEGER_LOAD_MAX_DEFAULT);
    ldm_regs_max = TE_Integer(t, "-zr", LDM_REGCOUNT_MAX_DEFAULT);

    {   char const *arch = toolenv_lookup(t, "-arch");
        char const *cpu = toolenv_lookup(t, "-cpu");
        Processor const *proc = NULL;
        if (TE_HasValue(t, ".nohalfwordstores", "?")) config |= CONFIG_NO_HALFWORD_STORES;

        /* architecture dependent configuration */
        if (arch != NULL) proc = LookupArchitecture(arch + 1);   /* skip the '#' */
        if (proc != NULL)
        {
            if (proc->flags & PROCESSOR_HAS_HALFWORDS) config |= CONFIG_HALFWORD_SPT;
            if (proc->flags & PROCESSOR_HAS_MULTIPLY) config |= CONFIG_LONG_MULTIPLY;
            if (proc->flags & PROCESSOR_HAS_32BIT_MODE) config |= CONFIG_32BIT;
            if (proc->flags & PROCESSOR_HAS_26BIT_MODE) config |= CONFIG_26BIT;
        }

        /* processor dependent configuration */
        if (cpu != NULL) proc = LookupProcessor(cpu + 1);
        config_mulbits = (proc != NULL) ? proc->mulbits : 0;
        config_multime = (proc != NULL) ? proc->multime : 0;
        config_mlatime = (proc != NULL) ? proc->mlatime : 0;
    }

    pcs_flags = 0;

    for (i = 0; pcs_opts[i].name != NULL; i++)
        if (TE_HasValue(t, pcs_opts[i].name, pcs_opts[i].val))
            pcs_flags |= pcs_opts[i].flag;

    {   char const *fpuname = toolenv_lookup(t, "-fpu");
        fpu_type = (StrEq(fpuname, "#amp")) ? fpu_amp : fpu_fpa;
    }
    dbg_setformat(toolenv_lookup(t, ".debugtable"));

    {   int bits;
        char v[8]; char *p = v;
        char *b = lib_variant;
        size_t vlen;
        if (!(config & CONFIG_SOFTWARE_FP)) {
          if (pcs_flags & PCS_FPE3)
            *p++ = (config & CONFIG_FPREGARGS) ? 'r' : 'h';
          else
            *p++ = (config & CONFIG_FPREGARGS) ? 'z' : '2';
        }
        if (pcs_flags & PCS_INTERWORK) {
            if (!(pcs_flags & PCS_NOSTACKCHECK)) *p++ = 's';
            *p++ = 'i';
            bits = 16;
        } else {
            if (pcs_flags & PCS_NOSTACKCHECK) *p++ = 'c';
            if (pcs_flags & PCS_CALLCHANGESPSR)
                bits = 32;
            else
                bits = 26;
            if (pcs_flags & PCS_NOFP) *p++ = 'n';
        }
        if (pcs_flags & PCS_REENTRANT) *p++ = 'e';
        vlen = p - v;
        if (vlen != 0) {
            *b++ = '_';
            memcpy(b, v, vlen);
            b += vlen;
        }
        sprintf(b, ".%d%c", bits, (config & CONFIG_BIG_ENDIAN) ? 'b' : 'l');
    }
}

void mcdep_set_options(ToolEnv *t) {
    IGNORE(t);
}


/********************************************************************************************/

#include "jopcode.h"
#include "mcdpriv.h"
#include "armops.h"
#include "aeops.h"
#include "inlnasm.h"
#include "flowgraf.h"

static uint32 movc_workregs1(Icode const *ic);


int32 a_loads_r1(PendingOp const* const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    if (op <= J_LAST_JOPCODE) return loads_r1(op);
    return a_attributes(op) & _a_set_r1;
}

int32 a_reads_r1(PendingOp const* const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    if (op <= J_LAST_JOPCODE)
        return reads_r1(op);
    return a_attributes(op) & _a_read_r1;
}

int32 a_uses_r1(PendingOp const* const p)
{
    return a_reads_r1(p) || a_loads_r1(p);
}

int32 a_loads_r2(PendingOp const* const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    if (p->peep & (P_PRE | P_POST)) return YES;
    if (op <= J_LAST_JOPCODE) return loads_r2(op);
    return (a_attributes(op) & _a_set_r2);
}

int32 a_reads_r2(PendingOp const* const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    if (op <= J_LAST_JOPCODE)
        return reads_r2(op);
    return a_attributes(op) & _a_read_r2;
}

int32 a_uses_r2(PendingOp const* const p)
{
    return a_reads_r2(p) || a_loads_r2(p);
}

int32 a_uses_r3(PendingOp const* const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    if (op <= J_LAST_JOPCODE) return reads_r3(op);
    return a_attributes(op) & _a_read_r3;
}

int32 a_uses_r4(PendingOp const* const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    if (p->peep & P_RSHIFT) return YES;
    if (op <= J_LAST_JOPCODE) return reads_r4(op);
    return (a_attributes(op) & _a_read_r4);
}

int32 a_uses_mem(PendingOp const* const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    if (op <= J_LAST_JOPCODE) return reads_mem(op) || writes_mem(op);
    return a_attributes(op) & (_a_modify_mem+_a_read_mem);
}

int32 a_modifies_mem(PendingOp const* const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    if (op <= J_LAST_JOPCODE) return writes_mem(op);
    return a_attributes(op) & _a_modify_mem;
}

int32 a_uses_stack(PendingOp const* const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    if (op <= J_LAST_JOPCODE) return uses_stack(op);
    return a_attributes(op) & _a_uses_stack;
}


/* Spot the differences between the next 4 functions! */

bool corrupts_r1(Icode const* ic)
{   J_OPCODE op = ic->op & J_TABLE_BITS;
    switch (op)
    {
        case J_MOVC:
        case J_CLRC:
            return 4*bitcount(movc_workregs1(ic)) < ic->r3.i;
        default:
            return NO;
    }
}

bool corrupts_r2(Icode const* ic)
{   J_OPCODE op = ic->op & J_TABLE_BITS;
    switch (op)
    {
        case J_MOVC:
            return 4*bitcount(movc_workregs1(ic)) < ic->r3.i;
        default:
            return NO;
    }
}

bool a_corrupts_r1(PendingOp const* p)
{   J_OPCODE op = p->ic.op & J_TABLE_BITS;
    switch (op)
    {
        case J_PUSHC:
            return NO;      /* PUSHC always pre decrements r1 */
        case J_MOVC:
        case J_CLRC:
            return 4*bitcount(movc_workregs1(&p->ic)) < p->ic.r3.i;
        default:
            return NO;
    }
}

bool a_corrupts_r2(PendingOp const* p)
{   J_OPCODE op = p->ic.op & J_TABLE_BITS;
    switch (op)
    {
        case J_PUSHC:
            return YES;
        case J_MOVC:
            if (p->peep & P_POST) return NO;    /* MOVC has optional post increment */
            if (!(p->dataflow & J_DEAD_R2) &&
                    4*bitcount(movc_workregs1(&p->ic)) >= p->ic.r3.i)
                return NO;
            return 4*bitcount(movc_workregs1(&p->ic)) + 4 < p->ic.r3.i;
        default:
            return NO;
    }
}

bool sets_psr(Icode const *ic)
{
    J_OPCODE op = ic->op & J_TABLE_BITS;
    if (is_compare(op))
        return YES;
#ifdef ARM_INLINE_ASSEMBLER
    if ((op == J_MSR || op == J_MSK) ||
        (ic->flags & SET_CC) ||
        ((op == J_BL || op == J_SWI) && (ic->r3.i & regbit(R_PSR))))
        return YES;
#endif
    if (op == J_CALLK && ic->r2.i & K_RESULTINFLAGS)
        return YES;
    return NO;
}

bool reads_psr(Icode const* ic)
{
    J_OPCODE op = ic->op & J_TABLE_BITS;
    PendingOp p;

    if (is_asminstr(op))
    {   p.ic = *ic;
        p.peep = 0;
        translate_asm_instr(&p);
        ic = &p.ic;
        op = ic->op & J_TABLE_BITS;
    }
    if (op == J_B && ic->op & Q_MASK != 0)
        return YES;
    if (op == J_ADCR || op == J_ADCK || op == J_SBCR || op == J_SBCK ||
        op == J_RSCR || op == J_RSCK)
        return YES;
#ifdef ARM_INLINE_ASSEMBLER
    if (op == J_MRS || ((op == J_BL || op == J_SWI) && (ic->r2.i & regbit(R_PSR))))
        return YES;
#endif
    if ((ic->op >> J_SHIFTPOS) & J_SHIFTMASK == SHIFT_ARITH + 0) /* ASR 0 = RRX, uses carry */
        return YES;
    return NO;
}

bool uses_psr(Icode const *ic)
{
    return sets_psr(ic) || reads_psr(ic);
}


bool corrupts_psr(Icode const *ic)
{
    J_OPCODE op = ic->op & J_TABLE_BITS;
    if (op == J_CASEBRANCH)
        return YES;
    if ((op == J_MOVC || op == J_CLRC || op == J_PUSHC) && ic->r3.i > MOVC_LOOP_THRESHOLD)
        return YES;
    if (op == J_OPSYSK && (var_cc_private_flags & 512L))
        return YES;
    if ((op == J_CALLR || op == J_CALLI) && (pcs_flags & PCS_CALLCHANGESPSR))
        return YES;
    if (op == J_CALLK)
    {
        if (ic->r2.i & K_RESULTINFLAGS)
            return NO;
        return (pcs_flags & PCS_CALLCHANGESPSR);
    }
    return NO;
}


/* MOVC/CLRC/PUSHC are weird instructions:
 *
 * MOVC dst, src, #N
 *   src may be SP, in which case the POST bit must be set (SP updated)
 * PUSHC SP, src, #N
 *   implies writeback to SP (thus a_loads_r1) and corrupts src.
 * CLRC dst, #N
 *
 * src is not corrupted if
 *   MOVC from SP (POST), or
 *   N <= 4*bitcount(freeregs), or
 *   dst dead and N-4 <= 4*bitcount(freeregs)
 *
 * dst is not corrupted if
 *   PUSHC, or
 *   N <= 4*bitcount(freeregs) - in gen.c
 */

static uint32 movc_workregs1(Icode const *ic)
{ /* p->op  is known to be one of CLRC, MOVC or PUSHC */
    uint32 set = regbit(R_A4) | regbit(R_IP);
    if (ic->r3.i > MOVC_LOOP_THRESHOLD)
        set |= regbit(R_A2) | regbit(R_A3);
    return set | ic->r4.i;
}

uint32 movc_workregs(PendingOp const *p)
{ /* p->op  is known to be one of CLRC, MOVC or PUSHC */
    uint32 set = movc_workregs1(&p->ic);
    /* Always preserve the store (&load for MOVC) addresses,
     * as gen.c can use writeback.
     */
    set &= ~(regbit(p->ic.r1.rr));
    if ((p->ic.op & ~J_ALIGNMENT) != J_CLRC)  /* MOVC or PUSHC */
        set &= ~regbit(p->ic.r2.rr);
    return set;
}

bool movc_preserving_r1r2(PendingOp const *p, bool dead_r2)
{
    int32 op = p->ic.op & ~J_ALIGNMENT;
    if (op == J_PUSHC) return NO;
    {   int32 workregs = movc_workregs(p);
        int32 workcount = 4*bitcount(workregs);
        if (op != J_CLRC && dead_r2)
            return p->ic.r3.i <= workcount + 4;
        else
            return p->ic.r3.i <= workcount;
    }
}


static uint32 GetUsedRegs(Binder *b)
{
    Symstr *s = (h0_(b) == s_binder) ? bindsym_(b) : (Symstr *) b;
    uint32 volatile_regs = regbit(R_IP) | reglist(R_A1, NARGREGS) | reglist(R_F0, NFLTARGREGS);
    /* The code below is because of the fact that there are 2 different representations
     * of binders, depending of whether you are pre or post regalloc.
     * This code tries to find out in which stage we are...
     * Note that symext_(sym) might not be initialized.
     */

    if (var_cc_private_flags & 1024L)   /* usedregs optimization disabled */
        return volatile_regs;
    return (symext_(s) != NULL) ? symext_(s)->usedregs.map[0] : volatile_regs;
}


static uint32 resultregs(Icode const * ic)  /* pre: iscall_(ic) */
{   /* return result registers including the default result reg */
    if (k_resultregs_(ic->r2.i) == 0) return regbit(ic->r1.r);  /* 0 means 1 result!!! */
    /* > 0 means N results, starting from R_A1 */
    return reglist(R_A1, R_A1 + k_resultregs_(ic->r2.i));
}


static uint32 argumentregs(uint32 argdesc)
{   uint32 regs;
    regs = reglist(R_A1, k_intregs_(argdesc));
    regs |= reglist(R_F0, k_fltregs_(argdesc));
    if (argdesc & K_SPECIAL_ARG)
        regs |= regbit(TARGET_SPECIAL_ARG_REG);
    return regs;
}


bool UnalignedLoadMayUse(RealRegister r)
{
    return r == R_IP || r == R_A1+3;
}


int32 MaxMemOffset(J_OPCODE op)
{
    switch (j_memsize(op))
    {
        case MEM_B:
            return (target_has_halfword_support &&
                (op & J_SIGNED) != 0) ? 255 : 4095;
        case MEM_W:
            return (target_has_halfword_support &&
                (op & J_ALIGNMENT) != J_ALIGN1) ? 254 : 4094;
        case MEM_I:
            return 4092;
        case MEM_F:
        case MEM_D:
            return 1020;
        case MEM_LL:
            return 0;
    }

    return 0;
}


int32 MinMemOffset(J_OPCODE op)
{
    return -MaxMemOffset(op);
}


int32 MemQuantum(J_OPCODE op)
{
    if ((op & J_ALIGNMENT) == J_ALIGN1)
        return 1;
    switch (j_memsize(op))
    {
        case MEM_B:
            return 1;
        case MEM_W:
            return 2;
        case MEM_I:
        case MEM_F:
        case MEM_D:
        case MEM_LL:
            return 4;
    }

    return 4;
}


static bool OverlargeMemOffset(const Icode *ic)
{
    int32 maxoffset, offset;

    if (reads_r3(ic->op))               /* filter out LDRxRs */
        return NO;

    maxoffset = MaxMemOffset(ic->op);
    if (uses_stack(ic->op))
    {
        if ((bindaddr_(ic->r3.b) & BINDADDR_MASK) == BINDADDR_ARG)
        {   /* argument */
            if (pcs_flags & PCS_NOFP)
                offset = max_argsize + greatest_stackdepth + TARGET_MAX_FRAMESIZE;
            else
                offset = max_argsize + 4;
        }
        else
        {   /* local variable */
            if (pcs_flags & PCS_NOFP)
                offset = greatest_stackdepth;
            else
                offset = greatest_stackdepth + TARGET_MAX_FRAMESIZE +
                    NARGREGS * 4 + NFLTARGREGS * 12;   /* WD: should use sizeof macro */
        }
        return offset > maxoffset;
    }
    else
        return ic->r3.i < -maxoffset || ic->r3.i > maxoffset;
}


void RealRegisterUse(const Icode *ic, RealRegUse *u)
{
    uint32 use = 0, def = 0, c_in = 0, c_out = 0;

    switch (ic->op & (J_TABLE_BITS | J_ALIGNMENT))
    {
        case J_MOVC+J_ALIGN4:
        case J_CLRC+J_ALIGN4:
        case J_PUSHC+J_ALIGN4:
            c_in = c_out = movc_workregs1(ic);
            /* Clear out the input registers after register allocation
             * if they are corrupted. This is to prevent gen.c to syserr
             * if the input registers and corrupted inputs overlap...
             */
            if (isany_realreg_(ic->r1.r))
                c_in &= ~regbit(ic->r1.rr);
            if (isany_realreg_(ic->r2.r))
                c_in &= ~regbit(ic->r2.rr);
            break;

        case J_LDRK+J_ALIGN1:
        case J_LDRVK+J_ALIGN1:
            c_out = regbit(R_IP) | regbit(R_A4);
            break;

        case J_STRK+J_ALIGN1:
        case J_STRVK+J_ALIGN1:
            c_in = regbit(R_IP);
            break;

        case J_LDRWK+J_ALIGN1:
        case J_LDRWVK+J_ALIGN1:
            c_out = regbit(R_IP);
            break;

        case J_STRWR+J_ALIGN2:
        case J_LDRWR+J_ALIGN2:
            if (target_has_halfword_support)
            {
                if ((ic->op & J_SHIFTMASK) != 0)
                    c_in = regbit(R_IP);
            }
            else if (config & CONFIG_NO_UNALIGNED_LOADS)
            {
                c_in  = regbit(R_IP);
                c_out = regbit(R_IP);
            }
            break;

        case J_LDRBR+J_ALIGN1:
            if (target_has_halfword_support && (ic->op & J_SIGNED) &&
                (ic->op & J_SHIFTMASK))
                c_in = regbit(R_IP);
            break;

        case J_COUNT:
            c_in  = regbit(R_LR);
            c_out = regbit(R_IP);
            break;
        case J_PUSHM:
            def = regbit(R_SP);
            use = regbit(R_SP) | ic->r3.i;
            break;
        case J_POPMB:
            use = regbit(R_SP);
            def = regbit(R_SP) | ic->r3.i;
            break;
        /* WD: PUSHR & PUSHL seem unused??? */
        case J_PUSHD:
        case J_PUSHF:
            use = def = regbit(R_SP);
            break;
        case J_MOVDIM:
        case J_MOVIDM:
            use = ic->r3.i;
            def = ic->r1.i;
            break;
#ifdef ARM_INLINE_ASSEMBLER
        case J_LDM:
        case J_LDMW:
            def = ic->r3.i;
            break;
        case J_STM:
        case J_STMW:
            use = ic->r3.i;
            break;
        case J_SWI:
        case J_BL:
            use = ic->r2.i;
            def = ic->r3.i;
            c_out = ic->r4.i;
            break;
        case J_ABINRK:
        {
            uint32 op = OPCODE(ic->flags);

            if ((ic->flags & SET_CC) && (op == A_ADD || op == A_SUB || op == A_ADC ||
                op == A_SBC || op == A_RSB || op == A_RSC))
                    c_in = regbit(R_IP);
            if (ic->flags & SET_PSR)             /* TEQP & TSTP */
                c_in = regbit(R_IP);
            break;
        }
        case J_ACMPK:
            if (ic->flags & (SET_CC | SET_PSR))
                c_in = regbit(R_IP);
            break;
#endif
        case J_OPSYSK:
            use = argumentregs(ic->r2.i);
            def = resultregs(ic);
            if (feature & FEATURE_INLINE_CALL_KILLS_LINKREG) c_in |= M_LR;
            c_out = reglist(R_A1, NARGREGS) | reglist(R_F0, NFLTARGREGS);
            c_out &= ~resultregs(ic);
            break;

        case J_CALLK:
        {
            uint32 usedregs = GetUsedRegs(ic->r3.b);
            uint32 volatile_regs = regbit(R_IP) | reglist(R_A1, NARGREGS) | reglist(R_F0, NFLTARGREGS);

            use = argumentregs(ic->r2.i);
            def = resultregs(ic);
            if (ic->r2.i & K_RESULTINFLAGS)
                def |= regbit(R_PSR);
            c_in = regbit(R_LR);
            c_out = (usedregs & volatile_regs) & ~resultregs(ic);
            break;
        }

        case J_CALLR:
        case J_CALLX:
        case J_CALLI:
        case J_CALLXR:
        case J_CALLIR:
            use = argumentregs(ic->r2.i);
            def = resultregs(ic);
            c_in = regbit(R_LR);
            c_out = regbit(R_IP) | reglist(R_A1, NARGREGS) | reglist(R_F0, NFLTARGREGS);
            c_out &= ~resultregs(ic);
            break;

        case J_TAILCALLK:
        case J_TAILCALLR:
        case J_TAILCALLX:
        case J_TAILCALLI:
        case J_TAILCALLXR:
        case J_TAILCALLIR:
            use = argumentregs(ic->r2.i);
            def = 0;
            break;
        /* J_ENTER & J_SAVE have quite complex register usage. As they are currently not
         * used in neither register allocation nor peepholing, this isn't implemented yet.
         * BEWARE for changes in this!
         */
        case J_SAVE:
            break;
        case J_ENTER:
            def = argumentregs(ic->r3.i);
            break;
#ifdef RANGECHECK_SUPPORTED
        case J_CHKNEFR:
#endif
        case J_CMPFR:
            if (fpu_type == fpu_amp) c_out = regbit(R_IP);
            break;

#ifdef RANGECHECK_SUPPORTED
        case J_CHKLK:
        case J_CHKUK:
        case J_CHKNEK:
#endif
        case J_CASEBRANCH:
        case J_CMPK:
            if (Arm_EightBits(ic->r3.i) < 0 && Arm_EightBits(-(ic->r3.i)) < 0)
                c_in = regbit(R_IP);
            break;

        case J_MULK:
            if (MultiplyNeedsWorkreg(ic->r3.i))
                c_in = regbit(R_IP);
            break;

        case J_FIXFR:
            if (fpu_type == fpu_amp)
            {
                c_in  = regbit(R_IP);
                c_out = regbit(R_IP);
            }
            break;

        case J_ADCON:
            if (arthur_module != 0)
                c_in = regbit(R_IP);
            break;

        case J_B:
            if ((LabelNumber*) ic->r3.b == RETLAB)
            {
                if (currentfunction.nresultregs <= 1)
                    use = regbit(currentfunction.baseresultreg);
                else
                    use = regbit(currentfunction.nresultregs) - regbit(R_A1);
            }
            break;

        default:
            break;
    }

    if ((ic->op & J_TABLE_BITS) < J_LAST_JOPCODE && j_is_ldr_or_str(ic->op)
        && OverlargeMemOffset(ic))
        c_in |= regbit(R_IP);

    u->use.map[0] = use;
    u->def.map[0] = def;
    u->c_in.map[0] = c_in;
    u->c_out.map[0] = c_out;
}


bool has_side_effects(Icode const *ic)
{
    J_OPCODE op = ic->op & J_TABLE_BITS;
    if (writes_mem(op)) return YES;
    if (op == J_NULLOP || op == J_MCR || op == J_MRC || op == J_CDP ||
        op == J_LDC || op == J_LDCW || op == J_STC || op == J_STCW ||
        op == J_BL || op == J_SWI)
        return YES;
    return NO;
}


char *CheckJopcode(const Icode *ic, CheckJopcode_flags flags)
{
    PendingOp p;
    p.ic = *ic;
    p.peep = 0;
    p.dataflow = p.ic.op & J_DEADBITS;
    p.cond = p.ic.op & Q_MASK;
    return CheckJopcodeP(&p, flags);
}


char *CheckJopcodeP(const PendingOp *p, CheckJopcode_flags flags)
{
    char *errmsg = NULL;
    const Icode *ic = &p->ic;

    /* Check alignment of memory instructions */
    if ((flags & JCHK_MEM) &&
        (ic->op & J_TABLE_BITS) < J_LAST_JOPCODE && j_is_ldr_or_str(ic->op))
    {
        if (!reads_r3(ic->op) && !uses_stack(ic->op))   /* LDRK/STRK */
        {
            if (ic->r3.i & (MemQuantum(ic->op) - 1))
                errmsg = "alignment error";
        }
        if ((ic->op & J_ALIGNMENT) == J_ALIGN1 && OverlargeMemOffset(ic))
        {
            if ((j_memsize(ic->op) == MEM_W && writes_mem(ic->op)) ||
                j_memsize(ic->op) == MEM_I)
                errmsg = "unaligned LDR/STR offset out of range";
        }
    }

    /* Check register numbers, usage, clashes and deadbits */
    if (flags & JCHK_REGS)
    {
        bool fault = NO;
        RegisterUsage u;

        /* Consistency check on deadbits */
        if (!a_uses_r1(p) && p->dataflow & J_DEAD_R1) fault = YES;
        if (!a_uses_r2(p) && p->dataflow & J_DEAD_R2) fault = YES;
        if (!a_uses_r3(p) && p->dataflow & J_DEAD_R3) fault = YES;
        if (!a_uses_r4(p) && p->dataflow & J_DEAD_R4) fault = YES;
        if (fault)
            errmsg = "corrupted deadbits";
        /* Consistency check on physical register numbers */
        fault = NO;
        if (a_uses_r1(p) && (uint32)p->ic.r1.rr >= 24) fault = YES;
        if (a_uses_r2(p) && (uint32)p->ic.r2.rr >= 24) fault = YES;
        if (a_uses_r3(p) && (uint32)p->ic.r3.rr >= 24) fault = YES;
        if (a_uses_r4(p) && (uint32)p->ic.r4.rr >= 24) fault = YES;
        if (fault)
            errmsg = "illegal register number";
        if (GetRegisterUsage(p, &u))
            errmsg = "corrupted register";

        fault = NO;
        switch (ic->op)
        {
            case J_MULR:
            case J_MLAR:
                if (p->ic.r1.r == p->ic.r3.r) fault = YES;
                break;

            case J_MULL:
            case J_MLAL:
                if (p->ic.r1.r == p->ic.r2.r) fault = YES;
                if (p->ic.r1.r == p->ic.r3.r) fault = YES;
                if (p->ic.r2.r == p->ic.r3.r) fault = YES;
                break;

#ifdef ARM_INLINE_ASSEMBLER
            case J_SWP:
            case J_SWPB:
                if (p->ic.r1.r == p->ic.r3.r) fault = YES;
                if (p->ic.r2.r == p->ic.r3.r) fault = YES;
                break;

            case J_LDMW:
                if (regbit(p->ic.r1.r) & p->ic.r3.i) fault = YES;
                break;
#endif
        }
        if (fault)
            errmsg = "register clash";
    }

    if ((flags & JCHK_SYSERR) && errmsg != NULL)
    {
        if (strcmp(errmsg, "alignment error") != 0)
            syserr(errmsg);
        else
            cc_warn("illegal unaligned load or store access - use __packed instead");
    }
    return errmsg;
}


/* TODO remove writeback should be generalized into a backend function remove_jopcode()
   with the dead flags as inputs. This will return a NOOP, a modified instruction or
   the same instruction...
*/

void remove_writeback(Icode *ic)
/* Remove writeback from LDM/STM/LDR/STR/LDC/STC if possible */
{
    J_OPCODE op = ic->op & J_TABLE_BITS;

    if (op == J_LDMW || op == J_STMW)
    {
        ic->flags &= ~M_WB;
        ic->op -= J_LDMW - J_LDM;
    }
    else if (op == J_ALDRKW || op == J_ASTRKW)
    {   /* convert postindex to preindex of #0 if not LDRT/STRT */
        ic->op -= J_ALDRKW - J_ALDRK;
        if (ic->flags & M_TRANS)
            ic->r3.i = 0;
        else
        {   ic->flags &= ~M_WB;
            if (!(ic->flags & M_PREIDX))
            {
                ic->flags |= M_PREIDX;
                ic->r3.i = 0;
            }
        }
    }
    else if (op == J_ALDRRW || op == J_ASTRRW)
    {   /* convert postindex reg to preindex of #0 if not LDRT/STRT */
        if (ic->flags & M_TRANS)
        {   ic->flags = (ic->flags & ~RN_OPND_MASK) | RN_CONST;
            ic->op -= J_ALDRRW - J_ALDRK;
            ic->r3.i = 0;
        }
        else
        {   ic->flags &= ~M_WB;
            ic->op -= J_ALDRRW - J_ALDRR;
            if (!(ic->flags & M_PREIDX))
            {   ic->flags = (ic->flags & ~RN_OPND_MASK) | RN_CONST;
                ic->op -= J_ALDRR - J_ALDRK;
                ic->flags |= M_PREIDX;
                ic->r3.i = 0;
            }
        }
    }
    else if (op == J_LDCW || op == J_STCW)
    {
        ic->op -= J_LDCW - J_LDC;
        ic->flags &= ~M_WB;
        /* do NOT convert postindex to preindex (Piccolo) */
    }
    if (debugging(DEBUG_REGS) && op != ic->op & J_TABLE_BITS)
        print_xjopcode(ic, "-> Removed writeback");
}

/* Returns the register usage of a pendingop. Returns true if the register usage
 * is incorrect (where inputs or outputs are being corrupted).
 */

bool GetRegisterUsage(const PendingOp *c, RegisterUsage *u)
{   RealRegUse usage;
    bool corrupted = NO;

    u->use = u->def = u->corrupt = u->dead = 0;

    if (a_loads_r1(c))
        u->def |= regbit(c->ic.r1.rr);
    if (a_loads_r2(c))
        u->def |= regbit(c->ic.r2.rr);
    if (sets_psr(&c->ic) || (c->peep & P_CMPZ))
        u->def |= regbit(R_PSR);

    if (a_corrupts_r1(c))
        u->corrupt |= regbit(c->ic.r1.rr);
    if (a_corrupts_r2(c))
        u->corrupt |= regbit(c->ic.r2.rr);
    if (corrupts_psr(&c->ic))
        u->corrupt |= regbit(R_PSR);

    if (a_reads_r1(c))
        u->use |= regbit(c->ic.r1.rr);
    if (a_reads_r2(c))
        u->use |= regbit(c->ic.r2.rr);
    if (a_uses_r3(c))
        u->use |= regbit(c->ic.r3.rr);
    if (a_uses_r4(c))
        u->use |= regbit(c->ic.r4.rr);
    if (reads_psr(&c->ic))
        u->use |= regbit(R_PSR);

    RealRegisterUse(&c->ic, &usage);
    u->use |= usage.use.map[0];
    u->def |= usage.def.map[0];
    if (u->use & usage.c_in.map[0])     /* inputs & corrupted inputs CANNOT overlap */
        corrupted = YES;
    if (u->def & usage.c_out.map[0])    /* output & corrupted output CANNOT overlap */
        corrupted = YES;
    /* corrupted inputs may overlap with definitions, hence we clear out the definitions */
    u->corrupt |= (usage.c_in.map[0] & ~u->def) | usage.c_out.map[0];

    if (c->dataflow & J_DEAD_R1)
        u->dead |= regbit(c->ic.r1.rr);
    if (c->dataflow & J_DEAD_R2)
        u->dead |= regbit(c->ic.r2.rr);
    if (c->dataflow & J_DEAD_R3)
        u->dead |= regbit(c->ic.r3.rr);
    if (c->dataflow & J_DEAD_R4)
        u->dead |= regbit(c->ic.r4.rr);
    u->dead &= ~u->def;         /* LDM R0, {R0} case - clear out all defined regs */
    if (a_loads_r1(c) && (c->dataflow & J_DEAD_R1)) /* ADD R0, R0, #1 case */
        u->dead |= regbit(c->ic.r1.rr);
    if (a_loads_r2(c) && (c->dataflow & J_DEAD_R2))
        u->dead |= regbit(c->ic.r2.rr);
    return corrupted;
}

bool arm_shiftop_allowed(int32 n, int32 m, int32 signedness, int32 op) {
    IGNORE(m);
    IGNORE(n);
    switch (op) {
    case J_LDRBK+J_ALIGN1: return signedness == J_UNSIGNED || !target_has_halfword_support;
    case J_LDRWK+J_ALIGN2: return !target_has_halfword_support;
    case J_LDRK+J_ALIGN4:  return YES;
    case J_LDRWK+J_ALIGN1:
    case J_LDRK+J_ALIGN1:  return NO;
    case J_LDRFK+J_ALIGN4:
    case J_LDRDK+J_ALIGN4:
    case J_LDRDK+J_ALIGN8: return NO;

    default:      return YES;
    }
}


int multiply_cycles(int val, bool accumulate)
{
    if (config_mulbits == 0)
        return 4;                                   /* guess an average multiply time */
    if (val < 0 && config_mulbits >= 8) val = -val;
    return (accumulate ? config_mlatime : config_multime) +
            logbase2(val) / config_mulbits;
}


/* end of arm/mcdep.c */
