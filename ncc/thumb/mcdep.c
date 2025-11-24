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

#include "toolenv.h"
#include "toolenv2.h"
#include "tooledit.h"

int arthur_module;
int32 config;
int32 pcs_flags;

#ifdef TARGET_IS_HELIOS
int in_stubs;
#endif

typedef struct {
  char const *name;
  char const *val;
} EnvItem;

#define str(s) #s
#define xstr(s) str(s)

static EnvItem const builtin_defaults[] = {
  { "-cpu", "#ARM7TM"},
  { "-arch", "#4T" },

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
#if (PCS_DEFAULTS & PCS_INTERWORK)
  { "-apcs.inter", "#/interwork"},
#else
  { "-apcs.inter", "#/nointerwork"},
#endif
  { "-apcs.32bit", "#/32"},
  { "-apcs.softfp", "#/softfp"},
  { "-apcs.fpis", "#/fpe3"},
  { "-apcs.fp", "#/nofp"},
  { "-apcs.fpr", "#/nofpregargs"},

  { "-zr",  "=" xstr(LDM_REGCOUNT_MAX_DEFAULT) },
  { "-zi",  "=" xstr(INTEGER_LOAD_MAX_DEFAULT) },
  { "-zas", "=4" },

  { ".areaperfn", "=-z+o" },

#if (PCS_DEFAULTS & PCS_UNWIDENED_NARROW_ARGS)
  { "-apcs.wide", "#/narrow"},
#else
  { "-apcs.wide", "#/wide"},
#endif

#ifdef CPLUSPLUS
  { ".debugtable", "=-dwarf" },
#else
  { ".debugtable", "=-asd" },
#endif

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

static char *EqualString(char *b, char const *s) {
  b[0] = '=';
  strcpy(&b[1], s);
  return b;
}

bool mcdep_config_option(char name, char const tail[], ToolEnv *t)
{   char b[64];
    switch (safe_tolower(name)) {
#ifndef TARGET_IS_UNIX
#ifdef TARGET_IS_HELIOS
    case 'r':
        suppress_module = 1;
        return YES;
#else
    case 'm':
        {   int m = 1;
            if (isdigit(tail[0])) m += (tail[0]-'0');
            sprintf(b, "=%d", m);
            tooledit_insert(t, "-zm", b);
            return YES;
        }
#endif
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
        return tooledit_insert(t, "-zi", EqualString(b, tail)) != TE_Failed;

    case 'r':
        return tooledit_insert(t, "-zr", EqualString(b, tail)) != TE_Failed;
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
    { "interwork",      "-apcs.inter",  "#/interwork"},
    { "nointerwork",    "-apcs.inter",  "#/nointerwork"},
    { "inter",          "-apcs.inter",  "#/interwork"},
    { "nointer",        "-apcs.inter",  "#/nointerwork"},
    { "fpe3",           "-apcs.fpis",   "#/fpe3"},
    { "swstackcheck",   "-apcs.swst",   "#/swst"},
    { "noswstackcheck", "-apcs.swst",   "#/noswst"},
    { "swst",           "-apcs.swst",   "#/swst"},
    { "noswst",         "-apcs.swst",   "#/noswst"},
    { "32bit",          "-apcs.32bit",  "#/32"},
    { "32",             "-apcs.32bit",  "#/32"},
    { "nofpregargs",    "-apcs.fpr",    "#/nofpregargs"},
    { "nofpr",          "-apcs.fpr",    "#/nofpregargs"},
    { "nofp",           "-apcs.fp",     "#/nofp"},
    { "softfp",         "-apcs.softfp", "#/softfp"},
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
            tooledit_insert(t, ".debugtable", EqualString(str, debug_table_keywords[i]));
            return KW_OK;
        }

    return KW_NONE;

}

static char lib_variant[16];

void target_lib_variant(char *b) {
    strcpy(b, lib_variant);
}

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

static bool EnvHasValue(ToolEnv *t, char const *name, char const *val) {
    char const *tval = toolenv_lookup(t, name);
    return tval != NULL && StrEq(val, tval);
}

typedef struct { char const *name; char const *val; uint32 flag; } Opt;

static Opt const config_opts[] = {
    {".bytesex",     "=-bi",        CONFIG_BIG_ENDIAN},
    {"-apcs.reent",  "#/reent",     CONFIG_REENTRANT_CODE},
    {"-apcs.wide",   "#/narrow",    CONFIG_UNWIDENED_NARROW_ARGS},
    {NULL, NULL, 0}
};

static Opt const pcs_opts[] = {
    {"-apcs.swst",   "#/noswst",    PCS_NOSTACKCHECK},
    {"-apcs.reent",  "#/reent",     PCS_REENTRANT},
    {"-apcs.inter",  "#/interwork", PCS_INTERWORK},
    {"-zd",          "=1",          PCS_ACCESS_CONSTDATA_WITH_ADR},
    {NULL, NULL, 0}
};

void config_init(ToolEnv *t)
{
    Uint i;
    config = CONFIG_SOFTWARE_FP;

    for (i = 0; config_opts[i].name != NULL; i++)
        if (EnvHasValue(t, config_opts[i].name, config_opts[i].val))
            config |= config_opts[i].flag;

    integer_load_max = TE_Integer(t, "-zi", INTEGER_LOAD_MAX_DEFAULT);
    ldm_regs_max = TE_Integer(t, "-zr", LDM_REGCOUNT_MAX_DEFAULT);

    pcs_flags = PCS_SOFTFP | PCS_NOFP | PCS_CALLCHANGESPSR;

    for (i = 0; pcs_opts[i].name != NULL; i++)
        if (EnvHasValue(t, pcs_opts[i].name, pcs_opts[i].val))
            pcs_flags |= pcs_opts[i].flag;

    dbg_setformat(toolenv_lookup(t, ".debugtable"));

    {   char v[8]; char *p = v;
        char *b = lib_variant;
        size_t vlen;
        if (!(pcs_flags & PCS_NOSTACKCHECK)) *p++ = 's';
        if (pcs_flags & PCS_INTERWORK) *p++ = 'i';
        if (pcs_flags & PCS_REENTRANT) *p++ = 'e';
        vlen = p - v;
        if (vlen != 0) {
            *b++ = '_';
            memcpy(b, v, vlen);
            b += vlen;
        }
        sprintf(b, ".16%c", (config & CONFIG_BIG_ENDIAN) ? 'b' : 'l');
    }
}

void mcdep_set_options(ToolEnv *t) {
    IGNORE(t);
}

/**********************************************************************************/

#include "jopcode.h"
#include "mcdpriv.h"
#include "ops.h"
#include "aeops.h"
#include "inlnasm.h"
#include "flowgraf.h"
#include "simplify.h"

int32 a_loads_r1(const PendingOp *const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    return (op > J_LAST_JOPCODE) ? a_attributes(op) & _a_set_r1:
                                   loads_r1(op);
}

int32 a_uses_r1(const PendingOp *const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    return (op > J_LAST_JOPCODE) ?
             a_attributes(op) & (_a_set_r1 | _a_read_r1) :
             uses_r1(op);
}

int32 a_reads_r1(const PendingOp *const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    return (op > J_LAST_JOPCODE) ? a_attributes(p->ic.op) & _a_read_r1 :
                                   reads_r1(op);
}

int32 a_loads_r2(const PendingOp *const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    return (op > J_LAST_JOPCODE) ? a_attributes(op) & _a_set_r2:
                                   loads_r2(op);
}

int32 a_uses_r2(const PendingOp *const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    return (op > J_LAST_JOPCODE) ?
             a_attributes(op) & (_a_set_r2 | _a_read_r2) :
             uses_r2(op);
}

int32 a_reads_r2(const PendingOp *const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    return (op > J_LAST_JOPCODE) ? a_attributes(op) & _a_read_r2 :
                                   reads_r2(op);
}

int32 a_uses_r3(const PendingOp *const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    return (op > J_LAST_JOPCODE) ? a_attributes(op) & _a_read_r3 :
                                   uses_r3(op);
}

int32 a_uses_r4(const PendingOp *const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    return
        ((op > J_LAST_JOPCODE) ? a_attributes(op) & _a_read_r4 :
                                 uses_r4(op));
}

int32 a_uses_mem(const PendingOp *const p)
{
    J_OPCODE op = p->ic.op & J_TABLE_BITS;
    if (a_modifies_mem(p)) return YES;
    return (op) > J_LAST_JOPCODE ?
        a_attributes(op) & (_a_modify_mem | _a_read_mem) :
        j_is_ldr_or_str(op);
}

bool sets_psr(const Icode *ic)
{   J_OPCODE op = ic->op & J_TABLE_BITS;
    if (op == J_CMPR || op == J_MOVR || op == J_NEGR || op == J_NOTR ||
                (op == J_MOVK && ic->r3.i >= 0 && ic->r3.i < 256) ||
                op == J_SHRK || op == J_SHLK || op == J_RORK ||
                op == J_SHLR || op == J_SHRR || op == J_RORR || op == J_RORK ||
                op == J_SUBK || op == J_ADDK || op == J_CMPK || op == J_MULK ||
                op == J_ANDK || op == J_ORRK || op == J_EORK || op == J_ADDR ||
                op == J_SUBR || op == J_ANDR || op == J_ORRR || op == J_EORR ||
                op == J_MULR || op == J_BICR
#ifdef THUMB_INLINE_ASSEMBLER
             ||
                op == J_ADCK || op == J_ADCR || op == J_SBCK || op == J_SBCR ||
                op == J_TSTK || op == J_TSTR || op == J_CMNK || op == J_CMNR ||
                op == J_BICK || op == J_MVNR
#endif
                /* HACK: these two are here because they may otherwise generate
                   corrupt-register. Need to find out how/why.
                   SetSPEnv for example should not corrupt the PSR.
                */
                || op == J_CASEBRANCH || op == J_BXX || J_SETSPENV
                )
        return 1;
    if (op == J_CALLK && ic->r2.i & K_RESULTINFLAGS)
        return YES;

    return NO;
}

bool reads_psr(const Icode *ic)
{   J_OPCODE op = ic->op & J_TABLE_BITS;
/* WD: asm BL can be assumed to read the PSR as well */
/* TODO problem: some instructions don't modify the V or C bit, and should probably
   be regarded as reading the PSR. But for C generated code, flags from previous
   instr are NEVER used, so we have a problem here...
 */
    return ((op == J_B && ic->op & Q_MASK != 0)
#ifdef THUMB_INLINE_ASSEMBLER
        || op == J_ADCK || op == J_ADCR || op == J_SBCK || op == J_SBCR ||
           op == J_TSTK || op == J_TSTR ||
           ((op == J_BL || op == J_SWI) && (ic->r2.i & regbit(R_PSR)))
#endif
        );
}

bool uses_psr(const Icode *ic)
{   return reads_psr(ic) || sets_psr(ic);
}

bool corrupts_psr(const Icode *ic)
{   J_OPCODE op = ic->op & J_TABLE_BITS;
    /* Some operatons might set the PSR as a side-effect (eg. LDRx) */
    if (
               (op == J_MOVK && (ic->r3.i < 0 || ic->r3.i >= 256)) ||
                op == J_OPSYSK || op == J_CALLR ||op == J_CLRC ||
                op == J_LDRBK || op == J_LDRWK || op == J_LDRK ||
                op == J_STRBK || op == J_STRWK || op == J_STRK ||
                op == J_LDRBV || op == J_LDRWV || op == J_LDRV ||
                op == J_STRBV || op == J_STRWV || op == J_STRV ||
                op == J_LDRBVK || op == J_LDRWVK || op == J_LDRVK ||
                op == J_STRBVK || op == J_STRWVK || op == J_STRVK)
        return 1;
    if (op == J_CALLK)
    {
        if (ic->r2.i & K_RESULTINFLAGS)
            return NO;
        return (pcs_flags & PCS_CALLCHANGESPSR);
    }
    if (op == J_MOVC)
        return ic->r3.i > MOVC_LOOP_THRESHOLD;
    if (op == J_ADCON)
        return 1;
    return 0;
}

int32 a_modifies_mem(const PendingOp *const p)
{   J_OPCODE op = p->ic.op & J_TABLE_BITS;
    return (op & J_TABLE_BITS) > J_LAST_JOPCODE ? a_attributes(op) & _a_modify_mem :
                                writes_mem(op);
}

bool corrupts_r1(const Icode *ic)
{   uint32 op = ic->op & J_TABLE_BITS;
    return op == J_MOVC || op == J_CLRC;
}

bool corrupts_r2(const Icode *ic)
{   uint32 op = ic->op & J_TABLE_BITS;
    return op == J_MOVC;
}

bool a_corrupts_r1(PendingOp const* p)
{   J_OPCODE op = p->ic.op & J_TABLE_BITS;
    return op == J_MOVC || op == J_CLRC;
}

bool a_corrupts_r2(PendingOp const* p)
{   J_OPCODE op = p->ic.op & J_TABLE_BITS;
    return op == J_MOVC;
}

static bool OutputsClashWithIP(const Icode *const p)
{
    RealRegister r1, r2, mr;
    int32 m;

    r1 = p->r1.rr;
    r2 = p->r2.rr;
    mr = p->r3.rr;
    m = p->r3.i;
#if 0
    printf("op = %08x, r1 = %d, r2 = %d, m = %d\n", p->op & J_TABLE_BITS, r1, r2, m);
#endif
    switch (p->op & J_TABLE_BITS) {
        case J_RORK:
            return YES;
        case J_SETSPENV: {
            BindList *to, *from;
            Binder *b;
            int32 diff;

            from = p->r2.bl;
            to = p->r3.bl;
            diff = 0;
            while (from) {
                b = from->bindlistcar;
                diff += bindmcrep_(b) & MCR_SIZE_MASK;
                from = from->bindlistcdr;
            }
            while (to) {
                b = to->bindlistcar;
                diff -= bindmcrep_(b) & MCR_SIZE_MASK;
                to = to->bindlistcdr;
            }
            if (diff <= -512 || diff >= 512) return YES;
            return NO;
        }

        default:
            return NO;
    }
}

static bool InputsClashWithIP(const Icode *const p)
{
    RealRegister r1, r2, mr;
    int32 m;

    r1 = p->r1.rr;
    r2 = p->r2.rr;
    mr = p->r3.rr;
    m = p->r3.i;
#if 0
    printf("op = %08x, r1 = %d, r2 = %d, m = %d\n", p->op & J_TABLE_BITS, r1, r2, m);
#endif
    switch (p->op & J_TABLE_BITS) {
        case J_MOVC:
        case J_CLRC:
            return YES;

        case J_RORK:
        case J_ORRK:
        case J_EORK:
        case J_MULK:

        case J_CASEBRANCH:
            return YES;

        case J_SHRR:
        case J_SHLR:
        case J_RORR:
            return YES;

        case J_SUBK:
            m = -m;
        case J_ADDK:
            if (r2 == R_SP)
            {   if (r1 == R_SP)
                    return m <= -512 || m >= 512;
                return NO;
            }
            return m < -(2*255+7) || m > 2*255+7;
#ifdef THUMB_INLINE_ASSEMBLER
        case J_ADCK:
        case J_SBCK:
        case J_SBCR:
            return YES;
        case J_CMNK:
            return m > 0 || m < -255;
        case J_TSTK:
        case J_BICK:
            return YES;
#endif
        case J_SETSPGOTO:
        case J_SETSP: {
            int32 diff;

            diff = m - r2;
            return diff <= -512 || diff >= 512;
        }

        case J_ANDK:
            return power_of_two(m+1) == -1 && power_of_two(-m) == -1;

        case J_CMPK: return m < 0 || m > 255;

#ifdef THUMB_CPLUSPLUS
        case J_THUNKTABLE:
            return NO;
#endif

        default:
            return NO;
    }
}


static int32 movc_workregs1(const Icode * const ic)
{ /* p->op  is known to be one of CLRC, MOVC or PUSHC */
    int32 set = regbit(R_A4) | regbit(R_IP);    /* R_IP happens to be R_A4 */
    if (ic->r3.i > MOVC_LOOP_THRESHOLD)
        set |= regbit(R_A2) | regbit(R_A3);
    return set;
}

int32 movc_workregs(const PendingOp *const p)
{ /* p->op  is known to be one of CLRC, MOVC or PUSHC */
    int32 set = movc_workregs1(&p->ic) | p->ic.r4.rr;
    set &= ~regbit(p->ic.r1.rr);
    return set;
}

bool movc_preserving_r1r2(PendingOp *p, bool dead_r2)
{
    IGNORE(p); IGNORE(dead_r2);
    return NO;
}

#ifdef DEBUG_THUMB_CPLUSPLUS
int sanity_check_has_callr;
#endif


bool UnalignedLoadMayUse(RealRegister r)
{ /* Some cases use A2: we must be pessimistic, since the interface doesn't  */
  /* give enough information for us to know for certain.                     */
    return r == R_IP || r == R_A1+2;
}


int32 MaxMemOffset(J_OPCODE op)
{
    if ((op & J_ALIGNMENT) == J_ALIGN1)
        return uses_stack(op) ? 1020+31 : 31;
    switch (j_memsize(op))
    {
        case MEM_B:
            return (uses_stack(op) && reads_mem(op)) ? 1020 + 31 : 31;
        case MEM_W:
            return (uses_stack(op) && reads_mem(op)) ? 1020 + 62 : 62;
        case MEM_I:
            return uses_stack(op) ? 1020 : 124;
        case MEM_F:
        case MEM_D:
        case MEM_LL:
        default:   /* that was a complete enumeration, but keep the     */
                   /* compiler quiet.                                   */
            return 0;
    }
}


int32 MinMemOffset(J_OPCODE op)
{
    IGNORE(op);
    return 0;
}


int32 MemQuantum(J_OPCODE op)
{
    if ((op & J_ALIGNMENT) == J_ALIGN1)
        return 1;
    switch(j_memsize(op))
    {
        case MEM_B: return 1;
        case MEM_W: return 2;
        case MEM_I: return 4;
        case MEM_F:
        case MEM_D:
        case MEM_LL:
        default:   /* that was a complete enumeration, but keep the     */
                   /* compiler quiet.                                   */
                    return 4;
    }
}


static bool OverlargeMemOffset(const Icode *ic)
{
    int32 maxoffset, offset;
    J_OPCODE op = ic->op;

    if (reads_r3(ic->op))               /* filter out LDRxRs */
        return NO;

    /* turn a LDRK with SP as base back into LDRV - these have different offsets... */
    if (!uses_stack(op) && ic->r2.r == R_SP)
        op += J_STRV - J_STRK;
    maxoffset = MaxMemOffset(op);

    if (uses_stack(ic->op))
    {
        if ((bindaddr_(ic->r3.b) & BINDADDR_MASK) == BINDADDR_ARG)
        {   /* argument */
            offset = max_argsize + greatest_stackdepth + TARGET_MAX_FRAMESIZE;
        }
        else
        {   /* local variable */
            offset = greatest_stackdepth;
        }
        return offset > maxoffset;
    }
    else
        return ic->r3.i < 0 || ic->r3.i > maxoffset;
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


static uint32 resultregs(Icode const* ic)  /* pre: iscall_(ic) */
{   /* return result registers including the default result reg */
    if (k_resultregs_(ic->r2.i) == 0) return regbit(ic->r1.r);  /* 0 means 1 result!!! */
    return reglist(R_A1, k_resultregs_(ic->r2.i));              /* > 0 means N results */
}

static uint32 argumentregs(uint32 argdesc)
{   uint32 regs;
    regs = reglist(R_A1, k_intregs_(argdesc));
    if (argdesc & K_SPECIAL_ARG)
                regs |= regbit(TARGET_SPECIAL_ARG_REG);
    return regs;
}


void RealRegisterUse(const Icode *ic, RealRegUse *u)
{
    uint32 use = 0, def = 0, c_in = 0, c_out = 0;
    switch (ic->op & (J_TABLE_BITS | J_ALIGNMENT)) {
        case J_MOVC+J_ALIGN4:
        case J_CLRC+J_ALIGN4:
            c_in = movc_workregs1(ic);
            break;

        case J_LDRBV:
        case J_LDRBVK:
            if (ic->op & J_SIGNED)
                c_out |= regbit(R_IP);
            break;
        case J_LDRBK:
            if (ic->r2.r == R_SP && ic->op & J_SIGNED)
                c_out |= regbit(R_IP);
            if (ic->op & J_SIGNED)
                c_in |= regbit(R_IP);
            break;
        case J_LDRBR:
            if (ic->r2.r == R_SP)   /* is this possible (peephole)? */
                c_in |= regbit(R_IP);
            break;

        case J_STRBV:
        case J_STRBVK:
            c_in |= regbit(R_IP);
            break;
        case J_STRBK:
            if (ic->r2.r == R_SP)
                c_in |= regbit(R_IP);
            break;
        case J_STRBR:
            if (ic->r2.r == R_SP)   /* is this possible (peephole)? */
                c_in |= regbit(R_IP);
            break;

        case J_LDRWV+J_ALIGN1:
        case J_LDRWVK+J_ALIGN1:
            c_in |= regbit(R_IP);
            c_out |= regbit(R_IP);
            break;
        case J_LDRWK+J_ALIGN1:
            if (ic->r2.r == R_SP)
                c_in |= regbit(R_IP);
            c_out |= regbit(R_IP);
            break;
        case J_LDRWV+J_ALIGN2:
        case J_LDRWVK+J_ALIGN2:
            if (ic->op & J_SIGNED)
                c_out |= regbit(R_IP);
            break;
        case J_LDRWK+J_ALIGN2:
            if (ic->op & J_SIGNED)
                c_in |= regbit(R_IP);
            if (ic->r2.r == R_SP && ic->op & J_SIGNED)
                c_out |= regbit(R_IP);
            break;
        case J_LDRWR+J_ALIGN2:
            if (ic->r2.r == R_SP)   /* is this possible (peephole)? */
                c_in |= regbit(R_IP);
            break;

        case J_STRWV+J_ALIGN1:
        case J_STRWVK+J_ALIGN1:
            c_in |= regbit(R_IP) | regbit(R_A3);
            break;
        case J_STRWK+J_ALIGN1:
            c_in |= regbit(R_IP);
            if (ic->r2.r == R_SP)
                c_in |= regbit(R_A3);
            break;
        case J_STRWV+J_ALIGN2:
        case J_STRWVK+J_ALIGN2:
            c_in |= regbit(R_IP);
            break;
        case J_STRWK+J_ALIGN2:
            if (ic->r2.r == R_SP)
                c_in |= regbit(R_IP);
            break;
        case J_STRWR+J_ALIGN2:
            if (ic->r2.r == R_SP)
                c_in |= regbit(R_IP);
            break;

        case J_LDRK+J_ALIGN1:
        case J_LDRVK+J_ALIGN1:
            c_in |= regbit(R_A3);   /* IP may be used for r2 */
            c_out |= regbit(R_IP) | regbit(R_A3);
            break;
        case J_LDRV+J_ALIGN4:
        case J_LDRVK+J_ALIGN4:
            break;
        case J_LDRK+J_ALIGN4:
            break;
        case J_LDRR+J_ALIGN4:
            if (ic->r2.r == R_SP)
                c_in |= regbit(R_IP);
            break;

        case J_STRV+J_ALIGN1:       /* ??? */
        case J_STRVK+J_ALIGN1:
            c_in |= regbit(R_IP) | regbit(R_A3);
            break;
        case J_STRK+J_ALIGN1:
            c_in |= regbit(R_IP);
            if (ic->r2.r == R_SP)
                c_in |= regbit(R_A3);
            break;
        case J_STRV+J_ALIGN4:
        case J_STRVK+J_ALIGN4:
            break;
        case J_STRK+J_ALIGN4:
            break;
        case J_STRR+J_ALIGN4:
            if (ic->r2.r == R_SP)
                c_in |= regbit(R_IP);
            break;

        case J_PUSHM:
            def = regbit(R_SP);
            use = regbit(R_SP) | ic->r3.i;
            break;
#ifdef THUMB_INLINE_ASSEMBLER
        case J_LDM:
        case J_LDMW:
            def |= ic->r3.i;
            break;
        case J_STM:
        case J_STMW:
            use |= ic->r3.i;
            break;
        case J_SWI:
        case J_BL:
            use  = ic->r2.i;
            def = ic->r3.i;
            c_out = ic->r4.i;
            break;
#endif
        case J_OPSYSK:
            use = argumentregs(ic->r2.i);
            def = resultregs(ic);
            if (HasFeature(Feature_InlineCallKillsLinkReg)) c_in |= M_LR;
            c_out = reglist(R_A1, NARGREGS);
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
#ifdef DEBUG_THUMB_CPLUSPLUS
            sanity_check_has_callr = 1;
#endif
            use = argumentregs(ic->r2.i);
            def = resultregs(ic);
            c_in = regbit(R_LR);
            c_out = regbit(R_IP) | reglist(R_A1, NARGREGS);
            c_out &= ~resultregs(ic);
            break;

        case J_TAILCALLK:
            use = argumentregs(ic->r2.i);
            def = 0;
            break;
        case J_TAILCALLR:
            /* NOT IMPLEMENTED in backend! */
            break;
        /* J_ENTER & J_SAVE have quite complex register usage. As they are currently not
         * used in neither register allocation nor peepholing, this isn't implemented yet.
         * Therefore their register usage is only implemented for gen.c
         * BEWARE for changes in this!
         */
        case J_SAVE:
            break;
        case J_ENTER:
            def = argumentregs(ic->r3.i);
            break;
        default:
            if (InputsClashWithIP(ic)) c_in = regbit(R_IP);
            if (OutputsClashWithIP(ic)) c_out = regbit(R_IP);
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
        switch (ic->op & (J_TABLE_BITS | J_ALIGNMENT))
        {
            case J_LDRWK+J_ALIGN1:
            case J_STRWK+J_ALIGN1:
                if (ic->r2.r != R_SP && (ic->r3.i < 0 || ic->r3.i >= 32))
                    errmsg = "unaligned LDRWK/STRWK with overlarge offset";
                break;

            case J_LDRK+J_ALIGN1:
            case J_STRK+J_ALIGN1:
                if (ic->r2.r != R_SP && (ic->r3.i < 0 || ic->r3.i >= 32))
                    errmsg = "unaligned LDRK/STRK with overlarge offset";
                break;
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
        if (a_uses_r1(p) && (uint32)p->ic.r1.rr >= 16) fault = YES;
        if (a_uses_r2(p) && (uint32)p->ic.r2.rr >= 16) fault = YES;
        if (a_uses_r3(p) && (uint32)p->ic.r3.rr >= 16) fault = YES;
        if (a_uses_r4(p) && (uint32)p->ic.r4.rr >= 16) fault = YES;
        if (fault)
            errmsg = "illegal register number";
        if (GetRegisterUsage(p, &u))
            errmsg = "corrupted register";

        fault = NO;
        switch (ic->op)
        {
            case J_MULR:
                if (p->ic.r1.r == p->ic.r3.r) fault = YES;
                break;
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


/* WD TODO: Need to alter this... has_side_effects should be a backend function, looking at a
   volatile bit, etc. Certain types of calls could be regarded as memory modifyable too.
   Also need something to prevent assembler loads/stores to be removed!
*/

bool has_side_effects(Icode const *ic)
{
    J_OPCODE op = ic->op & J_TABLE_BITS;
    if (writes_mem(op)) return YES;
#ifdef THUMB_INLINE_ASSEMLBER
    if (op == J_SWI || op == J_BL) return YES;
#endif
    return NO;
}

/* WD: TODO remove writeback should be a backend function, with the dead flags
   as inputs (are dead register set), and returns a NOOP, a modified instruction
   or the same instruction...
*/

void remove_writeback(Icode *ic)
{
    IGNORE(ic);
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


/* end of arm/mcdep.c */
