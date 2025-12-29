/* ARM and Thumb C compilers: file tooledit.c
 * Copyright (C) 1996 Advanced RISC Machines Limited. All rights reserved.
 * Common tooledit code for arm and thumb.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#include <string.h>
#include <ctype.h>

#include "globals.h"
#include "cgdefs.h"
#include "jopcode.h"
#include "compiler.h"
#include "mcdpriv.h"
#include "toolenv.h"
#include "tooledit.h"

static bool IsReadOnly(ToolEnv *t, char const *name) {
#ifdef TARGET_IS_THUMB
  if (StrEq(name, "-arch")
      || StrEq(name, "-cpu"))
    return YES;
  if (StrEq(name, "-apcs.32bit")
      || StrEq(name, "-apcs.softfp") || StrEq(name, "-apcs.fpis")
      || StrEq(name, "-apcs.fp") || StrEq(name, "-apcs.fpr"))
    return YES;
#else
  if (StrEq(name, "-arch"))
    return !TE_HasValue(t, "-cpu", "#generic");
#endif
  if (StrEq(name, "-gt"))
    return TE_HasValue(t, ".debugtable", "=-dwarf");
  return FALSE;
}

typedef struct { char const *name; char const *val; } EnvInit;

static EnvInit const pcc_implies[] = {
  {".Wf", "=-Wf"}, {".Wd", "=-Wd"}, {".Wa", "=-Wa"}, {".Wn", "=-Wn"},
  {".Wv", "=-Wv"}, {".Ep", "=-Ep"}, {".schar", "=-zc"},
  {"-D__STDC__", "="},
  {"-D__STDC_VERSION__", "="},
  {0, 0}
};

static EnvInit const ansi_implies[] = {
  {".Wf", "=-W+f"}, {".Wd", "=-W+d"}, {".Wa", "=-W+a"}, {".Wn", "=-W+n"},
  {".Wv", "=-W+v"}, {".Ep", "=-E+p"}, {".schar", "=-z+c"},
  {"-D__STDC__", "==1"},
  {"-D__STDC_VERSION__", "==199409L"},
  {0, 0}
};

static EnvInit const noswst_implies[] =  { { "-D__APCS_NOSWST", "?"}, {0, 0} };
static EnvInit const swst_implies[] =    { { "-D__APCS_NOSWST", "="}, {0, 0} };

static EnvInit const reent_implies[] =   { { "-D__APCS_REENT", "?"}, {0, 0} };
static EnvInit const noreent_implies[] = { { "-D__APCS_REENT", "="}, {0, 0} };

static EnvInit const inter_implies[] =   { { "-D__APCS_INTERWORK", "?"}, {0, 0} };
static EnvInit const nointer_implies[] = { { "-D__APCS_INTERWORK", "="}, {0, 0} };

static EnvInit const bi_implies[] =      { { "-D__BIG_ENDIAN", "?"}, {0, 0} };
static EnvInit const li_implies[] =      { { "-D__BIG_ENDIAN", "="}, {0, 0} };

static EnvInit const ft_implies[] =      { { "-D__REVERSE_BF_PACKING", "?"}, {0, 0} };
static EnvInit const noft_implies[] =    { { "-D__REVERSE_BF_PACKING", "="}, {0, 0} };

static EnvInit const dwarf_implies[] =   { { "-gt", "#p" }, {0, 0} };

static EnvInit const b32_implies[] =     { { "-D__APCS_32", "?"}, {0, 0} };
static EnvInit const nofp_implies[] =    { { "-D__APCS_NOFP", "?"}, {0, 0} };
static EnvInit const softfp_implies[] =  { { "-D__SOFTFP__", "?"}, { "-D__SOFT_DOUBLES__", "?"}, {0, 0} };
static EnvInit const softd_implies[] =   { { "-D__SOFTFP__", "="}, { "-D__SOFT_DOUBLES__", "?"}, {0, 0} };
static EnvInit const nofpr_implies[]  =  { { "-D__PCS_FPREGARGS", "="}, {0, 0} };
#ifndef TARGET_IS_THUMB
static EnvInit const b26_implies[] =     { { "-D__APCS_32", "="}, {0, 0} };
static EnvInit const fp_implies[] =      { { "-D__APCS_NOFP", "="}, {0, 0} };
static EnvInit const hardfp_implies[] =  { { "-D__SOFTFP__", "="}, { "-D__SOFT_DOUBLES__", "="}, {0, 0} };
static EnvInit const fpr_implies[]    =  { { "-D__PCS_FPREGARGS", "?"}, {0, 0} };
static EnvInit const amp_implies[]    =  { { "-apcs.softfp", "#/softdoubles"}, { "-apcs.fpr", "#/fpregargs"},
                                           { "-apcs.wide", "#/narrow"}, {0, 0} };
#endif

typedef struct { char const *val; EnvInit const *implies; } EnvValImplies;

static EnvValImplies const swst_vals[] = { {"#/swst", swst_implies}, {"#/noswst", noswst_implies}, {NULL, NULL} };
static EnvValImplies const reent_vals[] = { {"#/reent", reent_implies}, {"#/noreent", noreent_implies}, {NULL, NULL} };
static EnvValImplies const inter_vals[] = { {"#/interwork", inter_implies}, {"#/nointerwork", nointer_implies}, {NULL, NULL} };
static EnvValImplies const sex_vals[] = { {"=-bi", bi_implies}, {"=-li", li_implies}, {NULL, NULL} };
#ifndef TARGET_IS_THUMB
static EnvValImplies const softfp_vals[] = { {"#/softfp", softfp_implies}, {"#/hardfp", hardfp_implies},
                                             {"#/softdoubles", softd_implies}, {NULL, NULL} };
static EnvValImplies const fpr_vals[] = { {"#/fpregargs", fpr_implies}, {"#/nofpregargs", nofpr_implies}, {NULL, NULL} };
static EnvValImplies const fp_vals[] = { {"#/fp", fp_implies}, {"#/nofp", nofp_implies}, {NULL, NULL} };
static EnvValImplies const b32_vals[] = { {"#/32", b32_implies}, {"#/26", b26_implies}, {NULL, NULL} };
static EnvValImplies const fpis_vals[] = { {"#/fpe3", NULL}, {"#/fpe2", NULL}, {NULL, NULL} };
static EnvValImplies const fpu_vals[] = { {"#fpa", NULL}, {"#amp", amp_implies}, {"#vfp", NULL}, {NULL, NULL} };
#endif
static EnvValImplies const ec_vals[] = { {"=-Ec", NULL}, {"=-E+c", NULL}, {NULL, NULL} };
static EnvValImplies const ef_vals[] = { {"=-Ef", NULL}, {"=-E+f", NULL}, {NULL, NULL} };
static EnvValImplies const el_vals[] = { {"=-El", NULL}, {"=-E+l", NULL}, {NULL, NULL} };
static EnvValImplies const ep_vals[] = { {"=-Ep", NULL}, {"=-E+p", NULL}, {NULL, NULL} };
static EnvValImplies const ez_vals[] = { {"=-Ez", NULL}, {"=-E+z", NULL}, {NULL, NULL} };
static EnvValImplies const wa_vals[] = { {"=-Wa", NULL}, {"=-W+a", NULL}, {NULL, NULL} };
static EnvValImplies const wd_vals[] = { {"=-Wd", NULL}, {"=-W+d", NULL}, {NULL, NULL} };
static EnvValImplies const wf_vals[] = { {"=-Wf", NULL}, {"=-W+f", NULL}, {NULL, NULL} };
static EnvValImplies const wg_vals[] = { {"=-Wg", NULL}, {"=-W+g", NULL}, {NULL, NULL} };
static EnvValImplies const wl_vals[] = { {"=-Wl", NULL}, {"=-W+l", NULL}, {NULL, NULL} };
static EnvValImplies const wm_vals[] = { {"=-Wm", NULL}, {"=-W+m", NULL}, {NULL, NULL} };
static EnvValImplies const wn_vals[] = { {"=-Wn", NULL}, {"=-W+n", NULL}, {NULL, NULL} };
static EnvValImplies const wp_vals[] = { {"=-Wp", NULL}, {"=-W+p", NULL}, {NULL, NULL} };
static EnvValImplies const ws_vals[] = { {"=-Ws", NULL}, {"=-W+s", NULL}, {NULL, NULL} };
static EnvValImplies const wu_vals[] = { {"=-Wu", NULL}, {"=-W+u", NULL}, {NULL, NULL} };
static EnvValImplies const wv_vals[] = { {"=-Wv", NULL}, {"=-W+v", NULL}, {NULL, NULL} };
static EnvValImplies const ff_vals[] = { {"=-ff", NULL}, {"=-f+f", NULL}, {NULL, NULL} };
static EnvValImplies const fa_vals[] = { {"=-fa", NULL}, {"=-f+a", NULL}, {NULL, NULL} };
static EnvValImplies const fv_vals[] = { {"=-fv", NULL}, {"=-f+v", NULL}, {NULL, NULL} };
static EnvValImplies const ft_vals[] = { {"=-ft", ft_implies}, {"=-f+t", noft_implies}, {NULL, NULL} };
static EnvValImplies const fk_vals[] = { {"=-fk", NULL}, {"=-f+k", NULL}, {NULL, NULL} };
static EnvValImplies const fw_vals[] = { {"=-fw", NULL}, {"=-f+w", NULL}, {NULL, NULL} };
static EnvValImplies const fy_vals[] = { {"=-fy", NULL}, {"=-f+y", NULL}, {NULL, NULL} };
static EnvValImplies const zc_vals[] = { {"=-zc", NULL}, {"=-z+c", NULL}, {NULL, NULL} };
static EnvValImplies const fz_vals[] = { {"=-fz", NULL}, {"=-f+z", NULL}, {NULL, NULL} };
static EnvValImplies const g_vals[] = { {"=-", NULL}, {"=+", NULL}, {NULL, NULL} };
static EnvValImplies const za_vals[] = { {"=0", NULL}, {"=1", NULL}, {NULL, NULL} };
static EnvValImplies const zap_vals[] = { {"=0", NULL}, {"=1", NULL}, {NULL, NULL} };
static EnvValImplies const zd_vals[] = { {"=0", NULL}, {"=1", NULL}, {NULL, NULL} };
static EnvValImplies const zo_vals[] = { {"=-z+o", NULL}, {"=-zo", NULL}, {NULL, NULL} };

typedef struct {
  char const *name;
  EnvValImplies const *val;
} KnownVals;

static KnownVals const known[] = {
  {"-apcs.swst",   swst_vals },
  {"-apcs.reent",  reent_vals },
  {"-apcs.inter",  inter_vals },
  {".bytesex",     sex_vals },
#ifndef TARGET_IS_THUMB
  {"-apcs.softfp", softfp_vals },
  {"-apcs.fpr",    fpr_vals },
  {"-apcs.fp",     fp_vals },
  {"-apcs.32bit",  b32_vals },
  {"-apcs.fpis",   fpis_vals },
  { "-fpu",        fpu_vals},
#endif

  {".Ec",      ec_vals },
  {".Ef",      ef_vals },
  {".El",      el_vals },
  {".Ep",      ep_vals },
  {".Ez",      ez_vals },

  {".Wa",      wa_vals },
  {".Wd",      wd_vals },
  {".Wf",      wf_vals },
  {".Wg",      wg_vals },
  {".Wl",      wl_vals },
  {".Wm",      wm_vals },
  {".Wn",      wn_vals },
  {".Wp",      wp_vals },
  {".Ws",      ws_vals },
  {".Wu",      wu_vals },
  {".Wv",      wv_vals },

  {".ff",      ff_vals },
  {".fa",      fa_vals },
  {".fv",      fv_vals },
  {".ft",      ft_vals },
  {".-Isearch",fk_vals },
  {".rolits",  fw_vals },
  {".enums",   fy_vals },
  {".schar",   zc_vals },
  {".swilr",   fz_vals },
  {"-g",       g_vals },

  { "-za",     za_vals },
  { "-zap",    zap_vals },
  { "-zd",     zd_vals },

  { ".areaperfn", zo_vals },

  {NULL}
};

typedef struct {
  char const *name;
  struct { char const *val; EnvInit const *implies; } val;
} FixedVals;

static FixedVals const fixedvals[] = {
#ifdef TARGET_IS_THUMB
  {"-cpu",         {"#ARM7TM", NULL} },
  {"-arch",        {"#4T", NULL} },
  {"-apcs.softfp", {"#/softfp", softfp_implies} },
  {"-apcs.fpr",    {"#/nofpregargs", nofpr_implies} },
  {"-apcs.fp",     {"#/nofp", nofp_implies} },
  {"-apcs.32bit",  {"#/32", b32_implies} },
  {"-apcs.fpis",   {"#/fpe3", NULL} },
#endif
  {NULL,           {NULL, NULL} }
};

static bool CheckInsert(ToolEnv *t, char const *name, char const *val) {
  /* Insert <'name', 'val'> into 't', returning TRUE if the value
   * associated with 'name' is changed thereby.
   */
  char const *oldval = toolenv_lookup(t, name);
  if (oldval == NULL) {
    if (StrEq(val, "=") || StrEq(val, "#"))
      return FALSE;
    /* Attempting to delete something already absent from the env. */
  } else if (StrEq(oldval, val))
    return FALSE;

  tooledit_insert(t, name, val);
  return TRUE;
}

static bool SetDefaults(ToolEnv *t, EnvInit const *p) {
  bool changed = NO;
  for (; p->name != NULL; p++)
    changed = changed | CheckInsert(t, p->name, p->val);
  return changed;
}

static bool CheckRange(char const *val, Uint low, Uint high) {
  if (isdigit(val[0])) {
    char *endp;
    uint32 n = (uint32)strtol(val, &endp, 0);
    if (endp[0] == 0 && low <= n && n <= high) return YES;
  }
  return NO;
}

static bool CheckAlignValue(char const *val) {
  if (isdigit(val[0])) {
    char *endp;
    uint32 n = (uint32)strtol(val, &endp, 0);
    if (endp[0] == 0 && n > 0 && n <= 8 && (n & (0-n)) == n) return YES;
  }
  return NO;
}

static void TE_ReconstructEtc(ToolEnv *t);

static void TargetDefine(ToolEnv *t, char const *s1, char const *s2, bool define) {
  if (s2[0] != 0) {
    char b[64];
    sprintf(b, "-D__TARGET_%s_%s", s1, s2);
    toolenv_insert(t, b, define ? "?" : "=");
  }
}

ToolEdit_InsertStatus tooledit_insertwithjoin(
    ToolEnv *t, char const *name, int join, char const *value) {
  EnvInit const *implies = NULL;
  ToolEdit_InsertStatus status = TE_OK;
  if (IsReadOnly(t, name)) {
    /* If a toolenv entry is read-only, we still allow it to be written
     * provided the value is the correct one (to avoid a problem with
     * setting the default values, which go through here so that
     * consequential changes are done in just one place).
     */
    FixedVals const *p;
    for (p = fixedvals;; p++)
      if (p->name == NULL)
        return TE_Failed;
      else if (StrEq(name, p->name)) {
        if (join != p->val.val[0] || !StrEq(value, &p->val.val[1]))
          return TE_Failed;
        implies = p->val.implies;
        break;
      }
  }
  if (join != '=' && join != '#') {
    if (join != '?' || value[0] != 0) return TE_Failed;
  }
#ifndef TARGET_IS_THUMB
  if (StrEq(name, "-cpu") || StrEq(name, "-arch")) {
    char a[32], c[32];
    Processor const *cpu;
    char const *newcpu;
    { char const *oldarch = toolenv_lookup(t, "-arch");
      char const *oldcpu = toolenv_lookup(t, "-cpu");
      if (oldarch == NULL)
        a[0] = 0;
      else
        strcpy(a, oldarch+1);
      if (oldcpu == NULL)
        c[0] = 0;
      else
        strcpy(c, oldcpu+1);
    }
    if (StrEq(name, "-cpu")) {
      if (join == '#' && StrEq(value, "generic")) {
      /* Setting cpu to #generic does not actually alter anything
       * else in the environment, but it does change -arch from
       * read-only to writable.
       */
        cpu = LookupArchitecture(a);
        toolenv_insert(t, name, "#generic");
        status = TE_OKBut;
        newcpu = value;
      } else {
        cpu = LookupProcessor(value);
        if (cpu == NULL) return TE_Failed;
        /* Changing the cpu from generic may not change anything else
         * in the environment, but it does change -arch from writable
         * to read-only.
         */
        if (StrEq(c, "#generic")) status = TE_OKBut;
        if (toolenv_insertwithjoin(t, name, join, value) != 0) return TE_Failed;
        if (StrEq(value, "SA1500")) {
          tooledit_insert(t, "-fpu", "#amp");
          status = TE_OKBut;
        }
        newcpu = value;
      }

    } else /*(StrEq(name, "-arch"))*/ {
      if (!TE_HasValue(t, "-cpu", "#generic")) return TE_Failed;
      cpu = LookupArchitecture(value);
      newcpu = c;
    }
    if (cpu != NULL && !StrEq(a, cpu->arch+1)) {
      TargetDefine(t, "ARCH", a, NO);
      TargetDefine(t, "ARCH", cpu->arch+1, YES);
      TargetDefine(t, "FEATURE", "HALFWORD", cpu->flags & PROCESSOR_HAS_HALFWORDS);
      TargetDefine(t, "FEATURE", "THUMB", cpu->flags & PROCESSOR_HAS_THUMB);
      TargetDefine(t, "FEATURE", "MULTIPLY", cpu->flags & PROCESSOR_HAS_MULTIPLY);
      status = TE_OKBut;
    }
    if (!StrEq(c, newcpu)) {
      TargetDefine(t, "CPU", c, NO);
      TargetDefine(t, "CPU", newcpu, YES);
      status = TE_OKBut;
    }
    toolenv_insert(t, "-arch", cpu->arch);
    status = TE_OKBut;
    return status;
  } else if (StrEq(name, "-fpu")) {
    char const *oldfpu = toolenv_lookup(t, "-fpu");
    if (oldfpu != NULL) {
      if (StrEq(oldfpu+1, value)) return TE_OK;
      TargetDefine(t, "FPU", oldfpu+1, NO);
    }
    status = TE_OKBut;
    TargetDefine(t, "FPU", value, YES);
    /* And drop through to insert (with implications) through generic code */
  } else
#endif
  if (StrEq(name, ".lang")) {
    if (join == '=' && StrnEq(value, "-pcc", 4))
      implies = pcc_implies;
    else
      implies = ansi_implies;
  } else if (StrEq(name, ".debugtable")) {
    if (join == '=' && StrEq(value, "-dwarf"))
      implies = dwarf_implies;
    /* Read-only status of -gt may have changed */
    status = TE_OKBut;
  } else if (StrEq(name, "-zi")) {
    if (join != '=' || !CheckRange(value, 1, 4)) return TE_Failed;
  } else if (StrEq(name, "-zr")) {
    if (join != '=' || !CheckRange(value, LDM_REGCOUNT_MIN_DEFAULT, LDM_REGCOUNT_MAX_DEFAULT))
      return TE_Failed;
  } else if (StrEq(name, "-zas") || StrEq(name, "-zat")) {
    if (join != '=' || !CheckAlignValue(value))
      return TE_Failed;
  }
  if (implies == NULL) {
    KnownVals const *kv = known;
    for (; kv->name != NULL; kv++)
      if (StrEq(name, kv->name)) {
        EnvValImplies const *valp = kv->val;
        for (; ; valp++)
          if (valp->val == NULL)
            return TE_Failed;
          else if (join == valp->val[0] && StrEq(value, &valp->val[1])) {
            implies = valp->implies;
            break;
          }
        break;
      }
  }
  if (toolenv_insertwithjoin(t, name, join, value) != 0) return TE_Failed;
  if (StrEq(name, ".etc")) {
    TE_DecodeArgumentLine(t, value, YES);
    TE_ReconstructEtc(t);
    return TE_OKBut;
  }
  if (implies != NULL && SetDefaults(t, implies)) return TE_OKBut;
  return status;
}

ToolEdit_InsertStatus tooledit_insert(
    ToolEnv *t, char const *name, char const *value) {
  return tooledit_insertwithjoin(t, name, value[0], &value[1]);
}

char const *tooledit_lookup(
    ToolEnv *t, char const *name, bool *readonly) {
  /* lookup is simply toolenv_lookup, with a thin veneer to return */
  /* a readonly value.                                             */

  char const *val = toolenv_lookup(t, name);
  if (val != NULL) {
    *readonly = IsReadOnly(t, name);
  }
  return val;
}

static char const * const langname[] = {
  "=-pcc -strict",
  "=-pcc",
  "=-ansi",
  "=-ansi -fc",
  "=-ansi -strict",
#ifdef CPLUSPLUS
  "=-cpp",
  "=-cpp -fc",
  "=-cfront",
  "=-cfront -fc",
#endif
  NULL
};

#ifdef TARGET_IS_THUMB
static int valuecount_docpu(void) {
    return 1;
}

static int enumvalues_docpu(ToolEnvItemFn *f, void *arg) {
  return f(arg, "-cpu", "#ARM7TM");
}

static int valuecount_doarch(void) {
    return 1;
}

static int enumvalues_doarch(ToolEnvItemFn *f, void *arg) {
  return f(arg, "-arch", "#4T");
}
#else

static int countvalues_cpus(void *arg, Processor const *cpu) {
  (*(int *)arg)++;
  IGNORE(cpu);
  return 0;
}

static int valuecount_docpu(void) {
  int n = 1; /* #generic handled specially */
  EnumerateProcessors(countvalues_cpus, &n);
  return n;
}

typedef struct { ToolEnvItemFn *f; void *arg; } EnumValues_Cpu_Rec;

static int enumvalues_cpus(void *arg, Processor const *cpu) {
  EnumValues_Cpu_Rec *ep = (EnumValues_Cpu_Rec *)arg;
  return ep->f(ep->arg, "-cpu", cpu->name);
}

static int enumvalues_docpu(ToolEnvItemFn *f, void *arg) {
  EnumValues_Cpu_Rec er;
  er.arg = arg; er.f = f;
  f(arg, "-cpu", "#generic");
  return EnumerateProcessors(enumvalues_cpus, &er);
}

typedef struct { int n; char const *name[16]; } Enum_Arch_Rec;

static int enum_arch(void *arg, Processor const *cpu) {
  Enum_Arch_Rec *ep = (Enum_Arch_Rec *)arg;
  int i;
  for (i = 0; i < ep->n; i++) {
    if (StrEq(ep->name[i], cpu->arch))
      return 0;
  }
  ep->name[i] = cpu->arch;
  ep->n = i+1;
  return 0;
}

static int valuecount_doarch(void) {
  Enum_Arch_Rec er;
  er.n = 0;
  EnumerateProcessors(enum_arch, &er);
  return er.n;
}

static int enumvalues_doarch(ToolEnvItemFn *f, void *arg) {
  Enum_Arch_Rec er;
  int i;
  er.n = 0;
  EnumerateProcessors(enum_arch, &er);
  for (i = 0; i < er.n; i++) {
    int rc = f(arg, "-arch", er.name[i]);
    if (rc != 0) return rc;
  }
  return 0;
}
#endif

int tooledit_valuecount(ToolEnv *t, char const *name) {
  IGNORE(t);
  if (StrEq(name, "-cpu"))
    return valuecount_docpu();
  if (StrEq(name, "-cpu")) {
    return valuecount_doarch();
  } else if (StrEq(name, ".lang")) {
    int i = 0;
    for (; langname[i] != NULL; i++) continue;
    return i;
  }
  return -1;
}

int tooledit_enumeratevalues(
    ToolEnv *t, char const *name, ToolEnvItemFn *f, void *arg) {
  IGNORE(t);
  if (StrEq(name, "-cpu"))
    return enumvalues_docpu(f, arg);
  else if (StrEq(name, "-arch"))
    return enumvalues_doarch(f, arg);
  else if (StrEq(name, ".lang")) {
    int i = 0;
    for (; langname[i] != NULL; i++) {
      int rc = f(arg, name, langname[i]);
      if (rc != 0) return rc;
    }
    return 0;
  }
  return -1;
}

typedef struct {
  ToolEnv *t;
  ToolEdit_EnumFn *f;
  void *arg;
  char const *prefix;
  size_t prefix_len;
} TE_EnumRec;

static int TE_EnumFn(void *arg, char const *name, char const *val) {
  TE_EnumRec *tp = (TE_EnumRec *)arg;
  if (tp->prefix_len != 0 && !StrnEq(name, tp->prefix, tp->prefix_len))
    return 0;
  return tp->f(tp->arg, name, val, IsReadOnly(tp->t, name));
}

int tooledit_enumerate(
    ToolEnv *t, char const *prefix, ToolEdit_EnumFn *f, void *arg) {
  if (StrEq(prefix, "-I.") || StrEq(prefix, "-J.")) {
    return Tool_OrderedEnvEnumerate(t, prefix, f, arg);
  } else {
    TE_EnumRec tr;
    tr.t = t; tr.f = f; tr.arg = arg;
    tr.prefix = prefix; tr.prefix_len = strlen(prefix);
    return toolenv_enumerate(t, TE_EnumFn, &tr);
  }
}

typedef struct {
  char *buf;
  int len, maxlen;
} BufDesc;

typedef struct {
  BufDesc b;
  char const *etc;
  char const *cpu;
  char const *arch;
  uint32 fmap[2], Wmap[2], Emap[2];
  Uint napcs;
  char const *apcsqual[16];
} TE_GCLRec;

static void AddArgument(
    BufDesc *bd, char const *name, const char *val, bool protectspaces) {
  char const *dot = strchr(name, '.');
  size_t keylen = (dot == NULL
                   || (!isalnum(dot[1])
                       && dot[1] != '-')) ? strlen(name)
                                          : dot - name;
  int newlen = bd->len;
  int jointype = val[0];
  int spacecount = 0;
  size_t vallen = strlen(val);
  if (newlen != 0) newlen++;                /* a separating space */
  newlen += keylen;
  if (jointype != '?') {
    if (protectspaces) {
      char const *p = &val[1];
      for (; *p != 0; p++)
        if (isspace(*p)) {
          spacecount++;
          break;
        }
      if (name[0] == '.' && spacecount == 1)
        spacecount = 0;
    }
    newlen += vallen;
    if (jointype == '=') newlen--;  /* name and value concatenated */
    if (spacecount > 0) newlen += 2;
  }
  if (newlen + 1 <= bd->maxlen) {    /* allow for zero termination */
    int len = bd->len;
    char *b = bd->buf;
    if (len != 0) b[len++] = ' ';
    if (jointype == '=' && spacecount > 0) b[len++] = '"';
    memcpy(&b[len], name, keylen); len += keylen;
    if (jointype == '#') {
      b[len++] = ' ';
      if (spacecount > 0) b[len++] = '"';
    }
    if (jointype != '?') {
      memcpy(&b[len], &val[1], vallen-1);
      len += vallen-1;
      if (spacecount > 0) b[len++] = '"';
    }
  }
  bd->len = newlen;
}

static Uint MapChars(char *b, uint32 w, Uint ix) {
  int ch = 'a';
  for (; w != 0; w = w >> 1, ch++)
    if (w & 1) b[ix++] = ch;
  return ix;
}

static void AddMaps(TE_GCLRec *tp, int type, uint32 *map) {
  char b[64];
  Uint i = 0;
  if (map[0] == 0 && map[1] == 0) return;
  b[0] = '='; b[1] = '-'; b[2] = type;
  i = MapChars(b, map[0], 3);
  if (map[1] != 0) {
    b[i] = '+';
    i = MapChars(b, map[1], i+1);
  }
  b[i] = 0;
  AddArgument(&tp->b, ".dummy", b, FALSE);
}

static void SwitchFlag(TE_GCLRec *tp, int ix, Uint type, int ch) {
  uint32 bit = 1 << (ch - 'a');
  if (type == 'f') tp->fmap[ix] |= bit;
  else if (type == 'E') tp->Emap[ix] |= bit;
  else tp->Wmap[ix] |= bit;
}

static int Te_GCLFn(void *arg, const char *name, const char *val) {
  TE_GCLRec *tp = (TE_GCLRec *)arg;
  char const *defaultval = toolenv_lookup(cc_default_env, name);
  if (defaultval != NULL && StrEq(val, defaultval))
    return 0;
  if (StrEq(name, ".etc")) {
    tp->etc = val;
  } else if (StrEq(name, "-cpu")) {
    tp->cpu = val;
  } else if (StrEq(name, "-arch")) {
    tp->arch = val;
  } else if (StrnEq(name, "-apcs.", 6)) {
    tp->apcsqual[tp->napcs++] = &val[1];
  } else if (!StrnEq(name, "-I.", 3) &&
             !StrnEq(name, "-J.", 3) &&
             !StrnEq(name, "-D", 2)) {
    if (name[0] == '.' && val[0] == '=' && val[1] == '-') {
      int type = val[2];
      if (type == 'f' || type == 'E' || (type == 'W' && val[3] != 0)) {
        if (val[4] == 0) {
          SwitchFlag(tp, 0, type, val[3]);
          return 0;
        } else if (val[3] == '+' && val[5] == 0) {
          SwitchFlag(tp, 1, type, val[4]);
          return 0;
        }
      }
    }
    AddArgument(&tp->b, name, val, TRUE);
  }
  return 0;
}

static int Te_GCLFnI(void *arg, char const *name, char const *val, bool readonly) {
  TE_GCLRec *tp = (TE_GCLRec *)arg;
  char const *defaultval = toolenv_lookup(cc_default_env, name);
  IGNORE(readonly);
  if (defaultval == NULL || !StrEq(val, defaultval))
    AddArgument(&tp->b, name, val, TRUE);
  return 0;
}

int tooledit_getcommandline(ToolEnv *t, char *buf, int maxlen) {
  TE_GCLRec tr;
  tr.etc = tr.cpu = NULL; tr.arch = NULL;
  tr.b.buf = buf; tr.b.len = 0; tr.b.maxlen = maxlen;
  tr.fmap[0] = tr.fmap[1] = 0;
  tr.Emap[0] = tr.Emap[1] = 0;
  tr.Wmap[0] = tr.Wmap[1] = 0;
  tr.napcs = 0;
  toolenv_enumerate(t, Te_GCLFn, &tr);
  if (tr.napcs != 0) {
    char b[256];
    Uint i = 0;
    b[0] = '#'; b[1] = 0;
    for (; i < tr.napcs; i++) strcat(b, tr.apcsqual[i]);
    AddArgument(&tr.b, "-apcs", b, TRUE);
  }
  if (tr.cpu != NULL && !StrEq(tr.cpu, "#generic"))
    AddArgument(&tr.b, "-cpu", tr.cpu, TRUE);
  else if (tr.arch != NULL)
    AddArgument(&tr.b, "-arch", tr.arch, TRUE);
  AddMaps(&tr, 'f', tr.fmap);
  AddMaps(&tr, 'W', tr.Wmap);
  AddMaps(&tr, 'E', tr.Emap);
  tooledit_enumerate(t, "-D", Te_GCLFnI, &tr);
  tooledit_enumerate(t, "-I.", Te_GCLFnI, &tr);
  tooledit_enumerate(t, "-J.", Te_GCLFnI, &tr);
  if (tr.etc != NULL)
    AddArgument(&tr.b, "", tr.etc, FALSE);
  if (tr.b.len < maxlen) buf[tr.b.len] = 0;
  return tr.b.len+1;
}

typedef struct {
  ToolEnv *t;
  size_t n, size;
  EnvInit *p;
} MakeEtcRec;

static int MakeEtc(void *arg, char const *name, char const *val) {
  MakeEtcRec *mp = (MakeEtcRec *)arg;
  if (!StrEq(name, ".etc") && !StrEq(name, ".defaulttime")
      && !Tool_Configurable(mp->t, name)
      && cc_default_env != NULL) {
    char const *defaultval = toolenv_lookup(cc_default_env, name);
    if (defaultval == NULL || !StrEq(val, defaultval)) {
      if (mp->n == mp->size) {
        mp->size += 10;
        mp->p = (EnvInit *)realloc(mp->p, mp->size * sizeof(EnvInit));
      }
      mp->p[mp->n].name = name;
      mp->p[mp->n].val = val;
      mp->n++;
    }
  }
  return 0;
}

static void TE_ReconstructEtc(ToolEnv *t) {
  MakeEtcRec mr;
  mr.t = t; mr.n = 0; mr.size = 10;
  mr.p = (EnvInit *)malloc(10 * sizeof(EnvInit));
  toolenv_enumerate(t, MakeEtc, &mr);
  if (mr.n == 0) {
    toolenv_insert(t, ".etc", "=");
  } else {
    BufDesc bd;
    size_t i;
    bd.buf = NULL; bd.len = 0; bd.maxlen = 0;
    for (i = 0; i < mr.n; i++)
      AddArgument(&bd, mr.p[i].name, mr.p[i].val, TRUE);
    bd.buf = (char *)malloc(bd.len+1);
    bd.maxlen = bd.len+1; bd.len = 0;
    for (i = 0; i < mr.n; i++)
      AddArgument(&bd, mr.p[i].name, mr.p[i].val, TRUE);
    bd.buf[bd.len] = 0;
    toolenv_insertwithjoin(t, ".etc", '=', bd.buf);
    for (i = 0; i < mr.n; i++)
      toolenv_insert(t, mr.p[i].name, "=");
    free(bd.buf);
  }
  free(mr.p);
}

void TE_NormaliseEtc(ToolEnv *t) {
  char const *etc = toolenv_lookup(t, ".etc");
  if (etc != NULL) TE_DecodeArgumentLine(t, &etc[1], YES);
  TE_ReconstructEtc(t);
}

/* end of tooledit.c */
