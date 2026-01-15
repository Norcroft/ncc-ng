/*
 * driver.c - driver for Codemist compiler (RISC OS, DOS, Mac/MPW, Unix)
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Codemist Ltd., 1988-1992.
 * Copyright (C) Advanced RISC Machines Limited, 1990-1992.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$  Codemist 186
 * Checkin $Date$
 * Revising $Author$
 */

/* AM memo: we should look at a getenv() variable to find alternative    */
/* path names to /usr/include etc:  This would greatly facilitate        */
/* installing as an alternative C compiler and reduce the shambles       */
/* (which is being tidied) in env = 2; below.                            */
/* AM notes that DEC's version of MIPS C compiler uses env variables     */
/*   COMP_HOST_ROOT and COMP_TARGET_ROOT for this.                       */

/* AM, Jul 89: COMPILING and TARGET flag tests have been reviewed.       */
/* The effect is than running a RISCOS compiler on UNIX looks like a     */
/* unix compiler (i.e. -S not -s) except for target-specific flags.      */
/* Beware the TARGET_IS_HELIOS flags as not rationalised.                */

/* AM: This file should more properly be called unixdriv.c:  the        */
/* rationale is that it munges the command line and repeatedly calls    */
/* the compiler and possibly the linker just like the unix 'cc' cmd.    */
/* It is target-independent, but rather host dependent.  Accordingly    */
/* it needs not to be used on machines like the ibm370 under MVS etc.,  */
/* where the file munging done is totally inappropriate.                */
/* We need a HOST_ or COMPILING_ON_ test whether to include this file.  */
/* Further, we would like to suppress the LINK option unless the        */
/* host and target are have compatible object format.                   */

/* Host dependencies:
   1. use of getenv("c$libroot").
   2. file name munging.
   3. The HELP text in drivhelp.h
   More?
*/

#include <stddef.h>
#ifdef __STDC__
#  include <stdlib.h>
#  include <string.h>
#else
#  include <strings.h>
extern void exit();
extern char *getenv();
extern int  system();
#endif
#include <ctype.h>
#include <stdio.h>
#define uint HIDE_HPs_uint
#include <signal.h>
#undef uint
#include <setjmp.h>

#include "globals.h"
#include "errors.h"
#include "compiler.h"
#include "store.h"
#include "fname.h"
#include "version.h"
#include "drivhelp.h"
#include "mcdep.h"
#include "prgname.h"
#include "pp.h"
#ifdef FOR_ACORN
#include "dde.h"
#endif
#include "toolenv2.h"
#include "tooledit.h"
#include "toolbox.h"
#include "toolver.h"
#include "trackfil.h"

BackChatHandler backchat;
static jmp_buf exitbuf;

    /*************************************************************/
    /*                                                           */
    /*   Set up default compilation options (Arthur,Msdos,Unix)  */
    /*                                                           */
    /*************************************************************/

/* The meaning of the bits in the user's number n in '-On' */
#define MINO_CSE            0x1
#define MINO_NAO            0x2
#define MINO_MAX            0x3    /* sum of above */

#define SMALL_COMMAND       128
#define INCLUDE_BUFLEN      64     /* initial size of include buffer  */
#define MAX_TEXT            256    /* The longest filename I can handle */

/* #define BSD_CC              "/usr/ucb/cc" */

#define KEY_NEXT                    1L
#define KEY_HOST_LIB        0x0000002L
#define KEY_HELP            0x0000004L
#define KEY_LINK            0x0000008L
#define KEY_LISTING         0x0000010L
#define KEY_PCC             0x0000020L
#define KEY_CONFIG          0x0000040L

#define KEY_COMMENT         0x0000080L
#define KEY_ASM_OUT         0x0000100L
#define KEY_XPROFILE        0x0000200L
#define KEY_MAKEFILE        0x0000400L
#define KEY_PREPROCESS      0x0000800L
#define KEY_PROFILE         0x0001000L
#define KEY_RENAME          0x0002000L
#define KEY_MD              0x0008000L
#define KEY_READONLY        0x0010000L
#define KEY_STDIN           0x0020000L
#define KEY_COUNTS          0x0040000L
#ifdef  RISCiX113                       /* LDS 31-July-92 @@@ */
#  define KEY_RIX120        0x0080000L  /* Sad history; retire soon? */
#  define KEY_NOSYSINCLUDES 0x0000000L  /* Avoid spurious #ifdef RISCiX113 */
#else
#  define KEY_NOSYSINCLUDES 0x0080000L
#endif
#define KEY_ERRORSTREAM    0x00400000L
#define KEY_VIAFILE        0x00800000L
#define KEY_VERIFY         0x01000000L

#  define KEY_CFRONT       0x02000000L
#define KEY_DEBUG          0x08000000L

#ifndef FORTRAN
/* IDJ 25-Mar-94: re-use FORTRAN flags for DDE purposes */
#define KEY_THROWBACK      0x10000000L
#define KEY_DESKTOP        0x20000000L
#define KEY_DEPEND         0x40000000L
#define KEY_CFRONTPREPROCESS 0x80000000L
#else
#define KEY_F66            0x10000000L
#define KEY_ONETRIP        0x20000000L
#define KEY_UPPER          0x40000000L
#define KEY_LONGLINES      0x80000000L

/* The following are duplicated from ffe/feint.h. This is a temporary bodge. */
#define EXT_DOUBLECOMPLEX           1L
#define EXT_HINTEGER                2L
#define EXT_CASEFOLD                4L
#define EXT_LCKEYWORDS              8L
#define EXT_LCIDS                0x10L
#define EXT_FREEFORMAT           0x20L
#define EXT_IMPUNDEFINED         0x40L
#define EXT_RECURSION            0x80L
#define EXT_AUTO                0x100L
#define EXT_HOLLERITH           0x200L
#define EXT_TOPEXPRESS          0x400L
#define EXT_F66                 0x800L
#define EXT_MIXEDCOMM          0x1000L
#define EXT_VMSCHARS           0x2000L
#define EXT_VMSCASTS           0x4000L
#define EXT_VMSIO              0x8000L
#define EXT_VMSTYPES          0x10000L

#define OPT_STATICLOCALS     0x100000L
#define OPT_DEFHINTEGER      0x200000L
#define OPT_DEFDOUBLE        0x400000L
#define OPT_IMPUNDEFINED     0x800000L
#define OPT_CHECKSUB        0x1000000L
#define OPT_NOARGALIAS      0x2000000L
#define OPT_LONGLINES       0x4000000L
#define FFEOPTS            0xfff00000L

#define F66_ONETRIP       1L
#define F66_IOSUBLIST     2L
#define F66_INTRINSGO     4L
#endif /* FORTRAN */

/*************************************************************/
/*                                                           */
/*   Define the environment information structure            */
/*                                                           */
/*************************************************************/

#ifdef FORTRAN
#  define RISCIX_FORTRAN_PRAGMAX \
      (EXT_DOUBLECOMPLEX | EXT_HINTEGER | EXT_CASEFOLD | EXT_LCKEYWORDS |\
       EXT_FREEFORMAT | EXT_IMPUNDEFINED | EXT_RECURSION | EXT_AUTO |\
       EXT_HOLLERITH | EXT_TOPEXPRESS | EXT_F66 | EXT_MIXEDCOMM |\
       EXT_VMSCHARS | EXT_VMSCASTS | EXT_VMSIO | EXT_VMSTYPES |\
       OPT_STATICLOCALS | OPT_NOARGALIAS)
#endif

static char *driver_options[] = DRIVER_OPTIONS;

static struct EnvTable
{
      int                 unused;
      int32               initial_flags;
      int32               initial_pragmax;

      const char          *include_ansi_path,
                          *include_pcc_path,
                          *include_pas_path;
      const char          *lib_dir;
      char                *lib_root, *pas_lib_root;
      const char          *list;

      const char          *assembler_cmd;

      const char          *link_cmd;
/* 'output_file' is also used for non-link outputs.                     */
/* This unix convenience just causes pain here.                         */
      char                *output_file;
      const char          *link_ext;

      const char          *link_startup,
                          *profile_startup,
                          *profile_g_startup;

      const char          *default_lib,
                          *host_lib,
                          *profile_lib,
                          *fort_lib,
                          *fort_profile_lib,
                          *pas_lib;
}
     const initSetupenv =
#ifdef DRIVER_ENV
    DRIVER_ENV
#else
# ifdef COMPILING_ON_ARM
#  ifdef COMPILING_ON_RISC_OS
#     ifdef FOR_ACORN
    {
/*/* IDJ hack: 06-Jun-94 to make it work for DDE.  Needs sorting out! */
      0, (KEY_LINK), 0,
/* /* Perhaps $.clib, $.plib etc should be called $.lib */
      "$.clib", "$.clib", "$.plib", "", "$.clib.", "$.plib", "l",
      "ObjAsm -quit -stamp",
      "CHAIN:link", NULL, "",
      "", "", "",
      "o.stubs", "o.hostlib", "o.ansilib", "o.fortlib", "o.fortlib", "o.plib"
    }
#     else
    {
      0, (KEY_LINK), 0,
/* /* Perhaps $.clib, $.plib etc should be called $.lib */
      "$.clib", "$.clib", "$.plib", ".", "$.clib", "$.plib", "l",
      "ObjAsm",
      "CHAIN:link", NULL, "",
      "", "", "",
      "o.ansilib", "o.hostlib", "o.ansilib", "o.fortlib", "o.fortlib", "o.plib"
    }
#     endif
#  endif
#  ifdef COMPILING_ON_UNIX
    {
#    ifdef FORTRAN
      0, (KEY_LINK), RISCIX_FORTRAN_PRAGMAX,
#    else
      0, (KEY_PCC | KEY_LINK), 0,
#    endif
#    ifdef RISCiX113
      "/usr/include/ansi",
#    else
      "/usr/include",
#    endif
      "/usr/include", "/usr/include/iso", "/", "", "", "lst",
      "as",
      "/usr/bin/ld", "a.out", "",
#    ifdef RISCiX113
      "/lib/crt0.o", "/lib/mcrt0.o", "/lib/gcrt0.o",
#    else
      "/usr/lib/crt0.o", "/usr/lib/mcrt0.o", "/usr/lib/gcrt0.o",
#    endif
      "-lc", "", "-lc_p",
#    ifdef FORTRAN_NCLIB
      "-lnfc", "-lnfc_p",
#    else
      "-lF66,-lF77,-lI77,-lU77,-lm", "-lF66_p,-lF77_p,-lI77_p,-lU77_p,-lm_p",
#    endif
     "-lpc"
    }
#  endif /* COMPILING_ON_UNIX */
# else /* COMPILING_ON_ARM */
#  ifdef COMPILING_ON_MSDOS /* Zortech / WatCom / VC++  on MSDOS */
    {
       0, (KEY_LINK), 0,
       "\\arm\\lib", "\\arm\\lib", "", "\\", "\\arm\\lib", "", "lst",
       "armasm",
       "armlink", NULL, "",
       "", "", "",
       "armlib.o", "hostlib.o", "armlib.o", "", "", ""
    }
#  else
#  ifdef COMPILING_ON_MACINTOSH
/* arm_targetted cross_compilation : fortran & pascal not supported */
/* no default places (no root without knowing volume name) */
     {
#ifndef HOST_CANNOT_INVOKE_LINKER
       0, (KEY_LINK), 0,
#else
       0, 0, 0,
#endif
       "", "", "", ":", "", "", "lst",
       "armasm",
       "armlink", NULL, "",
       "", "", "",
       "armlib.o", "hostlib.o", "armlib.o", "", "", ""
     }
#   else
#     if defined(TARGET_IS_ARM) || defined(TARGET_IS_THUMB)
/* arm_targetted cross_compilation : fortran & pascal not supported */
       { 0, KEY_LINK, 0,
         "/usr/local/lib/arm", "/usr/local/lib/arm", "", "/", "/usr/local/lib/arm", "", "lst",
         "armasm",
         "armlink", NULL, "",
         "", "", "",
         "armlib.o", "hostlib.o", "armlib.o", "", "", ""
       }
#     else
#       error "No proper DRIVER_ENV information"
#     endif /* TARGET_IS_ARM */
#   endif /* COMPILING_ON_MACINTOSH */
#  endif /* COMPILING_ON_MSDOS */
# endif /* COMPILING_ON_ARM */
#endif /* DRIVER_ENV */
;

static struct EnvTable setupenv;

char const Tool_Name[] = TOOLFILENAME;

#ifdef COMPLING_ON_UNIX
#  define Compiling_On_Unix 1
#else
#  define Compiling_On_Unix 0
#endif

#if defined(PASCAL)
#  define LanguageIsPascal 1
#  define LanguageIsFortran 0
#elif defined(FORTRAN)
#  define LanguageIsPascal 0
#  define LanguageIsFortran 1
#else
#  define LanguageIsPascal 0
#  define LanguageIsFortran 0
#endif

typedef struct { char const **v; Uint sz; Uint n; } ArgV;
static ArgV cc_arg, cc_fil;
static ArgV ld_arg, ld_fil;

static int   cmd_error_count, main_error_count;
static int32 driver_flags;
#ifdef FORTRAN
static int32 pragmax_flags;
#endif

#ifdef HOST_OBJECT_INCLUDES_SOURCE_EXTN
#  define OBJ_EXTN LANG_EXTN_STRING ".o"
#  define ASM_EXTN LANG_EXTN_STRING ".s"
#else
#ifndef OBJ_EXTN
#  define OBJ_EXTN "o"
#endif
#ifndef ASM_EXTN
#  define ASM_EXTN "s"
#endif
#endif

static int compiler_exit_status;

void compiler_exit(int status)
{  compiler_exit_status = status;
#ifdef NLS
   msg_close(NULL);
#endif
   trackfile_finalise();
   alloc_finalise();
#ifdef COMPILING_ON_MSDOS
   (void) signal(SIGTERM, SIG_DFL);
#endif
   if (errors != NULL) fclose(errors);
   longjmp(exitbuf, 1);
}

/*
 * Join two path names and return the result.
 */

static const char *join_path(const char *root, const char *dir,
                             const char *name)
{
  if (root[0] != '\0' && name[0] != '\0')
  {   size_t rootlen = strlen(root),
             dirlen =  strlen(dir),
             namelen = strlen(name);
      char *new_name = (char *)PermAlloc((int32)rootlen+(int32)dirlen+(int32)namelen+1);
      memcpy(new_name, root, rootlen);
      memcpy(new_name+rootlen, dir, dirlen);
      memcpy(new_name+rootlen+dirlen, name, namelen+1);
      return new_name;
  }
  return name;
}

#define modifiablecopy(s) join_strs(s, "")
#define PermString(s) modifiablecopy(s)

static char *join_strs(const char *s1, const char *s2)
{
  size_t s1len = strlen(s1),
         s2len = strlen(s2);
  char *s = (char *)PermAlloc((int32)s1len + (int32)s2len + 1);
  memcpy(s, s1, s1len);
  memcpy(s+s1len, s2, s2len+1);
  return s;
}

static void AddArg(ArgV *p, char const *arg)
{
  if (p->n >= p->sz) {
    void *newv = PermAlloc(sizeof(char **) * 2 * p->sz);
    memcpy(newv, p->v, p->sz * sizeof(char **));
    p->v = (char const **)newv;
    p->sz *= 2;
  }
  p->v[p->n++] = arg;
}

static char *copy_unparse(UnparsedName *unparse,  const char *extn)
{   char *new_name;
    size_t n;
    UnparsedName u;
/* A NULL extn means use the UnparsedName as-is. A non-NULL extn means */
/* use the extn given and kill any leading path segment. In this case  */
/* we modify a local copy of the UnparsedName rather than unparse.     */
    if (extn)
    {   u = *unparse;
        u.elen = strlen(extn);
        if (u.elen == 0) extn = NULL;
        u.extn = extn;
#ifndef HOST_OBJECT_INCLUDES_SOURCE_EXTN
        u.path = NULL;
        u.plen = 0;
        u.vol  = NULL;
        u.vlen = 0;
        u.type &= ~FNAME_ROOTED;
#endif
        unparse = &u;
    }
/* Allocate space for the returned copy of the name. Allow some spare   */
/* for ^ -> .. (several times) + up to 2 extra path separators + a NUL. */
    n = unparse->vlen + unparse->plen + unparse->rlen + unparse->elen + 10;
    new_name = (char *)PermAlloc(n);
    if (fname_unparse(unparse, FNAME_AS_NAME, new_name, n) < 0)
        driver_abort("internal fault in \"copy_unparse\""); /* @@@ syserr? */
    return new_name;
}

/*
 * Get the value of an external environment variable
 */

static char *pathfromenv(char *var, char *ifnull)
{
  char *def = var==NULL ? NULL : getenv(var);
  if (def == NULL)
      return ifnull;
  else {
      def = modifiablecopy(def);
      if (Compiling_On_Unix)
      {   char *s = def;
          for (; *s != 0; s++) if (*s == ':') *s = ',';
      }
      return def;
  }
}

#ifndef C_INC_VAR
#  ifdef COMPILING_ON_RISC_OS
#    define C_INC_VAR "c$libroot"
#    define C_LIB_VAR "c$libroot"
#    define P_INC_VAR "p$libroot"
#    define P_LIB_VAR "p$libroot"
#  else
#    if defined(COMPILING_ON_UNIX) && defined(RELEASE_VSN)
#      define C_INC_VAR NULL
#      define C_LIB_VAR NULL
#      define P_INC_VAR NULL
#      define P_LIB_VAR NULL
#    else
#      define C_INC_VAR "NCC_INCLUDE_PATH"
#      define C_LIB_VAR "NCC_LIBRARY_PATH"
#      define P_INC_VAR "NPC_INCLUDE_PATH"
#      define P_LIB_VAR "NPC_LIBRARY_PATH"
#    endif
#  endif
#endif

static void get_external_environment(void)
{
  char *root = pathfromenv(C_INC_VAR, "");
  setupenv = initSetupenv;
  if (root[0] != 0)
      setupenv.include_ansi_path = setupenv.include_pcc_path = root;
  root = pathfromenv(C_LIB_VAR, setupenv.lib_root);
  if (root[0] != 0)
  {
/* Moreover the 'isalpha' is essential a file-is-rooted test.           */
/* similarly 'lib_dir' is just the (host) directory-separator.          */
#define lib_fixupname(path) \
    if (!Compiling_On_Unix || isalpha(path[0])) \
        path = join_path(root, setupenv.lib_dir, path)
    lib_fixupname(setupenv.default_lib);
    lib_fixupname(setupenv.host_lib);
    lib_fixupname(setupenv.profile_lib);
    lib_fixupname(setupenv.fort_lib);
    lib_fixupname(setupenv.fort_profile_lib);
    lib_fixupname(setupenv.link_startup);
    lib_fixupname(setupenv.profile_startup);
    lib_fixupname(setupenv.profile_g_startup);
  }
#ifdef PASCAL
  root = pathfromenv(P_INC_VAR, "");
  if (root[0] != 0)
      setupenv.include_pas_path = root;
  root = pathfromenv(P_LIB_VAR, setupenv.pas_lib_root);
  if (root[0] != 0)
  {   lib_fixupname(setupenv.pas_lib);
  }
#endif
}

typedef struct {
  char const *name;
  char const *val;
} NameVal;

typedef struct {
  ToolEnv *t;
  ToolEdit_EnumFn *f;
  void *arg;
  char const *prefix;
  size_t prefix_len;
  Uint n;
  NameVal *matches;
} TE_EnumRec;

typedef struct {
  char const *prefix;
  size_t prefix_len;
  Uint n;
} TE_CountRec;

static int TECount_F(void *arg, char const *name, char const *val) {
  TE_CountRec *tp = (TE_CountRec *)arg;
  IGNORE(val);
  if (tp->prefix_len == 0 || StrnEq(name, tp->prefix, tp->prefix_len))
    tp->n++;
  return 0;
}

Uint TE_Count(ToolEnv *t, char const *prefix) {
  TE_CountRec tr;
  tr.prefix = prefix; tr.prefix_len = strlen(prefix);
  tr.n = 0;
  toolenv_enumerate(t, TECount_F, &tr);
  return tr.n;
}

static int TE_EnumEnter(void *arg, char const *name, char const *val) {
  TE_EnumRec *tp = (TE_EnumRec *)arg;
  if (tp->prefix_len == 0 || StrnEq(name, tp->prefix, tp->prefix_len)) {
    tp->matches[tp->n].name = name;
    tp->matches[tp->n].val = val;
    tp->n++;
  }
  return 0;
}

static int CFNameVal(void const *a, void const *b) {
  NameVal const *ap = (NameVal const *)a;
  NameVal const *bp = (NameVal const *)b;
  uint32 an = strtoul(&ap->name[3], NULL, 16),
         bn = strtoul(&bp->name[3], NULL, 16);
  return an < bn  ? -1 :
         an == bn ? 0 :
                    1;
}

int Tool_OrderedEnvEnumerate(
    ToolEnv *t, char const *prefix, ToolEdit_EnumFn *f, void *arg) {
  Uint n = TE_Count(t, prefix);
  TE_EnumRec tr;
  int rc = 0;
  tr.t = t; tr.f = f; tr.arg = arg;
  tr.prefix = prefix; tr.prefix_len = strlen(prefix);
  if (n != 0) {
    Uint i;
    tr.matches = (NameVal *)malloc(n * sizeof(NameVal));
    tr.n = 0;
    toolenv_enumerate(t, TE_EnumEnter, &tr);
    qsort(tr.matches, tr.n, sizeof(NameVal), CFNameVal);
    for (i = 0; i < tr.n; i++) {
      rc = f(arg, tr.matches[i].name, tr.matches[i].val, FALSE);
      if (rc != 0) break;
    }
    free(tr.matches);
  }
  return rc;
}

Uint TE_Integer(ToolEnv *t, char const *name, Uint def) {
    char const *tval = toolenv_lookup(t, name);
    if (tval == NULL || tval[0] != '=') return def;
    return (Uint)strtoul(&tval[1], NULL, 10);
}

bool TE_HasValue(ToolEnv *t, char const *name, char const *val) {
    char const *tval = toolenv_lookup(t, name);
    return tval != NULL && StrEq(val, tval);
}

/*************************************************************/
/*                                                           */
/*      Find a command line keyword and return flag          */
/*                                                           */
/*************************************************************/

/* full case-insensitive */
bool cistreq(const char *s1, const char *s2) {
    for ( ; ; ) {
        int ch1 = *s1++, ch2 = *s2++;
        if (safe_tolower(ch1) != safe_tolower(ch2)) return NO;
        if (ch1 == 0) return YES;
    }
}

/* full case-insensitive */
bool cistrneq(const char *s1, const char *s2, size_t n) {
    while (0 < n--) {
        int ch1 = *s1++, ch2 = *s2++;
        if (safe_tolower(ch1) != safe_tolower(ch2)) return NO;
        if (ch1 == 0) return YES;
    }
    return YES;
}


/*************************************************************/
/*                                                           */
/*     Add an option to a link or assembler command.         */
/*                                                           */
/*************************************************************/

static int32 cmd_cat(char *cmd, int32 posn, const char *extra)
{
  size_t l = strlen(extra);
  if (posn != 0 && l != 0)
  {
      if (cmd != NULL) cmd[posn] = ' ';
      ++posn;
  }
  if (cmd != NULL && l != 0) memcpy(cmd + posn, extra, l+1);
  return posn + l;
}

/*************************************************************/
/*                                                           */
/*      Call the assembler to assemble a '.s' file           */
/*                                                           */
/*************************************************************/

#ifndef HOST_CANNOT_INVOKE_ASSEMBLER

#ifndef target_asm_options_
#  define target_asm_options_(x) ""
#endif

static int assembler(ToolEnv *t, const char *asm_file, const char *obj_file)
{
  int32 flags = driver_flags;
  char *cmd;
  char small_cmd[SMALL_COMMAND];

  alloc_perfileinit();
#ifndef NO_CONFIG
  config_init(t);
#endif
  cmd = NULL;
  for (;;)
  {   /* once round to count the length and once to copy the strings... */
      int32 cmdlen = cmd_cat(cmd, 0, setupenv.assembler_cmd);
      cmdlen = cmd_cat(cmd, cmdlen, target_asm_options_(t));
      if (flags & KEY_DEBUG)    cmdlen = cmd_cat(cmd, cmdlen, " -g");
      if (flags & KEY_READONLY) cmdlen = cmd_cat(cmd, cmdlen, " -R");
      if (!Compiling_On_Unix)   cmdlen = cmd_cat(cmd, cmdlen, asm_file);
      if (Compiling_On_Unix)    cmdlen = cmd_cat(cmd, cmdlen, "-o");
                                cmdlen = cmd_cat(cmd, cmdlen, obj_file);
      if (Compiling_On_Unix)    cmdlen = cmd_cat(cmd, cmdlen, asm_file);
      if (cmd != NULL) break;
      if (cmdlen < SMALL_COMMAND)
          cmd = small_cmd;
      else
          cmd = (char *)SynAlloc(cmdlen+1);
  }
  if (driver_flags & KEY_VERIFY) cc_msg("[%s]\n", cmd);
  {   int rc = system(cmd);
      drop_local_store();
      return rc;
  }
}

#endif

/*************************************************************/
/*                                                           */
/*      Link compiled files together                         */
/*                                                           */
/*************************************************************/

#ifndef target_lib_name_
#  define target_lib_name_(e,x) x
#endif

#ifndef HOST_CANNOT_INVOKE_LINKER

#ifndef LINKER_IS_SUBPROGRAM
typedef struct {
  char *cmd;
  int32 cmdlen;
  ToolEnv *t;
} LinkerLibRec;

static int LibEnum_F(void *arg, char const *name, char const *val, bool readonly) {
  LinkerLibRec *llr = (LinkerLibRec *)arg;
  IGNORE(readonly); IGNORE(name);
  llr->cmdlen = cmd_cat(llr->cmd, llr->cmdlen, target_lib_name_(llr->t, &val[1]));
  return 0;
}

#else
typedef struct {
  char **argv;
  int count;
  ToolEnv *t;
} LinkerLibRec;

static int LibEnum_F(void *arg, char const *name, char const *val, bool readonly) {
  LinkerLibRec *llr = (LinkerLibRec *)arg;
  IGNORE(readonly); IGNORE(name);
  llr->argv[llr->count++] = modifiablecopy(target_lib_name_(llr->t, &val[1]));
  return 0;
}

#endif

static void linker(ToolEnv *t, int32 flags)
{
#ifdef TARGET_IS_NULL          /* Hmmm, but, but ... */
  IGNORE(flags);
#else
  Uint count;
  const char *startup;

  alloc_perfileinit();
#ifndef NO_CONFIG
  config_init(t);
#endif
  switch (flags & (KEY_PROFILE | KEY_XPROFILE))
  {
case KEY_PROFILE:   startup = setupenv.profile_startup;    break;
case KEY_XPROFILE:  startup = setupenv.profile_g_startup;  break;
default:            startup = setupenv.link_startup;       break;
  }

#ifndef LINKER_IS_SUBPROGRAM
  { char *cmd = NULL;
    int32 cmdlen, libstart;
    char small_cmd[SMALL_COMMAND];

    for (;;)
    {   /* once round to count the length and once to copy the strings... */
        cmdlen = 0;
        cmdlen = cmd_cat(cmd, cmdlen, setupenv.link_cmd);

        for (count = 0;  count < ld_arg.n;  ++count)
            cmdlen = cmd_cat(cmd, cmdlen, ld_arg.v[count]);

        cmdlen = cmd_cat(cmd, cmdlen, "-o");
        cmdlen = cmd_cat(cmd, cmdlen, setupenv.output_file);
        cmdlen = cmd_cat(cmd, cmdlen, startup);

        for (count = 0;  count < ld_fil.n;  ++count)
            cmdlen = cmd_cat(cmd, cmdlen, ld_fil.v[count]);

        libstart = cmdlen;

        if (flags & KEY_HOST_LIB)
            cmdlen = cmd_cat(cmd, cmdlen, target_lib_name_(t, setupenv.host_lib));

#ifdef PASCAL
        cmdlen = cmd_cat(cmd, cmdlen, target_lib_name_(t, setupenv.pas_lib));
#endif
#ifdef FORTRAN
        cmdlen = cmd_cat(cmd, cmdlen, target_lib_name_(t, setupenv.fort_lib));
#endif
        {   LinkerLibRec llr;
            llr.cmd = cmd; llr.cmdlen = cmdlen; llr.t = t;
            Tool_OrderedEnvEnumerate(t, "-L.", LibEnum_F, &llr);
            cmdlen = llr.cmdlen;
        }
        if (cmd != NULL) break;
        if (cmdlen < SMALL_COMMAND)
            cmd = small_cmd;
        else
            cmd = (char *)SynAlloc(cmdlen+1);
    }
    for (; libstart < cmdlen; libstart++)
    { /* space-separate, rather than comma-join, the library list */
      if (cmd[libstart] == ',') cmd[libstart] = ' ';
    }

    if (driver_flags & KEY_VERIFY) cc_msg("[%s]\n", cmd);
    count = system(cmd);
  }
#else  /* LINKER_IS_SUBPROGRAM */
  { char **argv = (char **)SynAlloc((ld_arg.n+ld_fil.n+7+TE_Count(t, "-L.")) * sizeof(char **));
    extern int do_link(int argc, char **argv, backchat_Messenger *bc, void *bcarg);
    argv[0] = modifiablecopy(setupenv.link_cmd);
    memcpy(&argv[1], ld_arg.v, ld_arg.n * sizeof(char **));
    count = ld_arg.n+1;
    argv[count++] = "-o";
    argv[count++] = modifiablecopy(setupenv.output_file);
    if (*startup != 0) argv[count++] = modifiablecopy(startup);
    memcpy(&argv[count], ld_fil.v, ld_fil.n * sizeof(char **));
    count += ld_fil.n;
    if (flags & KEY_HOST_LIB)
      argv[count++] = modifiablecopy(target_lib_name_(t, setupenv.host_lib));

#ifdef PASCAL
    argv[count++] = modifiablecopy(target_lib_name_(t, setupenv.pas_lib));
#endif
#ifdef FORTRAN
    argv[count++] = modifiablecopy(target_lib_name_(t, setupenv.fort_lib));
#endif
    {   LinkerLibRec llr;
        llr.argv = argv; llr.count = count; llr.t = t;
        Tool_OrderedEnvEnumerate(t, "-L.", LibEnum_F, &llr);
        count = llr.count;
    }
    argv[count] = 0;
    count = do_link(count, argv, backchat.send, backchat.handle);
  }
#endif /* LINKER_IS_SUBPROGRAM */
  if (count != 0) ++main_error_count;

  /*
   * In PCC mode delete the '.o' file if only one file was compiled.
   * NB. (count==0) is used to check the link was ok.
   */
  if ((LanguageIsPascal || StrEq(toolenv_lookup(t, ".lang"), "=-pcc"))
      && cc_fil.n == 1 && ld_fil.n == 1 && count == 0)
      remove(ld_fil.v[0]);
  drop_local_store();
#endif  /* TARGET_IS_NULL */
}
#endif  /* HOST_CANNOT_INVOKE_LINKER */

static int PrintEnv(void *arg, char const *name, char const *val) {
  IGNORE(arg);
  cc_msg(" %s %s", name, val);
  return 0;
}

/*
 * Process input file names.
 */

static void process_file_names(ToolEnv *t, ArgV *v)
{
  Uint count, filc = v->n;
  int32 flags = driver_flags;
  UnparsedName unparse;

  /*
   * Reset cc_filc here - we use it to count the actual number of .c files
   * (so linker() can delete the intermediate object file in the case that
   * there is exactly 1 C file), rather than the number of files to be
   * processed by this function.
   */
  cc_fil.n = 0;

  for (count = 0; count < filc;  ++count)
  {   char const *current = v->v[count];
      int state = 0;            /* hack for contorted program flow */
      int extn_ch;
      char *source_file, *listing_file = NULL, *md_file = NULL;

      if (strlen(current) > MAX_TEXT-5)
      {   cc_msg_lookup(driver_ignored_filename_overlong, current);
          continue;
      }

      fname_parse(current, FNAME_SUFFIXES, &unparse);

#ifndef COMPILING_ON_UNIX
      if (unparse.extn == NULL)
      /* On non-Unix hosts use a sensible default if no extension was given */
#ifdef FOR_ACORN
      if (!cplusplus_flag)
#endif
      {   unparse.extn = LANG_EXTN_STRING;
          unparse.elen = sizeof(LANG_EXTN_STRING)-1;
      }
      extn_ch = unparse.extn[0];
#else
      if (unparse.extn == NULL)
          extn_ch = 0;
      else
          extn_ch = unparse.extn[0];
#endif

      switch(extn_ch)
      {
#ifndef HOST_CANNOT_INVOKE_LINKER
#  ifdef COMPILING_ON_UNIX
case 'a':
#  else
case 'O':
#  endif
case 'o':     if (!(flags & (KEY_PREPROCESS+KEY_MAKEFILE)))
              {
                  AddArg(&ld_fil, copy_unparse(&unparse, NULL));
                  break;
              }
              else cc_msg_lookup(driver_conflict_EM);
              /* and fall through ... */
#endif

default:      if (!(flags & (KEY_PREPROCESS+KEY_MAKEFILE)))
              {   if ((flags & KEY_CFRONTPREPROCESS) != 0) goto case_lang_extn;
                  cc_msg_lookup(driver_unknown_filetype, current);
                  ++cmd_error_count;
                  continue;
              }
              /* fall through again (-E, -M) */

#ifndef HOST_CANNOT_INVOKE_ASSEMBLER
/* The logical place for this code is at NO_OBJECT.. after ccom() call. */
#  ifndef COMPILING_ON_UNIX
case 'S':
#  endif
case 's':     if (!(flags & (KEY_PREPROCESS+KEY_MAKEFILE)))
              {   const char *asm_file = copy_unparse(&unparse, NULL);
                  const char *obj_file = copy_unparse(&unparse, OBJ_EXTN);
                  state = 1;
                  if (assembler(t, asm_file, obj_file) != 0)
                  {   main_error_count++;
                      remove(obj_file);
                  }
                  /* and fall through... foo.s... */
              }
              /* fall through again (-E, -M, foo.s) */
#endif

#ifdef COMPILING_ON_UNIX
case LANG_UC_EXTN:      /* unix foo.C for C++ (rework other hosts?)     */
case 'i':               /* for X/Open compliance (what about '.I'?)     */
#else
case LANG_UC_EXTN:
#endif
case_lang_extn:
case LANG_EXTN:
          {   char *out_file = setupenv.output_file;
              char *out_name = NULL;
              if ((flags & KEY_RENAME) && filc == 1 && !(flags & KEY_LINK))
                /* Assert: KEY_RENAME => setupenv.output_file != NULL */
                  out_name = out_file;
              else if (flags & KEY_ASM_OUT)
                  out_name = copy_unparse(&unparse, ASM_EXTN);

#ifdef NO_OBJECT_OUTPUT2
/* Turn "cc -c foo.c" into "cc -S foo.c"; as foo.s"                     */
              if (!(flags & (KEY_PREPROCESS|KEY_MAKEFILE|KEY_ASM_OUT)))
                  out_name = copy_unparse(&unparse, ASM_EXTN);
#endif
              if (flags & KEY_LISTING)
                  listing_file = copy_unparse(&unparse, setupenv.list);

              if (flags & KEY_MD)
                  md_file = copy_unparse(&unparse, "d");

              source_file = copy_unparse(&unparse, NULL);

              if (out_file == NULL           /* No default output file */
                  || filc != 1               /* more than 1 file */
                  || (flags & KEY_LINK)      /* going to link */
                  || !(flags & KEY_RENAME))  /* no -o <file> */
              {
                  out_file = copy_unparse(&unparse, OBJ_EXTN);
              }
                  /* else...
                   * -o && no-link && 1-file && default-op-file
                   */
              if (out_name == NULL) out_name = out_file;

              if (!(flags & (KEY_MAKEFILE+KEY_PREPROCESS)))
              {
                  AddArg(&ld_fil, out_file);
                  if (state == 1)
                     /* already called the assembler so... */ break;
              }

              if (flags & KEY_VERIFY) {
                  cc_msg("[");
                  toolenv_enumerate(t, PrintEnv, NULL);
                  cc_msg("]\n");
              }
              if (ccom(t, source_file, out_name, listing_file, md_file))
              {   ++main_error_count;
#ifdef COMPILING_ON_RISC_OS
/* The next line is dirty and should be done by checking return code,   */
/* not peeking at other's variables.                                    */
                  if (errorcount)  /* only delete o/p file if serious errors */
#endif
                      remove(out_name);
              }
#ifdef NO_OBJECT_OUTPUT2                /* @@@ '2' is a temp hack       */
#ifndef HOST_CANNOT_INVOKE_ASSEMBLER
              if (!(flags & (KEY_PREPROCESS|KEY_MAKEFILE|KEY_ASM_OUT)))
              {   if (assembler(t, out_name, out_file) != 0)
                  {   main_error_count++;
                      remove(out_file);
                  }
                  remove(out_name);
              }
#endif
#endif
          }
          /* and for the benefit of linker(), count the sources */
          ++cc_fil.n;
          break;
      }

      /*
       * If no output file has been given, derive one from the 1st file name.
       */
      if (setupenv.output_file == NULL && (flags & KEY_LINK))
          setupenv.output_file = copy_unparse(&unparse, setupenv.link_ext);
  }
}

#ifdef FORTRAN
#  define FortranUnimplementedOption(ch,current)\
    if (current[1] == ch) { nimp_option(current); break; }
#else
#  define FortranUnimplementedOption(ch,current)
#endif

/*************************************************************/
/*                                                           */
/*      Validate the command line keywords                   */
/*                                                           */
/*************************************************************/

static void validate_flags(void)
{
  int32 flags = driver_flags;

#ifdef WANT_WHINGY_MSGS_EVEN_WHEN_WRONG
  if (ld_arg.n != 0 && !(flags & KEY_LINK))
      /* Beware: the next line catches most curios, but not -lxxx   */
      cc_msg_lookup(driver_ignored_linkerflags);
#endif

  if (Compiling_On_Unix && (flags & KEY_HOST_LIB))
  {   cc_msg_lookup(driver_ignored_arthur_unix);
      flags &= ~KEY_HOST_LIB;
  }

  if (flags & KEY_COMMENT && !(flags & KEY_PREPROCESS)) flags &= ~KEY_COMMENT;

  if ((flags & (KEY_MAKEFILE+KEY_PREPROCESS+KEY_MD)) ==
               (KEY_MAKEFILE+KEY_PREPROCESS))
  {
      cc_msg_lookup(driver_conflict_EM);
      flags &= ~KEY_MAKEFILE;
  }

  if (flags & KEY_PROFILE && flags & KEY_XPROFILE) flags &= ~KEY_PROFILE;

#ifdef FORTRAN
    if (flags & KEY_STRICT)
    {   if (flags & KEY_ONETRIP)
        {   cc_msg_lookup(driver_conflict_strict_onetrip);
            flags &= ~KEY_ONETRIP;
        }
        if (flags & KEY_F66)
        {   cc_msg_lookup(driver_conflict_strict_f66);
            flags &= ~KEY_F66;
        }
        if (flags & KEY_LONGLINES)
        {   cc_msg_lookup(driver_conflict_strict_extend);
            flags &= ~KEY_LONGLINES;
        }
    }
    if ((flags & KEY_F66) && (flags & KEY_ONETRIP))
    {   cc_msg_lookup(driver_implies_f66_onetrip);
        flags &= ~KEY_ONETRIP;
    }
#endif

  driver_flags = flags;
}

static void give_help(const char *command_name)
{
#ifdef HOST_WANTS_NO_BANNER
    msg_printf(driver_banner);
#endif
#ifdef TIME_LIMIT
    {   time_t expire = TIME_LIMIT;
        msg_fprintf(driver_expire,VENDOR_NAME,ctime(&expire));
    }
#endif
    {   msg_t *p = driver_help_text;
        msg_printf(*p, command_name);
        while (*++p != NULL) msg_printf(*p,command_name);
    }
}

/*************************************************************/
/*                                                           */
/*      Set command line options for current flags           */
/*                                                           */
/*************************************************************/

#ifdef FORTRAN
static char pragmax[16];
static char pragmaw[16];
#endif

static void set_flag_options(ToolEnv *t)
{
#ifdef FORTRAN
  int32 flags = driver_flags;
  int32 pragmaw_flags = 0;
  if (flags & KEY_ONETRIP) pragmaw_flags |= F66_ONETRIP;
  if (flags & KEY_F66)
      pragmaw_flags |= (F66_ONETRIP + F66_IOSUBLIST + F66_INTRINSGO);
  if (flags & KEY_LONGLINES) pragmax_flags |= OPT_LONGLINES;
  if (flags & KEY_STRICT) pragmax_flags = 0;
  sprintf(pragmaw, "-zpw%-lu", pragmaw_flags);
  sprintf(pragmax, "-zpx%-lu", pragmax_flags);
  new_cc_arg(pragmaw);
  new_cc_arg(pragmax);
#endif

#if defined(TARGET_IS_UNIX) && defined (COMPILING_ON_ACORN_KIT)
  /* Remove -ZS<system> and -ZI<file> if -strict...                 */
  /* AM: why?  Maybe of more general use?                           */
  if (driver_flags & KEY_STRICT)
  {   tooledit_insert(t, "-ZI", NULL);
      tooledit_insert(t, "-ZS", NULL);
  }
#else
  IGNORE(t);
#endif
}

static void bad_option(const char *opt)
{
  cc_msg_lookup(driver_option_bad, opt);
  ++cmd_error_count;
}

#ifdef FORTRAN
static void nimp_option(const char *opt)
{
  cc_msg_lookup(driver_option_nimp, opt);
  ++cmd_error_count;
}
#endif

typedef struct {
  char const *prefix;
  size_t prefixlen;
  uint32 n;
} FindLastRec;

static int FindLast_F(void *arg, char const *name, char const *val) {
  FindLastRec *fr = (FindLastRec *)arg;
  IGNORE(val);
  if (StrnEq(name, fr->prefix, fr->prefixlen)) {
    uint32 n = strtoul(&name[fr->prefixlen], NULL, 16);
    if (n > fr->n) fr->n = n;
  }
  return 0;
}

static uint32 FindLast(ToolEnv *t, char const *prefix) {
  FindLastRec fr;
  fr.prefix = prefix; fr.prefixlen = strlen(prefix); fr.n = 0;
  toolenv_enumerate(t, FindLast_F, &fr);
  return fr.n;
}

static void AddInclude(ToolEnv *t, char const *prefix, char const *val) {
  char b[FILENAME_MAX+16];
  uint32 n = FindLast(t, prefix);
  sprintf(b, "%s%lx.%s", prefix, (long)((n + 0x1fffff) & ~0xfffff), val);
  tooledit_insertwithjoin(t, b, '=', val);
}

static struct { char const *name; char const *alias; } const EnvNames[] =
{ { ".-Isearch",".fk" },
  { ".rolits", ".fw" },
  { ".enums",  ".fy" },
  { ".swilr",  ".fz" }
};

static char const *EnvName(char const *alias) {
  Uint i;
  for (i = 0; i < sizeof(EnvNames) / sizeof(EnvNames[0]); i++)
    if (StrEq(alias, EnvNames[i].alias))
      return EnvNames[i].name;
  return alias;
}

static void EnvFlagSet(ToolEnv *t, char const *opts, int type, char const *valid, bool ignoreerrors) {
  char name[4]; char val[8];
  bool plus = NO;
  int opt;
  for (; (opt = *opts) != 0; ++opts)
    if (opt == '+')
      plus = YES;
    else if (opt == '-')
      plus = NO;
    else {
      int ch = safe_tolower(opt);
      if (strchr(valid, ch) == 0) {
        if (!ignoreerrors) cc_warn(warn_option_letter, type, opt);
      } else {
        sprintf(name, ".%c%c", type, ch);
        if (plus)
          sprintf(val, "=-%c+%c", type, ch);
        else
          sprintf(val, "=-%c%c", type, ch);
        tooledit_insert(t, EnvName(name), val);
      }
    }
}

static void AddDefine(ToolEnv *t, char const *s) {
  char b[256];
  char *equalp = strchr(s, '=');
  if (equalp == NULL) {
    sprintf(b, "-D%s", s);
    tooledit_insert(t, b, "?");
  } else {
    int l = equalp-s;
    sprintf(b, "-D%.*s", l, s);
    tooledit_insertwithjoin(t, b, '=', equalp);
  }
}

static void debug_set(char const *opts) {
  int opt;
  for (; (opt = *opts) != 0; ++opts) {
    uint32 debugmask = 0;
    switch (safe_toupper(opt))
    {
#ifdef ENABLE_AETREE
    case 'A': ++aetree_debugcount;
              debugmask = DEBUG_AETREE;    break;
#endif
    case 'B': debugmask = DEBUG_BIND;      break;
#ifdef ENABLE_CSE
    case 'C': ++cse_debugcount;
              debugmask = DEBUG_CSE;       break;
#endif
    case 'D': debugmask = DEBUG_DATA;      break;
    case 'E': debugmask = DEBUG_TEMPLATE;  break;
    case 'F': debugmask = DEBUG_FNAMES;    break;
    case 'G': debugmask = DEBUG_CG;        break;
    case 'H': debugmask = DEBUG_SPILL;     break;
    case 'I': ++files_debugcount;
              debugmask = DEBUG_FILES;     break;
    case 'J': debugmask = DEBUG_SR;        break;
#ifdef ENABLE_LOCALCG
    case 'K': ++localcg_debugcount;
              debugmask = DEBUG_LOCALCG;   break;
#endif
    case 'L': debugmask = DEBUG_LEX;       break;
    case 'M': debugmask = DEBUG_MAPSTORE;  break;
    case 'O': debugmask = DEBUG_OBJ;       break;
    case 'P': debugmask = DEBUG_PP;        break;
    case 'Q': debugmask = DEBUG_Q;         break;
    case 'R': debugmask = DEBUG_REGS;      break;
    case 'S': debugmask = DEBUG_SYN;       break;
    case 'T': debugmask = DEBUG_TYPE;      break;
    case 'U': debugmask = DEBUG_STORE;     break;
    case 'W': debugmask = DEBUG_2STORE;    break;
    case 'X': debugmask = DEBUG_X;         break;
    case 'Y': debugmask = DEBUG_LOOP;      break;

    case 'Z': ++syserr_behaviour;
#ifndef COMPILING_ON_MSDOS
#ifdef __CC_NORCROFT
              (void) signal(SIGINT, SIG_DFL);     /* permit NorCroft backtrace */
#endif
#endif
              break;
    default:  cc_warn(warn_option_zq, opt);
    }
    sysdebugmask |= debugmask;
  }
}

static void AddDebugFlags(char *s, uint32 tflags, char const *fl) {
  char const *p;
  for (p = fl; *p != 0; p++)
    if (!(tflags & (1L << (*p - 'a'))))
      *s++ = *p;
  *s++ = '+';
  for (p = fl; *p != 0; p++)
    if (tflags & (1L << (*p - 'a')))
      *s++ = *p;
  *s = 0;
}

static int ogflags;
#define OG_O 1
#define OG_G 2
#define OG_GX 4

static bool HandleArg(ToolEnv *t, char const *current, char const *nextarg, bool ignoreerrors) {
  int32 flags = driver_flags;
  int uc_opt = safe_toupper(current[1]);
  bool usednext = NO;
  char b[512];
  switch(uc_opt)
  {
#ifdef FORTRAN
  case 'F': if (current[1] == 'f') break;
/* @@@ LDS 10Aug89 - DO NOT CATCH 'O' HERE - IT BREAKS Unix Makefiles */
  case 'M': if (current[1] == 'M') break;
  case 'U':
  case 'V':
#else
#ifndef DISABLE_ERRORS
  case 'E': if (current[2] == 'S' && current[3] == 0) break;
#endif
#ifndef PASCAL /*ECN*/
  case 'R':
#endif
#endif
  case 'C':
  case 'S': if (current[2] == 0) break;
            if (!ignoreerrors) bad_option(current);
  }

  switch(uc_opt)
  {
#ifdef FORTRAN
  case '1':   flags |= KEY_ONETRIP;
              break;

  case 'C':   if (current[1] == 'c') flags &= ~KEY_LINK;
              else pragmax_flags |= OPT_CHECKSUB;
              break;

  case 'I':   if ((current[1] == 'i') && (current[2] == '2'))
                  pragmax_flags |= OPT_DEFHINTEGER;
              else goto may_take_next_arg;
              break;

  case 'N':   break;

  case 'O':   if (current[1] == 'o') goto may_take_next_arg;
              if (current[2] != 0) /* -O has no effect currently */
              {
                  int n = (current[2] - '0');
                  if ((current[3] != 0) || (n < 0) || (n > MINO_MAX)) {
                      if (!ignoreerrors) bad_option(current);
                  } else
                  {
                      new_cc_arg((n & MINO_CSE) ? "-ZPZ1" : "-ZPZ0");
                      if (n & MINO_NAO) pragmax_flags |= OPT_NOARGALIAS;
                      else pragmax_flags &= ~OPT_NOARGALIAS;
                  }
              }
              break;

  case 'R':   if (current[1] == 'R') nimp_option(current);
              else {
                if (current[2] == '8')
                  pragmax_flags |= OPT_DEFDOUBLE;
                else {
                  new_cc_arg("-R");
                  if (Compiling_On_Unix) flags |= KEY_READONLY;
                }
              } break;

  case 'U':   if (current[1] == 'U') pragmax_flags &= ~EXT_CASEFOLD;
              else pragmax_flags |= OPT_IMPUNDEFINED;
              break;

  case 'V':   if (current[1] == 'v') {
                 new_cc_arg("-FB");
                 if (!ignoreerrors) cc_msg_lookup(driver_banner);
              }
              else goto link_command;
              break;

#else /* FORTRAN */
  case 'C':   if (current[1] == 'c')
                  flags &= ~KEY_LINK;
              else
                  tooledit_insert(t, "-C", "?");
              break;

  case 'I':
  case 'J':   goto may_take_next_arg;

  case 'O':   if (current[1] == 'o') goto may_take_next_arg;
              ogflags |= OG_O;
              if (current[2] != 0) {
                  if (cistreq(&current[2], "time"))
                      tooledit_insert(t, "-O", "=time");
                  else if (cistreq(&current[2], "space"))
                      tooledit_insert(t, "-O", "=space");
                  else if (!ignoreerrors)
                      bad_option(current);
              }
              break;

#endif /* FORTRAN */

  case '\0':  flags |= KEY_STDIN;    /* '-' on its own denotes stdin... */
              break;

  case 'E':   FortranUnimplementedOption('E', current);
#ifdef DISABLE_ERRORS
              /* provide support for -Exyz to suppress certain errors.  */
              if (current[2] != 0) {
                  EnvFlagSet(t, &current[2], 'E', "acfilmpvz", ignoreerrors);
                  break;
              }
#endif
              if (Compiling_On_Unix && current[1] == 'e')
                  goto may_take_next_arg;      /* X/Open -e epsym to ld */
#ifdef COMPILING_ON_MVS
              if (current[2])
              {   if (!ignoreerrors) cc_warn(warn_option_E, current);
                  break;
              }
#endif
              tooledit_insert(t, ".pp_only", "?");
              flags &= ~KEY_LINK;
              break;

  case 'F':   FortranUnimplementedOption('F', current);
              EnvFlagSet(t, &current[2], 'f', "abcdefhijklmnopqrstuvwxyz", ignoreerrors);
              break;

  case 'G':   ogflags |= OG_G;
              if (current[2] == 0) {
                  tooledit_insert(t, "-g", "=+");
                  tooledit_insert(t, "-gt", "=+flvp");
                  tooledit_insert(t, "-gx", "?");
              } else if (current[2] == 'x') {
                  ogflags |= OG_GX;
                  tooledit_insertwithjoin(t, "-gx", '=', &current[3]);
                  /* just option setting; no -g implication */
                  break;
              } else if (current[2] == 't') {
                  tooledit_insertwithjoin(t, "-gt", '=', &current[3]);
                  /* just option setting; no -g implication */
                  break;
              } else if (current[2] == '-') {
                  tooledit_insert(t, "-g", "=-");
                  break;
              } else if (current[2] == '+') {
                  tooledit_insert(t, "-g", "=+");
                  break;
              } else {
                /* old fashioned -g with flags option */
                  char const *p = &current[2];
                  int ch;
                  uint32 tflags = 0, optflags = 0;
                  while ((ch = *p++) != 0)
                    switch (ch) {
                    case 'f': case 'l': case 'v': case 'p':
                      tflags |= (1L << (ch - 'a')); break;

                    case 'c': case 'r': case 'g': case 'o':
                      optflags |= (1L << (ch - 'a')); break;
                    }
                  if (tflags == 0)
                    tooledit_insert(t, "-gt", "=+flvp");
                  else {
                    char s[6];
                    AddDebugFlags(s, tflags, "flpv");
                    tooledit_insertwithjoin(t, "-gt", '=', s);
                  }
                  if (optflags == 0)
                    tooledit_insert(t, "-gx", "?");
                  else {
                    char s[5]; int i = 0;
                    for (ch = 'a'; ch <= 'z'; ch++)
                      if (optflags & (1L << (ch - 'a')))
                        s[i++] = ch;
                    s[i] = 0;
                    ogflags |= OG_GX;
                    tooledit_insertwithjoin(t, "-gx", '=', s);
                  }
                  tooledit_insert(t, "-g", "=+");
              }
              if (Compiling_On_Unix)
                  AddInclude(t, "-L.", "g");
              else {
                  flags |= KEY_DEBUG;
                  AddArg(&ld_arg, "-d");
              }
              break;

  case 'L':   if (Compiling_On_Unix)
              {   if (current[1] == 'l')
                      AddInclude(t, "-L.", &current[2]);
                  else
                      AddArg(&ld_arg, current);
              }
              else goto may_take_next_arg;
              break;

  case 'M':   FortranUnimplementedOption('m', current);
              if (Compiling_On_Unix && current[1] == 'm')  /* request link map */
                  AddArg(&ld_arg, current);
              else
              switch(safe_toupper(current[2]))
              {
      case 'X':   if (current[3] != 0) goto defolt;
                  tooledit_insert(t, "-M", "=<");
                  flags &= ~KEY_LINK;
                  break;
      case '\0':  tooledit_insert(t, "-M", "?");
                  flags &= ~KEY_LINK;
                  break;
      case 'D':   if (current[3] == '\0' ||
                      current[3] == '-' && current[4] == 0)
                  {   tooledit_insert(t, "-M", "=D");
                      if (current [3] == 0) flags |= KEY_MD;
                      break;
                  }
      default:
      defolt:     if (!ignoreerrors) bad_option(current);
              }
              break;

  case 'P':   uc_opt = safe_toupper(current[2]);
              switch(uc_opt)
              {
      case '\0':  flags |= KEY_PROFILE;
                  break;
      case 'G':
      case 'X':   if (current[3] == '\0')
                  {   flags |= KEY_XPROFILE;
                      break;
                  }
      default:    if (!ignoreerrors) bad_option(current);
                  return usednext;
              }
              if (current[2] == 0)
                  tooledit_insert(t, "-p", "?");
              else
                  tooledit_insertwithjoin(t, "-p", '=', &current[2]);
              if (setupenv.profile_lib[0] != '\0')
                  setupenv.default_lib = setupenv.profile_lib;
              if (setupenv.fort_profile_lib[0] != '\0')
                  setupenv.fort_lib = setupenv.fort_profile_lib;
              break;

#ifndef FORTRAN
  case 'R':
              if (Compiling_On_Unix && current[1] == 'r')
                  AddArg(&ld_arg, "-r");    /* X/Open compliance */
              else {
#ifdef PASCAL /*ECN*/
                  EnvFlagSet(t, &current[2], 'r', "acdnpr", ignoreerrors);
#else
                  tooledit_insert(t, ".rolits", "=-f+w");
#endif
                  if (Compiling_On_Unix) flags |= KEY_READONLY;
              }
              break;
#endif

  case 'S':
              if (Compiling_On_Unix && current[1] == 's')
                  AddArg(&ld_arg, "-s");
              else {
                  flags = (flags & ~KEY_LINK) | KEY_ASM_OUT;
                  tooledit_insert(t, ".asm_out","?");
              }
              break;

  case 'W':   if (current[2] == 0) {
                EnvFlagSet(t, "adfgilnprv", 'W', "acdfgilmnoprstuvz", ignoreerrors);
                tooledit_insert(t, ".nowarn", "=-W");
              } else
                EnvFlagSet(t, &current[2], 'W', "acdfgilmnoprstuvz", ignoreerrors);
              break;

  case 'Z':   uc_opt = safe_toupper(current[2]);
              switch(uc_opt)
              {
      case '\0':  /* Pass on '-z' to the linker */
                  goto link_command;

      case 'A':   if (safe_toupper(current[3]) == 'P' && isdigit(current[4])) {
                      if (tooledit_insertwithjoin(t, "-zap", '=', &current[4]) != TE_Failed)
                          break;
                  }
#ifdef MIN_ALIGNMENT_CONFIGURABLE
                  else if (safe_toupper(current[3]) == 'S' && isdigit(current[4])) {
                      if (tooledit_insertwithjoin(t, "-zas", '=', &current[4]) != TE_Failed)
                          break;
                  } else if (safe_toupper(current[3]) == 'T' && isdigit(current[4])) {
                      if (tooledit_insertwithjoin(t, "-zat", '=', &current[4]) != TE_Failed)
                          break;
                  }
#endif
                  goto check_mcdep;

      case 'C':   tooledit_insert(t, ".schar", "=-zc");
                  break;
      case 'I':   if (isdigit(current[3]))
                      goto check_mcdep;
                  goto may_take_next_arg;
      case 'Q':   debug_set(&current[3]); break;

      case 'O':   tooledit_insert(t, ".areaperfn", "=-zo");
                  break;
      case '+':   switch (safe_toupper(current[3])) {
                  case 'O': tooledit_insert(t, ".areaperfn", "=-z+o"); break;
                  case 'C': tooledit_insert(t, ".schar", "=-z+c"); break;
                  default:  goto check_mcdep;
                  }
                  break;
#ifndef NO_DUMP_STATE
      case 'G':   switch (safe_toupper(current[3])) {
                  case 'W': tooledit_insertwithjoin(t, "-zgw", '=', &current[4]); break;
                  case 'R': tooledit_insertwithjoin(t, "-zgr", '=', &current[4]); break;
                  default:  goto check_mcdep;
                  }
                  break;
#endif
      case 'J':   tooledit_insert(t, "-zj", "?");
                  break;
      case 'P':   if (isalpha(current[4])) {
                    bool negate;
                    PragmaSpelling const *p = keyword_pragma(&current[3], &negate);
                    if (p != NULL) {
                      int32 val = p->value;
                      if (negate) {
#ifdef FORTRAN
                        if (pragchar == 'x' || pragchar == 'w')
                          val = ~val;
                        else
#endif
                          val = !val;
                      }
                      sprintf(b, "-zp%c", p->code);
                      sprintf(&b[8], "=%#lx", (long)val);
                      tooledit_insert(t, b, &b[8]);
                    }
                  } else {
                    sprintf(b, "-zp%c", current[3]);
                    tooledit_insertwithjoin(t, b, '=', &current[4]);
                  }
                  break;
      case 'T':   tooledit_insert(t, "-disallow_tentative_statics", "?");
                  break;
      case 'Z':   if (safe_toupper(current[3]) == 'T')
                  {
                      tooledit_insert(t, "-disallow_tentative_statics", "?");
                      current++;
                  }
                  tooledit_insertwithjoin(t, "-zz", '=', &current[3]);
                  break;

      check_mcdep:
      default:    if (!mcdep_config_option(current[2], &current[3], t)) {
                      if (!ignoreerrors) cc_warn(warn_option, current);
                  }
                  break;
              }
              break;

  link_command:
  default:
#ifndef HOST_CANNOT_INVOKE_LINKER
              AddArg(&ld_arg, current);  break;
#else
              if (!ignoreerrors) bad_option(current);
              break;
#endif

#ifndef FORTRAN
  case 'U':
#endif
  case 'D':
  may_take_next_arg:
              uc_opt = safe_toupper(current[1]);
              if (uc_opt == 'Z')
              {   uc_opt = safe_toupper(current[2]);
                  if (uc_opt == 'I') uc_opt = 'S'; else uc_opt = 'Z';
              }
              if (current[2] == 0 || uc_opt == 'S' ||
                  current[3] == 0 && uc_opt == 'Z')
              {   if (nextarg == NULL) {
                      if (!ignoreerrors) cc_msg_lookup(driver_option_missing_arg, current);
                      ++cmd_error_count;
                      break;
                  }
                  usednext = YES;
              }
              else if (uc_opt == 'Z')
                  nextarg = &current[3];
              else
                  nextarg = &current[2];
              switch (uc_opt)
              {
#ifdef COMPILING_ON_UNIX
      case 'E':            /* actually can only be "-e" here... X/Open */
#endif
      case 'U':
                  if (Compiling_On_Unix && current[1] != uc_opt)  /* e or u */
                  {   char *next = join_strs("-e ", nextarg);
                      next[1] = current[1];
                      AddArg(&ld_arg, next);           /* X/Open */
                      break;
                  } /* 'U' falls through */
                  sprintf(b, "-D%s", nextarg);
                  tooledit_insert(t, b, "=");
                  break;

      case 'D':   AddDefine(t, nextarg);
                  break;
      case 'I':   AddInclude(t, "-I.", nextarg);
                  break;
      case 'J':   AddInclude(t, "-J.", nextarg);
                  break;
#ifndef HOST_CANNOT_INVOKE_LINKER
      case 'L':   AddInclude(t, "-L.", nextarg);
                  break;
#endif
      case 'O':   flags |= KEY_RENAME;
                  {   UnparsedName unparse;
                      fname_parse(nextarg, FNAME_SUFFIXES, &unparse);
                      setupenv.output_file = copy_unparse(&unparse, NULL);
                  }
                  break;
      case 'S':   /* -ZI<system> file */
                  tooledit_insertwithjoin(t, "-ZS", '=', &current[3]);
                  tooledit_insertwithjoin(t, "-ZI", '=', nextarg);
                  break;
      case 'Z':   tooledit_insertwithjoin(t, "-zz", '=', nextarg);
                  break;
              }
  }
  driver_flags = flags;
  return usednext;
}

/*
 * Extract compilation options from the command line.
 */

typedef struct { char const *name; int32 key; char const *envname; char const *envval; } KW;

static KW const keytab[] = {
      {"-help",      KEY_HELP, NULL, NULL},
      {"-h",         KEY_HELP, NULL, NULL},
      {"-verify",    KEY_VERIFY, NULL, NULL},
      {"-echo",      0, ".echo", "=-echo"},
      {"-link",      KEY_LINK, NULL, NULL},
      {"-list",      KEY_LISTING, NULL, NULL},
      {"-errors",    KEY_NEXT+KEY_ERRORSTREAM, NULL, NULL},
      {"-via",       KEY_NEXT+KEY_VIAFILE, NULL, NULL},
      {"-config",    KEY_CONFIG},
#ifdef TARGET_ENDIANNESS_CONFIGURABLE
      {"-littleend", 0, ".bytesex", "=-li"},
      {"-li",        0, ".bytesex", "=-li"},
      {"-bigend",    0, ".bytesex", "=-bi"},
      {"-bi",        0, ".bytesex", "=-bi"},
#endif
#if defined(PASCAL) /*ECN*/
      {"-iso",       0, ".lang", "-iso"},
      {"-arthur",    KEY_HOST_LIB, NULL, NULL},
      {"-super",     KEY_HOST_LIB, NULL, NULL},
      {"-counts",    KEY_COUNTS+KEY_LISTING, NULL, NULL},
#elif defined(FORTRAN)
#  ifndef TARGET_IS_UNIX
      {"-bsd",       KEY_PCC, NULL, NULL},
#  endif
      {"-onetrip",   KEY_ONETRIP, NULL, NULL},
      {"-fussy",     KEY_STRICT, NULL, NULL},
      {"-f66",       KEY_F66, NULL, NULL},
      {"-strict",    KEY_STRICT, NULL, NULL},
      {"-extend",    KEY_LONGLINES, NULL, NULL},
#else /* not FORTRAN or PASCAL */
      {"-ansi",      0, ".lang", "=-ansi"},
      {"-ansic",     0, ".lang", "=-ansi"},
      {"-pcc",       0, ".lang", "=-pcc"},
      {"-fussy",     0, ".lang", "=-strict"},
      {"-strict",    0, ".lang", "=-strict"},
      {"-pedantic",  0, ".lang", "=-strict"},
#ifdef CPLUSPLUS
      {"-cfront",    0, ".lang", "=-cfront"},
      {"-cpp",       0, ".lang", "=-cpp"},
#endif
      {"-arthur",    KEY_HOST_LIB, NULL, NULL},
      {"-super",     KEY_HOST_LIB, NULL, NULL},
      {"-counts",    KEY_COUNTS+KEY_LISTING, NULL, NULL},
#  ifdef FOR_ACORN
      {"-throwback", KEY_THROWBACK, NULL, NULL},
      {"-desktop",   KEY_NEXT+KEY_DESKTOP, NULL, NULL},
      {"-depend",    KEY_NEXT+KEY_DEPEND, NULL, NULL},
      {"-c++",       KEY_CFRONTPREPROCESS, NULL, NULL},
#  endif
#  ifdef RISCiX113
      {"-riscix1.2", KEY_RIX120, NULL, NULL},
#  endif
#if RECORD_SOURCE_LOCATION
      {"--asm-includes-location", 0, ".--asm-includes-location", "=1" },
#endif
#endif /* PASCAL */
};

static KW const *keyword(const char *string)
{
  unsigned count;
  for (count = 0;  count < sizeof(keytab)/sizeof(keytab[0]);  ++count)
      if (cistreq(string, keytab[count].name))
          return &keytab[count];

  return NULL;
}

typedef struct {
  char const *s;
  Uint i;
} ViaSRec;

static int vias_getc(void *arg) {
  ViaSRec *p = (ViaSRec *)arg;
  int ch = p->s[p->i];
  if (ch == 0) return EOF;
  p->i++;
  return ch;
}

static int via_getc(void *arg) {
  return fgetc((FILE *)arg);
}

static int mapvia(
  void *v, int (*getcfn)(void *), char const *viafile, char **newargv)
{   int ch, newargc;
    bool got_via = NO;
    char word[128];

    if (v == NULL)
    {   cc_msg_lookup(driver_via_not_opened, viafile);
        compiler_exit(1);
    }
    for (newargc = 0, ch = ' ';;)
    {   unsigned p = 0;
        while (ch != EOF && isspace(ch)) ch = getcfn(v);
        if (ch == EOF) break;
        if (ch == '"' || ch == '\'') {
            int quote = ch;
            for (;;) {
                ch = getcfn(v);
                if (ch == EOF || ch == quote) break;
                if (p < (sizeof(word)-1)) word[p++] = ch;
            }
        } else
            do
            {   if (p < (sizeof(word)-1)) word[p++] = ch;
                ch = getcfn(v);
            } while (ch != EOF && !isspace(ch));
        word[p] = 0;
        if (got_via)
        {   FILE *f = fopen(word, "r");
            newargc += mapvia(f, via_getc, word, newargv==NULL ? NULL : newargv+newargc);
            fclose(f);
            got_via = NO;
        }
        else if (cistreq(word, "-via"))
            got_via = YES;
        else
        {   if (newargv != NULL) {
                size_t len = strlen(word)+1;
                newargv[newargc] = (char *)memcpy(PermAlloc((int32)len), word, len);
            }
            ++newargc;
        }
    }
    return newargc;
}

static void read_options(
    int count, int argc, char **argv, ToolEnv *t, bool ignoreerrors) {
  for (; count < argc;  ++count)
  {   char const *arg = argv[count];
      KW const *key = keyword(arg);
      if (key == NULL)
      {   KW_Status status = mcdep_keyword(arg, argv[count+1], t);
          if (status == KW_OKNEXT) {
              count++;
              continue;
          } else if (status == KW_OK) {
              continue;
          } else if (status != KW_NONE) {
              if (!ignoreerrors) {
                  cc_msg_lookup(driver_option_bad1);
                  cc_msg("'%s", arg);
                  if (status == KW_BADNEXT)
                      cc_msg(" %s", argv[++count]);
                  cc_msg("'");      /* makes NLS string more sensible */
                  cc_msg_lookup(driver_option_bad2);
              }
              ++cmd_error_count;
              continue;
          }
      } else if (key->envname != NULL) {
          char b[64];
          char const *s = key->envval;
          if (StrEq(key->envname, ".lang")) {
              char const *val = toolenv_lookup(t, key->envname);
              if (StrEq(key->envval, "=-strict")) {
                  if (strchr(val, ' ') == NULL) {
                      strcpy(b, val);
                      strcat(b, " -strict");
                      s = b;
                  }
              } else if (StrEq(val, "=-strict")) {
                  strcpy(b, key->envval);
                  strcat(b, " -strict");
                  s = b;
              }
          }
          tooledit_insert(t, key->envname, s);
          continue;
      } else {
          if (key->key & KEY_NEXT) {
              if (++count >= argc) {
                  if (ignoreerrors)
                      return;
                  else {
                      cc_msg_lookup(driver_option_missing_filearg, arg);
                      compiler_exit(1);
                  }
              }
#ifdef FOR_ACORN
              if (key->key & KEY_DEPEND) {
                  tooledit_insert(t, "-M", "=+");
                  tooledit_insertwithjoin(t, ".depend", '=', argv[count]);
              }

              else if (key->key & KEY_DESKTOP)
                  dde_desktop_prefix = argv[count];

              else
#endif
              if (key->key & KEY_ERRORSTREAM) {
                  if (!ignoreerrors) {
                      errors = fopen(argv[count], "w");
                      if (errors == NULL) {
                          cc_msg_lookup(driver_cant_open_output, argv[count]);
                          compiler_exit(1);
                      }
                  }
                  argv[count] = NULL;
              } else if (key->key & KEY_VIAFILE) {
                  FILE *v = fopen(argv[count], "r");
                  int n = mapvia(v, via_getc, argv[count], NULL);
                  if (n < 0) {
                      if (ignoreerrors)
                          return;
                      else
                          compiler_exit(1);
                  }
                  if (n == 0)
                      ++count;
                  else {
                      char **newargv = (char **)
                          PermAlloc(sizeof(char *) * ((int32)argc - count + n + 1));
                      int j;
                      fseek(v, 0L, SEEK_SET);
                      n = mapvia(v, via_getc, NULL, &newargv[1]);
                      for (j = count;  ++j < argc;)
                          newargv[++n] = argv[j];
                      newargv[++n] = NULL;
                      count = 0;
                      argc = n;
                      argv = newargv;
                  }
                  fclose(v);
              }
          }
#if defined(FORTRAN) && !defined(TARGET_IS_UNIX)
          else if (key->key == KEY_PCC)
              pragmax_flags = RISCIX_FORTRAN_PRAGMAX;
#endif
#ifdef FOR_ACORN
          else if (key->key & KEY_THROWBACK)
              dde_throwback_flag = 1;
          else if (key->key & KEY_CFRONTPREPROCESS)
              cplusplus_flag = 1;
#endif
          else if (key->key & KEY_COUNTS) {
              tooledit_insert(t, "-K", "?");
              driver_flags |= key->key;
          } else
              driver_flags |= key->key;
          continue;
      }
        /* not a keyword argument */
      if (arg[0] == '-') {
          if (HandleArg(t, arg, argv[count+1], ignoreerrors))
              count++;
      } else {
          AddArg(&cc_fil, arg);
      }
  }
  if (ogflags & OG_O) {
      tooledit_insert(t, "-zpz", "=1");
      if (ogflags & OG_G && !(ogflags & OG_GX))
          tooledit_insert(t, "-gx", "=o");
  }

#ifdef PASCAL /*ECN*/
  driver_flags |= KEY_ANSI;
#endif
}

void TE_DecodeArgumentLine(ToolEnv *t, char const *s, bool ignoreerrors) {
  ViaSRec vr;
  int n;
  vr.i = 0; vr.s = s;
  n = mapvia(&vr, vias_getc, NULL, NULL);
  if (n < 0) compiler_exit(1);
  if (n > 0) {
    char **newargv = (char **)PermAlloc(sizeof(char *) * ((int32)n+1));
    vr.i = 0;
    n = mapvia(&vr, vias_getc, NULL, newargv);
    newargv[n] = NULL;
    read_options(0, n, newargv, t, ignoreerrors);
  }
}

static void FinishedOptions(ToolEnv *t) {
#ifdef RISCiX113
  if (!(driver_flags & KEY_RIX120))
      tooledit_insert(t, "-D__type", "==___type");
#endif

  if (FindLast(t, "-J.") == 0) {
      /*
       * No -J so add default system path to -I list
       */
#ifdef PASCAL
      const char *path = setupenv.include_pas_path;
#else
      const char *path = setupenv.include_pcc_path;
#  ifdef RISCiX113
      if (((flags & KEY_ANSI) || !(flags & (KEY_PCC))) &&
          !(flags & KEY_RIX120))
          path = setupenv.include_ansi_path;
#  endif
#endif
      AddInclude(t, "-I.", path);
  }

  /* If compiling on Unix and in Ansi mode add extra libraries. */
/*
 * ACN: Oh misery - if I am compiling and linking under Unix, but to generate
 * Helios binaries, I do not want to scan the extra libraries indicated
 * here.  I think the problem here is mostly because TARGET_IS_HELIOS
 * improperly sets the KEY_UNIX bit in flags - but to invent a KEY_HELIOS
 * would also be some work since elsewhere in this code there seems
 * to be a dichotomy assumed between Unix and Risc-OS...
 * AM: except for this file the alternative of MVS should be possible!
 * Thus the conditional
 * compilation here seems (in the short term) my easiest way out.
 */
#ifdef RISCiX113
  if (((flags & KEY_ANSI) || !(flags & (KEY_PCC))) &&
      !(flags & KEY_RIX120))
  {
      AddInclude(t, "-L.", "ansi");
      AddInclude(t, "-L.", "m");
  }
#endif

  if (FindLast(t, "-L.") == 0 || Compiling_On_Unix)
      AddInclude(t, "-L.", setupenv.default_lib);

}

/*
 * Main.
 */

static void InitArgV(ArgV *p, int n) {
  p->v = (char const **)PermAlloc(sizeof(char *) * n);
  p->sz = n; p->n = 0;
}

static char *progname_copy;
char const *compiler_name(void) { return progname_copy; }

static void *falloc(size_t n) { return PermAlloc(n); }

static int cc_main(int argc, char **argv, ToolEnv *t)
{
  char *progname;
  bool is_cpp = NO;
#if (defined(COMPILING_ON_UNIX) && defined(FORTRAN))
  progname = "f77"; /* rather than the "f77comp" we would get from argv[0] */
#else
  char p[32];
  char *default_output = setupenv.output_file;
#endif

  errors = NULL;
  sysdebugmask     = 0;
  syserr_behaviour = 0;
  aetree_debugcount = 0;
#ifdef ENABLE_CSE
  cse_debugcount   = 0;
#endif
  localcg_debugcount = 0;
#ifdef TARGET_HAS_DEBUGGER
  usrdbgmask       = 0;
#endif

  alloc_initialise();
  trackfile_initialise(falloc);
  errstate_initialise();

  progname = program_name(argv[0], p, 32);
  progname_copy = PermString(progname);
#ifdef TIME_LIMIT
  if (time(0) > TIME_LIMIT) {
    fprintf(stderr, "This time-limited software has expired.\nPlease contact "
                    VENDOR_NAME     /* specified in options.h */
                    " for an up to date release.\n");
    compiler_exit(99);
  }
#endif
  main_error_count = cmd_error_count = 0;

#ifdef CHECK_AUTHORIZED
  check_authorized();
#endif

#ifdef NLS
  msg_init(argv[0], MSG_TOOL_NAME);
#endif

#ifndef HOST_WANTS_NO_BANNER
    cc_msg_lookup(driver_banner);
#endif
#ifndef COMPILING_ON_UNIX
#ifndef COMPILING_ON_MSDOS
  (void) signal(SIGINT, compile_abort);
#else /* DOS, Windows, Win32 */
  (void) signal(SIGTERM, compile_abort);
#endif
#else
#  ifdef DRIVER_PRE_RELEASE_MSG
     cc_msg_lookup(driver_prerelease);
#  endif
#ifndef COMPILING_ON_MSDOS
  /* The signal ignore state can be inherited from the parent... */
  if (signal(SIGINT, SIG_IGN) != SIG_IGN)
    (void) signal(SIGINT, compile_abort);
#ifdef SIGHUP
  if (signal(SIGHUP, SIG_IGN) != SIG_IGN)
    (void) signal(SIGHUP, compile_abort);
#endif
  if (signal(SIGTERM, SIG_IGN) != SIG_IGN)
    (void) signal(SIGTERM, compile_abort);
#endif
#endif

  get_external_environment();
  driver_flags = setupenv.initial_flags;
#ifdef FORTRAN
  pragmax_flags = setupenv.initial_pragmax;
#endif

  if (argc == 1)
  {   /* used with no argument */
      give_help(progname);
      compiler_exit(1);
  }

  {   UnparsedName un;
      fname_parse(argv[0], ".exe .EXE" , &un);
      if (un.rlen == 3 &&
          (StrnEq(un.root, "cpp", 3) ||
           StrnEq(un.root, "CPP", 3)))
      {
          /* The compiler was called as '...cpp' - treat as 'cc -E'.  */
          driver_flags = (driver_flags | KEY_PREPROCESS) & ~KEY_LINK;
          tooledit_insert(t, ".pp_only", "?");
      }
  }

  InitArgV(&cc_arg, argc);
  InitArgV(&cc_fil, argc);
  InitArgV(&ld_arg, argc);
  InitArgV(&ld_fil, argc);

  { char const *etc = toolenv_lookup(t, ".etc");
    if (etc != NULL) TE_DecodeArgumentLine(t, &etc[1], NO);
  }
  read_options(1, argc, argv, t, NO);

#ifdef FOR_ACORN
  if (!(driver_flags & KEY_CFRONTPREPROCESS))
      /* IDJ: 06-Jun-94: banner if not -c++ */
      cc_msg_lookup(driver_banner);
#endif

  validate_flags();
  if (driver_flags & KEY_HELP)
  {   give_help(progname);
      compiler_exit(0);
  }
  if (driver_flags & KEY_CONFIG)
  {   if (toolenv_putinstallationdelta(t) != 0)
      {   cc_msg_lookup(driver_toolenv_writefail);
          compiler_exit(EXIT_error);
      }
      compiler_exit(0);
  }

  FinishedOptions(t);

  {   char const *echoval = toolenv_lookup(t, ".echo");
      if (echoval != NULL && StrEq(echoval, "=-echo")) {
          size_t atstart = 1;
          char line[256];
          char *dynline = NULL;
          char *linep = line;
          int len;
          if (argv[0] != NULL) atstart += strlen(argv[0])+1;
          len = tooledit_getcommandline(t, line+atstart, 254-atstart);
          if (len > (int)(254-atstart)) {
            dynline = (char *)malloc(len+2+atstart);
            len = tooledit_getcommandline(t, dynline+atstart, len+2);
            linep = dynline;
          }
          linep[0] = '[';
          if (argv[0] != NULL) {
            strcpy(linep+1, argv[0]);
            linep[atstart-1] = ' ';
          }
          linep[len+atstart-1] = ']';
          linep[len+atstart] = '\n';
          linep[len+atstart+1] = 0;
          cc_msg(linep);
          if (dynline != NULL) free(dynline);
      }
  }
  set_flag_options(t);

  if (toolenv_lookup(t, ".pp_only") != NULL)
  {   is_cpp = YES;
      if (cc_fil.n >= 2)
      {   if (cc_fil.n > 2)
              cc_msg_lookup(driver_cpp_toomanyfileargs);
          if (freopen(cc_fil.v[1], "w", stdout) == NULL)
          {   cc_msg_lookup(driver_cpp_cantopenoutput, cc_fil.v[1]);
              compiler_exit(EXIT_error);
          }
          cc_fil.n = 1;
      }
  }

  if (cc_fil.n > 0)
  {
      if (driver_flags & KEY_STDIN)
          cc_msg_lookup(driver_stdin_otherfiles);
      process_file_names(t, &cc_fil);
  }
  else if (is_cpp || (driver_flags & KEY_STDIN))
  {   char *output_file = setupenv.output_file == default_output ? NULL :
                                                   setupenv.output_file;
/* was: output_file = setupenv.output_file; but writes asm to a.out     */
/* we need to separate the differing uses of "output_file".             */
#ifdef DEFAULT_STDIN_OBJECT
      if (!(driver_flags & (KEY_PREPROCESS|KEY_MAKEFILE|KEY_ASM_OUT)) &&
          setupenv.output_file == NULL)
          output_file = DEFAULT_STDIN_OBJECT;
#endif
      if (ccom(t, "-", output_file, NULL, NULL))
      {  ++main_error_count;
         if (output_file != NULL)
#ifdef COMPILING_ON_RISC_OS
/* The next line is dirty and should be done by checking return code,   */
/* not peeking at other's variables.                                    */
            if (errorcount)  /* only delete o/p file if serious errors */
#endif
            remove(output_file);
      }
  }
  else cc_msg_lookup(driver_noeffect, progname);

#ifndef HOST_CANNOT_INVOKE_LINKER
#  ifdef LINKER_IS_SUBPROGRAM
/* IJR: hack to ensure that path gets passed to linker in argv[0] for NLS */
  { UnparsedName un;
    size_t n;
    char *new_name;
    fname_parse(argv[0], "" , &un);
    un.root = setupenv.link_cmd;
    un.rlen = strlen(un.root);
    n = un.vlen + un.plen + un.rlen + un.elen + 10;
    new_name = (char *)PermAlloc(n);
    if (fname_unparse(&un, FNAME_AS_NAME, new_name, n) < 0)
        driver_abort("internal fault in \"copy_unparse\""); /* @@@ syserr? */
    setupenv.link_cmd = new_name;
  }
#  endif
  if (main_error_count == 0 && (driver_flags & KEY_LINK) && ld_fil.n > 0)
      linker(t, driver_flags);
#endif

  /*
   * The SUN ignores the return value from main so exit() instead
   */
  compiler_exit(main_error_count + cmd_error_count > 0 ? EXIT_error : 0);

  return 0;
}

static int cc(int argc, ArgvType *argv, ToolEnv *t,
              backchat_Messenger *sendmsg, void *backchathandle)
{   int status;
    backchat.send = sendmsg;
    backchat.handle = backchathandle;
    status = setjmp(exitbuf);
    if (status == 0)
        status = cc_main(argc, argv, t);
    else
        status = compiler_exit_status;
    return status;
}

char const *toolenv_toolname(void) {
  return MSG_TOOL_NAME;
}

ToolEnv *cc_default_env;

static int cc_finalise(ToolEntryPoints const *te) {
  IGNORE(te);
  if (cc_default_env != NULL) toolenv_dispose(cc_default_env);
  return 0;
}

static int MergeEnv(ToolEnv *t, ToolEnvDelta delta) {
  int rc;
  alloc_initialise();
  rc = toolenv_merge(t, delta);
  if (rc == 0) TE_NormaliseEtc(t);
  alloc_finalise();
  return rc;
}

static int CC_EditEnv(ToolEnv *t, HWND wh) {
  int rc;
  alloc_initialise();
  rc = Tool_EditEnv(t, wh);
  alloc_finalise();
  return rc;
}

static ToolEntryPoints const entries = {
  cc_finalise,
  cc,
  toolenv_new,
  toolenv_dispose,
  MergeEnv,
  toolenv_mark,
  toolenv_getdelta,
  toolenv_putinstallationdelta,
  CC_EditEnv,
  NULL
};

const ToolEntryPoints *armccinit(void) {
  cc_default_env = NULL;
  return &entries;
}

typedef struct {
  char const *name;
  char const *val;
} EnvItem;

#ifdef TARGET_DEFAULT_BIGENDIAN
#  if TARGET_DEFAULT_BIGENDIAN
#    define BYTESEX_DEFAULT_STR "=-bi"
#  else
#    define BYTESEX_DEFAULT_STR "=-li"
#  endif
#else
#  define BYTESEX_DEFAULT_STR "=-li"
#endif

#define str(s) #s
#define xstr(s) str(s)

static ToolEdit_InsertStatus insert_suppress_defaults(ToolEnv *t);

static EnvItem const builtin_defaults[] = {
  {".bytesex", BYTESEX_DEFAULT_STR},
#if defined(CPLUSPLUS)
  {".lang",    "=-cpp"},
#elif defined(TARGET_IS_UNIX)
  {".lang",    "=-fc"},
#else
  {".lang",    "=-ansi"},
#endif

#ifdef TARGET_WANTS_FUNCTION_NAMES
  {".ff",      "=-f+f"},
#else
  {".ff",      "=-ff"},
#endif
  {".fa",      "=-f+a"},
  {".fv",      "=-f+v"},

  {".-Isearch","=-f+k"},
  {"-O",       "=mix"},
#if defined(TARGET_IS_UNIX) || defined(TARGET_HAS_SEPARATE_CODE_DATA_SEGS)
  {".rolits",  "=-fw"},
#else
  {".rolits",  "=-f+w"},
#endif
  {".enums",   "=-f+y"},
  {".schar",   "=-z+c"},
  {".swilr",   "=-f+z"},

  {"-gx",      "?"},
  {"-gt",      "=+p"},
  {"-g",       "=-"},

  {".nowarn",  "?"},
#ifdef PASCAL
  {".rd",      "=-rd"},
#endif
#ifdef DEFAULT_DOES_NO_CSE
  {"-zpz",     "=0"},
#else
  {"-zpz",     "=1"},
#endif
  {"-D__CC_NORCROFT", "==1"},
/*
 * Predefine some symbols that give basic information about the size
 * of objects.  These are made to exist because ANSI rules mean that
 * one can not go
 *    #if sizeof(xxx) == nnn
 * as a pre-processing directive.
 */
  {"-D__sizeof_int", "==" xstr(sizeof_int)},
  {"-D__sizeof_long", "==" xstr(sizeof_long)},
  {"-D__sizeof_ptr", "==" xstr(sizeof_ptr)},

  { "-zat", "=" xstr(alignof_toplevel_static_default) },

  {NULL, NULL}
};

int toolenv_insertdefaults(ToolEnv *t) {
  EnvItem const *p = builtin_defaults;
  char v[8];
  char const *s = TOOLVER_ARMCC;
  int i;
  int rc;
  v[0] = v[1] = '=';
  for (i = 2; isdigit(s[0]) || s[0] == '.'; i++, s++) v[i] = s[0];
  v[i] = 0;
  tooledit_insert(t, "-D__ARMCC_VERSION", v);
  for (; p->name != NULL; p++) {
    ToolEdit_InsertStatus rc = tooledit_insert(t, p->name, p->val);
    if (rc == TE_Failed) return 1;
  }
  if (insert_suppress_defaults(t) == TE_Failed) return 1;
  { int argc = 0;
    char **argp;
    for (argp = driver_options; *argp != NULL; ++argp) argc++;
    read_options(0, argc, driver_options, t, NO);
  }
  { static char const * const predefs[] = TARGET_PREDEFINES;
    Uint i;
    for (i=0; i < sizeof(predefs)/sizeof(predefs[0]); i++)
            /* note that the arg may be of the form "name" or "name=toks" */
            /* the "name" form is equivalent to "name=1".                 */
      AddDefine(t, predefs[i]);
  }
  if (setupenv.initial_flags & KEY_PCC)
    tooledit_insert(t, ".lang", "-pcc");

#ifdef TARGET_SUPPORTS_TOOLENVS
  rc = mcdep_toolenv_insertdefaults(t);
#endif
  TE_NormaliseEtc(t);
  if (cc_default_env == NULL) {
    cc_default_env = toolenv_copy(t);
  }
  return rc;
}

static bool is_builtin_suppressed(enum Suppress s) {
    switch (s) {
#define X(NAME) case Suppress_##NAME:
        SUPPRESS_DEFAULT_LIST
#undef X
            return true;

        default:
            return false;
    };
}

// As with toolenv_insertdefaults() above, this loops through all entries
// of its suppression array. It has the same number of entries as those
// removed from builtin_defailts[], but stores both possible strings. The only
// difference in the loop is that, for each entry, it calls to
// is_builtin_suppressed() to determine which of the strings to pass to toolenv.
static ToolEdit_InsertStatus insert_suppress_defaults(ToolEnv *t)
{
    const struct {
        enum Suppress entry;
        const char *name, *onVal, *offVal;
    } list[] = {
#define ENTRY(TYPE, LETTER, NAME) { Suppress_ ## NAME, "." #TYPE #LETTER, "=-" #TYPE #LETTER, "=-" #TYPE "+" #LETTER }
        // This list is the list SDT2.11a used in builtin_defaults[] for default
        // warning and error suppressions set at compile time via the
        // SUPPRESS_DEFAULT_LIST define (previously D_SUPPRESSED). It's a subset
        // of the full character mappings (ie. -E<c> and -W<c>) in compiler.c.
        //
        // Only these entries end up in the toolenv (which was shared between
        // ARM's tools), but that doesn't necessarily matter - any suppression
        // listed in SUPPRESS_DEFAULT_LIST will still be disabled for this
        // compiler instance as that's handled elsewhere.
        //
        // Note that builtin_defaults[] still contains entries for -ff, -fa
        // and -fv, which can not override the settings in the toolenv.
        //
        // Each entry contains both possible values to pass to toolenv, with the
        // chosen one determined when looping. Each expands to something like:
        //    "{ Suppress_ImplicitCast, ".Ec", "=-Ec", "=-E+c" }
        ENTRY(E, c, ImplicitCast),
        ENTRY(E, f, Cast),
        ENTRY(E, l, Linkage),
        ENTRY(E, p, PPAllowJunk),
        ENTRY(E, z, ZeroArray),

        ENTRY(W, a, AssignTest),
        ENTRY(W, d, Deprecated),
        ENTRY(W, f, ImplicitFns),
        ENTRY(W, g, GuardedInclude),
        ENTRY(W, l, LowerInWider),
        ENTRY(W, n, ImplicitNarrowing),
        ENTRY(W, m, MultiChar),
        ENTRY(W, o, LongLongConst),
        ENTRY(W, p, PPNoSysIncludeCheck),
        ENTRY(W, s, StructPadding),
        ENTRY(W, u, Future),
        ENTRY(W, v, ImplicitVoid),
        ENTRY(W, z, StructAssign),
#undef ENTRY
        { Suppress_MAX, 0, 0, 0 }
    }, *p = list;

    for (; p->name != NULL; p++) {
        const char* val = is_builtin_suppressed(p->entry) ? p->onVal : p->offVal;
        ToolEdit_InsertStatus rc = tooledit_insert(t, p->name, val);
        if (rc == TE_Failed) return 1;
    }

    return TE_OK;
}

/* End of driver.c */
