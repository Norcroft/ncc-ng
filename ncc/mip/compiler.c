/*
 * C compiler file compiler.c
 * Copyright (C) Codemist Ltd., 1987-1992.
 * Copyright (C) Acorn Computers Ltd., 1988-1990.
 * Copyright (C) Advanced RISC Machines Limited, 1990-1992.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$  Codemist 147
 * Checkin $Date$
 * Revising $Author$
 */

/* AM Mar 89: start 'ccom-like' interface.  I allow the compiler to produce */
/* both object and asm output (after all unix ccom cannot never allow       */
/* obj output!).  Fix up FLG_STDIN to allow 0 args.  Add '-' for stdin/out  */
/* Move compile_abort to here from misc.c -- move out to driver.c?          */

#include <stddef.h>
#include <time.h>
#ifdef __STDC__
#  include <stdlib.h>
#  include <string.h>
#else
#  include <strings.h>
#endif

#include <ctype.h>
#ifndef COMPILING_ON_MSDOS
#  include <signal.h>
#endif

#include "globals.h"
#include "compiler.h"
#include "fname.h"
#include "pp.h"
#include "lex.h"
#include "syn.h"
#include "sem.h"      /* init */
#include "bind.h"     /* init */
#include "builtin.h"  /* init */
#include "vargen.h"   /* initstaticvar */
#include "aetree.h"
#include "cg.h"
#include "mcdep.h"
#include "aeops.h"
#include "xrefs.h"
#include "store.h"
#include "version.h"            /* for CC_BANNER */
#include "errors.h"
#include "dump.h"
#if defined(FOR_ACORN) && defined(COMPILING_ON_RISCOS)
#include "dde.h"
#endif
#include "filestat.h"
#include "trackfil.h"

#ifndef COMPILING_ON_MVS
#  define BSD_LIKE_SEARCH 1     /* ansi trying to ban (like sysV/K&R) */
#endif

#ifdef  ENABLE_MAPSTORE
extern void _mapstore(void);
#endif

#define  MAX_NAME     256  /* The longest file name I'm prepared to handle */

#define  ccom_alloc(n)  GlobAlloc(SU_Other, n)

#define  INSTORE_FILE   2                     /* used in PathElement.flags */
#define  PE_USER        4                     /* used in PathElement.flags */
#define  PE_SYS         8                     /* used in PathElement.flags */

typedef struct PathElement
{   struct PathElement *link;      /* sometimes a stack; sometimes a queue */
    int    flags;
    char   name[2];         /* to allow for a trailing separator and a NUL */
} PathElement;

/* Peter Armistead - added to link Callable compiler */
#ifdef CALLABLE_COMPILER
void mcdep_set_options(ToolEnv *t) {
}

Uint TE_Integer(ToolEnv *t, char const *name, Uint def) {
    return def;
}

int Tool_OrderedEnvEnumerate(
    ToolEnv *t, char const *prefix, ToolEdit_EnumFn *f, void *arg) {
  return 0;
}

Uint TE_Count(ToolEnv *t, char const *prefix) {
  return 0;
}
#endif /* COMPILE CALLABLE_COMPILER */

/* AM/LDS: beware: the stack path_hd is assumed always to be non-empty, and  */
/* the first element is treated very specially (in BSD).  Maybe it should be */
/* a separate variable.                                                      */
static PathElement *path_hd, *path_tl, *path_sav;

/* @@@ AM: I would prefer to use listingfile = NULL/string instead of      */
/* FLG_LISTING etc.                                                        */
#define FLG_COMPILE                    1             /* various ccom_flags */
#define FLG_MAKEFILE                   4
#define FLG_PREPROCESS                 8
#define FLG_NO_OBJECT_OUTPUT          16
#define FLG_INSTORE_FILES_IMPLICITLY  32
#define FLG_COUNTS                   128
#define FLG_USE_SYSTEM_PATH          256
#define FLG_NOSYSINCLUDES            512

#define TEXT_FILE                      0
#define BINARY_OUTPUT                  1
#define TEXT_FILE_APPEND               2          /* for Acorn RISC OS DDE */
#define BINARY_INPUT                   3

static int ccom_flags;
time_t tmuse_front, tmuse_back;
bool host_lsbytefirst;
int files_debugcount;
#define FILES_DEBUG_LEVEL(i) (debugging(DEBUG_FILES) && (i) < files_debugcount)

#ifdef MIN_ALIGNMENT_CONFIGURABLE
int32 alignof_struct_val;
int32 alignof_toplevel_static_var;
#endif

int bss_threshold;
bool disallow_tentative_statics = NO;

/*
 * Define the following as global, for various debugger back-ends.
 */
char const *sourcefile;
char const *objectfile, *sourcemodule;
static const char *asmfile, *listingfile, *makefile;
/* system_flavour copes with enabling this compiler to rename synbols   */
/* to reflect libraries.  E.g. on BSD sprintf must be renamed to refer  */
/* to a different symbol from on ANSI (as their results differ).        */
static char const *system_flavour;
static FILE *makestream;
#ifndef NO_DUMP_STATE
static char const *compiledheader;
static FILE *dumpstream;
#endif

#ifdef COMPILING_ON_RISC_OS
#ifdef FOR_ACORN
static int makeflg = 0;
#endif

#include "riscos.h"

static void set_time_stamp(const char *file, bool good)
{   __riscos_osfile_block b;
    b.load = 0;
    /* OS_File(2, ...) sets the load address (type & ms part of time stamp) */
    /* OS_File(9, ...) sets the type to &FFD and the time stamp to now.     */
    __riscos_osfile((good ? 9 : 2), file, &b);
}

#endif

/* DEPEND_FORMAT used to output dependency line (-m option) */
#ifdef COMPILING_ON_MACINTOSH
#  define DEPEND_FORMAT     "%s\304\t%s\n"
#else
#  define DEPEND_FORMAT     "%s:\t%s\n"
#endif

/*
 * Abort compilation if major fault found.
 */

extern void driver_abort(char *message)
{
  cc_msg_lookup(driver_abort_msg, message);
  dbg_finalise();
  compiler_exit(EXIT_error);
}

static FILE *cc_open(const char *s, int mode)
{
    FILE *f;
    if (*s == 0 || StrEq(s, "-"))
        f = (mode == BINARY_INPUT) ? (s = "binary stdin", (FILE *)0) :
            (mode == BINARY_OUTPUT) ? (s = "binary stdout", (FILE *)0) : stdout;
    else
        f = fopen(s, (mode == BINARY_INPUT) ? FOPEN_RB :
                     (mode == BINARY_OUTPUT) ? FOPEN_WB :
                     (mode == TEXT_FILE_APPEND) ? "a" : "w");
    if (f == NULL)
    {   char msg[MAX_NAME];
        msg_sprintf(msg, (mode == BINARY_INPUT) ?
                           driver_couldnt_read :
                           driver_couldnt_write,
                    s);
        driver_abort(msg);
    }
    return f;
}

static void cc_close(FILE **fp, const char *file)
{
/* Be careful so that the following test always closes f when needed    */
/* but tests ferror before the close.  (There may be an I/O error, and  */
/* the file still be closeable in which case it must be closed!         */
/* Consider a floppy disc running out of space.)                        */
    FILE *f = *fp;
    int err;
    *fp = NULL;
    if (f != NULL && f != stdout && (err = ferror(f), fclose(f) || err))
        cc_fatalerr(compiler_fatalerr_io_error, file);
}

extern void compile_abort(int sig_no)
{
/* pre-conditions: initialisation done, closing not done.  Call from      */
/* SIGINT handler at your peril!                                          */
#ifndef COMPILING_ON_MSDOS
    (void) signal(SIGINT, SIG_IGN);
#endif
#ifndef NO_ASSEMBLER_OUTPUT
    if (asmstream)
    {   cc_close(&asmstream, asmfile);
#  ifndef COMPILING_ON_MVS
        if (asmfile != NULL) remove(asmfile);
#  endif
    }
#endif
#ifndef NO_LISTING_OUTPUT
    cc_close(&listingstream, listingfile);
#endif
#ifndef NO_OBJECT_OUTPUT
    if (objstream)
    {   cc_close(&objstream, objectfile);
#  ifndef COMPILING_ON_MVS
        remove(objectfile);
#  endif
    }
#endif
    if (makestream != NULL)
    {   cc_close(&makestream, makefile);
        if (makefile != NULL) remove(makefile);
    }
#ifndef NO_DUMP_STATE
    if (dumpstream != NULL)
    {   cc_close(&dumpstream, compiledheader);
        remove(compiledheader);
    }
#endif
    dbg_finalise();
    compiler_exit(sig_no == (-1) ? EXIT_fatal : EXIT_syserr);
}


#if 'A' == 193          /* HOST_USES_EBCDIC... */
extern char _etoa[];
#  define ASCII(x)      (_etoa[x])
#else
#  define ASCII(x)      (x)
#endif

/*
 * Disable warning messages.
 */
// Suppress_MAX is unused or complicated:
// 'n' has multiple values. 'd' and 'f' use the pragma db.
static enum Suppress const warning_flags[] = {
/*abc*/ Suppress_AssignTest,            Suppress_MAX,           Suppress_CFrontCaller,
/*def*/ Suppress_Deprecated /*'d'*/,    Suppress_MAX,           Suppress_ImplicitFns /*'f'*/,
/*ghi*/ Suppress_GuardedInclude,        Suppress_MAX,           Suppress_ImplicitCtor,
/*jkl*/ Suppress_MAX,                   Suppress_MAX,           Suppress_LowerInWider,
/*mno*/ Suppress_MultiChar,             Suppress_MAX /*'n'*/,   Suppress_LongLongConst,
/*pqr*/ Suppress_PPNoSysIncludeCheck,   Suppress_MAX,           Suppress_ImplicitVirtual,
/*stu*/ Suppress_StructPadding,         Suppress_UnusedThis,    Suppress_Future,
/*vwx*/ Suppress_ImplicitVoid,          Suppress_MAX,           Suppress_MAX,
/*yz */ Suppress_MAX,                   Suppress_StructAssign
};

// Note that Feature_MAX is used to flag unused or used by a different
// config option (eg. -fd and -fx set ccom_flags and suppress).
static enum Feature const feature_flags[] = {
/*abc*/  Feature_Anomoly,           Feature_Verbose,                Feature_LimitedPCC,
/*def*/  Feature_MAX, /* -fd */     Feature_6CharMonocase,          Feature_SaveName,
/*ghi*/  Feature_MAX, /* UNUSED */  Feature_Predeclare,             Feature_UserIncludeListing,
/*jkl*/  Feature_SysIncludeListing, Feature_KandRInclude,           Feature_DontUseLinkReg,
/*mno*/  Feature_PPNoUse,           Feature_SaveName,               Feature_WarnOldFns,
/*pqr*/  Feature_TellPtrInt,        Feature_AllowCountedStrings,    Feature_LetLongjmpCorruptRegVars,
/*stu*/  Feature_Annotate,          Feature_ReverseBitfields,       Feature_UnexpandedListing,
/*vwx*/  Feature_NoUse,             Feature_WRStrLits,              Feature_MAX, /* -fx */
/*yz */  Feature_EnumsAlwaysInt,    Feature_InlineCallKillsLinkReg
};

static bool const feature_flags_inverted[] = {
/*abc*/  false /* Anomoly */,           false /*Verbose */,                false /* LimitedPCC */,
/*def*/  false /*  -fd  */,             false /*6CharMonocase */,          true  /* SaveName */,
/*ghi*/  false /*  UNUSED  */,          false /*Predeclare */,             false /* UserIncludeListing */,
/*jkl*/  false /* SysIncludeListing */, false /*KandRInclude */,           false /* DontUseLinkReg */,
/*mno*/  false /* PPNoUse */,           false /*SaveName */,               false /* WarnOldFns */,
/*pqr*/  false /* TellPtrInt */,        false /*AllowCountedStrings */,    false /* LetLongjmpCorruptRegVars */,
/*stu*/  false /* Annotate */,          false /*ReverseBitfields */,       false /* UnexpandedListing */,
/*vwx*/  false /* NoUse */,             false /*WRStrLits */,              false /* -fx */,
/*yz */  false /* EnumsAlwaysInt */,    false /*InlineCallKillsLinkReg */
};

static int32 ClearOrSet(int32 val, int32 bits, bool clear) {
  if (clear)
    return val & ~bits;
  else
    return val | bits;
}

static int SetFeatures(void *arg, char const *name, char const *val) {
  size_t len;
  IGNORE(arg);
  if (StrEq(name, ".-Isearch")) name = ".fk";
  else if (StrEq(name, ".rolits")) name = ".fw";
  else if (StrEq(name, ".enums")) name = ".fy";
  else if (StrEq(name, ".swilr")) name = ".fz";
  len = strlen(name);
  if (len == 3 && name[0] == '.') {
    int ch = name[2];
    bool on = val[3] == '+';
    if (name[1] == 'W') {
      if (ch == 'd')
        var_warn_deprecated = on;
      else if (ch == 'f')
        var_warn_implicit_fns = on;
      else if (ch == 'n') {
        // Special-case '-fn' as the table can no longer hold multiple values.
        SuppressDB_ClearOrSet(Suppress_ImplicitNarrowing, on);
        SuppressDB_ClearOrSet(Suppress_LowerInWider, on);
      } else {
        enum Suppress w = warning_flags[ASCII(ch) - ASCII('a')];
        if (w != Suppress_MAX) {
            SuppressDB_ClearOrSet(w, on);
        }
      }
    }
#ifdef DISABLE_ERRORS
    else if (name[1] == 'E') {
      switch (ch) {
      case 'c': SuppressDB_ClearOrSet(Suppress_ImplicitCast, on);   break;
      case 'm': SuppressDB_ClearOrSet(Suppress_MPWCompatible, on);
                SuppressDB_ClearOrSet(Suppress_PPAllowJunk, on);
                SuppressDB_ClearOrSet(Suppress_ZeroArray, on);
                SuppressDB_ClearOrSet(Suppress_PPNoSysIncludeCheck, on);
                SuppressDB_ClearOrSet(Suppress_MultiChar, on);
                FeaturesDB_ClearOrSet(Feature_AllowCountedStrings, on);
                                                 break;
      case 'p': SuppressDB_ClearOrSet(Suppress_PPAllowJunk, on);    break;
#ifdef EXTENSION_VALOF
      case 'v': SuppressDB_ClearOrSet(Suppress_ValOfBlocks, on);    break;
#endif
      case 'z': SuppressDB_ClearOrSet(Suppress_ZeroArray, on);      break;
      case 'f': SuppressDB_ClearOrSet(Suppress_Cast, on);           break;  /* Force casts */
      case 'l': SuppressDB_ClearOrSet(Suppress_Linkage, on);        break;
      case 'a': SuppressDB_ClearOrSet(Suppress_Access, on);         break;
      case 'i': SuppressDB_ClearOrSet(Suppress_ImplicitInt, on);    break;
      }
    }
#endif
    else if (name[1] == 'f') {
      if (ch == 'x') {
#define X(name) SuppressDB_Clear(Suppress_##name);
        SUPPRESS_DEFAULT_LIST
#undef X
      } else if (ch == 'd') {
        ccom_flags = ccom_flags | FLG_USE_SYSTEM_PATH;
      } else {
        enum Feature flag = feature_flags[ASCII(ch) - ASCII('a')];
        if (flag != Feature_MAX) {
          if (feature_flags_inverted[ASCII(ch) - ASCII('a')])
            FeaturesDB_ClearOrSet(flag, !on);
          else
            FeaturesDB_ClearOrSet(flag, on);
        }
      }
    }
#ifdef PASCAL
    else if (name[1] == 'r')
      /* Disable run time checks */
      switch (ch) {
      case 'A': rtcheck |= RTCHECK_ARRAY;     break;
      case 'C': rtcheck |= RTCHECK_CASE;      break;
      case 'N': rtcheck |= RTCHECK_NIL;       break;
      case 'R': rtcheck |= RTCHECK_REFERENCE; break;
      case 'P': rtcheck |= RTCHECK_ASSERT;    break;
      case 'D': rtcheck |= RTCHECK_DEADCODE;  break;
      }
    }
#endif
  }
  return 0;
}

static int DoPredefine(void *arg, char const *name, char const *val) {
  IGNORE(arg);
  if (name[0] == '-') {
    if (name[1] == 'D') {
      size_t nlen = strlen(&name[2]),
             vlen = strlen(&val[1]);
      char *s = (char *)GlobAlloc(SU_PP, nlen+vlen+1);
      memcpy(s, &name[2], nlen);
      memcpy(&s[nlen], &val[1], vlen+1);
      pp_predefine(s);
    } else if (name[1] == 'z' && name[2] == 'p') {
      int pragmachar = safe_tolower(name[3]);
      int32 value = -1L;
      if (isdigit(val[1]))
      { value = strtol(&val[1], NULL, 0);  /* allow 0x... form too */
#ifdef FORTRAN
        if ((pragmachar == 'x' || pragmachar == 'w') &&
           pp_pragmavec[pragmachar-'a'] != -1)
        { pp_pragmavec[pragmachar-'a'] |= value;
          return;
        }
#endif
      }
      pp_pragmavec[pragmachar-'a'] = value;
    }
  }
  return 0;
}

/*
 * Enable the features for PCC style compilation.
 */

static void translate_fname(const char *file, UnparsedName *un, char *new_file)
{   fname_parse(file, FNAME_INCLUDE_SUFFIXES, un);
    fname_unparse(un, FNAME_AS_NAME, new_file, MAX_NAME);
}

static void translate_path(const char *path, UnparsedName *un, char *new_path)
{   fname_parse(path, FNAME_INCLUDE_SUFFIXES, un);
    fname_unparse(un, FNAME_AS_PATH, new_path, MAX_NAME);
#if defined(FOR_ACORN) && defined(COMPILING_ON_RISC_OS)
    /* DDE fix for paths like foo: ... */
    if (un->un_pathlen > 1 && new_path[un->un_pathlen-2] == ':')
        new_path[un->un_pathlen-1] = 0;          /* kill trailing separator */
#endif
}

static PathElement *mk_path_element(PathElement *link, int flags, char *name)
{ PathElement *p;
  if (FILES_DEBUG_LEVEL(1)) cc_msg("mk_path_element(%s)\n", name);
  p = (PathElement *) ccom_alloc((int32)strlen(name) + sizeof(PathElement));
  p->link = link;
  p->flags = flags;
  strcpy(p->name, name);
  return p;
}

/*
 * Set the user/sys include path (no difference for bsd!).
 */

static void set_include_path(const char *path, int flags)
{
  PathElement *p;
  UnparsedName unparse;
  int ch;
  char new_path[MAX_NAME];
  char path_element[MAX_NAME];

  for (ch = *path;  ch != 0;)
  {   /* one or more path elements joined by commas... */
      int length = 0;
      while (ch != ',' && ch != 0)
      {   if (length < (MAX_NAME-1)) path_element[length++] = ch;
          ch = *(++path);
      }
      if (ch == ',') ch = *(++path);
      path_element[length] = 0;
      if (length == 1 && path_element[0] == '-'    /* unix-like 'std place' */
#ifdef COMPILING_ON_ACORN_KIT
          /* backwards compatibility -- RISCOS only soon? */
          || StrEq(path_element, ":mem")
          || StrEq(path_element, ":MEM")
#endif
         )
      {
          flags |= INSTORE_FILE;  length = 0;
          ccom_flags &= ~FLG_INSTORE_FILES_IMPLICITLY;
          new_path[0] = 0;
      }
      else {
          translate_path(path_element, &unparse, new_path);
          dbg_notepath(new_path);
      }
      /* Add a new path element at the END of the list. */
      p = mk_path_element(NULL, flags, new_path);
      if (path_hd == NULL)
          path_tl = path_hd = p;
      else
          path_tl = (path_tl->link = p);
  }
}

static int AddInclude(void *arg, char const *name, char const *value, bool readonly) {
  IGNORE(arg); IGNORE(readonly);
  set_include_path(&value[1], name[1] == 'I' ? PE_USER : PE_SYS);
  return 0;
}
/*
 * Stack include path name.
 */

static char *push_include(char const *path, const char *name)
{
  /* Return a copy of the native (translated) file-name. Do this so ASD    */
  /* will have a file-name it can use directly for its 'type' command.     */
  char *hostname = strcpy((char *)ccom_alloc((int32)strlen(name)+1L), name);
#ifdef BSD_LIKE_SEARCH
  { PathElement *p;
    UnparsedName unparse;
    char new_path[MAX_NAME];

    if (HasFeature(Feature_KandRInclude)) return hostname;

    /* remove the head of the path and push it on the save stack */
    p = path_hd;
    path_hd = p->link;
    p->link = path_sav;
    path_sav = p;

    if (path != NULL)
    {   translate_fname(path, &unparse, new_path);
        new_path[unparse.un_pathlen] = 0;
        dbg_notepath(new_path);
    }
    else
        new_path[0] = 0;
    path_hd = p = mk_path_element(path_hd,
                                  /* @@@ next line flag PE_USER/SYS? */
                                  path == NULL ? INSTORE_FILE : 0,
                                  new_path);
  }
#endif
  return hostname;
}

static void pop_include(void)
{
#ifdef BSD_LIKE_SEARCH
    PathElement *p;
    if (HasFeature(Feature_KandRInclude)) return;
    /*
     * pop the saved path element off the save stack and
     * push it on to the front of the regular path element stack.
     */
    p = path_hd;
    path_hd = path_sav;
    path_sav = path_sav->link;
    path_hd->link = p->link;
#endif
}

static void preprocess_only(void)
{
#ifdef PASCAL /*ECN*/
  syn_init();
#endif

  if (ccom_flags & FLG_PREPROCESS)
  {   /* Selected if -E or -E -MD set */
      pp_copy();
  }
  else
  {   /* Selected if -M set */
      int character;
      while ((character = pp_nextchar()) != PP_EOF) continue;
  }
}

#ifdef  FOR_ACORN
#ifndef PASCAL
#ifndef FORTRAN
bool cplusplus_preprocessing(void)
{
    return (ccom_flags & FLG_PREPROCESS) && cplusplus_flag;
}
#endif
#endif
#endif

static void pre_include(char const *file)
{   FILE *f;
    if ((f = trackfile_open(file, "r")) != NULL)
    {   pp_notesource(file, f, YES);
        preprocess_only();
    }
    else
        cc_warn(warn_preinclude, file);
}

/*
 * Initialise compiler state.
 */

static void set_debug_options(ToolEnv *t)
{
#ifdef TARGET_HAS_DEBUGGER

  char const *dbgval = toolenv_lookup(t, "-g");
  if (dbgval != NULL && dbgval[1] == '+') {
    int ch;
    uint32 opt = 0;
    dbgval = toolenv_lookup(t, "-gx");
    while ((ch = *++dbgval) != 0)
    switch (ch) {
      case 'c': opt |= DBG_OPT_CSE; break;
      case 'r': opt |= (DBG_OPT_ALL-DBG_OPT_REG); break;
      case 'g': opt |= DBG_OPT_DEAD;break;
      case 'o': opt |= DBG_OPT_ALL; break;
    }
    dbgval = toolenv_lookup(t, "-gt");
    opt |= DBG_ANY;
    while ((ch = *++dbgval) != 0 && ch != '+')
      switch (ch) {
      case 'f': opt &= ~DBG_PROC;   break;
      case 'l': opt &= ~DBG_LINE;   break;
      case 'v': opt &= ~DBG_VAR;    break;
      case 'p': opt &= ~DBG_PP;     break;
    }
    if (ch == '+')
      while ((ch = *++dbgval) != 0)
        switch (ch) {
        case 'f': opt |= DBG_PROC;   break;
        case 'l': opt |= DBG_LINE;   break;
        case 'v': opt |= DBG_VAR;    break;
        case 'p': opt |= DBG_PP;     break;
      }
    usrdbgmask |= opt;
  }
#endif
}

static int makeflag;


static void pcc_features(void)
{
    SetFeature(Feature_PCC);
    SetFeature(Feature_UnixStyleLongjmp);
}


static void set_compile_options(ToolEnv *t)
{
  char const *val;
  int n;

  val = toolenv_lookup(t, ".lang");
#ifdef PASCAL
  if (StrEq(val, "=-iso")) SetFeature(Feature_ISO);
#else
  if (StrEq(val, "=-pcc")) {
    SetFeatures2(Feature_PCC, Feature_UnixStyleLongjmp);
    ClearFeature(Feature_ANSI);
    ClearFeature(Feature_CPP);
    ClearFeature(Feature_CFront);
  }
  else if (StrEq(val, "=-pcc -strict")) {
    SetFeatures3(Feature_PCC, Feature_UnixStyleLongjmp, Feature_Fussy);
    ClearFeatures3(Feature_ANSI, Feature_CPP, Feature_CFront);
  }
  else if (StrEq(val, "=-ansi -strict")) {
    SetFeatures2(Feature_ANSI, Feature_Fussy);
    ClearFeatures3(Feature_LimitedPCC, Feature_CPP, Feature_CFront);
  }
  else if (StrEq(val, "=-ansi")) {
    SetFeature(Feature_ANSI);
    ClearFeatures3(Feature_PCC, Feature_CPP, Feature_CFront);
  }
  else if (StrEq(val, "=-ansi -fc")) {
    SetFeatures2(Feature_ANSI, Feature_LimitedPCC);
    ClearFeatures3(Feature_PCC, Feature_CPP, Feature_CFront);
  }
#  ifdef CPLUSPLUS
  else if (StrEq(val, "=-cfront")) {
    SetFeatures2(Feature_CPP, Feature_CFront);
    ClearFeatures2(Feature_PCC, Feature_ANSI);
  }
  else if (StrEq(val, "=-cpp")) {
    SetFeature(Feature_CPP);
    ClearFeatures2(Feature_PCC, Feature_ANSI);
  }
  else if (StrEq(val, "=-cpp -strict")) {
    SetFeatures2(Feature_CPP, Feature_Fussy);
    ClearFeatures2(Feature_PCC, Feature_ANSI);
  }
#  endif
#endif

  toolenv_enumerate(t, SetFeatures, NULL);
  toolenv_enumerate(t, DoPredefine, NULL);
  Tool_OrderedEnvEnumerate(t, "-I.", AddInclude, NULL);
  if (TE_Count(t, "-J.") > 0) {
    ccom_flags &= ~FLG_INSTORE_FILES_IMPLICITLY;
    Tool_OrderedEnvEnumerate(t, "-J.", AddInclude, NULL);
  }

  if ((val = toolenv_lookup(t, "-ZI")) != NULL) pre_include(&val[1]);
  if ((val = toolenv_lookup(t, "-ZS")) != NULL) system_flavour = &val[1];
  if ((val = toolenv_lookup(t, "-zj")) != NULL) config |= CONFIG_INDIRECT_SETJMP;
  if ((val = toolenv_lookup(t, ".schar")) != NULL)
    FeaturesDB_ClearOrSet(Feature_SignedChar, val[3] == '+');
  if ((val = toolenv_lookup(t, ".areaperfn")) != NULL)
    FeaturesDB_ClearOrSet(Feature_AOFAreaPerFn, val[3] == '+');
#ifndef NO_DUMP_STATE
  if ((val = toolenv_lookup(t, "-zgw")) != NULL) { compiledheader = &val[1]; dump_state |= DS_Dump; }
  if ((val = toolenv_lookup(t, "-zgr")) != NULL) { compiledheader = &val[1]; dump_state |= DS_Load; }
#endif
  if ((val = toolenv_lookup(t, ".pp_only")) != NULL)
    ccom_flags = (ccom_flags | FLG_PREPROCESS) & ~FLG_COMPILE;
  if ((val = toolenv_lookup(t, "-K")) != NULL) ccom_flags |= FLG_COUNTS;
  if ((val = toolenv_lookup(t, "-C")) != NULL) SetFeature(Feature_PPComment);
  if ((val = toolenv_lookup(t, "-p")) != NULL)
    var_profile_option = val[0] == '=' ? 2 : 1;
  if ((val = toolenv_lookup(t, ".no_object")) != NULL) ccom_flags |= FLG_NO_OBJECT_OUTPUT;
  if ((val = toolenv_lookup(t, ".nowarn")) != NULL
      && val[0] != '?')
    SetFeature(Feature_NoWarnings);

  val = toolenv_lookup(t, "-O");
  if (StrEq(val, "=time"))
    config |= CONFIG_OPTIMISE_TIME;
  else if (StrEq(val, "=space"))
    config |= CONFIG_OPTIMISE_SPACE;

  n = TE_Integer(t, "-zap", 0);
  config = ClearOrSet(config, CONFIG_STRUCT_PTR_ALIGN, n == 0);
#ifdef MIN_ALIGNMENT_CONFIGURABLE
  if ((n = TE_Integer(t, "-zas", 0)) != 0) alignof_struct_val = n;
  if ((n = TE_Integer(t, "-zat", 0)) != 0) alignof_toplevel_static_var = n;
#endif
  if ((n = TE_Integer(t, "-zz", 0x12345)) != 0x12345) bss_threshold = n;
  if ((val = toolenv_lookup(t, "-disallow_tentative_statics")) != NULL)
      disallow_tentative_statics = YES;
  else
      disallow_tentative_statics = (LanguageIsCPlusPlus ? YES : NO);

  if ((val = toolenv_lookup(t, "-M")) != NULL) {
    ccom_flags |= FLG_MAKEFILE;
    if (val[0] == '?')
      ccom_flags &= ~(FLG_COMPILE+FLG_NOSYSINCLUDES);
    else if (val[1] == '<')
      ccom_flags = (ccom_flags | FLG_NOSYSINCLUDES) & ~FLG_COMPILE;
#ifdef FOR_ACORN
    else if (val[1] == '+')
      makefile = toolenv_lookup(t, ".depend");
#endif
    makeflag = 0;
  }
}

/*
 * Inner compile control routine.
 */

#ifndef NO_DUMP_STATE
static void DumpCompiledHeader(void);
#endif

static void compile_statements(void)
{   bool decls = NO;
    bool returneof = YES;
#ifndef PASCAL /*ECN*/
/* AM, Sept 91: I am inclined to think the best interface is to call    */
/* rd_topdecl(0) (1,2,3,...) until it returns NULL (or list1(s_eof))    */
/* Then all conceivable actions could be done, instead of this mess.    */
/* May 1993: process almost complete for C/C++...                       */
    for (;;)
#endif
    { TopDecl *d; AEop h0d;
      clock_t t0;
      phasename = "reinit";
      lex_beware_reinit();  /* preserve needed things over reinit */
      drop_local_store();   /* in case nextsym() above read #if   */
      alloc_reinit();
      lex_reinit();
      cg_reinit();          /* must be done BEFORE parsing */
#ifdef PASCAL /*ECN*/
      syn_init();           /* @@@ AM: surely is just part of rd_topdecl? */
                            /* then syn_init can be OK as usual.          */
#endif
      syn_reinit();

#ifndef PASCAL /*ECN*/
      t0 = clock();
#endif
      phasename = "parse";
      d = rd_topdecl(returneof);
      if (d == 0) syserr("rd_topdecl() => NULL");
      alloc_noteAEstoreuse();
#ifndef PASCAL /*ECN*/
      tmuse_front += clock() - t0;
#endif

      if (debugging(DEBUG_AETREE)) pr_topdecl(d);

      t0 = clock();
      phasename = "jopcode";
      h0d = h0_(d);             /* killed by drop_local_store()!        */
      if (h0d == s_fndef) cg_topdecl(d, curlex.fl);
      currentfunction.symstr = NULL;
      tmuse_back += clock() - t0;
      drop_local_store();
      if (h0d == s_eof) {
        if (returneof) {
#ifndef NO_DUMP_STATE
          if (dump_state & DS_Dump) DumpCompiledHeader();
#endif
          returneof = NO;
        } else
          break;
      } else
        decls = YES;
    }
#ifndef PASCAL /*ECN*/
    if (!decls && HasFeature(Feature_ANSI))   /* move to rd_topdecl()? */
    { if (HasFeature(Feature_Fussy))
        cc_rerr(compiler_rerr_no_extern_decl);
      else
        cc_warn(compiler_rerr_no_extern_decl);
    }
#endif
    if (LanguageIsCPlusPlus) vg_ref_dynamic_init();
}

static void cleanup(void)
{
  bind_cleanup();
  pp_tidyup();

  if (debugging(DEBUG_STORE))
  {
      cc_msg("Time: %ldcs front-end %ldcs back-end\n",
             (long) tmuse_front,(long) tmuse_back);
      show_store_use();
  }

  cg_tidy();

#ifndef NO_OBJECT_OUTPUT
# ifdef COMPILING_ON_ACORN_KIT
  {   bool have_obj = (objstream != NULL);
      /* objstream cannot be stdout, so cc_close does a spurious test. */
      cc_close(&objstream, objectfile);
#   ifdef COMPILING_ON_RISC_OS
      if (have_obj) set_time_stamp(objectfile, YES);
#   endif
#   ifdef COMPILING_ON_UNIX
      if (have_obj && system_flavour != NULL)
      {   char *cmd;
          cmd = GlobAlloc(SU_Other,
                          24 + strlen(system_flavour) + strlen(objectfile));
          sprintf(cmd,"/usr/bin/symrename -%s %s",system_flavour,objectfile);
          system(cmd);
      }
#   endif
  }
# else
  cc_close(&objstream, objectfile);
# endif
#endif

#ifndef NO_ASSEMBLER_OUTPUT
  cc_close(&asmstream, asmfile);
#endif

  cc_close(&listingstream, listingfile);
  cc_close(&makestream, makefile);

  summarise();

#ifdef ENABLE_MAPSTORE
  if (debugging(DEBUG_MAPSTORE)) _mapstore();
#endif

  alloc_perfilefinalise();
}

/*
 * Open include file for pre-processor.
 * (included here because of system dependencies).
 */

static void show_h_line(int32 line, const char *file, bool to_makefile)
{
  if (ccom_flags & FLG_PREPROCESS)
      printf("#%s %lu \"%s\"\n",
             HasFeature(Feature_PCC) ? "" : "line", (long)line, file);
  if (to_makefile && ccom_flags & FLG_MAKEFILE)
  {
      if (makestream == stdout)
      {
          backchat_InclusionDependency dep;
          dep.targetName = objectfile;
          dep.dependsonName = file;
          backchat.send(
              (backchat.handle != NULL) ? backchat.handle : (void *)stdout,
                  BC_INCLUDEMSG, &dep);
      }
      else
          fprintf(makestream, DEPEND_FORMAT, objectfile, file);
  }
}

void UpdateProgress(void) {
#ifdef COMPILING_ON_MPW
  UPDATE_PROGRESS();
#else
  backchat.send(backchat.handle, BC_NULLMSG, NULL);
#endif
}

#ifndef NO_INSTORE_FILES

static FILE *try_instore_file(const char *file, pp_uncompression_record **urp)
{   FILE *include_file = open_builtin_header(file, urp);
    if (include_file != NULL)
    {   if (debugging(DEBUG_FILES))
            cc_msg("Opened instore file '%s'\n", file);
        show_h_line(1, file, NO);
        push_include(NULL, file);
    }
    else if (FILES_DEBUG_LEVEL(1))
        cc_msg("Instore file '%s' not found.\n", file);
    return include_file;
}

#endif /* NO_INSTORE_FILES */

static FILE *incl_search(char const *file, const char *new_file,
                         bool systemheader,
                         pp_uncompression_record **urp,
                         char const **hostname)
{   FILE *new_include_file;
    PathElement *p;
#ifndef NO_INSTORE_FILES
    if ((ccom_flags & FLG_INSTORE_FILES_IMPLICITLY) && systemheader)
    {
/* Note that it is important for portability (even across unix/riscos)  */
/* to have the original 'file' and not the munged 'new_file' instore.   */
        new_include_file = try_instore_file(file, urp);
        if (new_include_file != NULL) return new_include_file;
    }
#endif
    p = path_hd;
    if (systemheader || (ccom_flags & FLG_USE_SYSTEM_PATH)) p = p->link;
    while (p != NULL)
    {   char current[MAX_NAME];
        if (p->flags & INSTORE_FILE)
        {
#ifndef NO_INSTORE_FILES
/* Note that it is important for portability (even across unix/riscos)  */
/* to have the original 'file' and not the munged 'new_file' instore.   */
            new_include_file = try_instore_file(file, urp);
            if (new_include_file != NULL) return new_include_file;
#endif
        }
        else /* current path is not :mem */
        {   strcpy(current, p->name);
            if (strlen(current) + strlen(new_file) + 1 <= MAX_NAME)
            {   strcat(current, new_file);
                if ((new_include_file = trackfile_open(current, "r")) != NULL)
                {   if (debugging(DEBUG_FILES))
                        cc_msg("Opened file '%s'\n", current);
                    if (!(systemheader && (ccom_flags & FLG_NOSYSINCLUDES)))
                        show_h_line(1, current, YES);
                    *hostname = push_include(current, current);
                    return new_include_file;
                }
                else if (FILES_DEBUG_LEVEL(1))
                    cc_msg("File '%s' not found.\n", current);
            }
        }
        p = p->link;
    }
#ifdef COMPILING_ON_RISC_OS
    /* IDJ 06-Jun-94: before trying instore headers we try just the filename
     * by itself.  This is because of something like <foo$dir>.h.bar which
     * may or may not be a rooted filename.
     */
    if ((new_include_file = trackfile_open(new_file, "r")) != NULL)
    {   if (debugging(DEBUG_FILES))
            cc_msg("Opened file '%s'\n", new_file);
        if (!(systemheader && (ccom_flags & FLG_NOSYSINCLUDES)))
            show_h_line(1, new_file, YES);
        *hostname = push_include(new_file, new_file);
        return new_include_file;
    }
    else if (FILES_DEBUG_LEVEL(1))
        cc_msg("File '%s' not found.\n", new_file);
#endif
#ifndef NO_INSTORE_FILES
/* Not found - ANSI require looking for "stdio.h" as <stdio.h> when all */
/* else has failed.                                                     */
/* Note that it is important for portability (even across unix/riscos)  */
/* to have the original 'file' and not the munged 'new_file' instore.   */
    return try_instore_file(file, urp);
#else
    return NULL;
#endif
}

extern FILE *pp_inclopen(char const *file, bool systemheader,
            pp_uncompression_record **urp, char const **hostname,
            FileLine fl)
{
  FILE *new_include_file;
  UnparsedName unparse;
  char new_file[MAX_NAME];

  *hostname = file;
  translate_fname(file, &unparse, new_file);

  if (!(unparse.type & FNAME_ROOTED))
  {   new_include_file = incl_search(file, new_file, systemheader, urp,
                                     hostname);
#ifdef RETRY_INCLUDE_LOWERCASE
      if (new_include_file == NULL)
      {   bool not_all_lowercase = NO;
          char *p = new_file;
          int c;
          while ((c = *p++) != '\0')
              if (isupper(c))
              {   not_all_lowercase = YES;
                  p[-1] = tolower(c);
              }
          if (not_all_lowercase)
              new_include_file = incl_search(file, new_file, systemheader,
                                             urp, hostname);
      }
#endif
      if (new_include_file != NULL && usrdbg(DBG_PP))
          dbg_include(*hostname, NULL, fl);
  }
  else  /* rooted file */
  {   if ((new_include_file = trackfile_open(new_file, "r")) != NULL)
      {   if (debugging(DEBUG_FILES))
              cc_msg("Opened file '%s'\n", new_file);
          if (!(systemheader && (ccom_flags & FLG_NOSYSINCLUDES)))
              show_h_line(1, new_file, YES);
          *hostname = push_include(new_file, new_file);
          if (usrdbg(DBG_PP)) dbg_include(*hostname, NULL, fl);
      }
      else if (FILES_DEBUG_LEVEL(1))
          cc_msg("File '%s' not found.\n", new_file);
  }
  return new_include_file;
}

extern void pp_inclclose(FileLine fl)
{
    if (debugging(DEBUG_FILES))
        cc_msg("Resuming file '%s' at line %d\n", fl.f, fl.l);
    if (usrdbg(DBG_PP)) dbg_include(NULL, NULL, fl);
    pop_include();
    show_h_line(fl.l, fl.f, NO);
}

#ifndef NO_DUMP_STATE
static void LoadCompiledHeader(void)
{   FILE *f = cc_open(compiledheader, BINARY_INPUT);
    uint32 w;
    fread(&w, sizeof(uint32), 1, f);
    if (w != DS_Version)
        cc_fatalerr(compiler_fatalerr_load_version, compiledheader);
    if (ferror(f) == 0)
        PP_LoadState(f);
    if (ferror(f) == 0)
        Bind_LoadState(f);
    if (ferror(f) == 0)
        Vargen_LoadState(f);
    cc_close(&f, compiledheader);
}

static void DumpCompiledHeader(void)
{   uint32 w = DS_Version;
    dumpstream = cc_open(compiledheader, BINARY_OUTPUT);
    fwrite(&w, sizeof(uint32), 1, dumpstream);
    if (ferror(dumpstream) == 0)
        PP_DumpState(dumpstream);
    if (ferror(dumpstream) == 0)
        Bind_DumpState(dumpstream);
    if (ferror(dumpstream) == 0)
        Vargen_DumpState(dumpstream);
    cc_close(&dumpstream, compiledheader);
}
#endif

bool inputfromtty;
#ifdef REBUFFERSTDOUT
char stdoutbuffer[8192];
#endif

extern int ccom(ToolEnv *t, char const *infile, char const *outfile,
                char const *listfile, char const *mdfile) {
  char *stdin_name = "<stdin>";
  FILE *sourcestream = NULL;
#ifdef HOST_USES_CCOM_INTERFACE
#ifndef  TARGET_IS_UNIX
  cc_msg("%s\n", CC_BANNER);
#ifndef COMPILING_ON_MSDOS
  (void) signal(SIGINT, compile_abort);
#endif
#else /* TARGET_IS_UNIX */
  /* The signal ignore state can be inherited from the parent... */
#define sig_ign ((void (*)(int))(SIG_IGN))
  if (signal(SIGINT,  sig_ign) != sig_ign)
    (void) signal(SIGINT, compile_abort);
  if (signal(SIGHUP,  sig_ign) != sig_ign)
    (void) signal(SIGHUP, compile_abort);
  if (signal(SIGTERM, sig_ign) != sig_ign)
    (void) signal(SIGTERM, compile_abort);
#endif
#endif

#if (defined NLS) && (defined HOST_USES_CCOM_INTERFACE)
  msg_init(argv[0],MSG_TOOL_NAME);
#endif

  ccom_flags = FLG_COMPILE + FLG_INSTORE_FILES_IMPLICITLY;
  makefile = mdfile;
  listingfile = listfile;

  sourcefile = objectfile = asmfile = NULL;
  sourcemodule = "";
#ifndef NO_DUMP_STATE
  compiledheader = NULL;
  dumpstream = NULL;
#endif

  dump_state = 0;
  system_flavour = NULL;

#ifndef NO_ASSEMBLER_OUTPUT
  asmstream = 0;
#endif
#ifndef NO_OBJECT_OUTPUT
  objstream = 0;
#endif
#ifndef NO_LISTING_OUTPUT
  listingstream = 0;
#endif
  makestream = 0;
  makeflag = 0;

  tmuse_front = tmuse_back = 0;

  path_hd = path_sav = 0;

#ifdef PASCAL /*ECN*/
  rtcheck  = 0;
#endif

  FeaturesDB_ClearAll();
  SuppressDB_InitDefaults();

#ifndef NO_CONFIG
  config_init(t);
#else
  config = 0;
#endif

  { static int endian_test = 1;
    host_lsbytefirst = *((char *)&endian_test) != 0;
  }

#ifdef MIN_ALIGNMENT_CONFIGURABLE
  alignof_struct_val = alignof_struct_default;
  alignof_toplevel_static_var = alignof_toplevel_static_default;
#endif
#ifdef BSS_THRESHOLD_DEFAULT
  bss_threshold = BSS_THRESHOLD_DEFAULT;
#endif

  phasename = "init";
  currentfunction.symstr = NULL;

  errstate_perfileinit();
  set_debug_options(t);
  /* -g options need to be known about before pp_init gets called (since   */
  /* that causes some macros to be defined, which may need to go into      */
  /* debug tables)                                                         */

  alloc_perfileinit();
  pp_init(&curlex.fl);
                  /* for pp_predefine() option and pragma on command line  */
                  /* must init_sym_tab here if pp shares its symbol tables */
  sourcefile = stdin_name; sourcemodule = "none";

#ifdef FORTRAN
  pp_pragmavec['x'-'a'] = 1;   /* Enable double-complex by default for now */
#endif

  var_cc_private_flags = 0;      /* No development options switched on yet */
  set_compile_options(t);
  mcdep_set_options(t);

  if (toolenv_lookup(t, ".asm_out") != NULL)
    asmfile = outfile;
  else
    objectfile = outfile;

  if (StrEq(infile, "-"))
  { /* then just leave as stdin */
    inputfromtty = filestat_istty(stdin);
    sourcestream = stdin;
#ifdef COMPILING_ON_RISC_OS
    /* Change default no-buffering to line buffering...  */
#  if defined(FOR_ACORN)
    /* A fault in the shared library forces the use of a */
    /* real buffer. NULL will not do...                  */
    {
    static char input_buffer[256];
    setvbuf(stdin, input_buffer, _IOLBF, sizeof(input_buffer));
    dde_prefix_init("");
    }
#  elif defined(TARGET_IS_ARM) && !defined(OBSOLETE_ARM_NAMES)
    setvbuf(stdin, NULL, _IOLBF, 256);
#  endif
#endif
    path_hd = mk_path_element(path_hd, PE_USER, "");
    if (path_hd->link == 0) path_tl = path_hd;
  } else {
#if defined(FOR_ACORN) && defined(COMPILING_ON_RISCOS)
    /* IDJ: 06-Jun-94. Set desktop "current directory" */
    dde_prefix_init(infile);
    dde_sourcefile_init();
#endif
    inputfromtty = NO;
    if ((sourcestream = trackfile_open(infile, "r")) == NULL)
    { char message[256];
      msg_sprintf(message, driver_couldnt_read, infile);
      driver_abort(message);

    } else {
      UnparsedName unparse;
      char new_dir[MAX_NAME], *mod;
      sourcefile = infile;
      /*
       * Add path name of source file to the -I list.
       */
      translate_fname(infile, &unparse, new_dir);
      new_dir[unparse.un_pathlen] = '\0';
      path_hd = mk_path_element(path_hd, PE_USER, new_dir);
/* Make sure path_tl is always the tail, even if file precedes -I    */
      if (path_hd->link == 0) path_tl = path_hd;
/* set up 'sourcemodule' from main part of file name:                   */
      mod = (char *)ccom_alloc(unparse.rlen+1L);
      memcpy(mod, unparse.root, unparse.rlen);
      mod[unparse.rlen] = 0;
      sourcemodule = mod;
    }
  }
  if (ccom_flags & FLG_COMPILE)
  {
    /* under the driver.c interface at most one of the following is true */
#ifndef NO_OBJECT_OUTPUT
    if (objectfile != NULL && !(ccom_flags & FLG_NO_OBJECT_OUTPUT))
    {  objstream = cc_open(objectfile, BINARY_OUTPUT);
# ifdef COMPILING_ON_RISC_OS
       set_time_stamp(objectfile, NO);
# endif
    }
#endif
#ifndef NO_ASSEMBLER_OUTPUT
    if (asmfile != NULL) asmstream = cc_open(asmfile, TEXT_FILE);
#endif
    if (objectfile == NULL && asmfile == NULL)
    {
#ifndef NO_ASSEMBLER_OUTPUT
      asmstream = stdout;
#endif
      SetFeature(Feature_Annotate);  /* simple test use */
    }

#ifndef NO_LISTING_OUTPUT
    if (listingfile != NULL)
    { if (listingfile[0] != '\0')
      { listingstream = cc_open(listingfile, TEXT_FILE);
        if (listingstream != stdout)   /* @@@ get rid of this hack */
          fprintf(listingstream, "     1  ");
      } else
        listingstream = stdout;
      if (ccom_flags & FLG_COUNTS)
      { FILE *map = fopen("counts", "rb");
        if (map == NULL) driver_abort(msg_lookup(driver_couldnt_read_counts));
        if (!map_init(map)) driver_abort(msg_lookup(driver_malformed_counts));
      }
    }
#endif
  }

  if (ccom_flags & FLG_MAKEFILE)
  { if (makefile == NULL)
    {   backchat_InclusionDependency dep;
        dep.targetName = objectfile;
        dep.dependsonName = sourcefile;
        backchat.send(
            (backchat.handle != NULL) ? backchat.handle : (void *)stdout,
                  BC_INCLUDEMSG, &dep);
        makestream = stdout;
    }
    else
    { /* if -M+, then open with append ("a") if already writing to  */
      /* makefile (makeflag != 0)                                   */
      makestream = cc_open(makefile,
              makeflag ? TEXT_FILE_APPEND : TEXT_FILE);
      makeflag = 1;
      /* Print out source file and object file for -M option...     */
      fprintf(makestream, DEPEND_FORMAT, objectfile, sourcefile);
    }
  }
  if (config & CONFIG_OPTIMISE_TIME) var_crossjump_enabled = 0;

#if REBUFFERSTDOUT
  if ((ccom_flags & FLG_PREPROCESS) || asmstream == stdout ||
        listingstream == stdout || makestream == stdout)
    setvbuf(stdout, stdoutbuffer, _IOFBF, sizeof stdoutbuffer);
#endif

  if (debugging(DEBUG_FILES))
    cc_msg("Compiling '%s'.\n", sourcefile);
  pp_notesource(sourcefile, sourcestream, NO);
  show_h_line(1, sourcefile, NO);
  if (sourcefile != stdin_name)
    dbg_include(sourcefile, path_hd->name, curlex.fl);

  aetree_init();
  bind_init();
  lex_init();                        /* sets curlex.sym to s_nothing   */
  builtin_init();                    /* change to setup from syn_init? */
  sem_init();
#ifndef PASCAL /*ECN*/
  syn_init();
#endif
  vargen_init();
  cg_init();

#ifndef NO_DUMP_STATE
  if (dump_state & DS_Load) LoadCompiledHeader();
#endif

  initstaticvar(datasegment, 1);    /* nasty here */
  drop_local_store();       /* required for alloc_reinit()             */

  if (ccom_flags & FLG_COMPILE)
    compile_statements();
  else
    preprocess_only();

  if (sourcefile != stdin_name)
      dbg_include(NULL, NULL, curlex.fl);
  cleanup();

  /* AM: re-open the discussion on return codes and errors.             */
  if (errorcount != 0) return EXIT_error;
  if (pp_pragmavec['e'-'a'] > 0) return 0; /* -zpe1 => "generous" mode */
  if (recovercount != 0) return EXIT_error;
  if (warncount != 0) return EXIT_warn;
  return 0;
}

/* end of compiler.c */
