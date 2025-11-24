/*
 * mip/globals.h - ubiquitously required definitions
 * Copyright (C) Acorn Computers Ltd., 1988.
 * Copyright (C)  Codemist Ltd., 1988.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#ifndef _globals_LOADED
#define _globals_LOADED

#ifdef __STDC__
#  include <stdarg.h>
#else
#  include <varargs.h>
#endif

#ifndef _host_LOADED
#  include "host.h"
#endif
#ifdef COMPILING_ON_MVS
/*
 * The following #included #define's ensure that external symbols are
 * limited to 6 chars without gratuitous changes to every file.
 */
#  include "sixchar.h"
#endif
#ifndef _options_LOADED
#  include "options.h"
#endif
#ifndef _target_LOADED
#  include "target.h"
#endif
#ifndef _defaults_LOADED
#  include "defaults.h"
#endif
#ifndef _defs_LOADED
#  include "defs.h"
#endif

#include "config.h"

#include "msg.h"

/*
 * DUFF_ADDR is used to initialise pointers which may not be dereferenced.
 * The address chosen traps on dereference on the machines we use.
 * No use is made of its value, save that is assumed to compare equal to
 * itself when used to initialise allocators.  It could, functionally,
 * equally well be NULL, or for the queasy, a pointer to one static byte.
 */
#define DUFF_ADDR (VoidStar)(~0x45245252L)     /* 0xbadbadad */

/* the following lines ease bootstrapping problems: "\v\f\r" respectively */
/* (allowing different settings from the usual ones below in options.h    */
#ifndef CHAR_NL
#  define CHAR_NL 10
#endif
#ifndef CHAR_VT
#  define CHAR_VT 11
#endif
#ifndef CHAR_FF
#  define CHAR_FF 12
#endif
#ifndef CHAR_CR
#  define CHAR_CR 13
#endif
#define CHAR_BEL ('A'==193 ? 0x2f : 7)

/* Beware the following, if n==32 then ANSI-undefined.                     */
#define lsbmask(n) (((unsigned32)1 << (n)) - 1)

#define memclr(a,n) memset(a,0,n)

extern int32 pp_pragmavec[];
/*
 * We put xx!=0 for switches that default to ON, and xx>0 for default off.
 */
#define warn_implicit_fns       (pp_pragmavec['a'-'a'] != 0)  /* cc only */
#define memory_access_checks    (pp_pragmavec['c'-'a'] > 0)   /* mip */
#define warn_deprecated         (pp_pragmavec['d'-'a'] != 0)  /* cc */
/* beware that #pragma -e is temporarily used for #error behaviour */
#define fpregargs_disabled      (pp_pragmavec['g'-'a'] > 0)
#define integerlike_enabled     (pp_pragmavec['h'-'a'] != 0)  /* cc */
#define crossjump_enabled       (pp_pragmavec['j'-'a'] != 0)  /* mip */
/* ECN - pragma to disable all gen optimisations */
#define gen_opt_disabled        (pp_pragmavec['k'-'a'] > 0)
#define ldm_enabled             (pp_pragmavec['m'-'a'] > 0)   /* arm */
/* ECN - pragma to disable tailcalls 'n' for Notailcalls */
#define no_tail_calls           (pp_pragmavec['n'-'a'] > 0)
#define multiple_aof_code_areas (pp_pragmavec['o'-'a'] > 0)   /* arm, mip */
#define profile_option          (pp_pragmavec['p'-'a'] > 0)   /* mip, arm */
#define full_profile_option     (pp_pragmavec['p'-'a'] > 1)   /* mip */
#define no_stack_checks         (pp_pragmavec['s'-'a'] > 0)   /* arm */
#define force_top_level         (pp_pragmavec['t'-'a'] != 0)  /* cc */
#define special_variad          pp_pragmavec['v'-'a']         /* cc */
#define pcrel_vtables           (pp_pragmavec['u'-'a'] > 0)
#define no_side_effects         (pp_pragmavec['y'-'a'] > 0)   /* cc */
#define cse_enabled             (pp_pragmavec['z'-'a'] > 0)   /* mip */
#define resultinflags           (pp_pragmavec['x'-'a'] > 0)

#define var_warn_implicit_fns       pp_pragmavec['a'-'a']
#define var_memory_access_checks    pp_pragmavec['c'-'a']
#define var_warn_deprecated         pp_pragmavec['d'-'a']
#define global_floatreg_var         pp_pragmavec['f'-'a']
#define var_include_once            pp_pragmavec['i'-'a']
#define var_crossjump_enabled       pp_pragmavec['j'-'a']
#define var_gen_opt_disabled        pp_pragmavec['k'-'a']
#define var_ldm_enabled             pp_pragmavec['m'-'a']
#define var_no_tail_calls           pp_pragmavec['n'-'a']
#define var_aof_code_area           pp_pragmavec['o'-'a']
#define var_profile_option          pp_pragmavec['p'-'a']
/* The next pragma provides flags to use during DEVELOPMENT. Permanent */
/* flags should be subsumed into feature, config or a proper pragma.   */
#define var_cc_private_flags        pp_pragmavec['q'-'a']
#define global_intreg_var           pp_pragmavec['r'-'a']
#define var_no_stack_checks         pp_pragmavec['s'-'a']
#define var_force_top_level         pp_pragmavec['t'-'a']
#define var_no_side_effects         pp_pragmavec['y'-'a']
#define var_cse_enabled             pp_pragmavec['z'-'a']
#define var_resultinflags           pp_pragmavec['x'-'a']

/*
 * Bits within var_cc_private_flags: PLEASE keep up to date.
 * 0x40000000            COMMON, CODE attribute - used internally
 * 0x20000000            currently generating code for a VTable - used internally
 * 0x01000000 16777216   Enable Standard scoping
 * 0x00800000 8388608    Suppress generation of fpdesc tables
 * 0x00400000 4194304    Show final function overloads
 * 0x00200000 2097152    Enable C++ generated fns debugging
 * 0x00100000 1048576    Disable direct substituion of inline function arguments
 * 0x00080000  524288    flowgraf: uh... tail recursion something?
 * 0x00040000  262144    flowgraf: Disable BLK2EXIT stuff
 * 0x00020000  131072    Disable struct binder splitting
 * 0x00010000   65536    Enable exprtemps debugging
 * 0x00008000   32768    Disable str compression (#ifdef STRING_COMPRESSION)
 * 0x00004000   16384    Show overload match value calculations
 * 0x00002000    8192    Disable function inlining (forces out-of-line)
 * 0x00001000    4096    Disable regalloc allocation preference calculation
 * 0x00000800    2048    Disable regalloc copy-avoidance preference
 * 0x00000400    1024    Disable preservation of unused a1-a4 across fn call
 * 0x00000200     512    J_OPSYSK sets the psr
 * 0x00000100     256    Disable live range splitting
 * 0x00000080     128    Enable generation of exception tables
 * 0x00000040      64    CSE: Disable propagating local values
 * 0x00000020      32    CSE: Disable heapptr dataflow
 * 0x00000010      16    Disable the tail continuation optimisation
 * 0x00000008       8    Disable peepholing
 * 0x00000004       4    Disable regalloc spill 'cleaning'
 * 0x00000002       2    Toggle allocate store for top-level non-addrof
                         simpletype consts (default: C/do, C++/don't)
 * 0x00000001       1    Ignore 'register' attribute on binders
 */

/* static options for compiler */

#define NAMEMAX       256L      /* max no of significant chars in a name  */
#define BIND_HASHSIZE 521L      /* no. of Symstr hash table buckets */
#define MAX_SAVED_LABELS 32L    /* max no of label to save in a label chain */

#define SEGSIZE     31744L      /* (bytes) - unit of alloc of hunks         */
                                /* (32K - 1024) for benefit of 16 bit ints  */
#define ICODESEGSIZE  512L      /* Icode vector now allocated in 8k hunks   */
#define CODEVECSEGBITS 10L      /* 4Kbyte unit of allocation                */
#define CODEVECSEGSIZE (1L<<CODEVECSEGBITS)
#define CODEVECSEGMAX 256L      /* max segments (max 1024K bytes/proc)      */
#define REGHEAPSEGBITS  9L      /* index array for segment of 512 vregs     */
#define REGHEAPSEGSIZE (1L<<REGHEAPSEGBITS)
#define REGHEAPSEGMAX  64L      /* max segments (hence max 32K vregs/proc)  */
/* An old comment claimed that LITPOOLSIZE was 1024 for 'max address range' */
/* I suspect that this is out of date now that litpool overflows gently.    */
#define LITPOOLSEGBITS  5L      /* index array for segment of 32 lits       */
#define LITPOOLSEGSIZE (1L<<LITPOOLSEGBITS)
#define LITPOOLSEGMAX  32L      /* max segments, so 1024 lits ovfl gently   */

#ifdef  FOR_ACORN
#ifndef PASCAL
#ifndef FORTRAN
/* support for CFront pre-processing (IDJ:6-Jun-94) */
extern int cplusplus_flag;
#endif
#endif
#endif

/*
 * disable error/warnings...
 */
extern int32 suppress;
#define D_IMPLICITCTOR          1L
#define D_ASSIGNTEST            2L
#define D_SHORTWARN             4L /* no longer used apparently */
#define D_PPNOSYSINCLUDECHECK   8L
#define D_IMPLICITVOID       0x10L
#define D_VALOFBLOCKS        0x20L
#define D_IMPLICITNARROWING  0x40L
#define D_ACCESS             0x80L
#define D_LONGFLOAT         0x100L
#define D_IMPLICITVIRTUAL   0x200L
#define D_STRUCTPADDING     0x400L
#define D_LOWERINWIDER      0x800L
#define D_GUARDEDINCLUDE   0x1000L

/* These two are currently pragmas rather than bits in suppress. Why? */
#define D_DEPRECATED       0x2000L
#define D_IMPLICITFNS      0x4000L
#define D_STRUCTASSIGN     0x8000L

#ifdef PASCAL /*ECN*/
#undef D_ASSIGNTEST
#define D_ASSIGNTEST          (~0)
#endif

/* The following are used in some implementations to suppress ERRORS.   */
/* Note: they partly duplicate the -FC (Feature_LimitedPCC) option.     */
/* Note: suppressing errors makes the implementation non-conforming.    */
#define D_ZEROARRAY       0x10000L
#define D_PPALLOWJUNK     0x20000L
#define D_IMPLICITCAST    0x40000L
#define D_MPWCOMPATIBLE   0x80000L
#define D_CAST           0x100000L /* Suppress errors about implicit casting of
                                      pointer to A to pointer to B (A != B)
                                    */
#define D_LINKAGE        0x200000L /* ECN - Suppress errors about static/extern
                                      linkage disagreements
                                    */
#define D_UNUSEDTHIS     0x400000L
#define D_FUTURE         0x800000L /* suppress C++ keyword in C, etc. */
#define D_CFRONTCALLER  0x1000000L /* warn about virtual fn calls, ptr to mem fns */
#define D_MULTICHAR     0x2000000L /* warn about 'foo' */
#define D_LONGLONGCONST 0x4000000L /* warn about 3000000000 being 3000000000ll */
#define D_IMPLICITINT   0x8000000L /* no implicit int in C++ */

/* warnings which are disabled by default */
#ifndef D_SUPPRESSED
#  define D_SUPPRESSED \
  (D_SHORTWARN | D_STRUCTPADDING | D_GUARDEDINCLUDE | D_PPNOSYSINCLUDECHECK | \
   D_IMPLICITCTOR | D_IMPLICITNARROWING | D_LOWERINWIDER | D_FUTURE | \
   D_CFRONTCALLER | D_STRUCTASSIGN)
#endif

#ifdef PASCAL /*ECN*/
/*
 * run time checks
 */
extern int32 rtcheck;
#define RTCHECK_ARRAY                   1L   /* pc */
#define RTCHECK_CASE                    2L   /* pc */
#define RTCHECK_NIL                     4L   /* pc */
#define RTCHECK_REFERENCE               8L   /* pc */
#define RTCHECK_ASSERT                 16L   /* pc */
#define RTCHECK_DEADCODE               32L   /* pc */
#endif

#ifdef CPLUSPLUS
#define LanguageIsCPlusPlus HasFeature(Feature_CPP)
#else
#define LanguageIsCPlusPlus 0
#endif

/*
 * Dynamic configuration flags.
 */
extern int32 config;
/*                               1L  CONFIG_HAS_MULTIPLY now defunct    */
/*                               2L  CONFIG_SLOW_COND_FP_EXEC now defunct */
#define CONFIG_INDIRECT_SETJMP   4L  /* a fn ptr may point to setjmp()  */
#define CONFIG_CLIPPER30         8L  /* Special for Intergraph Clipper  */
#define CONFIG_ALT_REGUSE     0x10L  /* to generalise normal_sp_sl      */
#define CONFIG_FPREGARGS      0x20L
#define CONFIG_BIG_ENDIAN     0x40L
#define CONFIG_ENDIANNESS_SET 0x80L  /* if this is set (by config_init())  */
                                     /* default of target byte sex to host */
                                     /* does not apply                     */
#define CONFIG_NO_UNALIGNED_LOADS 0x100L
#define CONFIG_REENTRANT_CODE     0x200L
#define CONFIG_OPTIMISE_SPACE     0x400L
#define CONFIG_OPTIMISE_TIME      0x800L
#define CONFIG_SOFTWARE_FLOATS   0x1000L
#define CONFIG_SOFTWARE_DOUBLES  0x2000L
#define CONFIG_SOFTWARE_FP       (CONFIG_SOFTWARE_FLOATS+CONFIG_SOFTWARE_DOUBLES)

#define CONFIG_HALFWORD_SPT      0x4000L
#define CONFIG_STRUCT_PTR_ALIGN  0x8000L /* take advantage of alignment of ptrs to structs */
#define CONFIG_NO_HALFWORD_STORES 0x10000L
#define CONFIG_UNWIDENED_NARROW_ARGS 0x20000L
#define CONFIG_LONG_MULTIPLY    0x40000L /* target has long multiply */
#define CONFIG_32BIT            0x80000L /* target supports 32 bit mode */
#define CONFIG_26BIT           0x100000L /* target supports 26 bit mode */

#ifdef TARGET_IS_BIG_ENDIAN
#define target_lsbytefirst 0
#else
#ifdef TARGET_IS_LITTLE_ENDIAN
#define target_lsbytefirst 1
#else
#define target_lsbytefirst ((config & CONFIG_BIG_ENDIAN) == 0)
#endif
#endif

/* Note: 3 separate endianness variables:                                  */
/*   target_lsbytefirst                    - big/little-endian             */
/*   target_lsbitfirst                     - bitfields within machine word */
/*   HasFeature(Feature_ReverseBitfields)  - reverse bfs within container  */

/* Currently force lsbitfirst to by lsbytefirst until there is a mechanism */
/* for changing it (IJR).                                                  */
#define target_lsbitfirst target_lsbytefirst

extern bool host_lsbytefirst;

extern FILE *asmstream, *objstream;
extern char const *sourcefile;
extern char const *objectfile;
extern int32 xwarncount, warncount, recovercount, errorcount;
extern bool list_this_file;
extern FILE *listingstream;
extern FILE *errors;
extern bool implicit_return_ok;
extern char *phasename;
typedef struct CurrentFnDetails {
    Symstr *symstr;
    int xrflags;
    Binder *structresult;
    VRegnum baseresultreg;
    int nresultregs;
    int32 flags, auxflags;
    int32 maxstack;
    int32 maxargsize;
    int32 argwords;
    int32 fltargwords;
    BindList *argbindlist;
    int32 fnname_offset;      /* for xxx/gen.c    */
    FileLine fl;
} CurrentFnDetails;

extern CurrentFnDetails currentfunction;

#define procflags currentfunction.flags
#define procauxflags currentfunction.auxflags
#define greatest_stackdepth currentfunction.maxstack
#define argument_bindlist currentfunction.argbindlist
#define max_argsize currentfunction.maxargsize
#define cg_fnname_offset_in_codeseg currentfunction.fnname_offset

#ifdef TARGET_IS_ARM_OR_THUMB
  extern int arthur_module;
#endif

extern int bss_threshold;
extern bool disallow_tentative_statics;

Int64Con *mkint64const(SET_BITMAP m, int64 const *i64);

extern FloatCon *real_of_string(const char *s, int32 flag);
extern FloatCon *real_to_real(FloatCon *fc, SET_BITMAP m);
extern FloatCon *int_to_real(int32 n, int32 u, SET_BITMAP m);

extern int32 length(List const *l);
extern List *dreverse(List *x);
extern Binder *dreverse_binder(Binder *x);
extern List *nconc(List *x, List *y);
extern bool generic_member(IPtr a, List const *l);
extern List *generic_ndelete(IPtr a, List *l);
/* Destructively modify the argument reglist by removing from it the   */
/* first entry whose data field is 'a'.                                */

extern int32 max(int32 a, int32 b);
extern int32 bitcount(int32 n);
extern int32 logbase2(int32 n);

extern void errstate_perfileinit(void);
extern void errstate_initialise(void);

extern int32 aetree_debugcount;
extern int32 cse_debugcount;
extern int32 localcg_debugcount;
extern int32 syserr_behaviour;
extern int files_debugcount;

char const *compiler_name(void);

#ifdef __CC_NORCROFT
  /*
   * The next procedure takes a string as a format... check args.
   * Note use of a cryptic pragma rather than a nice spelt out one,
   * since the option is only intended for support of this compiler
   */
#  pragma -v3
#endif
extern void cc_msg(char *s, ...);  /* NB still an uncompressed string */
#ifdef __CC_NORCROFT
#  pragma -v0
#endif
#ifdef NLS
extern void cc_msg_lookup(msg_t errcode, ...);
#else
#  define cc_msg_lookup cc_msg
#endif

/* The following 4 functions are used by the Fortran front end. */
extern void cc_rerr_l(int32 line, msg_t errorcode, va_list a);
extern void cc_warn_l(int32 line, msg_t errorcode, va_list a);
extern void cc_err_l(int32 line, msg_t errorcode, va_list a);
extern void cc_fatalerr_l(int32 line, msg_t errorcode, va_list a);

extern void flt_report_error(int);
extern void compile_abort(int);
extern void summarise(void);
extern void listing_diagnostics(void);

#ifdef CALLABLE_COMPILER
#define reg_setallused(s) ((void)(s))
#else
#ifndef NON_CODEMIST_MIDDLE_END
extern void reg_setallused(RealRegSet *s);      /* not as nasty as memcpy */
#endif
#endif

#define StrEq(a, b) (strcmp((a), (b)) == 0)
#define StrnEq(a, b, n) (strncmp((a), (b), (n)) == 0)

#endif

/* end of mip/globals.h */
