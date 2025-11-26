/*
 * options.h -- compiler configuration options set at compile time
 * Copyright (C) Acorn Computers Ltd. 1988
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#ifndef _options_LOADED
#define _options_LOADED

/*
 * The following conditional settings allow the produced compiler (TARGET)
 * to depend on the HOST (COMPILING_ON) environment.
 * Note that we choose to treat this independently of the target-machine /
 * host-machine issue.
 */

#define CPLUSPLUS 1

#define TARGET_HAS_DWARF 1

#define TARGET_VTAB_ELTSIZE  4
    /* for indirect VTABLEs optimised for single inheritance */

/* Expire this version at 00:00:01 on Saturday 01 Oct 94 */
/*#define UNIX_TIME_LIMIT 780969601                      */

#define TARGET_ENDIANNESS_CONFIGURABLE 1
/* #define TARGET_DEFAULT_BIGENDIAN 0 */ /* 1 => bigendian default */
                                         /* 0 => littleendian default */
                                         /* unset => defaults to host */

#define DISABLE_ERRORS       1 /* -- to enable -Exyz... error suppression */
#define EXTENSION_SYSV       1 /* -- to allow #ident ... */

#define TARGET_HAS_INLINE_ASSEMBLER     1
#define ARM_INLINE_ASSEMBLER            1
#define PROFILE_COUNTS_INLINE           1

#ifndef __acorn

#  ifdef TARGET_IS_NEWTON
#    define TARGET_MACHINE    "Newton"
#    define TARGET_SYSTEM     "Newton OS"
#    define TARGET_IS_NEWTONOS 1
#    define TARGET_DEFAULT_BIGENDIAN 1
#    define STRUCT_PTR_ALIGN_DEFAULT 0 /* do not assume struct ptrs are 4-byte aligned */
#    define NO_INSTORE_FILES  1          /* no in-store headers for Newton.     */
#    define PCS_DEFAULTS (PCS_CALLCHANGESPSR | PCS_FPE3 | PCS_NOSTACKCHECK)
     /* Exploiting registers preserved by callee saves only 200 bytes in the    */
     /* Newton ROM and makes patching more difficult                            */
#    define DRIVER_OPTIONS     {"-zpu1", NULL} /* pc-rel vtables */
#    define DO_NOT_EXPLOIT_REGISTERS_PRESERVED_BY_CALLEE 1
#    define CFRONT_COMPATIBLE_DESTRUCTORS 1
#    define HOST_OBJECT_INCLUDES_SOURCE_EXTN 1  /* .c -> .c.o */
#    define EXTENSION_COUNTED_STRINGS     1  /* to enable Pascal-style strings  */
#    define EXTENSION_UNSIGNED_STRINGS 1     /* and they are unsigned char[]    */
#    define ALLOW_WHITESPACE_IN_FILENAMES 1  /* to allow as it says...          */
#    define ONLY_WARN_ON_NONPRINTING_CHAR 1  /* to do as it says...             */
#    define HOST_DOES_NOT_FORCE_TRAILING_NL 1
#    define HOST_WANTS_NO_BANNER 1           /* no routine banner output        */
#    define DISABLE_ERRORS 1
#    define TARGET_WANTS_LINKER_TO_RESOLVE_FUNCTION_REFERENCES 1
#    define HOST_CANNOT_INVOKE_ASSEMBLER 1
#    define HOST_CANNOT_INVOKE_LINKER 1
#    define PUT_FILE_NAME_IN_AREA_NAME 1
#    define CHAR_NL 13 /* as MPW C '\n' */
#    define CHAR_CR 10 /* as MPW C '\r' */
#    define CFRONT_MODE_WARN_LACKS_STORAGE_TYPE 0

#define SUPPRESS_DEFAULT_LIST \
    X(ShortWarn) \
    X(StructPadding) \
    X(PPNoSysIncludeCheck) \
    X(ImplicitCtor) \
    X(LowerInWider) \
    X(CFrontCaller) \
    X(MultiChar) \
    X(StructAssign) \

#    define HOST_DOESNT_WANT_FP_OFFSET_TABLES 1
#    ifndef COMPILING_ON_MACINTOSH /* ifdef HOST_FILENAMES_ARE_CASE_SENSISTIVE */
#      define RETRY_INCLUDE_LOWERCASE
#    endif
#    ifdef MAKE_WCHAR_T_UNSIGNED_SHORT
       /* make wchar_t be unsigned short */
       /* maybe this should be cfe somewhere */
#      define sizeof_wchar sizeof_short
#      define wchar_typespec (bitoftype_(unsigned)|bitoftype_(short)) /* for sem.c */
#      define NUM_WCHAR    (NUM_INT|NUM_SHORT|NUM_UNSIGN)  /* for lex.c */
#    endif
#  else /* NOT TARGET_IS_NEWTON */
     /* usual cross-development case... */
#    define TARGET_SYSTEM     ""
#    define TARGET_IS_RISC_OS 1
#    define TARGET_DEFAULT_BIGENDIAN 0
#    define PCS_DEFAULTS  (PCS_CALLCHANGESPSR | PCS_FPE3 | PCS_SOFTFP)
                       /* | PCS_NOSTACKCHECK */
                       /* | PCS_REENTRANT */
                       /* | PCS_FPREGARGS */
#  endif

#  define HOST_WANTS_NO_BANNER 1

#  define TARGET_HAS_DIVREM_FUNCTION 1 /* divide fn also returns remainder.*/
#  define TARGET_HAS_DIV_10_FUNCTION 1 /* fast divide by 10                */
                                        /* the last two would be in target.h*/
                                        /* but are OS-dependent too. */
#  ifndef DRIVER_OPTIONS
     /* -D__arm done by TARGET_PREDEFINES */
#    define DRIVER_OPTIONS       {NULL}
#  endif

#else /* __acorn is defined */

#  ifdef __unix
#    define TARGET_SYSTEM     "RISCiX"
#    define TARGET_IS_UNIX    1
#    define NO_INSTORE_FILES  1     /* no in-store headers under Unix.  */
#    define HOST_WANTS_NO_BANNER 1
/* #define TARGET_HAS_DIVREM_FUNCTION 1 -- divide fn also returns remainder.*/
/* #define TARGET_HAS_DIV_10_FUNCTION 1 -- fast divide by 10            */
                                        /* but not under ARM Unix...    */
#  ifndef DRIVER_OPTIONS
     /* -D__arm done by TARGET_PREDEFINES */
#    define DRIVER_OPTIONS     {"-zps1", "-D__unix", "-D__acorn", NULL}
#  endif
#endif

# ifdef __riscos
#   define TARGET_SYSTEM     "RISC OS"
#   define TARGET_IS_RISC_OS 1
#   define TARGET_HAS_DIVREM_FUNCTION 1 /* divide fn also returns remainder.*/
#   define TARGET_HAS_DIV_10_FUNCTION 1 /* fast divide by 10            */
                                   /* the last two would be in target.h */
                                   /* but are OS-dependent too.         */
#   ifndef DRIVER_OPTIONS
      /* -D__arm done by TARGET_PREDEFINES */
#     define DRIVER_OPTIONS     {"-D__riscos", "-D__acorn", NULL}
#   endif
#  endif

#endif /* defined(__acorn) */

#include "toolver.h"
#define NON_RELEASE_VSN TOOLVER_ARMCPP

#ifndef TARGET_IS_NEWTON
# define PROFILE_COUNTS_INLINE 1
  /* to avoid conflict with host compilers */
# define C_INC_VAR  "ARMINC"
# define C_LIB_VAR  "ARMLIB"
#else
# define PROFILE_DISABLES_TAILCALL 1
# define  C_INC_VAR  "ARMCIncludes"
# define  C_LIB_VAR  NULL
#endif

/* #define DO_NOT_EXPLOIT_REGISTERS_PRESERVED_BY_CALLEE 1 */
/* #define MOVC_KILLS_REGISTER_PRESERVED_BY_CALLEE_EXPLOITATION 1 */

/* #define TARGET_STACK_MOVES_ONCE 1  / * Experimental option */

#ifndef RELEASE_VSN
#  define ENABLE_ALL          1 /* -- to enable all debugging options */
#endif

/* mac-specific options - find a better home for these sometime! */
#ifdef macintosh
  /* The origin of time is 0th Jan 1904... */
#  ifdef UNIX_TIME_LIMIT
#    define TIME_LIMIT (UNIX_TIME_LIMIT+(66*365+16)*24*3600)
#  endif
#  ifdef applec
     /* work-around for MPW C */
#    define NO_STATIC_BANNER 1
#  endif
   pascal void SpinCursor(short increment);     /* copied from CursorCtl.h */
#  define ExecuteOnSourceBufferFill()   SpinCursor(1)
#  ifdef __MWERKS__
#    define REBUFFERSTDOUT 1
#  endif

#else /* NOT macintosh */
# ifdef UNIX_TIME_LIMIT
#  define TIME_LIMIT UNIX_TIME_LIMIT
# endif
#endif

#ifdef TARGET_IS_NEWTON
#endif

#ifdef TIME_LIMIT
# define VENDOR_NAME "Advanced RISC Machines Limited"
#endif

#ifdef CPLUSPLUS
# ifndef CFRONT_MODE_WARN_LACKS_STORAGE_TYPE
#  define CFRONT_MODE_WARN_LACKS_STORAGE_TYPE 1
# endif
#endif

#define MSG_TOOL_NAME  "armcpp"  /* used to load correct NLS message file */

#define TARGET_HAS_ASD

#endif

/* end of cpparm/options.h */
