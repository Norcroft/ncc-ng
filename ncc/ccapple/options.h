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

/*
 * This is a prototype file documenting (some of) the available
 * things which might go in target.h or options.h.
 * Insert all such flags in here.
 */

#ifndef _options_LOADED
#define _options_LOADED

#include "toolver.h"
#define NON_RELEASE_VSN TOOLVER_ARMCC

/* Include the following line to make an Apple APG compiler;
 * Exclude it to make a standard toolkit compiler.
 */

/*#define TARGET_IS_APPLEAPGMACHINE        1*/

/*
 * Firstly set TARGET_MACHINE and TARGET_SYSTEM.  Note that you should
 * follow the general line below.
 */
#ifdef TARGET_IS_APPLEAPGMACHINE
#  define TARGET_MACHINE    "Apple APG Machine"
/*
 * Since host.h is #included previously we can simply make the TARGET
 * OS depend on host, e.g.
 */
#  define TARGET_SYSTEM     "Apple Newton"
#  define TARGET_IS_APPLEAPG 1

#  define HOST_OBJECT_INCLUDES_SOURCE_EXTN 1  /* .c -> .c.o */

#else

#  define TARGET_SYSTEM     ""
#  define TARGET_IS_RISC_OS 1

#endif

#define TARGET_ENDIANNESS_CONFIGURABLE 1
#define TARGET_DEFAULT_BIGENDIAN 1               /* 1 => bigendian default */

/* Now here, or more likely in target.h you specify machine properties */
/* #define TARGET_IS_BIG_ENDIAN    1 /* -- if your target is big endian...  */
/* #define TARGET_IS_LITTLE_ENDIAN 1 -- if your target is little endian  */

#define DO_NOT_EXPLOIT_REGISTERS_PRESERVED_BY_CALLEE 1

/* #define TARGET_STACK_MOVES_ONCE 1  / * Experimental option */

#define TARGET_HAS_DIVREM_FUNCTION 1  /* divide fn also returns remainder. */
#define TARGET_HAS_DIV_10_FUNCTION 1  /* fast divide by 10                 */
                                      /* the last two would be in target.h */
                                      /* but are OS-dependent too.         */

/*
 * Now parameterisations as to facilities of the compiler you wish,
 * note that you are unlikely to need to specify many of these.
 */

/* #define EXTENSION_VALOF     1 -- to build a compiler with ACN's extension */
/* #define NO_ASSEMBLER_OUTPUT 1 -- to build a compiler sans ... capability */
/* #define NO_OBJECT_OUTPUT    1 -- to build a compiler sans ... capability */
/* #define NO_LISTING_OUTPUT   1 -- to build a compiler sans ... capability */
/* #define NO_INSTORE_FILES    1 -- to build a compiler sans in-store hdrs */
/* #define NO_DEBUGGER         1 -- to build a compiler sans debugger suppt */
/* #define NO_SELF_CHECKS      1 -- to avoid building checks aimed at itself */
/* #define NO_VERSION_STRINGS  1 -- to avoid module version strings */

#ifndef RELEASE_VSN
#  define ENABLE_ALL          1 /* -- to enable all debugging options */
#endif

#ifdef TARGET_IS_APPLEAPGMACHINE

#  define EXTENSION_COUNTED_STRINGS     1  /* to enable Pascal-style strings */
#  define ALLOW_KEYWORDS_IN_HASHIF      1  /* to allow keywords in #if expns */
#  define ALLOW_WHITESPACE_IN_FILENAMES 1  /* to allow as it says...         */
#  define ONLY_WARN_ON_NONPRINTING_CHAR 1  /* to do as it says...            */
#  define HOST_DOES_NOT_FORCE_TRAILING_NL 1
#  define HOST_WANTS_NO_BANNER 1           /* no routine banner output       */
#  define DISABLE_ERRORS 1

#  define  C_ENV_VAR  "ARMCInclude"
#  define PCS_DEFAULTS (PCS_CALLCHANGESPSR + PCS_NOSTACKCHECK)

#  ifndef DRIVER_OPTIONS
#    define DRIVER_OPTIONS        { "-zps1", NULL } /* -- e.g. no stack checks */
#  endif

#else  /* toolkit compiler */

#  define  C_ENV_VAR  "ARMLIB"

#  define PCS_DEFAULTS  PCS_CALLCHANGESPSR  /* 32 bit */
                        /* + PCS_FPE3 */
                        /* + PCS_NOSTACKCHECK */
                        /* + PCS_REENTRANT */
                        /* + PCS_FPREGARGS */
#  ifndef DRIVER_OPTIONS
#    define DRIVER_OPTIONS           { NULL }
#  endif

#endif

#  define NO_STATIC_BANNER 1

pascal void SpinCursor(short increment);        /* copied from CursorCtl.h */
#define ExecuteOnSourceBufferFill()   SpinCursor(1)

#define CHAR_CR '\r'    /* like MPW C, '\r' == 10 and '\n' == 13 */
/* #define CORRECT_IS_BETTER_THAN_FAST 1           /* fix bug in pp.c */

#endif

/* end of ccapple/options.h */
