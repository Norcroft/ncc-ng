/*
 * options.h -- compiler configuration options set at compile time
 * Copyright (C) 1991, 1992 Advanced RISC Machines Ltd. All rights reserved.
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

#include "toolver.h"
#define NON_RELEASE_VSN TOOLVER_ARMCC

#define TARGET_ENDIANNESS_CONFIGURABLE 1
#define TARGET_DEFAULT_BIGENDIAN 0       /* 1 => bigendian default */
                                         /* 0 => littleendian default */
                                         /* unset => defaults to host */

#define PCS_DEFAULTS  (PCS_CALLCHANGESPSR  /* 32 bit */ \
                         | PCS_FPE3                     \
                         | PCS_SOFTFP                   \
                      /* | PCS_NOSTACKCHECK */          \
                      /* | PCS_REENTRANT */             \
                      /* | PCS_FPREGARGS */             \
                      )

#define TARGET_SYSTEM     ""
#define TARGET_IS_RISC_OS 1
#define TARGET_HAS_DIVREM_FUNCTION 1 /* divide fn also returns remainder.*/
#define TARGET_HAS_DIV_10_FUNCTION 1 /* fast divide by 10                */
                                     /* the last two would be in target.h*/
                                     /* but are OS-dependent too. */

#define TARGET_HAS_INLINE_ASSEMBLER
#define ARM_INLINE_ASSEMBLER
#define PROFILE_COUNTS_INLINE 1

/* #define DO_NOT_EXPLOIT_REGISTERS_PRESERVED_BY_CALLEE 1 */
/* #define MOVC_KILLS_REGISTER_PRESERVED_BY_CALLEE_EXPLOITATION 1 */

/* #define TARGET_STACK_MOVES_ONCE 1  / * Experimental option */

#ifndef DRIVER_OPTIONS         /* -D__arm done by TARGET_PREDEFINES */
#  define DRIVER_OPTIONS       {NULL}
#endif

/* to avoid conflict with host compilers */
#define C_INC_VAR  "ARMINC"
#define C_LIB_VAR  "ARMLIB"

#ifndef RELEASE_VSN
#  define ENABLE_ALL          1 /* -- to enable all debugging options */
#endif

#define HOST_WANTS_NO_BANNER 1

/* mac-specific options - find a better home for these sometime! */
#ifdef macintosh
#  define NO_STATIC_BANNER 1
   pascal void SpinCursor(short increment);        /* copied from CursorCtl.h */
#  define ExecuteOnSourceBufferFill()   SpinCursor(1)
#endif

#define TARGET_STACK_MOVES_ONCE
#define target_stack_moves_once (var_cc_private_flags & 32768L)

#define DISABLE_ERRORS

#define MSG_TOOL_NAME  "armcc"  /* used to load correct NLS message file */

#define TARGET_HAS_ASD
#define TARGET_HAS_DWARF

#define RECORD_SOURCE_LOCATION 1
#define PRETTY_DISASSEMBLY 1

#endif

/* end of ccarm/options.h */
