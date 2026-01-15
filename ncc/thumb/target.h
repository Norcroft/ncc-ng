
/*
 * C compiler file thumb/target.h, version 1
 * Copyright (C) Codemist Ltd., 1988-94.
 * SPDX-Licence-Identifier: Apache-2.0
 */

/*
 * RCS $Revision$
 * Checkin $Date$
 * Revising $Author$
 */

#ifndef _target_LOADED
#define _target_LOADED 1

#define TARGET_IS_THUMB 1

#include "toolenv.h"

#ifndef TARGET_MACHINE
#  define TARGET_MACHINE "Thumb"
#endif

#define TARGET_PREDEFINES { "__arm", \
                            "__thumb", \
                            "__CLK_TCK=100", \
                            "__JMP_BUF_SIZE=22" }

#define EXTENSION_SYSV 1

#define localcg_newliteralpool_exists 1

#define SOFTWARE_FLOATING_POINT 1
#define software_floating_point_enabled 1
#define software_floats_enabled 1
#define software_doubles_enabled 1
#define SOFTWARE_FLOATING_POINT_RETURNS_DOUBLES_IN_REGISTERS 1
#define TARGET_SOFTFP_SUPPORT_INCLUDES_REVERSE_OPS 1
#define TARGET_FP_ARGS_IN_FP_REGS 1
#define TARGET_HAS_IEEE         1

#define TARGET_ENDIANNESS_CONFIGURABLE 1

#ifndef TARGET_IS_BIG_ENDIAN
#  ifndef TARGET_ENDIANNESS_CONFIGURABLE
#    define TARGET_IS_LITTLE_ENDIAN       1
#  endif
#endif

#define TARGET_HAS_DATA_VTABLES 1
#define target_has_data_vtables 1

#define NON_ALIGNED_DATA

#define TARGET_HAS_NATURALLY_ALIGNED_STATICS 1
#define TARGET_HAS_FP_OFFSET_TABLES   1
#define TARGET_HAS_DEBUGGER           1
#define TARGET_DEBUGGER_WANTS_MACROS  1

#define TARGET_HAS_NEGATIVE_INDEXING    1
/* #define TARGET_HAS_SCALED_ADDRESSING */
extern int target_scalable(int32 m, int32 n);
/* #define TARGET_HAS_SWITCH_BRANCHTABLE   1 */
#define TARGET_HAS_TAILCALL             1
/*#define TARGET_HAS_TAILCALLR            1*/
#define TARGET_HAS_RECURSIVE_TAILCALL_ONLY 1
#define TARGET_HAS_MULTIPLY             1
#define TARGET_HAS_ROTATE               1
#define TARGET_HAS_BLOCKMOVE            1
#define THUMB_MOVC                      1
/* #define TARGET_ALLOWS_COMPARE_CSES      1 */
#define TARGET_HAS_2ADDRESS_CODE        1
#define two_address_code(op) (((op) & J_TABLE_BITS) == J_SHLR || \
                              ((op) & J_TABLE_BITS) == J_SHRR || \
                              ((op) & J_TABLE_BITS) == J_RORR)

#define TARGET_HAS_HALFWORD_INSTRUCTIONS 1

#define TARGET_HAS_SPECIAL_VARARGS      1

#define TARGET_GEN_NEEDS_VOLATILE_INFO  1

#define DO_NOT_EXPLOIT_REGISTERS_PRESERVED_BY_CALLEE 1

/* #define TARGET_INLINES_MONADS           1 */

#define TARGET_LACKS_RR_UNALIGNED_ACCESSES 1

#define TARGET_LACKS_UNSIGNED_FIX       1

#define TARGET_ADDRESSES_UNSIGNED       1
#define TARGET_LDRK_MIN                 0
#define TARGET_LDRK_MAX                 127L
#define TARGET_LDRWK_MIN                0
#define TARGET_LDRWK_MAX                63L
#define TARGET_LDRBK_MIN                0
#define TARGET_LDRBK_MAX                31L

#define TARGET_SP_LDRK_MIN                 0
#define TARGET_SP_LDRK_MAX                 1023L

/* Thumb lacks LDRB/LDRH [sp,...] instructions, but MAX values still = 1023
 * as we will use ADD ip, sp, #N to address the object.
 */
#define TARGET_SP_LDRWK_MIN                0
#define TARGET_SP_LDRWK_MAX                1023L
#define TARGET_SP_LDRBK_MIN                0
#define TARGET_SP_LDRBK_MAX                1023L

#define TARGET_MAX_FRAMESIZE            (5*4)

/* help please on the 0-1 controversy */
#define R_A1            0L
#define R_F0           16L
#define R_V1            4L
#define NARGREGS        4L

#define NVARREGS        4L
#define MAXGLOBINTREG   8L
#define TARGET_HAS_BSS  1
#define CONST_DATA_IN_CODE 1

#define NINTREGS       16L  /* same as smallest fp reg, usually R_F0 */
/* ECN - Lie about no. of FLT regs to prevent pointless register spillage when
 * cg thinks its has no FP register available. See cg_expr1
 */
#define NFLTARGREGS     8L
#define NFLTVARREGS     8L
#define R_FV1           (R_F0+NFLTARGREGS)
#define MAXGLOBFLTREG   0L

#define R_P1            R_A1

/*
 * ALLOCATION_ORDER is pretty suspect - it defines an order for looking at
 * registers and is intended to interact well with the copy-avoidance code.
 * When the copy-avoidance code is better this may not be needed any more.
 * The following lines are a temporary admission of defeat
 */

/* We choose to use SL = 10, FP = 11, IP = 12, SP = 13 here (= APCS_R) so
   that SL and FP (sometimes var regs) are contiguous with the var regs.
 */

/*
 * IP is uses as scratch workspace in many places, and is not made available
 * to the general register allocator.  It must neverthless be preserved
 * across procedure calls for ARM inter-working to be possible. Ugh.
 */
#define ARM_R_IP            12L
#define R_IP                0x3L
/*
 * FR is used in the creation of stack frames. It may be the same as
 * IP but it may not be one of the arg registers, hence the separation.
 */
#define R_FR                0x7L

#define ALLOCATION_ORDER    {0,1,2,3,7,4,5,6,255}

#define R_SP                13L    /* stack pointer */
#define R_LR                14L    /* link addr in fn calls or work reg */
#define R_PSR               15L

#define TARGET_SPECIAL_ARG_REG R_V1

/* emphasise non-obvious defaults in mip/defaults.h */
#ifndef alignof_double
#  define alignof_double    4
#endif

#define MIN_ALIGNMENT_CONFIGURABLE

#ifndef COMPILING_ON_ARM
   extern char const *target_lib_name(ToolEnv *, char const *);
#  define target_lib_name_(x,e) target_lib_name(x,e)
#endif
#define target_asm_options_(x) ""

#ifndef TARGET_HAS_COFF
#  ifndef TARGET_HAS_AOUT
#    define TARGET_HAS_AOF 1
#  endif
#endif

#ifdef TARGET_HAS_AOF
#  define TARGET_HAS_ADCON_AREA 1
#  define TARGET_HAS_MULTIPLE_CODE_AREAS 1
#endif


#ifndef INTEGER_LOAD_MAX_DEFAULT
#  define INTEGER_LOAD_MAX_DEFAULT  2
#endif

#ifndef LDM_REGCOUNT_MAX_DEFAULT
#  define LDM_REGCOUNT_MAX_DEFAULT 16
#endif
#ifndef LDM_REGCOUNT_MIN_DEFAULT
#  define LDM_REGCOUNT_MIN_DEFAULT  3
#endif

#define TARGET_PREFIX(fname) "__16" fname

#ifdef TARGET_HAS_DEBUGGER
#  ifndef TARGET_HAS_DWARF
#    define TARGET_HAS_ASD
#  endif
#  ifdef TARGET_HAS_ASD
#    ifdef TARGET_HAS_DWARF
#      define TARGET_HAS_MULTIPLE_DEBUG_FORMATS
#    endif
#  endif
#  define DEBUGGER_NEEDS_NO_FRAMEPOINTER
#  define NEW_DBG_PROC_INTERFACE
#endif

#define TARGET_SUPPORTS_TOOLENVS

#define TOOLNAME armcc  /* So there's just one entrypoint name, viz armccinit */
#ifdef CPLUSPLUS
#  define TOOLFILENAME "tcpp"
#else
#  define TOOLFILENAME "tcc"
#endif

#define TARGET_HAS_INLINE_ASSEMBLER 1
#define THUMB_INLINE_ASSEMBLER 1

#endif

/* end of thumb/target.h */
