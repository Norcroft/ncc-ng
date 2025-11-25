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

#include "toolver.h"
#define NON_RELEASE_VSN TOOLVER_ARMCC

#ifdef FOR_ACORN

#define msg_driver_help  "\nUsage :         %s [options] file1 file2 ... fileN\n",\
"",\
"Keyword options:",\
"",\
"-help           Output this information",\
"-pcc            Compile UNIX PCC style C source code",\
"-fussy, -strict Be extra strict about enforcing conformance to standards",\
"-list           Create a listing file",\
"-via <file>     Read in extra command line arguments from <file>",\
"-errors <file>  Write error output to file",\
"-littleend, -li Compile code for little-endian memory",\
"-bigend, -be    Compile code for big-endian memory",\
"-apcs [3]<q*>   Specify variant of APCS in use, with one or more qualifiers",\
"-depend <file>  Write 'make' include file dependency information to <file>",\
"-throwback      Support error processing by Desktop Tools & other compliant tools",\
"-desktop <dir>  Set the work directory for the compiler as <dir>",\
"-C++            Alter cc to compile C++ in conjunction with C++ translator",\
"",\
"Preprocessor options:",\
"",\
"-I<directory>   Include <directory> on the #include search path",\
"-j<directory*>  Replace the default #include path with the path <directory*>",\
"-E              Preprocess the C source code only - do not compile or link it",\
"-C              Prevent the preprocessor from removing comments (use with -E)",\
"-M              Preprocess the C code, and output 'make' file dependency information",\
"-D<symbol>=<value>,",\
"-D<symbol>      Define <symbol> on entry to the compiler",\
"-U<symbol>      Undefine <symbol> on entry to the compiler",\
"",\
"Code generation options:",\
"",\
"-o<file>        Name the <file> that will hold the compilation's final output",\
"-g[<options>]   Generate code that may be used with the debugger",\
"-Ospace         Optimise for image size at the expense of execution time",\
"-Otime          Optimise for execution time at the expense of image size",\
"-p[<options>]   Generate code suitable for profiling",\
"-S              Output assembly code instead of object code",\
"-zM             Generate code suitable for building a RISC OS relocatable module",\
"",\
"Linker options:",\
"",\
"-c              Do not link the files being compiled",\
"-l<libs>        Specify a list of libraries to link with instead of the standard one",\
"",\
"Warning and error message options:",\
"",\
"-W<options>     Disable all or selected warning messages",\
"-e<options>     Disable all or selected error messages",\
"",\
"Additional feature options:",\
"",\
"-zp<alpha><num> Emulate #pragma directives, given in their short <alpha><num> form",\
"-zr<num>        Restrict size of LDMs and STMs to help control interrupt latency",\
"-f<features>    Enable a selection of compiler defined features"

#define PROFILE_COUNTS_INLINE 1
#define DISABLE_ERRORS 1
#define TARGET_IS_ACORN_RISC_OS 1
#define TARGET_WANTS_FUNCTION_NAMES 1

#endif

#define TARGET_ENDIANNESS_CONFIGURABLE
/* #define TARGET_DEFAULT_BIGENDIAN 1 */ /* 1 => bigendian default */
                                         /* 0 => littleendian default */
                                         /* unset => defaults to host */

#ifdef COMPILING_ON_UNIX
#  define HOST_WANTS_NO_BANNER 1

/* #define TARGET_HAS_DIVREM_FUNCTION 1 -- divide fn also returns remainder.*/
/* #define TARGET_HAS_DIV_10_FUNCTION 1 -- fast divide by 10                */
                                        /* but not under ARM Unix...        */
#endif

#define TARGET_SYSTEM     "RISC OS"
#define TARGET_IS_RISC_OS 1
#define TARGET_HAS_DIVREM_FUNCTION 1 /* divide fn also returns remainder.*/
#define TARGET_HAS_DIV_10_FUNCTION 1 /* fast divide by 10                */
                                     /* the last two would be in target.h*/
                                        /* but are OS-dependent too. */

/* #define DO_NOT_EXPLOIT_REGISTERS_PRESERVED_BY_CALLEE 1 */
/* #define MOVC_KILLS_REGISTER_PRESERVED_BY_CALLEE_EXPLOITATION 1 */

#ifndef DRIVER_OPTIONS
#  ifdef COMPILING_ON_ARM        /* -D__arm done by TARGET_PREDEFINES */
#    ifdef TARGET_IS_UNIX
#      define DRIVER_OPTIONS     {"-zps1", "-D__unix", "-D__acorn", NULL}
#    else /* not Unix, probably RISC_OS. */
#      define DRIVER_OPTIONS     {"-D__riscos", "-D__acorn", NULL}
#    endif
#  else /* not compiling_on_arm */
#    ifdef TARGET_IS_UNIX
#      define DRIVER_OPTIONS     {"-zps1", "-D__unix", NULL}
#    else /* not Unix */
#      define DRIVER_OPTIONS     { NULL }
#    endif
#  endif
#endif

#ifndef RELEASE_VSN
#  define ENABLE_ALL          1 /* -- to enable all debugging options */
#endif

#define TARGET_STACK_MOVES_ONCE
#define target_stack_moves_once (var_cc_private_flags & 32768L)

#define MSG_TOOL_NAME  "cc"

#define TARGET_HAS_ASD
#define TARGET_HAS_DWARF

#define RECORD_SOURCE_LOCATION 1
#define PRETTY_DISASSEMBLY 1

#endif

/* end of ccacorn/options.h */
