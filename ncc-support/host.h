/* Copyright 2025 Piers Wombwell
 *
 * Licensed under the Apache License, Version 2.0 (the "License");
 * you may not use this file except in compliance with the License.
 * You may obtain a copy of the License at
 *
 *     http://www.apache.org/licenses/LICENSE-2.0
 *
 * Unless required by applicable law or agreed to in writing, software
 * distributed under the License is distributed on an "AS IS" BASIS,
 * WITHOUT WARRANTIES OR CONDITIONS OF ANY KIND, either express or implied.
 * See the License for the specific language governing permissions and
 * limitations under the License.
 */

#pragma once
#define _host_LOADED

#include <stdio.h>

#include "ncc-types.h"

#ifndef COMPILING_ON_RISC_OS
  #define COMPILING_ON_UNIX 1
#endif

#define TARGET_HAS_DEBUGGER 1
#define TARGET_HAS_AOF 1

#define TARGET_HAS_DIVREM_FUNCTION 1
#define TARGET_HAS_DIV_10_FUNCTION 1

#define FALSE 0
#define TRUE 1
#define NO 0
#define YES 1

#define BELL 7

#define IGNORE(x) ((void)(x))

#define my_EOF    (-1)

#define safe_tolower(c) ((c) == my_EOF ? my_EOF : tolower((unsigned char)(c)))
#define safe_toupper(c) ((c) == my_EOF ? my_EOF : toupper((unsigned char)(c)))

/* Ensure no macro remaps ‘sprintf’ before misc.c’s static version */
#ifndef _sprintf
#define _sprintf sprintf
#endif

#define EXIT_error 1
#define EXIT_fatal 2
#define EXIT_syserr 3
#define EXIT_warn 0
