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

// Norcroft has two different demanglers:
//   unmangle*() - used by Norcroft C++ (if (LanguageIsCPlusPlus)).
//   demangle()  - used when compiling C, as output from CFront.
//
// demangle is in dem.h (CFront name demangling)

#include <stddef.h>

extern const char* unmangle_class(const char* name, char *buf, size_t size);
extern const char* unmangle2(const char* name, char *buf, size_t size);
extern const char* unmangle_with_class(const char* name,
                                       const char* class_name,
                                       size_t class_len,
                                       char *buf,
                                       size_t size);
