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

// AMP as in SA1500/SA1501. Intel canned that yonks ago, so I can't even
// be bothered to see if the FP instruction set was documented.

typedef enum { AMP_DisassCP } disass_addcopro_type;

extern void disass_addcopro(disass_addcopro_type copro);
