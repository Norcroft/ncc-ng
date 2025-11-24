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

/*
 * features
 */
enum Features {
#define FEATURE(x) Feature_ ## x,
#include "config_features.def"
#undef FEATURE
    Feature_MAX
};

#define FEATURE_WORD(f)  ((f) / 32)
#define FEATURE_MASK(f)  (1u << ((f) % 32))
extern uint32_t config_features[(Feature_MAX + 31) / 32];

// The idea here is that it's moving towards a C++ encapsulation.
static inline int Features_Has(enum Features f)
{
    return (config_features[FEATURE_WORD(f)] & FEATURE_MASK(f)) != 0;
}

extern void Features_Set(enum Features f);
extern void Features_Clear(enum Features f);
extern void Features_ClearOrSet(enum Features f, bool clear);
extern void Features_ClearAll(void);
extern void Features_Dump(void);

#define HasFeature(F) Features_Has(F)
#define SetFeature(F) Features_Set(F)
#define ClearFeature(F) Features_Clear(F)
#define ClearOrSetFeature(F, CLEAR) Features_ClearOrSet(F, CLEAR)

// Overloads
#define SetFeatures2(F, G) do { Features_Set(F); Features_Set(G); } while (0)
#define SetFeatures3(F, G, H) do { Features_Set(F); Features_Set(G); Features_Set(H); } while (0)
#define ClearFeatures2(F, G) do { Features_Clear(F); Features_Clear(G); } while (0)
#define ClearFeatures3(F, G, H) do { Features_Clear(F); Features_Clear(G); Features_Clear(H); } while (0)
