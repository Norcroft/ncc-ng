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

// The idea here is that it's moving towards a templated C++ encapsulation.
// config_features, config_suppress variables should be considered private,
// but an inline member will still give fast lookup (if that's actually needed?)

/*
 * features
 */
enum Feature {
#define FEATURE(x) Feature_ ## x,
#include "config_features.def"
#undef FEATURE
    Feature_MAX
};

#define CONFIG_WORD(f)  ((f) / 32)
#define CONFIG_MASK(f)  (1u << ((f) % 32))
extern uint32_t config_features[(Feature_MAX + 31) / 32];

static inline int FeaturesDB_Has(enum Feature f)
{
    return (config_features[CONFIG_WORD(f)] & CONFIG_MASK(f)) != 0;
}

extern void FeaturesDB_Set(enum Feature f);
extern void FeaturesDB_Clear(enum Feature f);
extern void FeaturesDB_ClearOrSet(enum Feature f, bool clear);
extern void FeaturesDB_ClearAll(void);
extern void FeaturesDB_Dump(void);

#define HasFeature(F) FeaturesDB_Has(F)
#define SetFeature(F) FeaturesDB_Set(F)
#define ClearFeature(F) FeaturesDB_Clear(F)
#define ClearOrSetFeature(F, CLEAR) FeaturesDB_ClearOrSet(F, CLEAR)

// Overloads
#define SetFeatures2(F, G) do { FeaturesDB_Set(F); FeaturesDB_Set(G); } while (0)
#define SetFeatures3(F, G, H) do { FeaturesDB_Set(F); FeaturesDB_Set(G); FeaturesDB_Set(H); } while (0)
#define ClearFeatures2(F, G) do { FeaturesDB_Clear(F); FeaturesDB_Clear(G); } while (0)
#define ClearFeatures3(F, G, H) do { FeaturesDB_Clear(F); FeaturesDB_Clear(G); FeaturesDB_Clear(H); } while (0)

/*
 * disable error/warnings...
 */
enum Suppress {
#define SUPPRESS(x) Suppress_ ## x,
#include "config_suppress.def"
#undef SUPPRESS
    Suppress_MAX
};

extern uint32_t config_suppress[(Suppress_MAX + 31) / 32];

extern void SuppressDB_InitDefaults(void);

static inline int SuppressDB_Has(enum Suppress w)
{
    return (config_suppress[CONFIG_WORD(w)] & CONFIG_MASK(w)) != 0;
}

extern void SuppressDB_Set(enum Suppress w);
extern void SuppressDB_Clear(enum Suppress w);
extern void SuppressDB_ClearOrSet(enum Suppress w, bool clear);
extern void SuppressDB_ClearAll(void);
extern void SuppressDB_Dump(void);
