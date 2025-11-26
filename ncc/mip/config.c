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

#include "ncc-types.h"
#include "globals.h"
#include "errors.h"

#include <stdio.h>

uint32_t config_features[(Feature_MAX + 31) / 32];
uint32_t config_suppress[(Suppress_MAX + 31) / 32];

static const char *feature_names[] = {
#define FEATURE(x) #x,
#include "config_features.def"
#undef FEATURE
};

static const char *suppress_names[] = {
#define SUPPRESS(x) #x,
#include "config_suppress.def"
#undef SUPPRESS
};

// FeaturesDB -----
void FeaturesDB_Clear(enum Feature f)
{
    if (f >= Feature_MAX) syserr("FeaturesDB: Index out of bounds.");

    config_features[CONFIG_WORD(f)] &= ~CONFIG_MASK(f);
}

void FeaturesDB_Set(enum Feature f)
{
    if (f >= Feature_MAX) syserr("FeaturesDB: Index out of bounds.");

#ifdef PASCAL /*ECN*/
    if (f == Feature_Predeclare ||
        f == Feature_WarnOldFns ||
        f == Feature_SysIncludeListing ||
        f == Feature_WRStrLits ||
        f == Feature_PCC ||
        f == Feature_Anomoly ||
        f == Feature_TellPtrInt ||
        f == Feature_6CharMonocase)
        return;
#endif
    config_features[CONFIG_WORD(f)] |= CONFIG_MASK(f);
}

void FeaturesDB_ClearOrSet(enum Feature f, bool clear)
{
    if (clear)
        FeaturesDB_Clear(f);
    else
        FeaturesDB_Set(f);
}

void FeaturesDB_ClearAll(void)
{
    size_t n = sizeof(config_features) / sizeof(config_features[0]);
    size_t i;
    for (i = 0; i < n; i++)
        config_features[i] = 0;
}

void FeaturesDB_Dump(void)
{
    unsigned n = sizeof(config_features) / sizeof(config_features[0]);
    unsigned i, bit;

    printf("Enabled features:\n");

    for (i = 0; i < n; ++i) {
        uint32_t mask = config_features[i];
        if (!mask) continue;

        for (bit = 0; bit < 32; ++bit) {
            if (mask & (1u << bit)) {
                enum Feature f = (enum Feature)(i * 32 + bit);
                if (f < Feature_MAX)
                    printf("  %u (%s)\n", f, feature_names[f]);
            }
        }
    }
}

// SuppressDB ----------
void SuppressDB_Clear(enum Suppress w)
{
    if (w >= Suppress_MAX) syserr("SuppressDB: Index out of bounds.");

    config_suppress[CONFIG_WORD(w)] &= ~CONFIG_MASK(w);
}

void SuppressDB_Set(enum Suppress w)
{
    if (w >= Suppress_MAX) syserr("SuppressDB: Index out of bounds.");

    config_suppress[CONFIG_WORD(w)] |= CONFIG_MASK(w);
}

void SuppressDB_ClearOrSet(enum Suppress w, bool clear)
{
    if (clear)
        SuppressDB_Clear(w);
    else
        SuppressDB_Set(w);
}

void SuppressDB_ClearAll(void)
{
    unsigned n = sizeof(config_suppress) / sizeof(config_suppress[0]);
    unsigned i;
    for (i = 0; i < n; i++)
        config_suppress[i] = 0;
}

void SuppressDB_InitDefaults(void)
{
    SuppressDB_ClearAll();

#define X(s)  SuppressDB_Set(Suppress_ ## s);
    SUPPRESS_DEFAULT_LIST
#undef X
}

void SuppressDB_Dump(void)
{
    size_t n = sizeof(config_suppress) / sizeof(config_suppress[0]);
    size_t i, bit;

    printf("Enabled suppressions:\n");

    for (i = 0; i < n; ++i) {
        uint32_t mask = config_suppress[i];
        if (!mask) continue;

        for (bit = 0; bit < 32; ++bit) {
            if (mask & (1u << bit)) {
                enum Suppress w = (enum Suppress)(i * 32 + bit);
                if (w < Suppress_MAX)
                    printf("  %u (%s)\n", w, suppress_names[w]);
            }
        }
    }
}
