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
#include "config.h"

#include <stdio.h>

uint32_t config_features[(Feature_MAX + 31) / 32];

static const char *feature_names[] = {
#define FEATURE(x) #x,
#include "config_features.def"
#undef FEATURE
};

void Features_Clear(enum Features f)
{
    config_features[FEATURE_WORD(f)] &= ~FEATURE_MASK(f);
}

void Features_Set(enum Features f)
{
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
    config_features[FEATURE_WORD(f)] |= FEATURE_MASK(f);
}

void Features_ClearOrSet(enum Features f, bool clear)
{
    if (clear)
        Features_Clear(f);
    else
        Features_Set(f);
}

void Features_ClearAll(void)
{
    unsigned n = sizeof(config_features) / sizeof(config_features[0]);
    int i;
    for (i = 0; i < n; i++)
        config_features[i] = 0;
}

const char *FeatureName(enum Features f)
{
    if (f >= 0 && f < Feature_MAX)
        return feature_names[f];
    return "<invalid>";
}

void Features_Dump(void)
{
    unsigned n = sizeof(config_features) / sizeof(config_features[0]);
    unsigned i, bit;

    printf("Enabled features:\n");

    for (i = 0; i < n; ++i) {
        uint32_t w = config_features[i];
        if (!w) continue;

        for (bit = 0; bit < 32; ++bit) {
            if (w & (1u << bit)) {
                enum Features f = (enum Features)(i * 32 + bit);
                if (f < Feature_MAX)
                    printf("  %u (%s)\n", f, FeatureName(f));
            }
        }
    }
}
