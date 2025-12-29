// RUN: %cc %s -S -o -

float sumf(float *p, int n) {
    float s = 0.0f;
    int i;

    // CHECK: vldr
    // CHECK: vadd.f32
    for (i = 0; i < n; ++i) {
        s += p[i];
    }

    return s;
}
