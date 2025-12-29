// RUN: %cc %s -S -o -

double neg_abs_mix(float a, double b) {
    // CHECK: vneg.f32
    float n = -a;      // vneg.f32

    // CHECK: vcmp.f64
    double ab = b < 0 ? -b : b; // peepholer could optimise to vabs.f64 !

    // CHECK: vneglt.f64
    return (double)n + ab;
}
