// RUN: %cc %s -S -o -

// These currently compile to use VCMP, not VCMPZ. I need to investigate the
// peephole code!
int is_zero_f(float x) {
    // CHECK: vcmp.f32
    // CHECK: vmrs
    // CHECK: moveq
    return x == 0.0f;
}

int is_neg_zero_f(float x) {
    // CHECK: vcmp.f32
    // CHECK: vmrs
    // CHECK: moveq
    return x == -0.0f;
}

int is_zero_d(double x) {
    // CHECK: vcmp.f64
    // CHECK: vmrs
    // CHECK: moveq
    return x == 0.0f;
}

int is_neg_zero_d(double x) {
    // CHECK: vcmp.f64
    // CHECK: vmrs
    // CHECK: moveq
    return x == -0.0f;
}
