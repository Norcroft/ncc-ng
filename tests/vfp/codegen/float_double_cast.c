// RUN: %cc %s -S -o -

double widen_then_narrow(float x) {
    // CHECK: vcvt.f64.f32  d0, s0
    double y = (double)x;

    // CHECK: vcvt.f32.f64  s0, d0
    // CHECK: vmov.f32      s2, #112        @ =1.0 (0x3f800000)
    // CHECK: vadd.f32      s0, s0, s2

    // CHECK: vcvt.f64.f32  d0, s0
    // CHECK: mov           pc, lr
    return (float)y + 1.0f;
}

float narrow_then_widen(double x) {
    // CHECK: vcvt.f32.f64    s0, d0
    float y = (float)x;

    // CHECK: vcvt.f64.f32    d0, s0
    // CHECK: vmov.f64        d1, #112        @ =1.0 (0x3ff00000...0)
    // CHECK: vadd.f64        d0, d0, d1

    // CHECK: vcvt.f32.f64    s0, d0
    // CHECK: mov             pc, lr
    return (double)y + 1.0f;
}
