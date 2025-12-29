// RUN: %cc %s -S -o -

// Layout with S-slots:
//  a: float  -> s0
//  b: double -> (align to even) d1 (s2/s3)
//  c: float  -> s4
//  d: double -> d2 (s4 was taken by c, so next even is s6 -> d3 if you add more)
// Keep the expression straightforward to force direct use of argument regs.
double mix4(float a, double b, float c, double d) {
    // CHECK: vadd.f64 d
    double bd = b + d;          // expect vadd.f64 probably using d1 & d3

    // CHECK: vadd.f32 s
    float  ac = a + c;          // expect vadd.f32 probably using s0 & s4

    // CHECK: vcvt.f32.f64
    // CHECK: vadd.f32
    // CHECK: vcvt.f64.f32
    // CHECK: mov    pc, lr
    return ac + (float)bd;      // expect a f64->f32, add, then f32->f64
}
