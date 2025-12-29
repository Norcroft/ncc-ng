// RUN: %cc %s -S -o -

// These tests have been checked for correctness against a hybrid of the FPA
// hardfp APCS and the VFP hardfp AAPCS.
//
// There are two main problems with supporting the proper VFP hardfp AAPCS:
// - No support for overlaying D registers on two S registers. Therefore, only
//   even-numbered S registers are used (ie. D register number * 2).
// - Can't currently have runtime configuration for number of FP registers.
//   Given FPA is clearly more useful, that makes VFP have to follow the FPA
//   register saving standard, which is very different.

// ---------- Test 1: argument order (float, double, float)
// Expected VFP arg placement: a:s0, b:d1 (s2,s3), c:s4
float t_arg_fdf(float a, double b, float c) {
    // CHECK: vcvt.f32.f64    s2, d1
    // CHECK: vadd.f32    s0, s0, s2
    // CHECK: vadd.f32    s0, s0, s4
    // CHECK: mov    pc, lr
    return a + (float)b + c;
}

void call_t_arg_fdf() {
    // CHECK: vmov.f32    s4, #28    @ =7.0
    // CHECK: vmov.f64    d1, #24    @ =6.0
    // CHECK: vmov.f32    s0, #20    @ =5.0
    // CHECK: b
    t_arg_fdf(5.0, 6.0, 7.0);
}

// ---------- Test 2: argument order (float, float, double)
// Expected: a:s0, b:s1, c:d1 (s2,s3)
// Actual:   a:s0 (d0), b:s2 (d1), c:d2
double t_arg_ffd(float a, float b, double c) {
    // No concept of odd-numbered S registers, so this can't match AAPCS.
    // CHECK: vcvt.f64.f32    d0, s0
    // CHECK: vcvt.f64.f32    d1, s2
    // CHECK: vadd.f64    d0, d0, d1
    // CHECK: vadd.f64    d0, d0, d2
    // CHECK: mov    pc, lr
    return (double)a + (double)b + c;
}

// ---------- Test 3: boundary fill (five doubles)
// Expected: a..e consume d0..d4
double t_arg_5d(double a, double b, double c, double d, double e) {
    // CHECK: vadd.f64    d0, d0, d1
    // CHECK: vadd.f64    d0, d0, d2
    // CHECK: vadd.f64    d0, d0, d3
    // CHECK: vadd.f64    d0, d0, d4
    // CHECK: mov    pc, lr
    return a + b + c + d + e;
}

// ---------- Test 4: mixed with alignment bump
// Expected: f0:s0, f1:s1, f2:s2, d0:d2 (aligned at s4), f3:s6
// Actual: f0:s0 (d0), f1:s2 (d1), f2:s4 (d2), d0:d3, f3:s8 (d4)
double t_arg_mixed(float f0, float f1, float f2, double d0, float f3) {
    // CHECK: vcvt.f64.f32    d0, s0
    // CHECK: vcvt.f64.f32    d1, s2
    // CHECK: vadd.f64    d0, d0, d1
    // CHECK: vcvt.f64.f32    d2, s4
    // CHECK: vadd.f64    d0, d0, d2
    // CHECK: vadd.f64    d0, d0, d3
    // CHECK: vcvt.f64.f32    d4, s8
    // CHECK: vadd.f64    d0, d0, d4
    // CHECK: mov    pc, lr
    return (double)f0 + (double)f1 + (double)f2 + d0 + (double)f3;
}

// ---------- Test 5: float return in s0 (low half of d0)
// Expected: a:s0, b:s1
// Actual: a:s0 (d0), b:s2 (d1)
float t_ret_fadd(float a, float b) {
    // CHECK: vadd.f32    s0, s0, s2
    // CHECK: mov    pc, lr
    return a + b;
}

// ---------- Test 6: double return in d0
// Expected: a:d0, b:d1
double t_ret_dadd(double a, double b) {
    // CHECK: vadd.f64    d0, d0, d1
    // CHECK: mov    pc, lr
    return a + b;
}

// ---------- Test 7: float:int (truncate toward zero)
// C cast truncates toward zero; codegen should prefer VCVT.S32.F32.
int t_cvt_trunc_f2i(float x) {
    // CHECK: vcvt.s32.f32    s30, s0
    // CHECK: vmov    r0, s30
    // CHECK: mov    pc, lr
    return (int)x;
}

// ---------- Test 8: double:int (truncate toward zero)
// C cast truncates toward zero; codegen should prefer VCVT.S32.F64.
int t_cvt_trunc_d2i(double x) {
    // CHECK: vcvt.s32.f64    s30, d0
    // CHECK: vmov    r0, s30
    // CHECK: mov    pc, lr
    return (int)x;
}

// ---------- Test 9: float:int (floor towards −∞)
float floorf(float); /* declare to avoid pulling headers */
int t_cvt_floor_f2i(float x) {
    // CHECK: bl
    // CHECK: vcvt.s32.f32    s30, s0
    // CHECK: vmov    r0, s30
    // CHECK: ldmdb    fp, {fp, sp, pc}
    return (int)floorf(x);
}

// ---------- Test 10: double:float conversion (narrow) */
float t_cvt_d2f(double x) {
    // CHECK: vcvt.f32.f64    s0, d0
    // CHECK: mov    pc, lr
    return (float)x;
}

// ---------- Test 11: float:double conversion (widen) */
double t_cvt_f2d(float x) {
    // CHECK: vcvt.f64.f32    d0, s0
    // CHECK: mov    pc, lr
    return (double)x;
}

// ---------- Test 12: simple FP loop to exercise register pressure
float t_loop_fma_sum(const float *p, int n) {
    // CHECK: eor    ip, ip, ip
    // CHECK: vmov    s0, ip
    float acc = 0.0f;
    int i;

    // n:r1, i:r2
    // CHECK: mov    r2, #0
    // CHECK: cmp    r1, #0
    // CHECK: movle    pc, lr
    for (i = 0; i < n; ++i) {
        // CHECK: vmov.f32    s2, #120    @ =1.5
        // CHECK: add    r3, r0, r2, lsl #2
        // CHECK: vldr    s4, [r3]
        // CHECK: vmul.f32    s4, s4, s2
        // CHECK: vadd.f32    s0, s4, s0
        acc = acc + p[i] * 1.5f;

        // CHECK: add    r2, r2, #1
        // CHECK: cmp    r2, r1
        // CHECK: blt
    }

    // CHECK: mov    pc, lr
    return acc;
}

// ---------- Test 13: variadic call (should fall back to core regs/stack)
int printf(const char *, ...);
int t_varargs(float a, double b) {
    // a -> double
    // CHECK: vpush    {d16-d15}
    // CHECK: vcvt.f64.f32    d0, s0

    // adr d0, "%f %f\n"
    // CHECK: add    r0, pc, #2, 30

    // r2, r3 = d0 (=a). Correctly aligned for vfp AAPCS. r1 unused.
    // CHECK: vmov    r2, r3, d0
    // CHECK: bl    
    // CHECK: ldmdb    fp, {fp, sp, pc}
    return printf("%f %f\n", (double)a, b);
}

// ---------- Test 14: pass/return aliases sanity
// Attempts to forces use of both s and d views of the same storage.
// Fails with our implementation
double t_alias_mix(float a, double b, float c) {
    // CHECK: vcvt.f64.f32    d0, s0
    // CHECK: vadd.f64    d0, d0, d1
    double x = (double)a + b;

    // CHECK: vcvt.f32.f64    s0, d0
    // CHECK: vadd.f32    s0, s0, s4
    float  y = (float)x + c;

    // CHECK: vcvt.f64.f32    d0, s0
    // CHECK: vadd.f64    d0, d0, d1
    // CHECK: mov    pc, lr
    return (double)y + b;
}

// ---------- Test 15: many floats to cross d-boundaries
// Expect greedy single allocation across s0..s7
float t_many_f(float a, float b, float c, float d,
               float e, float f, float g, float h/*,
               float i, float j, float k, float l,
               float m, float n, float o, float p,
               float q, float r, float s, float t*/) {
    // CHECK: vadd.f32    s0, s0, s2
    // CHECK: vadd.f32    s0, s0, s4
    // CHECK: vadd.f32    s0, s0, s6
    // CHECK: vadd.f32    s0, s0, s8
    // CHECK: vadd.f32    s0, s0, s10
    // CHECK: vadd.f32    s0, s0, s12
    // CHECK: vadd.f32    s0, s0, s14
    // CHECK: vadd.f32    s0, s0, s16
    // CHECK: vadd.f32    s0, s0, s18
    // CHECK: mov    pc, lr
    return a + b + c + d + e + f + g + h /*+
           i + j + k + l + m + n + o + p +
           q + r + s + t*/;
}

// ---------- Test 15: many floats to cross d-boundaries
// Expect greedy single allocation across s0..s7
float t_most_f(float a, float b, float c, float d,
               float e, float f, float g, float h,
               float i, float j, float k, float l,
               float m, float n, float o, float p,
               float q, float r, float s, float t) {
    // CHECK: vadd.f32    s0, s0, s2
    // CHECK: vadd.f32    s0, s0, s4
    // CHECK: vadd.f32    s0, s0, s6
    // CHECK: vadd.f32    s0, s0, s8
    // CHECK: vadd.f32    s0, s0, s10
    // CHECK: vadd.f32    s0, s0, s12
    // CHECK: vadd.f32    s0, s0, s14
    // CHECK: vadd.f32    s0, s0, s16
    // CHECK: vadd.f32    s0, s0, s18
    // CHECK: mov    pc, lr
    return a + b + c + d + e + f + g + h +
           i + j + k + l + m + n + o + p +
           q + r + s + t;
}
