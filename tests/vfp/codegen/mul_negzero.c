// RUN: %cc %s -S -o -

// RHS literal -0.0f comes from VMOV (from core) + VNEG, not an immediate.

// Newer VFPs support VEOR to D registers only. Should decide policy for S
// registers as our current register usage means we could blat the D register
// that overays the S reg.

// We pass x as an unknown value to force the constant path.
float f32_mul_negzero(float x) {
    // CHECK: eor       ip, ip, ip
    // CHECK: vmov      s2, ip
    // CHECK: vneg.f32  s2, s2
    // CHECK: vmul.f32  s0, s0, s2
    return x * (-0.0f);
}

float d64_mul_negzero(double x) {
    // CHECK: veor          d1, d1, d1
    // CHECK: vneg.f64      d1, d1
    // CHECK: vmul.f64      d0, d0, d1
    // CHECK: vcvt.f32.f64  s0, d0
    return x * (-0.0f);
}
