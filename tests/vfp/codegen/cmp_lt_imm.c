// RUN: %cc %s -S -o -

int is_lt_imm_float1(float x) {
    // 3e4ccccd = 0.2 in single precision.
    // CHECK: vldr    s2, [pc
    // CHECK: vcmp.f32     s0, s2
    // CHECK: vmrs     APSR_nzcv, fpscr
    // CHECK: movlt
    // CHECK: mov    pc, lr
    return x < 0.2f;
    // check literal
    // CHECK: 3e4ccccd
}

int is_lt_imm_double2(float x) {
    // CHECK: vcvt.f64.f32 d0, s0
    // CHECK: vcmp.f64     d0, d1
    // CHECK: vmrs     APSR_nzcv, fpscr
    // CHECK: movlt
    // CHECK: mov    pc, lr
    return x < 0.2; // upcasts 'x' to double.
    // CHECK: 9999999a
    // CHECK: 3fc99999
}
