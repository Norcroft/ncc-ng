// RUN: %cc %s -S -o -

int is_y1(float x, int y) {
    // CHECK: vmov    s2, r0
    // CHECK: vcvt.f32.s32 s2, s2
    // CHECK: vcmp.f32     s0, s2
    // CHECK: vmrs     APSR_nzcv, fpscr
    // CHECK: moveq
    // CHECK: mov    pc, lr
    return x == y;
}

// No unsigned jopcode yet so does ugly 'bias' trick (eor onwards)
int is_y2(float x, unsigned int y) {
    // CHECK: eor     r0, r0,
    // CHECK: vmov
    // CHECK: vcvt.f64.s32
    // CHECK: vldr    d
    // CHECK: vadd.f64
    // CHECK: vcvt.f32.f64
    // CHECK: vcmp.f32
    // CHECK: vmrs
    // CHECK: moveq
    return x == y;
}
