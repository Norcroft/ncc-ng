// RUN: %cc %s -S -o -

int to_int_f(float x) {
    // CHECK: vcvt.s32.f32
    // CHECK: vmov
    return (int)x;
}
