// RUN: %cc %s -S -o -

float to_float_i(int x) {
    // CHECK: vmov
    // CHECK: vcvt.f32.s32
    return (float)x;
}
