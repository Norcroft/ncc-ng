// RUN: %cc %s -S -o -

float to_float_i(int x) {
    // CHECK: flts  f0, r0
    // CHECK: mov   pc, lr
    return (float)x;
}
