// RUN: %cc %s -S -o -

float f32_mul_negzero(float x) {
    // f0 = x
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: mvfs      f0, f0

    // f1 = -0
    // CHECK: mnfs      f1, #&0         @ =0.0

    // multiple and return
    // CHECK: mufs      f0, f0, f1
    // CHECK: mov       pc, lr
    return x * (-0.0f);
}

float d64_mul_negzero(double x) {
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: mnfd      f1, #&0         @ =0.0
    // CHECK: mufd      f0, f0, f1
    // CHECK: mvfs      f0, f0
    // CHECK: mov       pc, lr
    return x * (-0.0f);
}
