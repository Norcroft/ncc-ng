// RUN: %cc %s -S -o -

double widen_then_narrow(float x) {
    // f0 = x
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: mvfs      f0, f0
    double y = (double)x;

    // Pointlessly cast to float again
    // CHECK: mvfs      f0, f0

    // add 1 (as float)
    // CHECK: adfs      f0, f0, #&1     @ =1.0
    // CHECK: mov       pc, lr
    return (float)y + 1.0f;
}
