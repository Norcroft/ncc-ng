// RUN: %cc %s -S -o -

double neg_abs_mix(float a, double b) {
    // f1 = -a
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f1, [sp], #&8
    // CHECK: stmdb     sp!, {r2-r3}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: mvfs      f1, f1
    // CHECK: mnfs      f1, f1
    float n = -a;

    // CHECK: cmfe      f0, #&0         @ =0.0
    // CHECK: mnfltd    f0, f0
    double ab = b < 0 ? -b : b;

    // CHECK: adfd      f0, f1, f0
    // CHECK: mov       pc, lr
    return (double)n + ab;
}
