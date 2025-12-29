// RUN: %cc %s -S -o -

int is_zero_f(float x) {
    // f0 = x
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: mvfs      f0, f0

    // compare & return
    // CHECK: cmf       f0, #&0
    // CHECK: movne     r0, #0
    // CHECK: moveq     r0, #1
    // CHECK: mov       pc, lr
    return x == 0.0f;
}

int is_neg_zero_f(float x) {
    // f0 = x
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: mvfs      f0, f0

    // f1 = -0
    // CHECK: mnfs      f1, #&0         @ =0.0

    // compare & return
    // CHECK: cmf       f0, f1
    // CHECK: movne     r0, #0
    // CHECK: moveq     r0, #1
    // CHECK: mov       pc, lr
    return x == -0.0f;
}

int is_zero_d(double x) {
    // f0 = x
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f0, [sp], #&8

    // compare & return
    // CHECK: cmf       f0, #&0
    // CHECK: movne     r0, #0
    // CHECK: moveq     r0, #1
    // CHECK: mov       pc, lr
    return x == 0.0f;
}

int is_neg_zero_d(double x) {
    // f0 = x
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f0, [sp], #&8

    // f1 = -0
    // CHECK: mnfd      f1, #&0         @ =0.0

    // compare & return
    // CHECK: cmf       f0, f1
    // CHECK: movne     r0, #0
    // CHECK: moveq     r0, #1
    // CHECK: mov       pc, lr
    return x == -0.0f;
}
