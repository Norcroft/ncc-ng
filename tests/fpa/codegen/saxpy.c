// RUN: %cc %s -S -o -

void saxpy(float *x, float *y, int n, float a) {
    int i;

    // f0 = a
    // CHECK: mov             ip, sp
    // CHECK: stmdb           sp!, {r0-r3}
    // CHECK: stmdb           sp!, {fp-ip, lr-pc}
    // CHECK: sub             fp, ip, #20
    // CHECK: ldfd            f0, [fp, #&10]
    // CHECK: mvfs            f0, f0

    // i = 0, i < n
    // CHECK: mov             r3, #0
    // CHECK: cmp             r2, #0
    // CHECK: ldmdble         fp, {fp, sp, pc}

    // CHECK: |L000030.J4.saxpy|
    for (i = 0; i < n; ++i) {
        // f1 = x[i]
        // CHECK: add             ip, r0, r3, lsl #2
        // CHECK: ldfs            f1, [ip]

        // f1 = a * x[i]
        // CHECK: mufs            f1, f1, f0

        // f2 = y[i]
        // CHECK: add             ip, r1, r3, lsl #2
        // CHECK: ldfs            f2, [ip]

        // f1 = (a * x[i]) + y[i]
        // CHECK: adfs            f1, f1, f2

        // y[i] = f1
        // CHECK: stfs            f1, [ip]

        // ++i, i < n
        // CHECK: add             r3, r3, #1
        // CHECK: cmp             r3, r2
        // CHECK: blt             |L000030.J4.saxpy|
        y[i] = a * x[i] + y[i];
    }

    // CHECK: ldmdb           fp, {fp, sp, pc}
}
