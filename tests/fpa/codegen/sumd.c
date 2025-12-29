// RUN: %cc %s -S -o -

double sumd(double *p, int n)
{
    // CHECK: mvfd            f0, #&0         @ =0.0
    double s = 0.0;
    int i;

    // i = 0
    // CHECK: mov             r2, #0
    // CHECK: cmp             r1, #0
    // CHECK: movle           pc, lr

    // CHECK: |L000010.J4.sumd|
    for (i = 0; i < n; ++i) {
        // CHECK: add             r3, r0, r2, lsl #3
        // CHECK: ldfd            f1, [r3]
        // CHECK: adfd            f0, f1, f0
        s += p[i];

        // ++1, i < n
        // CHECK: add             r2, r2, #1
        // CHECK: cmp             r2, r1
        // CHECK: blt             |L000010.J4.sumd|
    }

    // CHECK: mov             pc, lr
    return s;
}
