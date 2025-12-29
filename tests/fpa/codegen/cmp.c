// RUN: %cc %s -S -o -

int is_equal(float x, int y) {
    // Put 'x' in f0
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: mvfs      f0, f0

    // Widen 'y' to float.
    // CHECK: flts      f1, r2

    // Compare and return 0/1
    // CHECK: cmf       f0, f1
    // CHECK: movne     r0, #0
    // CHECK: moveq     r0, #1
    // CHECK: mov       pc, lr
    return x == y;
}

// No unsigned jopcode yet so does ugly 'bias' trick (eor onwards)
int is_equal2(float x, unsigned int y) {
    // Put 'x' in f0 (from widened float on r0-r1)
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: mvfs      f0, f0

    // negate 'y' and put in f1.
    // CHECK: eor       r0, r2, #2147483648
    // CHECK: fltd      f1, r0

    // f2 = 2^31, f1 = (unsigned)y
    // CHECK: ldfd      f2, [pc, #L000050-.-8]
    // CHECK: adfd      f1, f1, f2

    // f1 = single(f1)
    // CHECK: mvfs      f1, f1

    // compare
    // CHECK: cmf       f0, f1
    // CHECK: movne     r0, #0
    // CHECK: moveq     r0, #1
    // CHECK: mov       pc, lr
    return x == y;
    // CHECK: L000050
    // CHECK: DCFD     2147483648.0
}
