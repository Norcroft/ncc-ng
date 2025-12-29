// RUN: %cc %s -S -o -

int is_lt_y1(float x, int y) {
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: mvfs      f0, f0

    // CHECK: flts      f1, r2

    // CHECK: cmfe      f0, f1
    // CHECK: movge     r0, #0
    // CHECK: movlt     r0, #1
    // CHECK: mov       pc, lr
    return x < y;
}

// No unsigned jopcode yet so does ugly 'bias' trick (eor onwards)
int is_lt_y2(float x, unsigned int y) {
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: mvfs      f0, f0
    // CHECK: eor       r0, r2, #2147483648
    // CHECK: fltd      f1, r0
    // CHECK: ldfd      f2, [pc, #L000050-.-8]
    // CHECK: adfd      f1, f1, f2
    // CHECK: mvfs      f1, f1
    // CHECK: cmfe      f0, f1
    // CHECK: movge     r0, #0
    // CHECK: movlt     r0, #1
    // CHECK: mov       pc, lr
    return x < y;
}
