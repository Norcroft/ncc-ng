// RUN: %cc %s -S -o -

int is_lt_imm_float(float x) {
    // load f0 from r0-r1 as float
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: mvfs      f0, f0

    // f1 = 0.2 (float)
    // CHECK: ldfs      f1, [pc, #L000020-.-8]

    // compare, return
    // CHECK: cmfe      f0, f1
    // CHECK: movge     r0, #0
    // CHECK: movlt     r0, #1
    // CHECK: mov       pc, lr
    return x < 0.2f;
    // check literal
    // CHECK: DCFS     0.2
}

int is_lt_imm_double(float x) {
    // load f0 from r0-r1 as float
    // CHECK: stmdb    sp!, {r0-r1}
    // CHECK: ldfd     f0, [sp], #&8
    // CHECK: mvfs     f0, f0

    // f1 = 0.2 (double)
    // CHECK: ldfd     f1, [pc, #L000044-.-8]

    // CHECK: cmfe     f0, f1
    // CHECK: movge    r0, #0
    // CHECK: movlt    r0, #1
    // CHECK: mov      pc, lr
    return x < 0.2; // upcasts 'x' to double.
    // CHECK: DCFD     0.2
}
