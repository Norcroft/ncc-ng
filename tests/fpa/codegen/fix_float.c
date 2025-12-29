// RUN: %cc %s -S -o -

int to_int_f(float x) {
    // f0 = x
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: mvfs      f0, f0

    // CHECK: fixsz     r0, f0
    // CHECK: mov       pc, lr
    return (int)x;
}
