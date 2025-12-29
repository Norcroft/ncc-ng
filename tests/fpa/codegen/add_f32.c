// RUN: %cc %s -S -o -

double addf(float a, float b) {
    // mov 'a' from int r0-r1 to f1
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f1, [sp], #&8

    // mov 'b' from int r2-r3 to f0
    // CHECK: stmdb     sp!, {r2-r3}
    // CHECK: ldfd      f0, [sp], #&8

    // narrow f0 and f1 (no rounding needed as were floats before APCS widened)
    // CHECK: mvfs      f1, f1
    // CHECK: mvfs      f0, f0

    // add, result in f0 which is returned.
    // CHECK: adfs      f0, f1, f0
    return a + b;
    // CHECK: mov       pc, lr
}
