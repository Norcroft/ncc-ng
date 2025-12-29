// RUN: %cc %s -S -o -

double muld(double a, double b) {
    // CHECK: stmdb           sp!, {r0-r3}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: ldfd            f1, [sp], #&8
    // CHECK: mufd            f0, f0, f1
    // CHECK: mov             pc, lr
    return a * b;
}
