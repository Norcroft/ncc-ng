// RUN: %cc %s -S -o -

int is_gt_pi(double x) {
    // f1 = x
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f1, [sp], #&8

    // f0 = pi
    // CHECK: ldfd      f0, [pc, #L00001c-.-8]

    // compare & return
    // CHECK: cmfe      f1, f0
    // CHECK: movle     r0, #0
    // CHECK: movgt     r0, #1
    // CHECK: mov       pc, lr

    const double pi = 3.141592653589793238462643383279502884;
    return x > pi;

    // CHECK: L00001c
    // CHECK: DCFD     3.141592653589793238462643383279502884
}
