// RUN: %cc %s -S -o -

double mix4(float a, double b, float c, double d) {
    // f0 = a, f3 = b, f1 = c, f2 = d
    // CHECK: stmdb     sp!, {r0-r3}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: ldfd      f3, [sp], #&8
    // CHECK: ldfd      f1, [sp]
    // CHECK: ldfd      f2, [sp, #&8]

    // f0, f1 are floats (a & c)
    // CHECK: mvfs      f0, f0
    // CHECK: mvfs      f1, f1

    // f2 = b + d
    // CHECK: adfd      f2, f3, f2

    // f0 = a + c
    // CHECK: adfs      f0, f0, f1

    // f1 = float(f2)
    // CHECK: mvfs      f1, f2

    double bd = b + d;

    float  ac = a + c;

    // return a+c + b+d
    // CHECK: adfs      f0, f0, f1
    // CHECK: mov       pc, lr
    return ac + (float)bd;
}
