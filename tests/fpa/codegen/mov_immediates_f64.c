// RUN: %cc %s -S -o -

double add_lit(double x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: ldfd            f1, [pc, #L000014-.-8]
    // CHECK: adfd            f0, f0, f1
    // CHECK: mov             pc, lr
    return x + 2.5f;
}
// CHECK: L000014
// CHECK: DCFD     2.5

double f64_ret_p05(double x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: adfd            f0, f0, #&6     @ =0.5
    // CHECK: mov             pc, lr
    return x + 0.5f;
}

double f64_ret_p10(double x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: adfd            f0, f0, #&1     @ =1.0
    // CHECK: mov             pc, lr
    return x + 1.0f;
}

double f64_ret_p1125(double x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: ldfd            f1, [pc, #L000050-.-8]
    // CHECK: adfd            f0, f0, f1
    // CHECK: mov             pc, lr
    return x + 1.125f;
}
// CHECK: L000050
// CHECK: DCFD     1.125

double f64_ret_p15(double x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: ldfd            f1, [pc, #L00006c-.-8]
    // CHECK: adfd            f0, f0, f1
    // CHECK: mov             pc, lr
    return x + 1.5f;
}
// CHECK: L00006c
// CHECK: DCFD     1.5

double f64_ret_p25(double x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: ldfd            f1, [pc, #L000014-.-8]
    // CHECK: adfd            f0, f0, f1
    // CHECK: mov             pc, lr
    return x + 2.5f;
}

double f64_ret_p30(double x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: adfd            f0, f0, #&3     @ =3.0
    // CHECK: mov             pc, lr
    return x + 3.0f;
}

double f64_ret_p40(double x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: adfd            f0, f0, #&4     @ =4.0
    // CHECK: mov             pc, lr
    return x + 4.0f;
}

double f64_ret_n05(double x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: sufd            f0, f0, #&6     @ =0.5
    // CHECK: mov             pc, lr
    return x + -0.5f;
}

double f64_ret_n25(double x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: ldfd            f1, [pc, #L0000cc-.-8]
    // CHECK: adfd            f0, f0, f1
    // CHECK: mov             pc, lr
    return x + -2.5f;
}
// CHECK: L0000cc
// CHECK: DCD      0xc0040000, 0x00000000
