// RUN: %cc %s -S -o -

float add_lit(float x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f0, f0
    // CHECK: ldfs            f1, [pc, #L000018-.-8]
    // CHECK: adfs            f0, f0, f1
    // CHECK: mov             pc, lr
    return x + 2.5f;
}
// CHECK: L000018
// CHECK: DCFS     2.5

float f32_ret_p05(float x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f0, f0
    // CHECK: adfs            f0, f0, #&6     @ =0.5
    // CHECK: mov             pc, lr
    return x + 0.5f;
}

float f32_ret_p10(float x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f0, f0
    // CHECK: adfs            f0, f0, #&1     @ =1.0
    // CHECK: mov             pc, lr
    return x + 1.0f;
}

float f32_ret_p1125(float x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f0, f0
    // CHECK: ldfs            f1, [pc, #L00005c-.-8]
    // CHECK: adfs            f0, f0, f1
    // CHECK: mov             pc, lr
    return x + 1.125f;
}
// CHECK: DCFS     1.125

float f32_ret_p15(float x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f0, f0
    // CHECK: ldfs            f1, [pc, #L000078-.-8]
    // CHECK: adfs            f0, f0, f1
    // CHECK: mov             pc, lr
    return x + 1.5f;
}
// CHECK: L000078
// CHECK: DCFS     1.5

float f32_ret_p25(float x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f0, f0
    // CHECK: ldfs            f1, [pc, #L000018-.-8]
    // CHECK: adfs            f0, f0, f1
    // CHECK: mov             pc, lr
    return x + 2.5f;
}

float f32_ret_p30(float x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f0, f0
    // CHECK: adfs            f0, f0, #&3     @ =3.0
    // CHECK: mov             pc, lr
    return x + 3.0f;
}

float f32_ret_p40(float x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f0, f0
    // CHECK: adfs            f0, f0, #&4     @ =4.0
    // CHECK: mov             pc, lr
    return x + 4.0f;
}

float f32_ret_n05(float x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f0, f0
    // CHECK: sufs            f0, f0, #&6     @ =0.5
    // CHECK: mov             pc, lr
    return x + -0.5f;
}

float f32_ret_n25(float x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f0, f0
    // CHECK: ldfs            f1, [pc, #L0000e8-.-8]
    // CHECK: adfs            f0, f0, f1
    // CHECK: mov             pc, lr
    return x + -2.5f;
}
// CHECK: L0000e8
// CHECK: DCD      0xc0200000
