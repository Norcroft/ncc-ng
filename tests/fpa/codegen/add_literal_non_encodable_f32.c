// RUN: %cc %s -S -o -

float f32_ret_p12(void) {
    // CHECK: ldfs    f0, [pc, #L000008-.-8]
    return 1.2f;                // 1.2f (not encodable)
    // CHECK: L000008
    // CHECK: DCFS     1.2
}

float f32_ret_p33(void) {
    // CHECK: ldfs    f0, [pc, #L000014-.-8]
    return 3.3f;                // 3.3f (not encodable)
    // CHECK: L000014
    // CHECK: DCFS     3.3
}

float f32_ret_pi(void) {
    // CHECK: ldfs    f0, [pc, #L000020-.-8]
    return 3.1415927f;          // pi (not encodable)
    // CHECK: L000020
    // CHECK: DCFS     3.1415927
}

float f32_add_p12(float a) {
    // CHECK: ldfd   f0, [sp], #&8
    // CHECK: mvfs   f0, f0
    // CHECK: ldfs   f1, [pc, #L000008-.-8]
    // CHECK: adfs   f0, f0, f1
    return a + 1.2f;            // re-use 1.2 literal from above [pc + neg #]
}

float f32_mul_p33(float a) {
    // CHECK: ldfd   f0, [sp], #&8
    // CHECK: mvfs   f0, f0
    // CHECK: ldfs   f1, [pc, #L000014-.-8]
    // CHECK: mufs   f0, f0, f1
    return a * 3.3f;            // re-use 3.3 literal from above [pc + neg #]
}
