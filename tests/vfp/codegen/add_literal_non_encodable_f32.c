// RUN: %cc %s -S -o -

float f32_ret_p12(void) {
    // CHECK: vldr    s0, [pc
    return 1.2f;                // 1.2f (not encodable)
}

float f32_ret_p33(void) {
    // CHECK: vldr    s0, [pc
    return 3.3f;                // 3.3f (not encodable)
}

float f32_ret_pi(void) {
    // CHECK: vldr    s0, [pc
    return 3.1415927f;          // pi (not encodable)
}

float f32_add_p12(float a) {
    // CHECK: vldr    s
    return a + 1.2f;            // re-use 1.2 literal from above
}

float f32_mul_p33(float a) {
    // CHECK: vldr    s
    return a * 3.3f;            // re-use 3.3 literal from above
}
