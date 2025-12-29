// RUN: %cc %s -S -o -

float add_lit(float x) {
    // CHECK: vmov.f32    s2, #4
    return x + 2.5f;
}

float f32_ret_p05(float x) {
    // CHECK: vmov.f32    s2, #96
    return x + 0.5f;
}

float f32_ret_p10(float x) {
    // CHECK: vmov.f32    s2, #112
    return x + 1.0f;
}

float f32_ret_p1125(float x) {
    // CHECK: vmov.f32    s2, #114
    return x + 1.125f;
}

float f32_ret_p15(float x) {
    // CHECK: vmov.f32    s2, #120
    return x + 1.5f;
}

float f32_ret_p25(float x) {
    // CHECK: vmov.f32    s2, #4
    return x + 2.5f;
}

float f32_ret_p30(float x) {
    // CHECK: vmov.f32    s2, #8
    return x + 3.0f;
}

float f32_ret_p40(float x) {
    // CHECK: vmov.f32    s2, #16
    return x + 4.0f;
}

float f32_ret_n05(float x) {
    // CHECK: vmov.f32    s2, #224
    return x + -0.5f;
}

float f32_ret_n25(float x) {
    // CHECK: vmov.f32    s2, #132
    return x + -2.5f;
}
