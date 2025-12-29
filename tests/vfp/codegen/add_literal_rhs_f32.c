// RUN: %cc %s -S -o -

// Literals should all map to VMOV(imm) (followed by a VADD/VSUB/VMUL/VDIV).

float f32_add_p25(float x) {
    // CHECK: vmov.f32    s2, #4
    return x + 2.5f;
}

float f32_sub_p15(float x) {
    // CHECK: vmov.f32    s2, #120
    return x - 1.5f;
}

float f32_mul_p30(float x) {
    // CHECK: vmov.f32    s2, #8
    return x * 3.0f;
}

float f32_div_p05(float x) {
    // CHECK: vmov.f32    s2, #96
    return x / 0.5f;
}


float f32_add_n25(float x) {
    // CHECK: vmov.f32    s2, #132
    return x + (-2.5f);
}
