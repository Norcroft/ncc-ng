// RUN: %cc %s -S -o -

// Valid literals are 0, 1, 2, 3, 4, 5, 0.5 and 10.

float f32_add(float x) {
    // CHECK: ldfd  f0, [sp], #&8
    // CHECK: mvfs  f0, f0
    // CHECK: adfs  f0, f0, #&6     @ =0.5
    return x + 0.5f;
}

float f32_sub(float x) {
    // CHECK: ldfd  f0, [sp], #&8
    // CHECK: mvfs  f0, f0
    // CHECK: sufs  f0, f0, #&7     @ =10.0
    return x - 10.0f;
}

float f32_mul(float x) {
    // CHECK: ldfd  f0, [sp], #&8
    // CHECK: mvfs  f0, f0
    // CHECK: mufs  f0, f0, #&5     @ =5.0
    return x * 5.0f;
}

float f32_div(float x) {
    // CHECK: ldfd  f0, [sp], #&8
    // CHECK: mvfs  f0, f0
    // CHECK: dvfs  f0, f0, #&4     @ =4.0
    return x / 4.0f;
}

float f32_add2(float x) {
    // CHECK: ldfd  f0, [sp], #&8
    // CHECK: mvfs  f0, f0
    // CHECK: adfs  f0, f0, #&3     @ =3.0
    return x + 3.0f;
}
