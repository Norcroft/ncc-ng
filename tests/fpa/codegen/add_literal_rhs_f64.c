// RUN: %cc %s -S -o -

// Valid literals are 0, 1, 2, 3, 4, 5, 0.5 and 10.

double f64_add_p25(double x) {
    // CHECK: ldfd  f0, [sp], #&8
    // CHECK: adfd  f0, f0, #&6     @ =0.5
    return x + 0.5;
}

double f64_sub_p15(double x) {
    // CHECK: ldfd  f0, [sp], #&8
    // CHECK: sufd  f0, f0, #&7     @ =10.0
    return x - 10.0;
}

double f64_mul_p30(double x) {
    // CHECK: ldfd  f0, [sp], #&8
    // CHECK: mufd  f0, f0, #&5     @ =5.0
    return x * 5.0;
}

double f64_div_p05(double x) {
    // CHECK: ldfd  f0, [sp], #&8
    // CHECK: dvfd  f0, f0, #&4     @ =4.0
    return x / 4.0;
}

double f64_add_n25(double x) {
    // CHECK: ldfd  f0, [sp], #&8
    // CHECK: adfd  f0, f0, #&3     @ =3.0
    return x + 3.0;
}
