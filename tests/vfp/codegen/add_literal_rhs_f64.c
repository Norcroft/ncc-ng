// RUN: %cc %s -S -o -

// Literals should all map to VMOV(imm) (followed by a VADD/VSUB/VMUL/VDIV).

double f64_add_p25(double x) {
    // CHECK: vmov.f64    d1, #4
    return x + 2.5;
}

double f64_sub_p15(double x) {
    // CHECK: vmov.f64    d1, #120
    return x - 1.5;
}

double f64_mul_p30(double x) {
    // CHECK: vmov.f64    d1, #8
    return x * 3.0;
}

double f64_div_p05(double x) {
    // CHECK: vmov.f64    d1, #96
    return x / 0.5;
}


double f64_add_n25(double x) {
    // CHECK: vmov.f64    d1, #132
    return x + (-2.5);
}
