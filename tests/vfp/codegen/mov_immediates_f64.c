// RUN: %cc %s -S -o -

double add_lit(double x) {
    // vmov.f64    s1, #4
    return x + 2.5f;
}

double f64_ret_p05(double x) {
    // vmov.f64    s1, #96
    return x + 0.5f;
}

double f64_ret_p10(double x) {
    // vmov.f64    s1, #112
    return x + 1.0f;
}

double f64_ret_p1125(double x) {
    // vmov.f64    s1, #114
    return x + 1.125f;
}

double f64_ret_p15(double x) {
    // vmov.f64    s1, #120
    return x + 1.5f;
}

double f64_ret_p25(double x) {
    // vmov.f64    s1, #4
    return x + 2.5f;
}

double f64_ret_p30(double x) {
    // vmov.f64    s1, #8
    return x + 3.0f;
}

double f64_ret_p40(double x) {
    // vmov.f64    s1, #16
    return x + 4.0f;
}

double f64_ret_n05(double x) {
    // vmov.f64    s1, #224
    return x + -0.5f;
}

double f64_ret_n25(double x) {
    // vmov.f64    s1, #132
    return x + -2.5f;
}
