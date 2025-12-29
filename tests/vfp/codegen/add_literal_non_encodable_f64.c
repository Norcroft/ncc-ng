// RUN: %cc %s -S -o -

double f64_ret_p12(void) {
    // CHECK: vldr    d0, [pc
    return 1.2;
}

double f64_ret_p33(void) {
    // CHECK: vldr    d0, [pc
    return 3.3;
}

double f64_ret_pi(void)  {
    // CHECK: vldr    d0, [pc
    return 3.141592653589793;
}


double f64_add_p12(double x) {
    // CHECK: vldr    d1, [pc
    return x + 1.2;             // re-use 1.2 from earlier
}

double f64_mul_p33(double x) {
    // CHECK: vldr    d1, [pc
    return x * 3.3;             // re-use 3.3 from earlier
}
