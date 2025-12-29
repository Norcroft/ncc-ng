// RUN: %cc %s -S -o -

double f64_ret_p12(void) {
    // CHECK: ldfd    f0, [pc, #L000008-.-8]
    return 1.2;
    // CHECK: L000008
    // CHECK: DCFD     1.2
}

double f64_ret_p33(void) {
    // CHECK: ldfd    f0, [pc, #L000018-.-8]
    return 3.3;
    // CHECK: L000018
    // CHECK: DCFD     3.3
}

double f64_ret_pi(void)  {
    // CHECK: ldfd    f0, [pc, #L000028-.-8]
    return 3.141592653589793;
    // CHECK: L000028
    // CHECK: DCFD     3.141592653589793
}


double f64_add_p12(double x) {
    // CHECK: ldfd   f0, [sp], #&8
    // CHECK: ldfd   f1, [pc, #L000008-.-8]
    // CHECK: adfd   f0, f0, f1
    return x + 1.2;             // re-use 1.2 from earlier
}

double f64_mul_p33(double x) {
    // CHECK: ldfd   f0, [sp], #&8
    // CHECK: ldfd   f1, [pc, #L000018-.-8]
    // CHECK: mufd   f0, f0, f1
    return x * 3.3;             // re-use 3.3 from earlier
}
