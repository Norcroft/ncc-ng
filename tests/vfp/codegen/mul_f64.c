// RUN: %cc %s -S -o -

double muld(double a, double b) {
    // CHECK: vmul.f64
    return a * b;
}
