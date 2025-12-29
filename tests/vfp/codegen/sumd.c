// RUN: %cc %s -S -o -

double sumd(double *p, int n) {

    double s = 0.0;
    int i;

    // CHECK: vldr
    // CHECK: vadd.f64
    for (i = 0; i < n; ++i) {
        s += p[i];
    }

    return s;
}
