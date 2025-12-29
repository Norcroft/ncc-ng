// RUN: %cc %s -S -o -

// CHECK: vldr
// CHECK: vcmp.f64
// CHECK: vmrs
// CHECK: movgt

int is_gt_pi(double x) {
    // Force a non-zero double literal (needs literal pool load + VCMP)
    const double pi = 3.141592653589793238462643383279502884;
    return x > pi;
}
