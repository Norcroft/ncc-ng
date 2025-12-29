// RUN: %cc %s -S -o -

double addf(float a, float b) {
    // CHECK: vadd.f32
    return a + b;
}
