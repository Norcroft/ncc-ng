// RUN: %cc %s -S -o -

// The vcvt only appears if not compiling with apcs 3/narrow.
// NO-CHECK: vcvt.f32.f64    s0, d0
// CHECK: mov     r3, #0
// CHECK: cmp     r2, #0
// CHECK: movle   pc, lr
// CHECK: add     ip, r0, r3, lsl #2
// CHECK: vldr    s2, [ip]
// CHECK: vmul.f32        s2, s2, s0
// CHECK: add     ip, r1, r3, lsl #2
// CHECK: vldr    s4, [ip]
// CHECK: vadd.f32        s2, s2, s4
// CHECK: vstr    s2, [ip]
// CHECK: add     r3, r3, #1
// CHECK: cmp     r3, r2
// CHECK: blt     

void saxpy(float *x, float *y, int n, float a) {
    int i;

    for (i = 0; i < n; ++i) {
        y[i] = a * x[i] + y[i];
    }
}

// on entry
// r0 = x
// r1 = y
// r2 = n
// s0 = a (converted from double if not compiling with /narrow)

// r3 = i

// loops around:
// ip = index into x (x + i*4), calculated on each loop iteration.
// s1 = vldr from ip
// mul s1 <- s1 * s0
// ip = index into y (x + i*4), calculated on each loop iteration.
// s0 = vldr from ip
// s1 = vadd s1 + s2
// vstr s1, [ip]
// r3++
// compare r2, r3. loop
