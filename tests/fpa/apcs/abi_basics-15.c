// RUN: %cc %s -S -o -

// ---------- Test 1: argument order (float, double, float)
float t_arg_fdf(float a, double b, float c) {
    // CHECK: stmdb     sp!, {r0-r3}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: ldfd      f2, [sp], #&8
    // CHECK: ldfd      f1, [sp]
    // CHECK: mvfs      f0, f0
    // CHECK: mvfs      f1, f1
    // CHECK: mvfs      f2, f2
    // CHECK: adfs      f0, f0, f2
    // CHECK: adfs      f0, f0, f1
    // CHECK: mov       pc, lr
    return a + (float)b + c;
}

void call_t_arg_fdf() {
    // CHECK: mov       ip, sp
    // CHECK: stmdb     sp!, {fp-ip, lr-pc}
    // CHECK: sub       fp, ip, #4
    // CHECK: cmp       sp, r10
    // CHECK: blmi      __rt_stkovf_split_small
    // CHECK: ldfd      f0, [pc, #L000070-.-8]
    // CHECK: stfd      f0, [sp, #-&8]!
    // CHECK: add       r2, pc, #L000078-.-8
    // CHECK: add       r0, pc, #L000080-.-8
    // CHECK: ldmia     r0, {r0-r1}
    // CHECK: ldmia     r2, {r2-r3}
    // CHECK: bl        t_arg_fdf
    // CHECK: ldmdb     fp, {fp, sp, pc}
    t_arg_fdf(5.0, 6.0, 7.0);
}
// CHECK: L000070
// CHECK: DCFD     7.0
// CHECK: L000078
// CHECK: DCFD     6.0
// CHECK: L000080
// CHECK: DCFD     5.0

// ---------- Test 2: argument order (float, float, double)
double t_arg_ffd(float a, float b, double c) {
    // CHECK: stmdb     sp!, {r0-r1}
    // CHECK: ldfd      f1, [sp], #&8
    // CHECK: stmdb     sp!, {r2-r3}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: ldfd      f2, [sp]
    // CHECK: mvfs      f1, f1
    // CHECK: mvfs      f0, f0
    // CHECK: adfd      f0, f1, f0
    // CHECK: adfd      f0, f0, f2
    // CHECK: mov       pc, lr
    return (double)a + (double)b + c;
}

// ---------- Test 3: boundary fill (five doubles)
double t_arg_5d(double a, double b, double c, double d, double e) {
    // CHECK: sfm             f4, 1, [sp, #-&c]!
    // CHECK: stmdb           sp!, {r0-r3}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: ldfd            f4, [sp], #&8
    // CHECK: ldfd            f3, [sp, #&c]
    // CHECK: ldfd            f2, [sp, #&14]
    // CHECK: ldfd            f1, [sp, #&1c]
    // CHECK: adfd            f0, f0, f4
    // CHECK: adfd            f0, f0, f3
    // CHECK: adfd            f0, f0, f2
    // CHECK: adfd            f0, f0, f1
    // CHECK: lfm             f4, 1, [sp], #&c
    // CHECK: mov             pc, lr
    return a + b + c + d + e;
}

// ---------- Test 4: mixed with alignment bump
double t_arg_mixed(float f0, float f1, float f2, double d0, float f3) {
    // CHECK: sfm             f4, 1, [sp, #-&c]!
    // CHECK: stmdb           sp!, {r0-r3}
    // CHECK: ldfd            f1, [sp], #&8
    // CHECK: ldfd            f3, [sp], #&8
    // CHECK: ldfd            f0, [sp, #&c]
    // CHECK: ldfd            f4, [sp, #&14]
    // CHECK: ldfd            f2, [sp, #&1c]
    // CHECK: mvfs            f1, f1
    // CHECK: mvfs            f3, f3
    // CHECK: mvfs            f0, f0
    // CHECK: mvfs            f2, f2
    // CHECK: adfd            f1, f1, f3
    // CHECK: adfd            f0, f1, f0
    // CHECK: adfd            f0, f0, f4
    // CHECK: adfd            f0, f0, f2
    // CHECK: lfm             f4, 1, [sp], #&c
    // CHECK: mov             pc, lr
    return (double)f0 + (double)f1 + (double)f2 + d0 + (double)f3;
}

// ---------- Test 5: float return in f0
float t_ret_fadd(float a, float b) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f1, [sp], #&8
    // CHECK: stmdb           sp!, {r2-r3}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f1, f1
    // CHECK: mvfs            f0, f0
    // CHECK: adfs            f0, f1, f0
    // CHECK: mov             pc, lr
    return a + b;
}

// ---------- Test 6: double return in f0
double t_ret_dadd(double a, double b) {
    // CHECK: stmdb           sp!, {r0-r3}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: ldfd            f1, [sp], #&8
    // CHECK: adfd            f0, f0, f1
    // CHECK: mov             pc, lr
    return a + b;
}

// ---------- Test 7: float:int (truncate toward zero)
int t_cvt_trunc_f2i(float x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f0, f0
    // CHECK: fixsz           r0, f0
    // CHECK: mov             pc, lr
    return (int)x;
}

// ---------- Test 8: double:int (truncate toward zero)
int t_cvt_trunc_d2i(double x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: fixsz           r0, f0
    // CHECK: mov             pc, lr
    return (int)x;
}

// ---------- Test 9: float:int (floor towards −∞)
float floorf(float); /* declare to avoid pulling headers */
int t_cvt_floor_f2i(float x) {
    // CHECK: mov             ip, sp
    // CHECK: stmdb           sp!, {r0-r1, fp-ip, lr-pc}
    // CHECK: sub             fp, ip, #4
    // CHECK: cmp             sp, r10
    // CHECK: blmi            __rt_stkovf_split_small
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f0, f0
    // CHECK: stfd            f0, [sp, #-&8]!
    // CHECK: ldmia           sp!, {r0-r1}
    // CHECK: bl              floorf
    // CHECK: fixsz           r0, f0
    // CHECK: ldmdb           fp, {fp, sp, pc}
    return (int)floorf(x);
}

// ---------- Test 10: double:float conversion (narrow) */
float t_cvt_d2f(double x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f0, f0
    // CHECK: mov             pc, lr
    return (float)x;
}

// ---------- Test 11: float:double conversion (widen) */
double t_cvt_f2d(float x) {
    // CHECK: stmdb           sp!, {r0-r1}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: mvfs            f0, f0
    // CHECK: mov             pc, lr
    return (double)x;
}

// ---------- Test 12: simple FP loop to exercise register pressure
float t_loop_fma_sum(const float *p, int n) {
    // CHECK: mvfs      f0, #&0         @ =0.0
    float acc = 0.0f;
    int i;

    // n:r1, i:r2
    // CHECK: mov       r2, #0
    // CHECK: cmp       r1, #0
    // CHECK: movle     pc, lr
    // CHECK: ldfs      f1, [pc, #L00021c-.-8]

    // CHECK: |L0001fc.J4.t_loop_fma_sum|
    for (i = 0; i < n; ++i) {
        // CHECK: add       r3, r0, r2, lsl #2
        // CHECK: ldfs      f2, [r3]
        // CHECK: mufs      f2, f2, f1
        // CHECK: adfs      f0, f2, f0
        acc = acc + p[i] * 1.5f;

        // CHECK: add       r2, r2, #1
        // CHECK: cmp       r2, r1
        // CHECK: blt       |L0001fc.J4.t_loop_fma_sum|
    }

    // CHECK: mov       pc, lr
    return acc;
}
// CHECK: L00021c
// CHECK: DCFS     1.5

// ---------- Test 13: variadic call (should fall back to core regs/stack)
int printf(const char *, ...);
int t_varargs(float a, double b) {
    // CHECK: mov             ip, sp
    // CHECK: stmdb           sp!, {r0-r3, fp-ip, lr-pc}
    // CHECK: sub             fp, ip, #4
    // CHECK: cmp             sp, r10
    // CHECK: blmi            __rt_stkovf_split_small
    // CHECK: stmdb           sp!, {r0-r3}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: ldfd            f1, [sp], #&8
    // CHECK: mvfs            f0, f0
    // CHECK: stfd            f1, [sp, #-&8]!
    // CHECK: add             r0, pc, #L00026c-.-8
    // CHECK: stfd            f0, [sp, #-&8]!
    // CHECK: ldmia           sp!, {r1-r3}
    // CHECK: bl              printf
    // CHECK: ldmdb           fp, {fp, sp, pc}
    return printf("%f %f\n", (double)a, b);
}

// ---------- Test 14: pass/return aliases sanity
double t_alias_mix(float a, double b, float c) {
    // CHECK: stmdb           sp!, {r0-r3}
    // CHECK: ldfd            f0, [sp], #&8
    // CHECK: ldfd            f1, [sp], #&8
    // CHECK: ldfd            f2, [sp]
    // CHECK: mvfs            f0, f0
    // CHECK: mvfs            f2, f2
    // CHECK: adfd            f0, f0, f1
    // CHECK: mvfs            f0, f0
    // CHECK: adfs            f0, f0, f2
    // CHECK: adfd            f0, f0, f1
    // CHECK: mov             pc, lr
    double x = (double)a + b;

    float  y = (float)x + c;

    return (double)y + b;
}

// ---------- Test 15: many floats to cross d-boundaries
float t_many_f(float a, float b, float c, float d,
               float e, float f, float g, float h)
{
    // CHECK: sfm       f4, 4, [sp, #-&30]!
    // CHECK: stmdb     sp!, {r0-r3}
    // CHECK: ldfd      f0, [sp], #&8
    // CHECK: ldfd      f1, [sp], #&8
    // CHECK: ldfd      f2, [sp, #&30]
    // CHECK: ldfd      f3, [sp, #&38]
    // CHECK: ldfd      f4, [sp, #&40]
    // CHECK: ldfd      f5, [sp, #&48]
    // CHECK: ldfd      f7, [sp, #&50]
    // CHECK: ldfd      f6, [sp, #&58]
    // CHECK: mvfs      f0, f0
    // CHECK: mvfs      f1, f1
    // CHECK: mvfs      f2, f2
    // CHECK: mvfs      f3, f3
    // CHECK: mvfs      f4, f4
    // CHECK: mvfs      f5, f5
    // CHECK: mvfs      f7, f7
    // CHECK: mvfs      f6, f6
    // CHECK: adfs      f0, f0, f1
    // CHECK: adfs      f0, f0, f2
    // CHECK: adfs      f0, f0, f3
    // CHECK: adfs      f0, f0, f4
    // CHECK: adfs      f0, f0, f5
    // CHECK: adfs      f0, f0, f7
    // CHECK: adfs      f0, f0, f6
    // CHECK: lfm       f4, 4, [sp], #&30
    // CHECK: mov       pc, lr
    return a + b + c + d + e + f + g + h;
}

float t_most_f(float a, float b, float c, float d,
               float e, float f, float g, float h,
               float i, float j, float k, float l,
               float m, float n, float o, float p,
               float q, float r, float s, float t)
{
    // CHECK: mov       ip, sp
    // CHECK: stmdb     sp!, {r0-r3}
    // CHECK: stmdb     sp!, {fp-ip, lr-pc}
    // CHECK: sub       fp, ip, #20
    // CHECK: sfm       f4, 4, [sp, #-&30]!
    // CHECK: ldfd      f7, [fp, #&4]
    // CHECK: ldfd      f6, [fp, #&14]
    // CHECK: ldfd      f5, [fp, #&1c]
    // CHECK: ldfd      f4, [fp, #&24]
    // CHECK: ldfd      f3, [fp, #&2c]
    // CHECK: ldfd      f2, [fp, #&34]
    // CHECK: ldfd      f1, [fp, #&3c]
    // CHECK: ldfd      f0, [fp, #&44]
    // CHECK: mvfs      f7, f7
    // CHECK: stfs      f7, [sp, #-&34]!
    // CHECK: ldfd      f7, [fp, #&c]
    // CHECK: mvfs      f7, f7
    // CHECK: mvfs      f6, f6
    // CHECK: stfs      f6, [sp, #&4]
    // CHECK: mvfs      f5, f5
    // CHECK: stfs      f5, [sp, #&8]
    // CHECK: mvfs      f4, f4
    // CHECK: stfs      f4, [sp, #&c]
    // CHECK: mvfs      f3, f3
    // CHECK: stfs      f3, [sp, #&10]
    // CHECK: mvfs      f2, f2
    // CHECK: stfs      f2, [sp, #&14]
    // CHECK: mvfs      f1, f1
    // CHECK: stfs      f1, [sp, #&18]
    // CHECK: mvfs      f0, f0
    // CHECK: stfs      f0, [sp, #&1c]
    // CHECK: ldfd      f0, [fp, #&4c]
    // CHECK: mvfs      f0, f0
    // CHECK: stfs      f0, [sp, #&20]
    // CHECK: ldfd      f0, [fp, #&54]
    // CHECK: mvfs      f0, f0
    // CHECK: stfs      f0, [sp, #&24]
    // CHECK: ldfd      f0, [fp, #&5c]
    // CHECK: mvfs      f0, f0
    // CHECK: stfs      f0, [sp, #&28]
    // CHECK: ldfd      f0, [fp, #&64]
    // CHECK: mvfs      f0, f0
    // CHECK: stfs      f0, [sp, #&2c]
    // CHECK: ldfd      f0, [fp, #&6c]
    // CHECK: mvfs      f0, f0
    // CHECK: stfs      f0, [sp, #&30]
    // CHECK: ldfd      f0, [fp, #&74]
    // CHECK: mvfs      f0, f0
    // CHECK: ldfd      f1, [fp, #&7c]
    // CHECK: mvfs      f1, f1
    // CHECK: ldfd      f2, [fp, #&84]
    // CHECK: mvfs      f2, f2
    // CHECK: ldfd      f3, [fp, #&8c]
    // CHECK: mvfs      f3, f3
    // CHECK: ldfd      f4, [fp, #&94]
    // CHECK: mvfs      f4, f4
    // CHECK: ldfd      f5, [fp, #&9c]
    // CHECK: mvfs      f6, f5
    // CHECK: ldfs      f5, [sp]
    // CHECK: adfs      f5, f5, f7
    // CHECK: ldfs      f7, [sp, #&4]
    // CHECK: adfs      f7, f5, f7
    // CHECK: ldfs      f5, [sp, #&8]
    // CHECK: adfs      f5, f7, f5
    // CHECK: ldfs      f7, [sp, #&c]
    // CHECK: adfs      f5, f5, f7
    // CHECK: ldfs      f7, [sp, #&10]
    // CHECK: adfs      f5, f5, f7
    // CHECK: ldfs      f7, [sp, #&14]
    // CHECK: adfs      f5, f5, f7
    // CHECK: ldfs      f7, [sp, #&18]
    // CHECK: adfs      f5, f5, f7
    // CHECK: ldfs      f7, [sp, #&1c]
    // CHECK: adfs      f5, f5, f7
    // CHECK: ldfs      f7, [sp, #&20]
    // CHECK: adfs      f5, f5, f7
    // CHECK: ldfs      f7, [sp, #&24]
    // CHECK: adfs      f5, f5, f7
    // CHECK: ldfs      f7, [sp, #&28]
    // CHECK: adfs      f5, f5, f7
    // CHECK: ldfs      f7, [sp, #&2c]
    // CHECK: adfs      f5, f5, f7
    // CHECK: ldfs      f7, [sp, #&30]
    // CHECK: adfs      f5, f5, f7
    // CHECK: adfs      f0, f5, f0
    // CHECK: adfs      f0, f0, f1
    // CHECK: adfs      f0, f0, f2
    // CHECK: adfs      f0, f0, f3
    // CHECK: adfs      f0, f0, f4
    // CHECK: adfs      f0, f0, f6
    // CHECK: lfm       f4, 4, [fp, #-&3c]
    // CHECK: ldmdb     fp, {fp, sp, pc}
    return a + b + c + d + e + f + g + h +
           i + j + k + l + m + n + o + p +
           q + r + s + t;
}
