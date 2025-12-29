// RUN: %cc %s -S -o -

#include <stdarg.h>

double sumd(int n, ...)
{
    // CHECK: mov       ip, sp
    // CHECK: stmdb     sp!, {r0-r3}
    // CHECK: stmdb     sp!, {fp-ip, lr-pc}
    // CHECK: sub       fp, ip, #20
    // CHECK: add       r1, fp, #8

    double s;
    int i;

    va_list ap;
    va_start(ap, n);

    // CHECK: mvfd      f0, #&0         @ =0.0
    s = 0.0;

    // r0 = i (0)
    // r2 = n
    // CHECK: mov             r0, #0
    // CHECK: ldr             r2, [fp, #4]
    // CHECK: cmp             r2, #0
    // CHECK: ldmdble         fp, {fp, sp, pc}

    // CHECK: |L000034.J4.sumd|
    for (i = 0; i < n; i++) {
        // CHECK: add             r1, r1, #3
        // CHECK: bic             r1, r1, #3
        // CHECK: add             r1, r1, #8
        // CHECK: ldfd            f1, [r1, #-&8]
        // CHECK: adfd            f0, f1, f0
        // CHECK: add             r0, r0, #1
        // CHECK: cmp             r0, r2
        // CHECK: blt             |L000034.J4.sumd|
        s += va_arg(ap, double);
    }

    va_end(ap);

    // CHECK: ldmdb           fp, {fp, sp, pc}
    return s;
}

// CHECK-LABEL: main:
int main()
{
    // CHECK: mov             ip, sp
    // CHECK: stmdb           sp!, {fp-ip, lr-pc}
    // CHECK: sub             fp, ip, #4
    // CHECK: cmp             sp, r10
    // CHECK: blmi            __rt_stkovf_split_small
    // CHECK: mvfd            f0, #&3         @ =3.0
    // CHECK: stfd            f0, [sp, #-&8]!
    // CHECK: mvfd            f0, #&2         @ =2.0
    // CHECK: stfd            f0, [sp, #-&8]!
    // CHECK: add             r1, pc, #L0000a4-.-8
    // CHECK: ldmia           r1, {r1-r2}
    // CHECK: mov             r0, #3
    // CHECK: ldr             r3, [sp], #4

    // CHECK: bl              sumd

    // CHECK: fixsz           r0, f0
    // CHECK: ldmdb           fp, {fp, sp, pc}
    return (int)sumd(3, 1.0, 2.0, 3.0);
}
// CHECK: L0000a4
// CHECK: DCFD     1.0
