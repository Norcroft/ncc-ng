// RUN: %cc %s -S -o -

// Note registers need changing when toggling proper AAPCS
// (doubles in int regs are aligned to even/odd regs, so r2/3, never r1/2)

// Layout (fpregargs):
//  Caller of variadic must pass FP args via core regs/stack, not VFP arg regs.
//      r0: n (3)
//      r1: skipped for alignment
//      r2/r3: first double (1.0) 8-byte aligned
//      stack: remaining doubles (2.0, 3.0)
//
//  Expected return from sumd: float in S0 (then VFIX to int)

// What to see in sumd:

#include <stdarg.h>

// CHECK-LABEL: sumd:
double sumd(int n, ...)
{
    //  All arguments should be pushed to stack
    // CHECK: stmdb           sp!, {r0-r3}

    //   [fp, #4]: n
    //   [fp, #8]: double (should be aligned, but not yet enforced)

    double s;
    int i;

    va_list ap;
    va_start(ap, n);

    // CHECK: veor    d0, d0, d0
    s = 0.0;

    // Surprised this isn't just an add, with the alignment outside the loop.
    // CHECK: add    r0, r0, #3
    // CHECK: bic    r0, r0, #3
    // CHECK: add    r0, r0, #8

    // CHECK: vldr    d1, [r0,
    // CHECK: vadd.f64    d0, d1, d0
    // CHECK: add    r1, r1, #1
    for (i = 0; i < n; i++)
        s += va_arg(ap, double);

    va_end(ap);

    // CHECK: mov    ip, sp
    return s;
}

// CHECK-LABEL: main:
int main()
{
    // CHECK: vmov.f64    d0, #8    @ =3.0
    // CHECK: vpush    {d0
    // CHECK: vmov.f64    d0, #0    @ =2.0
    // CHECK: vpush    {d0

    // r2,r3 = 1.0 in int regs. currently LDMs, but could MOV # sequence.
    // CHECK: ldmia  r1, {r1-r2}
    // CHECK: mov    r0, #3

    // CHECK: bl
    // return: convert double result to int.
    // CHECK: vcvt.s32.f64
    return (int)sumd(3, 1.0, 2.0, 3.0);
}
