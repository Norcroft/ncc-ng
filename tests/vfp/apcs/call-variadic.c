// RUN: %cc %s -S -o -

// Note registers need changing when toggling proper AAPCS
// (doubles in int regs are aligned to even/odd regs, so r2/3, never r1/2)

// Layout (fpregargs):
//  Caller of variadic must pass FP args via core regs/stack, not VFP arg regs.
//      r0: n (3)
//      r1: skipped for alignment (see above)
//      r2/r3: first double (1.0) 8-byte aligned
//      stack: remaining doubles (2.0, 3.0)
//
//  Expected return from sumd: float in S0 (then cast to int)

#include <stdarg.h>

float sumd(int n, ...);

// CHECK-LABEL: main:
int main()
{
    // CHECK: vmov.f64    d0, #8    @ =3.0
    // CHECK: vpush    {d0
    // CHECK: vmov.f64    d0, #0    @ =2.0
    // CHECK: vpush    {d0

    // r2,r3 = 1.0 in int regs. currently LDMs, but could MOV # sequence.
    // Currently AAPCS disabled.
    // CHECK: ldmia  r1, {r1-r2}
    // CHECK: mov    r0, #3

    // CHECK: bl
    // return: convert float result to int.
    // CHECK: vcvt.s32.f32
    return (int)sumd(3, 1.0, 2.0, 3.0);
}
