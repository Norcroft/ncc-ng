// RUN: %cc %s -S -o -

#include <stdarg.h>

float sumd(int n, ...);

int main()
{
    // CHECK: mov       ip, sp
    // CHECK: stmdb     sp!, {fp-ip, lr-pc}
    // CHECK: sub       fp, ip, #4
    // CHECK: cmp       sp, r10
    // CHECK: blmi      __rt_stkovf_split_small

    // Put doubles for 2 and 3 on stack... (but...)
    // CHECK: mvfd      f0, #&3         @ =3.0
    // CHECK: stfd      f0, [sp, #-&8]!
    // CHECK: mvfd      f0, #&2         @ =2.0
    // CHECK: stfd      f0, [sp, #-&8]!

    // arg 2 (= 1.0) in r1, r2
    // CHECK: add       r1, pc, #L00004c-.-8
    // CHECK: ldmia     r1, {r1-r2}

    // arg 1 (= 3) in r0
    // CHECK: mov       r0, #3

    // half of arg 4 (= 3.0) loaded from stack... nice.
    // CHECK: ldr       r3, [sp], #4

    // CHECK: bl        sumd

    // CHECK: fixsz     r0, f0
    // CHECK: ldmdb     fp, {fp, sp, pc}
    return (int)sumd(3, 1.0, 2.0, 3.0);
}
// CHECK: L00004c
// CHECK: DCFD      1.0
