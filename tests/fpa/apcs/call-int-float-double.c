// RUN: %cc %s -S -o -


static int g;
static volatile double gd;

int callee(int a, float b, double c) {
    // CHECK: mov       ip, sp
    // CHECK: stmdb     sp!, {r0-r3}
    // CHECK: stmdb     sp!, {fp-ip, lr-pc}
    // CHECK: sub       fp, ip, #20

    // f0 = b, f1 = c (maybe other way round)
    // CHECK: ldfd      f0, [fp, #&8]
    // CHECK: ldfd      f1, [fp, #&10]
    // CHECK: mvfs      f0, f0

    // r1 = (int)c
    // CHECK: fixsz     r1, f0

    // r0 = a + (int)c
    // CHECK: add       r0, r0, r1

    // r1 = (int)b
    // CHECK: fixsz     r1, f0

    // r1 = (a + (int)c) + b
    // CHECK: add       r1, r0, r1

    // r0 = addr of 'g'
    // CHECK: ldr       r0, [pc, #L000058-.-8]

    g = a + (int)b + (int)c;

    // f0 = c + b
    // CHECK: adfd      f0, f1, f0

    // store r1 at g
    // CHECK: str       r1, [r0]

    // store f0 in gd (volatile so loaded again)
    // CHECK: stfd      f0, [r0, #&4]
    // CHECK: ldfd      f0, [r0, #&4]
    gd = c + b;

    // CHECK: fixsz     r0, f0
    // CHECK: add       r0, r1, r0
    // CHECK: ldmdb     fp, {fp, sp, pc}
    return g + (int)gd;
}

int main()
{
    // CHECK: mov       ip, sp
    // CHECK: stmdb     sp!, {fp-ip, lr-pc}
    // CHECK: sub       fp, ip, #4
    // CHECK: cmp       sp, r10
    // CHECK: blmi      __rt_stkovf_split_small

    // f0 = 9.25. Store on stack.
    // CHECK: ldfd      f0, [pc, #L00009c-.-8]
    // CHECK: stfd      f0, [sp, #-&8]!

    // r1,r2 = 3.5 (arg1)
    // CHECK: add       r1, pc, #L0000a4-.-8
    // CHECK: ldmia     r1, {r1-r2}

    // r0 = 7 (arg0)
    // CHECK: mov       r0, #7

    // r3 = half of arg2 (9.25)
    // CHECK: ldr       r3, [sp], #4

    // CHECK: bl        callee
    // CHECK: ldmdb     fp, {fp, sp, pc}
    return callee(7, 3.5f, 9.25);
}
// CHECKL: L00009c
// CHECKL: DCFD     9.25
// CHECKL: L0000a4
// CHECKL: DCFD     3.5

// CHECK: g
// CHECK: DCD      0x00000000
// CHECK: gd
// CHECK: DCFD     0.0
