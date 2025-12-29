// RUN: %cc %s -S -o -

typedef struct {
    int x;
    double y;
} P;

// CHECK-LABEL: f:
double f(int a, P p, float b)
{
    // CHECK: mov       ip, sp
    // CHECK: stmdb     sp!, {r0-r3}
    // CHECK: stmdb     sp!, {fp-ip, lr-pc}
    // CHECK: sub       fp, ip, #20

    // f0 = b
    // CHECK: ldfd      f0, [fp, #&14]
    // CHECK: mvfs      f0, f0

    // r1 = p.x (2)
    // CHECK: ldr       r1, [fp, #8]

    // r0 = a + p.x
    // f2 = a + p.x
    // CHECK: add       r0, r0, r1
    // CHECK: fltd      f2, r0

    // f1 = p.y
    // CHECK: ldfd      f1, [fp, #&c]

    // f1 = (a + p.x) + p.y
    // CHECK: adfd      f1, f2, f1

    // f0 = f1 + b
    // CHECK: adfd      f0, f1, f0

    // CHECK: ldmdb     fp, {fp, sp, pc}
    return a + p.x + p.y + b;
}

int main()
{
    P p = {2, 4.5};

    // CHECK: mov       ip, sp
    // CHECK: stmdb     sp!, {fp-ip, lr-pc}
    // CHECK: sub       fp, ip, #4
    // CHECK: cmp       sp, r10
    // CHECK: blmi      __rt_stkovf_split_small
    // CHECK: sub       sp, sp, #12

    // Copy constant data {2, 4.5} to stack
    // CHECK: ldr       r0, [pc, #L00008c-.-8]
    // CHECK: ldmia     r0, {r1-r3}
    // CHECK: stmia     sp, {r1-r3}

    // f0 = 3. Store on stack as arg3.
    // CHECK: mvfd      f0, #&3         @ =3.0
    // CHECK: stfd      f0, [sp, #-&8]!

    // r0 = 1
    // CHECK: mov       r0, #1

    // {r1-r3} = contents of 'P p'
    // CHECK: add       r3, sp, #8
    // CHECK: ldmia     r3, {r1-r3}

    // CHECK: bl        f
    // CHECK: fixsz     r0, f0
    // CHECK: ldmdb     fp, {fp, sp, pc}
    return (int)f(1, p, 3.0f);
}
// CHECK: L00008c
// CHECK: DCD      |x$constdata|

// CHECK: |x$constdata|
// CHECK: DCD      0x00000002
// CHECK: DCFD     4.5
