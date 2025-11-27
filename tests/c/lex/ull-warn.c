typedef unsigned long long uint64_t;

unsigned int hex(unsigned int a)
{
    // CHECK-ERR: Serious error: Number fffff0fffffffffff too large for 64-bit implementation
    // CHECK-ERR-NOT: Warning: 'fffff0fffffffffff'
    uint64_t  xl = 0xfffff0fffffffffffULL; // Invalid as greater than 2^64.

    // CHECK-ERR-NOT: Warning: 'ffff1fffffffffff'
    uint64_t ull = 0xffff1fffffffffffULL; // OK

    // CHECK-ERR-NOT: Warning: 'ffff2fffffffffff'
    uint64_t  ll = 0xffff2fffffffffffLL;  // OK. Silently forced to unsigned

    // CHECK-ERR-NOT: Warning: 'ffff3fffffffffff'
    uint64_t   l = 0xffff3fffffffffffL;   // OK. Silently forced to unsigned.

    // CHECK-ERR-NOT: FFFFF
    uint64_t llong_min = ~0x7FFFFFFFFFFFFFFF; // OK
    uint64_t llong_max = 0x7FFFFFFFFFFFFFFF;  // OK
    uint64_t ullong_max = 0xFFFFFFFFFFFFFFFF; // OK

    return xl + ull + ll + l + llong_min + llong_max + ullong_max;
}

unsigned int d(unsigned int a)
{
    // Warning: '18446744073709551615' treated as '18446744073709551615ull'
    uint64_t  xl = 18446744073709551615;    // signed 2^64-1 warn: forced to unsigned

    uint64_t ull = 18446744073709551615ULL; // unsigned 2^64-1 ok

    // Warning: '9223372036854775809' treated as '9223372036854775809ull'
    uint64_t mll = 9223372036854775809;    // (INT64_MAX+1) warn: forced to unsigned

    return xl + ull + mll;
}
