#include <stdint.h>

// CHECK-ERR: Serious error: Number 1ffffffffffffffff too large for 64-bit implementation
unsigned long long a = 0x1ffffffffffffffffULL;     /* 2^65-1  */

// CHECK-ERR: Serious error: Number fffffffffffffffff too large for 64-bit implementation
unsigned long long b = 0xfffffffffffffffffULL;     /* 68-bit or so */

// CHECK_ERR: Serious error: Number 18446744073709551616 too large for 64-bit implementation
unsigned long long c = 18446744073709551616ULL;    /* 2^64, decimal */
