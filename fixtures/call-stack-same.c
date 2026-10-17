#include <stdint.h>

__attribute__((noinline)) uint64_t helper(uint64_t x) {
    return x + 1;
}

uint64_t caller(uint64_t x) {
    return helper(x) + 1;
}
