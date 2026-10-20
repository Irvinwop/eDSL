#include <stdint.h>

__attribute__((noinline)) uint64_t helper(uint64_t x) {
    return x + 1;
}
