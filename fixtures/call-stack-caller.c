#include <stdint.h>

extern uint64_t helper(uint64_t x);

uint64_t caller(uint64_t x) {
    return helper(x) + 1;
}
