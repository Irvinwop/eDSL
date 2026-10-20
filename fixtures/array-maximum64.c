#include <stdint.h>
uint64_t maximum64_array(const uint64_t *data, uint64_t count)
{
    uint64_t result = 0;
    for (uint64_t i = 0; i < count; ++i)
        if (data[i] > result)
            result = data[i];
    return result;
}
