#if !defined(__cplusplus) || __cplusplus <= 202302L
#error "The C++ compiler must select the C++26 language mode."
#endif

#ifdef __STRICT_ANSI__
#error "GNU extensions must remain enabled."
#endif

#include <atomic>

// Compile-only capability probe, not an eDSL API or runtime implementation.
int edsl_toolchain_gnucxx26(std::atomic<int>& value)
{
    return ({
        auto previous = value.fetch_add(1, std::memory_order_relaxed);
        previous;
    });
}
