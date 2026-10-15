#if !defined(__STDC_VERSION__) || __STDC_VERSION__ < 202311L
#error "The C compiler must select the C23 language mode."
#endif

#ifdef __STRICT_ANSI__
#error "GNU extensions must remain enabled."
#endif

#include <stdatomic.h>

/* Compile-only capability probe, not an eDSL API or runtime implementation. */
int edsl_toolchain_gnu23(_Atomic(int) *value)
{
    return ({
        typeof(0) previous = atomic_fetch_add_explicit(value, 1, memory_order_relaxed);
        previous;
    });
}
