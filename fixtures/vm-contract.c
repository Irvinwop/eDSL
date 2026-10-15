/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#include <errno.h>
#include <signal.h>
#include <stdint.h>
#include <stdio.h>
#include <sys/mman.h>
#include <sys/resource.h>
#include <sys/wait.h>
#include <unistd.h>

/* Owned negative probes: a child checks that Linux denies the access; the
 * parent checks the signal and keeps testing the neighboring mapping. These
 * are contract-conformance observations, not a proof of a kernel build. */
static int expect_denied(volatile unsigned char *address, int write_access)
{
    pid_t child = fork();
    if (child < 0)
        return 2;
    if (child == 0) {
        if (write_access)
            *address = 0x7b;
        else {
            volatile unsigned char observed = *address;
            (void)observed;
        }
        _exit(1);
    }
    int status;
    while (waitpid(child, &status, 0) < 0) {
        if (errno != EINTR)
            return 2;
    }
    if (!WIFSIGNALED(status) || WTERMSIG(status) != SIGSEGV) {
        fprintf(stderr, "expected SIGSEGV for a denied %s, got status %d\n",
                write_access ? "write" : "read", status);
        return 1;
    }
    return 0;
}

int main(void)
{
    /* Negative fixtures must not leave crash dumps in the checkout/artifacts. */
    const struct rlimit no_core = {0, 0};
    if (setrlimit(RLIMIT_CORE, &no_core) != 0)
        return 2;
    long page_size = sysconf(_SC_PAGESIZE);
    if (page_size < 16 || (uintmax_t)page_size > SIZE_MAX / 2)
        return 2;
    size_t page = (size_t)page_size;
    unsigned char *memory = mmap(NULL, page * 2, PROT_READ | PROT_WRITE,
                                 MAP_PRIVATE | MAP_ANONYMOUS, -1, 0);
    if (memory == MAP_FAILED)
        return 2;
    int result = 0;
    for (size_t i = 0; i < page * 2; ++i) {
        if (memory[i] != 0) {
            fprintf(stderr, "anonymous mapping was not zero initialized\n");
            result = 1;
            goto cleanup_both;
        }
    }
    memory[0] = 0x31;
    memory[page] = 0xd6;
    if (mprotect(memory, page, PROT_READ) != 0) {
        result = 2;
        goto cleanup_both;
    }
    result = expect_denied(memory, 1);
    if (result != 0)
        goto cleanup_both;
    if (memory[0] != 0x31 || memory[page] != 0xd6) {
        result = 1;
        goto cleanup_both;
    }
    if (mprotect(memory, page, PROT_NONE) != 0) {
        result = 2;
        goto cleanup_both;
    }
    result = expect_denied(memory, 0);
    if (result != 0)
        goto cleanup_both;
    memory[page] = 0x68;
    if (mprotect(memory, page, PROT_READ) != 0) {
        result = 2;
        goto cleanup_both;
    }
    if (memory[0] != 0x31 || memory[page] != 0x68) {
        result = 1;
        goto cleanup_both;
    }
    if (munmap(memory, page) != 0) {
        result = 2;
        goto cleanup_both;
    }
    result = expect_denied(memory, 0);
    if (memory[page] != 0x68)
        result = 1;
    if (munmap(memory + page, page) != 0)
        return 2;
    if (result == 0)
        puts("Linux mapping/protection/unmapping contract probes passed");
    return result;

cleanup_both:
    if (munmap(memory, page * 2) != 0)
        return 2;
    return result;
}
