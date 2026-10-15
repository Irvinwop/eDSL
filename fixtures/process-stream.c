/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#define _GNU_SOURCE
#include <errno.h>
#include <fcntl.h>
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <sys/types.h>
#include <sys/wait.h>
#include <unistd.h>

static void fail(const char *message)
{
    fprintf(stderr, "process stream check: %s\n", message);
    exit(1);
}

static pid_t launch(const char *executable, int reader, int writer)
{
    pid_t child = fork();
    if (child < 0) fail("fork failed");
    if (child == 0) {
        if (dup2(writer, STDOUT_FILENO) < 0) _exit(126);
        if (reader != STDOUT_FILENO) close(reader);
        if (writer != STDOUT_FILENO) close(writer);
        execl(executable, executable, (char *)NULL);
        _exit(127);
    }
    return child;
}

static void expect_exit42(pid_t child)
{
    int status;
    pid_t waited;
    do { waited = waitpid(child, &status, 0); } while (waited < 0 && errno == EINTR);
    if (waited != child || !WIFEXITED(status) || WEXITSTATUS(status) != 42)
        fail("owned process did not exit with status 42");
}

static void full_write(const char *executable)
{
    int stream[2];
    if (pipe(stream) != 0) fail("pipe failed");
    pid_t child = launch(executable, stream[0], stream[1]);
    close(stream[1]);
    unsigned char observed[16];
    size_t length = 0;
    for (;;) {
        ssize_t count = read(stream[0], observed + length, sizeof observed - length);
        if (count < 0 && errno == EINTR) continue;
        if (count < 0) fail("pipe read failed");
        if (count == 0) break;
        length += (size_t)count;
        if (length == sizeof observed) fail("unexpected extra output");
    }
    close(stream[0]);
    expect_exit42(child);
    if (length != 3 || memcmp(observed, "OK\n", 3) != 0)
        fail("successful stream output differs from independent OK/newline contract");
}

static void failed_write(const char *executable)
{
    int stream[2];
    if (pipe2(stream, O_NONBLOCK) != 0) fail("nonblocking pipe failed");
    unsigned char block[4096];
    memset(block, 0xa5, sizeof block);
    size_t filled = 0;
    for (;;) {
        ssize_t count = write(stream[1], block, sizeof block);
        if (count < 0 && errno == EINTR) continue;
        if (count < 0 && errno == EAGAIN) break;
        if (count <= 0) fail("pipe fill failed");
        filled += (size_t)count;
    }
    /* A one-byte probe ensures even a three-byte write cannot fit. Keep the
       reader idle until the child finishes, so the actual syscall must fail. */
    while (write(stream[1], block, 1) == 1) ++filled;
    if (errno != EAGAIN) fail("pipe capacity probe failed");
    pid_t child = launch(executable, stream[0], stream[1]);
    expect_exit42(child);
    close(stream[1]);
    size_t drained = 0;
    for (;;) {
        ssize_t count = read(stream[0], block, sizeof block);
        if (count < 0 && errno == EINTR) continue;
        if (count < 0) fail("pipe drain failed");
        if (count == 0) break;
        for (ssize_t index = 0; index < count; ++index)
            if (block[index] != 0xa5) fail("failed write changed existing stream bytes");
        drained += (size_t)count;
    }
    close(stream[0]);
    if (drained != filled) fail("failed write changed stream length");
}

int main(int argc, char **argv)
{
    if (argc != 2) fail("expected an owned write-exit42 ELF path");
    full_write(argv[1]);
    failed_write(argv[1]);
    puts("Native stream success and actual EAGAIN paths both exit 42");
    return 0;
}
