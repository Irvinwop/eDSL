.text
.globl edsl_futex_predicate_probe
.type edsl_futex_predicate_probe,@function
edsl_futex_predicate_probe:
    pushq %rbx
    pushq %rbp
    pushq %r12
    pushq %r13
    pushq %r14
    pushq %r15
    subq $488, %rsp
    movq %rdi, 432(%rsp)
    movq %rsi, 440(%rsp)
    movq %rdx, 448(%rsp)
    movq %rcx, 456(%rsp)
    movq %r8, 464(%rsp)
    movq %rsp, 120(%rsp)
    leaq .Lreturned(%rip), %rax
    movq %rax, 136(%rsp)
    movabsq $0x13579bdf2468ace0, %rax
    movq %rax, 184(%rsp)
    movabsq $0xabcdef0198765432, %rax
    movq %rax, 192(%rsp)
    movabsq $0x0123456789abcdef, %rax
    movq %rax, 200(%rsp)
    movabsq $0xfedcba9876543210, %rax
    movq %rax, 208(%rsp)
    movabsq $0xa15b26c37d48e9f0, %rax
    movq %rax, -16(%rsp)
    movq %rax, 248(%rsp)
    movabsq $0xb26c37d48e59f001, %rax
    movq %rax, -24(%rsp)
    movq %rax, 256(%rsp)
    movabsq $0xc37d48e59f600112, %rax
    movq %rax, -32(%rsp)
    movq %rax, 264(%rsp)
    movabsq $0xd48e59f600711223, %rax
    movq %rax, -40(%rsp)
    movq %rax, 272(%rsp)
    movabsq $0x1122334455667788, %rbx
    movabsq $0x2233445566778899, %rbp
    movabsq $0x33445566778899aa, %r12
    movabsq $0x445566778899aabb, %r13
    movabsq $0x5566778899aabbcc, %r14
    movabsq $0x66778899aabbccdd, %r15
    xorl %r8d, %r8d
    xorl %r9d, %r9d
    movabsq $0x99aabbccddeeff00, %rcx
    movabsq $0xaabbccddeeff0011, %r11
    movq 440(%rsp), %rdi
    movq 464(%rsp), %rsi
    xorl %edx, %edx
    xorl %r10d, %r10d
    xorl %eax, %eax
    pushfq
    popq 152(%rsp)
    movabsq $0xbbccddeeff001122, %rax
    movq %rax, 312(%rsp)
    movq %rbx, 320(%rsp)
    movq %rcx, 328(%rsp)
    movq %rdx, 336(%rsp)
    movq %rsi, 344(%rsp)
    movq %rdi, 352(%rsp)
    movq %rbp, 360(%rsp)
    movq %r8, 368(%rsp)
    movq %r9, 376(%rsp)
    movq %r10, 384(%rsp)
    movq %r11, 392(%rsp)
    movq %r12, 400(%rsp)
    movq %r13, 408(%rsp)
    movq %r14, 416(%rsp)
    movq %r15, 424(%rsp)
    call *432(%rsp)
.Lreturned:
    movq %rax, 0(%rsp)
    movq %rbx, 8(%rsp)
    movq %rcx, 16(%rsp)
    movq %rdx, 24(%rsp)
    movq %rsi, 32(%rsp)
    movq %rdi, 40(%rsp)
    movq %rbp, 48(%rsp)
    movq %r8, 56(%rsp)
    movq %r9, 64(%rsp)
    movq %r10, 72(%rsp)
    movq %r11, 80(%rsp)
    movq %r12, 88(%rsp)
    movq %r13, 96(%rsp)
    movq %r14, 104(%rsp)
    movq %r15, 112(%rsp)
    movq %rsp, 128(%rsp)
    movq -8(%rsp), %rax
    movq %rax, 144(%rsp)
    movq -16(%rsp), %rax
    movq %rax, 280(%rsp)
    movq -24(%rsp), %rax
    movq %rax, 288(%rsp)
    movq -32(%rsp), %rax
    movq %rax, 296(%rsp)
    movq -40(%rsp), %rax
    movq %rax, 304(%rsp)
    pushfq
    popq 160(%rsp)
    movq 184(%rsp), %rax
    movq %rax, 216(%rsp)
    movq 192(%rsp), %rax
    movq %rax, 224(%rsp)
    movq 200(%rsp), %rax
    movq %rax, 232(%rsp)
    movq 208(%rsp), %rax
    movq %rax, 240(%rsp)
    movq 440(%rsp), %rax
    movl (%rax), %eax
    movq %rax, 168(%rsp)
    movq 448(%rsp), %rax
    movl (%rax), %eax
    movq %rax, 176(%rsp)
    movq 456(%rsp), %rdi
    movq %rsp, %rsi
    movl $54, %ecx
    cld
    rep movsq
    addq $488, %rsp
    popq %r15
    popq %r14
    popq %r13
    popq %r12
    popq %rbp
    popq %rbx
    ret
.size edsl_futex_predicate_probe,.-edsl_futex_predicate_probe

.globl edsl_futex_predicate_wake_one
.type edsl_futex_predicate_wake_one,@function
edsl_futex_predicate_wake_one:
    movl $202, %eax
    movl $129, %esi
    movl $1, %edx
    xorl %r10d, %r10d
    xorl %r8d, %r8d
    xorl %r9d, %r9d
    syscall
    ret
.size edsl_futex_predicate_wake_one,.-edsl_futex_predicate_wake_one
.section .note.GNU-stack,"",@progbits
