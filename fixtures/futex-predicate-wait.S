.section .text.edsl_futex_predicate_wait_stub,"ax",@progbits
.globl edsl_futex_predicate_wait_stub
.type edsl_futex_predicate_wait_stub,@function
edsl_futex_predicate_wait_stub:
.Lretry:
    movl (%rdi), %eax
    cmpl $0, %eax
    jne .Ldone
    movl $202, %eax
    movl $128, %esi
    syscall
    movl $1, %eax
    cmpl $0, %eax
    jne .Lretry
.Ldone:
    ret
.size edsl_futex_predicate_wait_stub,.-edsl_futex_predicate_wait_stub
.section .note.GNU-stack,"",@progbits
