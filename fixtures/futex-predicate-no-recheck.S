.section .text.edsl_futex_predicate_no_recheck_stub,"ax",@progbits
.globl edsl_futex_predicate_no_recheck_stub
.type edsl_futex_predicate_no_recheck_stub,@function
edsl_futex_predicate_no_recheck_stub:
    movl (%rdi), %eax
    cmpl $0, %eax
    jne .Ldone
    movl $202, %eax
    movl $128, %esi
    syscall
    movl $1, %eax
    cmpl $0, %eax
    jne .Ldone
.Ldone:
    ret
.size edsl_futex_predicate_no_recheck_stub,.-edsl_futex_predicate_no_recheck_stub
.section .note.GNU-stack,"",@progbits
