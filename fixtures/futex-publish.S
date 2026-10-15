/* Copyright 2026 Irvinwop. SPDX-License-Identifier: Apache-2.0 */
#ifndef EDSL_FUTEX_CLIENT_PAYLOAD
#define EDSL_FUTEX_CLIENT_PAYLOAD 0x11223344
#endif
#ifndef EDSL_FUTEX_CLIENT_STORE
#define EDSL_FUTEX_CLIENT_STORE 0x06
#endif
#ifndef EDSL_FUTEX_CLIENT_EXCHANGE_VALUE
#define EDSL_FUTEX_CLIENT_EXCHANGE_VALUE 1
#endif
#ifndef EDSL_FUTEX_CLIENT_EXCHANGE
#define EDSL_FUTEX_CLIENT_EXCHANGE 0x07
#endif
#ifndef EDSL_FUTEX_CLIENT_WAKE_COUNT
#define EDSL_FUTEX_CLIENT_WAKE_COUNT 1
#endif
#ifndef EDSL_FUTEX_CLIENT_RETURN
#define EDSL_FUTEX_CLIENT_RETURN 0xc3
#endif
.section .text.edsl_futex_publish_stub,"ax",@progbits
.globl edsl_futex_publish_stub
.type edsl_futex_publish_stub,@function
edsl_futex_publish_stub:
    movl $EDSL_FUTEX_CLIENT_PAYLOAD, %eax
    .byte 0x89, EDSL_FUTEX_CLIENT_STORE /* STORE [RSI], EAX */
    movl $EDSL_FUTEX_CLIENT_EXCHANGE_VALUE, %eax
    .byte 0x87, EDSL_FUTEX_CLIENT_EXCHANGE /* XCHG [RDI], EAX */
    movl $202, %eax
    movl $129, %esi
    movl $EDSL_FUTEX_CLIENT_WAKE_COUNT, %edx
    syscall
    .byte EDSL_FUTEX_CLIENT_RETURN
.size edsl_futex_publish_stub,.-edsl_futex_publish_stub
.section .note.GNU-stack,"",@progbits
