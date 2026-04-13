// Test: LDR + REV32 byte swap for SHA-256 message data.
// Loads 16 bytes, reverses bytes within each 32-bit lane.

        .text
        .globl sha256_rev32_test
        .type sha256_rev32_test, %function
        .align 4

sha256_rev32_test:
        ldr     q4, [x0]
        rev32   v4.16b, v4.16b
        ret

        .size sha256_rev32_test, .-sha256_rev32_test
