
    .globl sum8
sum8:
    addi sp, sp, -96
    sw s0, 0(sp)
    sw s1, 4(sp)
    sw s2, 8(sp)
    sw s3, 12(sp)
    sw s4, 16(sp)
    sw s5, 20(sp)
    sw s6, 24(sp)
    sw s7, 28(sp)
    sw s8, 32(sp)
    sw s9, 36(sp)
    sw s10, 40(sp)
    sw s11, 44(sp)
    sw ra, 48(sp)

    sw a0, 52(sp)
    sw a1, 56(sp)
    sw a2, 60(sp)
    sw a3, 64(sp)
    sw a4, 68(sp)
    sw a5, 72(sp)
    sw a6, 76(sp)
    sw a7, 80(sp)

    lw t0, 52(sp)
    lw t1, 56(sp)
add t2, t0, t1
    lw t1, 60(sp)
add t2, t2, t1
    lw t1, 64(sp)
add t2, t2, t1
    lw t1, 68(sp)
add t2, t2, t1
    lw t1, 72(sp)
add t2, t2, t1
    lw t1, 76(sp)
add t2, t2, t1
    lw t1, 80(sp)
add t2, t2, t1
    mv a0, t2
    lw ra, 48(sp)
    lw s11, 44(sp)
    lw s10, 40(sp)
    lw s9, 36(sp)
    lw s8, 32(sp)
    lw s7, 28(sp)
    lw s6, 24(sp)
    lw s5, 20(sp)
    lw s4, 16(sp)
    lw s3, 12(sp)
    lw s2, 8(sp)
    lw s1, 4(sp)
    lw s0, 0(sp)
    addi sp, sp, 96
    ret



    .globl sum16
sum16:
    addi sp, sp, -128
    sw s0, 0(sp)
    sw s1, 4(sp)
    sw s2, 8(sp)
    sw s3, 12(sp)
    sw s4, 16(sp)
    sw s5, 20(sp)
    sw s6, 24(sp)
    sw s7, 28(sp)
    sw s8, 32(sp)
    sw s9, 36(sp)
    sw s10, 40(sp)
    sw s11, 44(sp)
    sw ra, 48(sp)

    sw a0, 52(sp)
    sw a1, 56(sp)
    sw a2, 60(sp)
    sw a3, 64(sp)
    sw a4, 68(sp)
    sw a5, 72(sp)
    sw a6, 76(sp)
    sw a7, 80(sp)
    lw t0, 0(sp)
    sw t0, 84(sp)
    lw t0, 4(sp)
    sw t0, 88(sp)
    lw t0, 8(sp)
    sw t0, 92(sp)
    lw t0, 12(sp)
    sw t0, 96(sp)
    lw t0, 16(sp)
    sw t0, 100(sp)
    lw t0, 20(sp)
    sw t0, 104(sp)
    lw t0, 24(sp)
    sw t0, 108(sp)
    lw t0, 28(sp)
    sw t0, 112(sp)

    lw t0, 52(sp)
    lw t1, 56(sp)
add t2, t0, t1
    lw t1, 60(sp)
add t2, t2, t1
    lw t1, 64(sp)
add t2, t2, t1
    lw t1, 68(sp)
add t2, t2, t1
    lw t1, 72(sp)
add t2, t2, t1
    lw t1, 76(sp)
add t2, t2, t1
    lw t1, 80(sp)
add t2, t2, t1
    lw t1, 84(sp)
add t2, t2, t1
    lw t1, 88(sp)
add t2, t2, t1
    lw t1, 92(sp)
add t2, t2, t1
    lw t1, 96(sp)
add t2, t2, t1
    lw t1, 100(sp)
add t2, t2, t1
    lw t1, 104(sp)
add t2, t2, t1
    lw t1, 108(sp)
add t2, t2, t1
    lw t1, 112(sp)
add t2, t2, t1
    mv a0, t2
    lw ra, 48(sp)
    lw s11, 44(sp)
    lw s10, 40(sp)
    lw s9, 36(sp)
    lw s8, 32(sp)
    lw s7, 28(sp)
    lw s6, 24(sp)
    lw s5, 20(sp)
    lw s4, 16(sp)
    lw s3, 12(sp)
    lw s2, 8(sp)
    lw s1, 4(sp)
    lw s0, 0(sp)
    addi sp, sp, 128
    ret



    .globl sum32
sum32:
    addi sp, sp, -192
    sw s0, 0(sp)
    sw s1, 4(sp)
    sw s2, 8(sp)
    sw s3, 12(sp)
    sw s4, 16(sp)
    sw s5, 20(sp)
    sw s6, 24(sp)
    sw s7, 28(sp)
    sw s8, 32(sp)
    sw s9, 36(sp)
    sw s10, 40(sp)
    sw s11, 44(sp)
    sw ra, 48(sp)

    sw a0, 52(sp)
    sw a1, 56(sp)
    sw a2, 60(sp)
    sw a3, 64(sp)
    sw a4, 68(sp)
    sw a5, 72(sp)
    sw a6, 76(sp)
    sw a7, 80(sp)
    lw t0, 0(sp)
    sw t0, 84(sp)
    lw t0, 4(sp)
    sw t0, 88(sp)
    lw t0, 8(sp)
    sw t0, 92(sp)
    lw t0, 12(sp)
    sw t0, 96(sp)
    lw t0, 16(sp)
    sw t0, 100(sp)
    lw t0, 20(sp)
    sw t0, 104(sp)
    lw t0, 24(sp)
    sw t0, 108(sp)
    lw t0, 28(sp)
    sw t0, 112(sp)
    lw t0, 32(sp)
    sw t0, 116(sp)
    lw t0, 36(sp)
    sw t0, 120(sp)
    lw t0, 40(sp)
    sw t0, 124(sp)
    lw t0, 44(sp)
    sw t0, 128(sp)
    lw t0, 48(sp)
    sw t0, 132(sp)
    lw t0, 52(sp)
    sw t0, 136(sp)
    lw t0, 56(sp)
    sw t0, 140(sp)
    lw t0, 60(sp)
    sw t0, 144(sp)
    lw t0, 64(sp)
    sw t0, 148(sp)
    lw t0, 68(sp)
    sw t0, 152(sp)
    lw t0, 72(sp)
    sw t0, 156(sp)
    lw t0, 76(sp)
    sw t0, 160(sp)
    lw t0, 80(sp)
    sw t0, 164(sp)
    lw t0, 84(sp)
    sw t0, 168(sp)
    lw t0, 88(sp)
    sw t0, 172(sp)
    lw t0, 92(sp)
    sw t0, 176(sp)

    lw t0, 52(sp)
    lw t1, 56(sp)
add t2, t0, t1
    lw t1, 60(sp)
add t2, t2, t1
    lw t1, 64(sp)
add t2, t2, t1
    lw t1, 68(sp)
add t2, t2, t1
    lw t1, 72(sp)
add t2, t2, t1
    lw t1, 76(sp)
add t2, t2, t1
    lw t1, 80(sp)
add t2, t2, t1
    sw t2, 180(sp)
    lw t0, 84(sp)
    lw t1, 88(sp)
add t2, t0, t1
    lw t1, 92(sp)
add t2, t2, t1
    lw t1, 96(sp)
add t2, t2, t1
    lw t1, 100(sp)
add t2, t2, t1
    lw t1, 104(sp)
add t2, t2, t1
    lw t1, 108(sp)
add t2, t2, t1
    lw t1, 112(sp)
add t2, t2, t1
    sw t2, 184(sp)
    lw t0, 116(sp)
    lw t1, 120(sp)
add t2, t0, t1
    lw t1, 124(sp)
add t2, t2, t1
    lw t1, 128(sp)
add t2, t2, t1
    lw t1, 132(sp)
add t2, t2, t1
    lw t1, 136(sp)
add t2, t2, t1
    lw t1, 140(sp)
add t2, t2, t1
    lw t1, 144(sp)
add t2, t2, t1
    sw t2, 188(sp)
    lw t0, 148(sp)
    lw t1, 152(sp)
add t2, t0, t1
    lw t1, 156(sp)
add t2, t2, t1
    lw t1, 160(sp)
add t2, t2, t1
    lw t1, 164(sp)
add t2, t2, t1
    lw t1, 168(sp)
add t2, t2, t1
    lw t1, 172(sp)
add t2, t2, t1
    lw t1, 176(sp)
add t2, t2, t1
    sw t2, 192(sp)
    lw t0, 180(sp)
    lw t1, 184(sp)
add t2, t0, t1
    lw t1, 188(sp)
add t2, t2, t1
    lw t1, 192(sp)
add t2, t2, t1
    mv a0, t2
    lw ra, 48(sp)
    lw s11, 44(sp)
    lw s10, 40(sp)
    lw s9, 36(sp)
    lw s8, 32(sp)
    lw s7, 28(sp)
    lw s6, 24(sp)
    lw s5, 20(sp)
    lw s4, 16(sp)
    lw s3, 12(sp)
    lw s2, 8(sp)
    lw s1, 4(sp)
    lw s0, 0(sp)
    addi sp, sp, 192
    ret



    .globl sum64
sum64:
    addi sp, sp, -320
    sw s0, 0(sp)
    sw s1, 4(sp)
    sw s2, 8(sp)
    sw s3, 12(sp)
    sw s4, 16(sp)
    sw s5, 20(sp)
    sw s6, 24(sp)
    sw s7, 28(sp)
    sw s8, 32(sp)
    sw s9, 36(sp)
    sw s10, 40(sp)
    sw s11, 44(sp)
    sw ra, 48(sp)

    sw a0, 52(sp)
    sw a1, 56(sp)
    sw a2, 60(sp)
    sw a3, 64(sp)
    sw a4, 68(sp)
    sw a5, 72(sp)
    sw a6, 76(sp)
    sw a7, 80(sp)
    lw t0, 0(sp)
    sw t0, 84(sp)
    lw t0, 4(sp)
    sw t0, 88(sp)
    lw t0, 8(sp)
    sw t0, 92(sp)
    lw t0, 12(sp)
    sw t0, 96(sp)
    lw t0, 16(sp)
    sw t0, 100(sp)
    lw t0, 20(sp)
    sw t0, 104(sp)
    lw t0, 24(sp)
    sw t0, 108(sp)
    lw t0, 28(sp)
    sw t0, 112(sp)
    lw t0, 32(sp)
    sw t0, 116(sp)
    lw t0, 36(sp)
    sw t0, 120(sp)
    lw t0, 40(sp)
    sw t0, 124(sp)
    lw t0, 44(sp)
    sw t0, 128(sp)
    lw t0, 48(sp)
    sw t0, 132(sp)
    lw t0, 52(sp)
    sw t0, 136(sp)
    lw t0, 56(sp)
    sw t0, 140(sp)
    lw t0, 60(sp)
    sw t0, 144(sp)
    lw t0, 64(sp)
    sw t0, 148(sp)
    lw t0, 68(sp)
    sw t0, 152(sp)
    lw t0, 72(sp)
    sw t0, 156(sp)
    lw t0, 76(sp)
    sw t0, 160(sp)
    lw t0, 80(sp)
    sw t0, 164(sp)
    lw t0, 84(sp)
    sw t0, 168(sp)
    lw t0, 88(sp)
    sw t0, 172(sp)
    lw t0, 92(sp)
    sw t0, 176(sp)
    lw t0, 96(sp)
    sw t0, 180(sp)
    lw t0, 100(sp)
    sw t0, 184(sp)
    lw t0, 104(sp)
    sw t0, 188(sp)
    lw t0, 108(sp)
    sw t0, 192(sp)
    lw t0, 112(sp)
    sw t0, 196(sp)
    lw t0, 116(sp)
    sw t0, 200(sp)
    lw t0, 120(sp)
    sw t0, 204(sp)
    lw t0, 124(sp)
    sw t0, 208(sp)
    lw t0, 128(sp)
    sw t0, 212(sp)
    lw t0, 132(sp)
    sw t0, 216(sp)
    lw t0, 136(sp)
    sw t0, 220(sp)
    lw t0, 140(sp)
    sw t0, 224(sp)
    lw t0, 144(sp)
    sw t0, 228(sp)
    lw t0, 148(sp)
    sw t0, 232(sp)
    lw t0, 152(sp)
    sw t0, 236(sp)
    lw t0, 156(sp)
    sw t0, 240(sp)
    lw t0, 160(sp)
    sw t0, 244(sp)
    lw t0, 164(sp)
    sw t0, 248(sp)
    lw t0, 168(sp)
    sw t0, 252(sp)
    lw t0, 172(sp)
    sw t0, 256(sp)
    lw t0, 176(sp)
    sw t0, 260(sp)
    lw t0, 180(sp)
    sw t0, 264(sp)
    lw t0, 184(sp)
    sw t0, 268(sp)
    lw t0, 188(sp)
    sw t0, 272(sp)
    lw t0, 192(sp)
    sw t0, 276(sp)
    lw t0, 196(sp)
    sw t0, 280(sp)
    lw t0, 200(sp)
    sw t0, 284(sp)
    lw t0, 204(sp)
    sw t0, 288(sp)
    lw t0, 208(sp)
    sw t0, 292(sp)
    lw t0, 212(sp)
    sw t0, 296(sp)
    lw t0, 216(sp)
    sw t0, 300(sp)
    lw t0, 220(sp)
    sw t0, 304(sp)

    lw t0, 52(sp)
    lw t1, 56(sp)
add t2, t0, t1
    lw t1, 60(sp)
add t2, t2, t1
    lw t1, 64(sp)
add t2, t2, t1
    lw t1, 68(sp)
add t2, t2, t1
    lw t1, 72(sp)
add t2, t2, t1
    lw t1, 76(sp)
add t2, t2, t1
    lw t1, 80(sp)
add t2, t2, t1
    sw t2, 308(sp)
    lw t0, 84(sp)
    lw t1, 88(sp)
add t2, t0, t1
    lw t1, 92(sp)
add t2, t2, t1
    lw t1, 96(sp)
add t2, t2, t1
    lw t1, 100(sp)
add t2, t2, t1
    lw t1, 104(sp)
add t2, t2, t1
    lw t1, 108(sp)
add t2, t2, t1
    lw t1, 112(sp)
add t2, t2, t1
    sw t2, 312(sp)
    lw t0, 116(sp)
    lw t1, 120(sp)
add t2, t0, t1
    lw t1, 124(sp)
add t2, t2, t1
    lw t1, 128(sp)
add t2, t2, t1
    lw t1, 132(sp)
add t2, t2, t1
    lw t1, 136(sp)
add t2, t2, t1
    lw t1, 140(sp)
add t2, t2, t1
    lw t1, 144(sp)
add t2, t2, t1
    sw t2, 316(sp)
    lw t0, 148(sp)
    lw t1, 152(sp)
add t2, t0, t1
    lw t1, 156(sp)
add t2, t2, t1
    lw t1, 160(sp)
add t2, t2, t1
    lw t1, 164(sp)
add t2, t2, t1
    lw t1, 168(sp)
add t2, t2, t1
    lw t1, 172(sp)
add t2, t2, t1
    lw t1, 176(sp)
add t2, t2, t1
    sw t2, 320(sp)
    lw t0, 180(sp)
    lw t1, 184(sp)
add t2, t0, t1
    lw t1, 188(sp)
add t2, t2, t1
    lw t1, 192(sp)
add t2, t2, t1
    lw t1, 196(sp)
add t2, t2, t1
    lw t1, 200(sp)
add t2, t2, t1
    lw t1, 204(sp)
add t2, t2, t1
    lw t1, 208(sp)
add t2, t2, t1
    sw t2, 324(sp)
    lw t0, 212(sp)
    lw t1, 216(sp)
add t2, t0, t1
    lw t1, 220(sp)
add t2, t2, t1
    lw t1, 224(sp)
add t2, t2, t1
    lw t1, 228(sp)
add t2, t2, t1
    lw t1, 232(sp)
add t2, t2, t1
    lw t1, 236(sp)
add t2, t2, t1
    lw t1, 240(sp)
add t2, t2, t1
    sw t2, 328(sp)
    lw t0, 244(sp)
    lw t1, 248(sp)
add t2, t0, t1
    lw t1, 252(sp)
add t2, t2, t1
    lw t1, 256(sp)
add t2, t2, t1
    lw t1, 260(sp)
add t2, t2, t1
    lw t1, 264(sp)
add t2, t2, t1
    lw t1, 268(sp)
add t2, t2, t1
    lw t1, 272(sp)
add t2, t2, t1
    sw t2, 332(sp)
    lw t0, 276(sp)
    lw t1, 280(sp)
add t2, t0, t1
    lw t1, 284(sp)
add t2, t2, t1
    lw t1, 288(sp)
add t2, t2, t1
    lw t1, 292(sp)
add t2, t2, t1
    lw t1, 296(sp)
add t2, t2, t1
    lw t1, 300(sp)
add t2, t2, t1
    lw t1, 304(sp)
add t2, t2, t1
    sw t2, 336(sp)
    lw t0, 308(sp)
    lw t1, 312(sp)
add t2, t0, t1
    lw t1, 316(sp)
add t2, t2, t1
    lw t1, 320(sp)
add t2, t2, t1
    lw t1, 324(sp)
add t2, t2, t1
    lw t1, 328(sp)
add t2, t2, t1
    lw t1, 332(sp)
add t2, t2, t1
    lw t1, 336(sp)
add t2, t2, t1
    mv a0, t2
    lw ra, 48(sp)
    lw s11, 44(sp)
    lw s10, 40(sp)
    lw s9, 36(sp)
    lw s8, 32(sp)
    lw s7, 28(sp)
    lw s6, 24(sp)
    lw s5, 20(sp)
    lw s4, 16(sp)
    lw s3, 12(sp)
    lw s2, 8(sp)
    lw s1, 4(sp)
    lw s0, 0(sp)
    addi sp, sp, 320
    ret



    .globl main
main:
    addi sp, sp, -64
    sw s0, 0(sp)
    sw s1, 4(sp)
    sw s2, 8(sp)
    sw s3, 12(sp)
    sw s4, 16(sp)
    sw s5, 20(sp)
    sw s6, 24(sp)
    sw s7, 28(sp)
    sw s8, 32(sp)
    sw s9, 36(sp)
    sw s10, 40(sp)
    sw s11, 44(sp)
    sw ra, 48(sp)


    li t0, 1
    sw t0, 52(sp)
    li t0, 2
    sw t0, 56(sp)
    li t0, 3
    sw t0, 60(sp)
    li t0, 4
    sw t0, 64(sp)
    li t0, 5
    sw t0, 68(sp)
    li t0, 6
    sw t0, 72(sp)
    li t0, 7
    sw t0, 76(sp)
    li t0, 8
    sw t0, 80(sp)
    li t0, 9
    sw t0, 84(sp)
    li t0, 10
    sw t0, 88(sp)
    li t0, 11
    sw t0, 92(sp)
    li t0, 12
    sw t0, 96(sp)
    li t0, 13
    sw t0, 100(sp)
    li t0, 14
    sw t0, 104(sp)
    li t0, 15
    sw t0, 108(sp)
    li t0, 16
    sw t0, 112(sp)
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t0, 52(sp)
    mv a0, t0    li t0, 1
    mv a1, t0    lw t0, 60(sp)
    mv a2, t0    li t0, 2
    mv a3, t0    lw t0, 68(sp)
    mv a4, t0    li t0, 3
    mv a5, t0    lw t0, 76(sp)
    mv a6, t0    li t0, 4
    mv a7, t0    call sum8
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t0, a0
    sw t0, 116(sp)
    addi sp, sp, -64
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t0, 52(sp)
    mv a0, t0    lw t0, 56(sp)
    mv a1, t0    lw t0, 60(sp)
    mv a2, t0    lw t0, 64(sp)
    mv a3, t0    lw t0, 68(sp)
    mv a4, t0    lw t0, 72(sp)
    mv a5, t0    lw t0, 76(sp)
    mv a6, t0    lw t0, 80(sp)
    mv a7, t0    li t0, 1
    sw t0, 28(sp)    li t0, 2
    sw t0, 32(sp)    li t0, 3
    sw t0, 36(sp)    li t0, 4
    sw t0, 40(sp)    lw t0, 116(sp)
    lw t1, 100(sp)
add t2, t0, t1
    sw t2, 44(sp)    lw t0, 116(sp)
    lw t1, 104(sp)
add t2, t0, t1
    sw t2, 48(sp)    lw t0, 116(sp)
    lw t1, 108(sp)
add t2, t0, t1
    sw t2, 52(sp)    lw t0, 116(sp)
    lw t1, 112(sp)
add t2, t0, t1
    sw t2, 56(sp)    call sum16
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 64
    mv t0, a0
    sw t0, 120(sp)
    li t0, 17
    sw t0, 124(sp)
    li t0, 18
    sw t0, 128(sp)
    li t0, 19
    sw t0, 132(sp)
    li t0, 20
    sw t0, 136(sp)
    li t0, 21
    sw t0, 140(sp)
    li t0, 22
    sw t0, 144(sp)
    li t0, 23
    sw t0, 148(sp)
    li t0, 24
    sw t0, 152(sp)
    li t0, 25
    sw t0, 156(sp)
    li t0, 26
    sw t0, 160(sp)
    li t0, 27
    sw t0, 164(sp)
    li t0, 28
    sw t0, 168(sp)
    li t0, 29
    sw t0, 172(sp)
    li t0, 30
    sw t0, 176(sp)
    li t0, 31
    sw t0, 180(sp)
    li t0, 32
    sw t0, 184(sp)
    addi sp, sp, -128
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t0, 52(sp)
    mv a0, t0    lw t0, 56(sp)
    mv a1, t0    lw t0, 60(sp)
    mv a2, t0    lw t0, 64(sp)
    mv a3, t0    lw t0, 68(sp)
    mv a4, t0    lw t0, 72(sp)
    mv a5, t0    lw t0, 76(sp)
    mv a6, t0    lw t0, 80(sp)
    mv a7, t0    lw t0, 84(sp)
    sw t0, 28(sp)    lw t0, 88(sp)
    sw t0, 32(sp)    lw t0, 92(sp)
    sw t0, 36(sp)    lw t0, 96(sp)
    sw t0, 40(sp)    lw t0, 100(sp)
    sw t0, 44(sp)    lw t0, 104(sp)
    sw t0, 48(sp)    lw t0, 108(sp)
    sw t0, 52(sp)    lw t0, 112(sp)
    sw t0, 56(sp)    lw t0, 124(sp)
    sw t0, 60(sp)    lw t0, 128(sp)
    sw t0, 64(sp)    lw t0, 132(sp)
    sw t0, 68(sp)    lw t0, 136(sp)
    sw t0, 72(sp)    lw t0, 140(sp)
    sw t0, 76(sp)    lw t0, 144(sp)
    sw t0, 80(sp)    lw t0, 148(sp)
    sw t0, 84(sp)    lw t0, 152(sp)
    sw t0, 88(sp)    lw t0, 156(sp)
    sw t0, 92(sp)    lw t0, 160(sp)
    sw t0, 96(sp)    lw t0, 164(sp)
    sw t0, 100(sp)    lw t0, 168(sp)
    sw t0, 104(sp)    lw t0, 172(sp)
    sw t0, 108(sp)    lw t0, 176(sp)
    sw t0, 112(sp)    lw t0, 180(sp)
    sw t0, 116(sp)    lw t0, 184(sp)
    sw t0, 120(sp)    call sum32
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 128
    mv t0, a0
    sw t0, 188(sp)
    addi sp, sp, -256
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t0, 52(sp)
    mv a0, t0    lw t0, 56(sp)
    mv a1, t0    lw t0, 60(sp)
    mv a2, t0    lw t0, 64(sp)
    mv a3, t0    lw t0, 68(sp)
    mv a4, t0    lw t0, 72(sp)
    mv a5, t0    lw t0, 76(sp)
    mv a6, t0    lw t0, 80(sp)
    mv a7, t0    li t0, 9
    sw t0, 28(sp)    li t0, 10
    sw t0, 32(sp)    li t0, 11
    sw t0, 36(sp)    li t0, 12
    sw t0, 40(sp)    li t0, 13
    sw t0, 44(sp)    li t0, 14
    sw t0, 48(sp)    li t0, 15
    sw t0, 52(sp)    li t0, 16
    sw t0, 56(sp)    lw t0, 124(sp)
    sw t0, 60(sp)    lw t0, 128(sp)
    sw t0, 64(sp)    lw t0, 132(sp)
    sw t0, 68(sp)    lw t0, 136(sp)
    sw t0, 72(sp)    lw t0, 140(sp)
    sw t0, 76(sp)    lw t0, 144(sp)
    sw t0, 80(sp)    lw t0, 148(sp)
    sw t0, 84(sp)    lw t0, 152(sp)
    sw t0, 88(sp)    li t0, 25
    sw t0, 92(sp)    li t0, 26
    sw t0, 96(sp)    li t0, 27
    sw t0, 100(sp)    li t0, 28
    sw t0, 104(sp)    li t0, 29
    sw t0, 108(sp)    li t0, 30
    sw t0, 112(sp)    li t0, 31
    sw t0, 116(sp)    li t0, 32
    sw t0, 120(sp)    lw t0, 52(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 124(sp)    lw t0, 56(sp)
    li t1, 2
add t2, t0, t1
    sw t2, 128(sp)    lw t0, 60(sp)
    li t1, 3
add t2, t0, t1
    sw t2, 132(sp)    lw t0, 64(sp)
    li t1, 4
add t2, t0, t1
    sw t2, 136(sp)    lw t0, 68(sp)
    li t1, 5
add t2, t0, t1
    sw t2, 140(sp)    lw t0, 72(sp)
    li t1, 6
add t2, t0, t1
    sw t2, 144(sp)    lw t0, 76(sp)
    li t1, 7
add t2, t0, t1
    sw t2, 148(sp)    lw t0, 80(sp)
    li t1, 8
add t2, t0, t1
    sw t2, 152(sp)    lw t0, 84(sp)
    li t1, 9
mul t2, t0, t1
    sw t2, 156(sp)    lw t0, 88(sp)
    li t1, 10
mul t2, t0, t1
    sw t2, 160(sp)    lw t0, 92(sp)
    li t1, 11
mul t2, t0, t1
    sw t2, 164(sp)    lw t0, 96(sp)
    li t1, 12
mul t2, t0, t1
    sw t2, 168(sp)    lw t0, 100(sp)
    li t1, 13
mul t2, t0, t1
    sw t2, 172(sp)    lw t0, 104(sp)
    li t1, 14
mul t2, t0, t1
    sw t2, 176(sp)    lw t0, 108(sp)
    li t1, 15
mul t2, t0, t1
    sw t2, 180(sp)    lw t0, 112(sp)
    li t1, 16
mul t2, t0, t1
    sw t2, 184(sp)    lw t0, 52(sp)
    lw t1, 124(sp)
add t2, t0, t1
    sw t2, 188(sp)    lw t0, 56(sp)
    lw t1, 128(sp)
add t2, t0, t1
    sw t2, 192(sp)    lw t0, 60(sp)
    lw t1, 132(sp)
add t2, t0, t1
    sw t2, 196(sp)    lw t0, 64(sp)
    lw t1, 136(sp)
add t2, t0, t1
    sw t2, 200(sp)    lw t0, 68(sp)
    lw t1, 140(sp)
add t2, t0, t1
    sw t2, 204(sp)    lw t0, 72(sp)
    lw t1, 144(sp)
add t2, t0, t1
    sw t2, 208(sp)    lw t0, 76(sp)
    lw t1, 148(sp)
add t2, t0, t1
    sw t2, 212(sp)    lw t0, 80(sp)
    lw t1, 152(sp)
add t2, t0, t1
    sw t2, 216(sp)    lw t0, 52(sp)
    lw t1, 84(sp)
mul t2, t0, t1
    lw t1, 188(sp)
add t2, t2, t1
    sw t2, 220(sp)    lw t0, 56(sp)
    lw t1, 88(sp)
mul t2, t0, t1
    lw t1, 188(sp)
add t2, t2, t1
    sw t2, 224(sp)    lw t0, 60(sp)
    lw t1, 92(sp)
mul t2, t0, t1
    lw t1, 188(sp)
add t2, t2, t1
    sw t2, 228(sp)    lw t0, 64(sp)
    lw t1, 96(sp)
mul t2, t0, t1
    lw t1, 188(sp)
add t2, t2, t1
    sw t2, 232(sp)    lw t0, 68(sp)
    lw t1, 100(sp)
mul t2, t0, t1
    lw t1, 188(sp)
add t2, t2, t1
    sw t2, 236(sp)    lw t0, 72(sp)
    lw t1, 104(sp)
mul t2, t0, t1
    lw t1, 188(sp)
add t2, t2, t1
    sw t2, 240(sp)    lw t0, 76(sp)
    lw t1, 108(sp)
mul t2, t0, t1
    lw t1, 188(sp)
add t2, t2, t1
    sw t2, 244(sp)    lw t0, 80(sp)
    lw t1, 112(sp)
mul t2, t0, t1
    lw t1, 116(sp)
    lw t2, 120(sp)
add t3, t1, t2
    lw t2, 188(sp)
add t3, t3, t2
add t2, t2, t3
    sw t2, 248(sp)    call sum64
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 256
    mv t0, a0
    sw t0, 192(sp)
    lw t0, 116(sp)
    lw t1, 120(sp)
add t2, t0, t1
    lw t1, 188(sp)
add t2, t2, t1
    lw t1, 192(sp)
add t2, t2, t1
    sw t2, 196(sp)
    lw t0, 196(sp)
    li t1, 256
rem t2, t0, t1
    mv a0, t2
    lw ra, 48(sp)
    lw s11, 44(sp)
    lw s10, 40(sp)
    lw s9, 36(sp)
    lw s8, 32(sp)
    lw s7, 28(sp)
    lw s6, 24(sp)
    lw s5, 20(sp)
    lw s4, 16(sp)
    lw s3, 12(sp)
    lw s2, 8(sp)
    lw s1, 4(sp)
    lw s0, 0(sp)
    addi sp, sp, 64
    ret
