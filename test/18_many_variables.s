
    .globl abs
abs:
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

    sw a0, 52(sp)

    lw t0, 52(sp)
    li t1, 0
slt t2, t0, t1
    beqz t2, .Lif_else1
    j .Lif_then0
.Lif_else1:
    lw t1, 52(sp)
    mv a0, t1
    j .Lif_end2
.Lif_then0:
    lw t1, 52(sp)
neg t2, t1
    mv a0, t2
.Lif_end2:
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



    .globl compute
compute:
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
    lw t2, 60(sp)
mul t3, t1, t2
add t2, t0, t3
    lw t1, 64(sp)
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t2, 68(sp)
    mv a0, t2    call abs
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t2, a0
    li t3, 1
add t4, t2, t3
div t3, t1, t4
sub t2, t2, t3
    lw t1, 72(sp)
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t2, 76(sp)
    mv a0, t2    call abs
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t2, a0
    li t3, 1
add t4, t2, t3
rem t3, t1, t4
    lw t2, 80(sp)
mul t3, t3, t2
add t2, t2, t3
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
    li t0, 17
    sw t0, 116(sp)
    li t0, 18
    sw t0, 120(sp)
    li t0, 19
    sw t0, 124(sp)
    li t0, 20
    sw t0, 128(sp)
    li t0, 21
    sw t0, 132(sp)
    li t0, 22
    sw t0, 136(sp)
    li t0, 23
    sw t0, 140(sp)
    li t0, 24
    sw t0, 144(sp)
    li t0, 25
    sw t0, 148(sp)
    li t0, 26
    sw t0, 152(sp)
    li t0, 27
    sw t0, 156(sp)
    li t0, 28
    sw t0, 160(sp)
    li t0, 29
    sw t0, 164(sp)
    li t0, 30
    sw t0, 168(sp)
    li t0, 31
    sw t0, 172(sp)
    li t0, 32
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
    sw t2, 196(sp)

    lw t0, 52(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 200(sp)
    lw t0, 56(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 204(sp)
    lw t0, 60(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 208(sp)
    lw t0, 64(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 212(sp)
    lw t0, 68(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 216(sp)
    lw t0, 72(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 220(sp)
    lw t0, 76(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 224(sp)
    lw t0, 80(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 228(sp)
    lw t0, 84(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 232(sp)
    lw t0, 88(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 236(sp)
    lw t0, 92(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 240(sp)
    lw t0, 96(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 244(sp)
    lw t0, 100(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 248(sp)
    lw t0, 104(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 252(sp)
    lw t0, 108(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 256(sp)
    lw t0, 112(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 260(sp)
    lw t0, 116(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 264(sp)
    lw t0, 120(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 268(sp)
    lw t0, 124(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 272(sp)
    lw t0, 128(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 276(sp)
    lw t0, 132(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 280(sp)
    lw t0, 136(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 284(sp)
    lw t0, 140(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 288(sp)
    lw t0, 144(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 292(sp)
    lw t0, 148(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 296(sp)
    lw t0, 152(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 300(sp)
    lw t0, 156(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 304(sp)
    lw t0, 160(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 308(sp)
    lw t0, 164(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 312(sp)
    lw t0, 168(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 316(sp)
    lw t0, 172(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 320(sp)
    lw t0, 176(sp)
    li t1, 2
mul t2, t0, t1
    sw t2, 324(sp)
    lw t0, 200(sp)
    lw t1, 204(sp)
add t2, t0, t1
    lw t1, 208(sp)
add t2, t2, t1
    lw t1, 212(sp)
add t2, t2, t1
    lw t1, 216(sp)
add t2, t2, t1
    lw t1, 220(sp)
add t2, t2, t1
    lw t1, 224(sp)
add t2, t2, t1
    lw t1, 228(sp)
add t2, t2, t1
    sw t2, 328(sp)
    lw t0, 232(sp)
    lw t1, 236(sp)
add t2, t0, t1
    lw t1, 240(sp)
add t2, t2, t1
    lw t1, 244(sp)
add t2, t2, t1
    lw t1, 248(sp)
add t2, t2, t1
    lw t1, 252(sp)
add t2, t2, t1
    lw t1, 256(sp)
add t2, t2, t1
    lw t1, 260(sp)
add t2, t2, t1
    sw t2, 332(sp)
    lw t0, 264(sp)
    lw t1, 268(sp)
add t2, t0, t1
    lw t1, 272(sp)
add t2, t2, t1
    lw t1, 276(sp)
add t2, t2, t1
    lw t1, 280(sp)
add t2, t2, t1
    lw t1, 284(sp)
add t2, t2, t1
    lw t1, 288(sp)
add t2, t2, t1
    lw t1, 292(sp)
add t2, t2, t1
    sw t2, 336(sp)
    lw t0, 296(sp)
    lw t1, 300(sp)
add t2, t0, t1
    lw t1, 304(sp)
add t2, t2, t1
    lw t1, 308(sp)
add t2, t2, t1
    lw t1, 312(sp)
add t2, t2, t1
    lw t1, 316(sp)
add t2, t2, t1
    lw t1, 320(sp)
add t2, t2, t1
    lw t1, 324(sp)
add t2, t2, t1
    sw t2, 340(sp)
    lw t0, 328(sp)
    lw t1, 332(sp)
add t2, t0, t1
    lw t1, 336(sp)
add t2, t2, t1
    lw t1, 340(sp)
add t2, t2, t1
    sw t2, 344(sp)

    lw t0, 200(sp)
    lw t1, 52(sp)
add t2, t0, t1
    sw t2, 348(sp)
    lw t0, 204(sp)
    lw t1, 56(sp)
add t2, t0, t1
    sw t2, 352(sp)
    lw t0, 208(sp)
    lw t1, 60(sp)
add t2, t0, t1
    sw t2, 356(sp)
    lw t0, 212(sp)
    lw t1, 64(sp)
add t2, t0, t1
    sw t2, 360(sp)
    lw t0, 216(sp)
    lw t1, 68(sp)
add t2, t0, t1
    sw t2, 364(sp)
    lw t0, 220(sp)
    lw t1, 72(sp)
add t2, t0, t1
    sw t2, 368(sp)
    lw t0, 224(sp)
    lw t1, 76(sp)
add t2, t0, t1
    sw t2, 372(sp)
    lw t0, 228(sp)
    lw t1, 80(sp)
add t2, t0, t1
    sw t2, 376(sp)
    lw t0, 232(sp)
    lw t1, 84(sp)
add t2, t0, t1
    sw t2, 380(sp)
    lw t0, 236(sp)
    lw t1, 88(sp)
add t2, t0, t1
    sw t2, 384(sp)
    lw t0, 240(sp)
    lw t1, 92(sp)
add t2, t0, t1
    sw t2, 388(sp)
    lw t0, 244(sp)
    lw t1, 96(sp)
add t2, t0, t1
    sw t2, 392(sp)
    lw t0, 248(sp)
    lw t1, 100(sp)
add t2, t0, t1
    sw t2, 396(sp)
    lw t0, 252(sp)
    lw t1, 104(sp)
add t2, t0, t1
    sw t2, 400(sp)
    lw t0, 256(sp)
    lw t1, 108(sp)
add t2, t0, t1
    sw t2, 404(sp)
    lw t0, 260(sp)
    lw t1, 112(sp)
add t2, t0, t1
    sw t2, 408(sp)
    lw t0, 264(sp)
    lw t1, 116(sp)
add t2, t0, t1
    sw t2, 412(sp)
    lw t0, 268(sp)
    lw t1, 120(sp)
add t2, t0, t1
    sw t2, 416(sp)
    lw t0, 272(sp)
    lw t1, 124(sp)
add t2, t0, t1
    sw t2, 420(sp)
    lw t0, 276(sp)
    lw t1, 128(sp)
add t2, t0, t1
    sw t2, 424(sp)
    lw t0, 280(sp)
    lw t1, 132(sp)
add t2, t0, t1
    sw t2, 428(sp)
    lw t0, 284(sp)
    lw t1, 136(sp)
add t2, t0, t1
    sw t2, 432(sp)
    lw t0, 288(sp)
    lw t1, 140(sp)
add t2, t0, t1
    sw t2, 436(sp)
    lw t0, 292(sp)
    lw t1, 144(sp)
add t2, t0, t1
    sw t2, 440(sp)
    lw t0, 296(sp)
    lw t1, 148(sp)
add t2, t0, t1
    sw t2, 444(sp)
    lw t0, 300(sp)
    lw t1, 152(sp)
add t2, t0, t1
    sw t2, 448(sp)
    lw t0, 304(sp)
    lw t1, 156(sp)
add t2, t0, t1
    sw t2, 452(sp)
    lw t0, 308(sp)
    lw t1, 160(sp)
add t2, t0, t1
    sw t2, 456(sp)
    lw t0, 312(sp)
    lw t1, 164(sp)
add t2, t0, t1
    sw t2, 460(sp)
    lw t0, 316(sp)
    lw t1, 168(sp)
add t2, t0, t1
    sw t2, 464(sp)
    lw t0, 320(sp)
    lw t1, 172(sp)
add t2, t0, t1
    sw t2, 468(sp)
    lw t0, 324(sp)
    lw t1, 176(sp)
add t2, t0, t1
    sw t2, 472(sp)
    lw t0, 348(sp)
    lw t1, 352(sp)
add t2, t0, t1
    lw t1, 356(sp)
add t2, t2, t1
    lw t1, 360(sp)
add t2, t2, t1
    lw t1, 364(sp)
add t2, t2, t1
    lw t1, 368(sp)
add t2, t2, t1
    lw t1, 372(sp)
add t2, t2, t1
    lw t1, 376(sp)
add t2, t2, t1
    sw t2, 476(sp)
    lw t0, 380(sp)
    lw t1, 384(sp)
add t2, t0, t1
    lw t1, 388(sp)
add t2, t2, t1
    lw t1, 392(sp)
add t2, t2, t1
    lw t1, 396(sp)
add t2, t2, t1
    lw t1, 400(sp)
add t2, t2, t1
    lw t1, 404(sp)
add t2, t2, t1
    lw t1, 408(sp)
add t2, t2, t1
    sw t2, 480(sp)
    lw t0, 412(sp)
    lw t1, 416(sp)
add t2, t0, t1
    lw t1, 420(sp)
add t2, t2, t1
    lw t1, 424(sp)
add t2, t2, t1
    lw t1, 428(sp)
add t2, t2, t1
    lw t1, 432(sp)
add t2, t2, t1
    lw t1, 436(sp)
add t2, t2, t1
    lw t1, 440(sp)
add t2, t2, t1
    sw t2, 484(sp)
    lw t0, 444(sp)
    lw t1, 448(sp)
add t2, t0, t1
    lw t1, 452(sp)
add t2, t2, t1
    lw t1, 456(sp)
add t2, t2, t1
    lw t1, 460(sp)
add t2, t2, t1
    lw t1, 464(sp)
add t2, t2, t1
    lw t1, 468(sp)
add t2, t2, t1
    lw t1, 472(sp)
add t2, t2, t1
    sw t2, 488(sp)
    lw t0, 476(sp)
    lw t1, 480(sp)
add t2, t0, t1
    lw t1, 484(sp)
add t2, t2, t1
    lw t1, 488(sp)
add t2, t2, t1
    sw t2, 492(sp)

    lw t0, 348(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 496(sp)
    lw t0, 352(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 500(sp)
    lw t0, 356(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 504(sp)
    lw t0, 360(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 508(sp)
    lw t0, 364(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 512(sp)
    lw t0, 368(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 516(sp)
    lw t0, 372(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 520(sp)
    lw t0, 376(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 524(sp)
    lw t0, 380(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 528(sp)
    lw t0, 384(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 532(sp)
    lw t0, 388(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 536(sp)
    lw t0, 392(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 540(sp)
    lw t0, 396(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 544(sp)
    lw t0, 400(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 548(sp)
    lw t0, 404(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 552(sp)
    lw t0, 408(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 556(sp)
    lw t0, 412(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 560(sp)
    lw t0, 416(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 564(sp)
    lw t0, 420(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 568(sp)
    lw t0, 424(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 572(sp)
    lw t0, 428(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 576(sp)
    lw t0, 432(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 580(sp)
    lw t0, 436(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 584(sp)
    lw t0, 440(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 588(sp)
    lw t0, 444(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 592(sp)
    lw t0, 448(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 596(sp)
    lw t0, 452(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 600(sp)
    lw t0, 456(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 604(sp)
    lw t0, 460(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 608(sp)
    lw t0, 464(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 612(sp)
    lw t0, 468(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 616(sp)
    lw t0, 472(sp)
    li t1, 1
add t2, t0, t1
    sw t2, 620(sp)
    lw t0, 496(sp)
    lw t1, 500(sp)
add t2, t0, t1
    lw t1, 504(sp)
add t2, t2, t1
    lw t1, 508(sp)
add t2, t2, t1
    lw t1, 512(sp)
add t2, t2, t1
    lw t1, 516(sp)
add t2, t2, t1
    lw t1, 520(sp)
add t2, t2, t1
    lw t1, 524(sp)
add t2, t2, t1
    sw t2, 624(sp)
    lw t0, 528(sp)
    lw t1, 532(sp)
add t2, t0, t1
    lw t1, 536(sp)
add t2, t2, t1
    lw t1, 540(sp)
add t2, t2, t1
    lw t1, 544(sp)
add t2, t2, t1
    lw t1, 548(sp)
add t2, t2, t1
    lw t1, 552(sp)
add t2, t2, t1
    lw t1, 556(sp)
add t2, t2, t1
    sw t2, 628(sp)
    lw t0, 560(sp)
    lw t1, 564(sp)
add t2, t0, t1
    lw t1, 568(sp)
add t2, t2, t1
    lw t1, 572(sp)
add t2, t2, t1
    lw t1, 576(sp)
add t2, t2, t1
    lw t1, 580(sp)
add t2, t2, t1
    lw t1, 584(sp)
add t2, t2, t1
    lw t1, 588(sp)
add t2, t2, t1
    sw t2, 632(sp)
    lw t0, 592(sp)
    lw t1, 596(sp)
add t2, t0, t1
    lw t1, 600(sp)
add t2, t2, t1
    lw t1, 604(sp)
add t2, t2, t1
    lw t1, 608(sp)
add t2, t2, t1
    lw t1, 612(sp)
add t2, t2, t1
    lw t1, 616(sp)
add t2, t2, t1
    lw t1, 620(sp)
add t2, t2, t1
    sw t2, 636(sp)
    lw t0, 624(sp)
    lw t1, 628(sp)
add t2, t0, t1
    lw t1, 632(sp)
add t2, t2, t1
    lw t1, 636(sp)
add t2, t2, t1
    sw t2, 640(sp)
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t0, 196(sp)
    mv a0, t0    lw t0, 344(sp)
    mv a1, t0    lw t0, 492(sp)
    mv a2, t0    lw t0, 640(sp)
    mv a3, t0    lw t0, 180(sp)
    mv a4, t0    lw t0, 328(sp)
    mv a5, t0    lw t0, 476(sp)
    mv a6, t0    lw t0, 624(sp)
    mv a7, t0    call compute
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t0, a0
    sw t0, 644(sp)
    lw t0, 644(sp)
    mv a0, t0
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
