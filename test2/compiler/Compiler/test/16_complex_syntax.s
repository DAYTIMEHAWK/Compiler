
    .globl factorial
factorial:
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

    li t0, 1
    sw t0, 56(sp)
    lw t0, 52(sp)
    li t1, 0
slt t2, t1, t0
    xori t2, t2, 1
    beqz t2, .Lif_else1
    j .Lif_then0
.Lif_else1:
.Lloop_begin3:    lw t1, 52(sp)
    li t2, 1
slt t3, t2, t1
    beqz t3, .Lloop_end4
    lw t2, 56(sp)
    lw t3, 52(sp)
mul t4, t2, t3
    sw t4, 56(sp)
    lw t2, 52(sp)
    li t3, 1
sub t4, t2, t3
    sw t4, 52(sp)
    j .Lloop_begin3
.Lloop_end4:
    lw t1, 56(sp)
    mv a0, t1
    j .Lif_end2
.Lif_then0:
    li t1, 1
    mv a0, t1
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
neg t1, t0
    sw t1, 52(sp)
    li t0, 3
neg t1, t0
    sw t1, 56(sp)
    li t0, 0
    sw t0, 60(sp)
    lw t0, 52(sp)
    lw t1, 56(sp)
slt t2, t1, t0
    lw t1, 52(sp)
    lw t2, 56(sp)
sub t3, t1, t2
    li t2, 1
slt t3, t2, t3
and t2, t2, t3
    beqz t2, .Lif_else1
    j .Lif_then0
.Lif_else1:    lw t1, 52(sp)
    lw t2, 56(sp)
slt t3, t1, t2
    lw t2, 52(sp)
    lw t3, 56(sp)
sub t4, t2, t3
    seqz t4, t4
or t3, t3, t4
    beqz t3, .Lif_else4
    j .Lif_then3
.Lif_else4:
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t2, 52(sp)
    lw t3, 56(sp)
mul t4, t2, t3
    mv a0, t4    call factorial
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t2, a0
    sw t2, 60(sp)
    j .Lif_end5
.Lif_then3:
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t2, 52(sp)
    lw t3, 56(sp)
add t4, t2, t3
neg t3, t4
    mv a0, t3    call factorial
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t2, a0
    sw t2, 60(sp)
.Lif_end5:
    j .Lif_end2
.Lif_then0:
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t1, 52(sp)
    mv a0, t1    call factorial
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t1, a0
    sw t1, 60(sp)
.Lif_end2:
.Lloop_begin6:    lw t0, 60(sp)
    li t1, 100
slt t2, t1, t0
    beqz t2, .Lloop_end7
    lw t1, 60(sp)
    li t2, 2
rem t3, t1, t2
    li t2, 0
sub t3, t3, t2
    seqz t3, t3
    beqz t3, .Lif_else9
    j .Lif_then8
.Lif_else9:
    lw t2, 60(sp)
    li t3, 1
sub t4, t2, t3
    sw t4, 60(sp)
    j .Lif_end10
.Lif_then8:
    lw t2, 60(sp)
    li t3, 2
div t4, t2, t3
    sw t4, 60(sp)
.Lif_end10:
    j .Lloop_begin6
.Lloop_end7:
    lw t0, 60(sp)
    li t1, 8
rem t2, t0, t1
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    li t1, 3
    mv a0, t1    call factorial
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t1, a0
div t2, t2, t1
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
