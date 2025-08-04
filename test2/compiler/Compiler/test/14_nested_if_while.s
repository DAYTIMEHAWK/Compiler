
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


    li t0, 0
    sw t0, 52(sp)
.Lloop_begin0:    lw t0, 52(sp)
    li t1, 5
slt t2, t0, t1
    beqz t2, .Lloop_end1
    lw t1, 52(sp)
    li t2, 2
rem t3, t1, t2
    li t2, 0
sub t3, t3, t2
    seqz t3, t3
    beqz t3, .Lif_else3
    j .Lif_then2
.Lif_else3:
    lw t2, 52(sp)
    li t3, 1
add t4, t2, t3
    sw t4, 52(sp)
    j .Lif_end4
.Lif_then2:
    lw t2, 52(sp)
    li t3, 2
add t4, t2, t3
    sw t4, 52(sp)
.Lif_end4:
    j .Lloop_begin0
.Lloop_end1:
    lw t0, 52(sp)
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
