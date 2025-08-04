
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


    li t0, 3
    sw t0, 52(sp)
    lw t0, 52(sp)
    li t1, 2
slt t2, t1, t0
    beqz t2, .Lif_else1
    j .Lif_then0
.Lif_else1:
    lw t1, 52(sp)
    li t2, 1
sub t3, t1, t2
    sw t3, 52(sp)
    j .Lif_end2
.Lif_then0:
    lw t1, 52(sp)
    li t2, 1
add t3, t1, t2
    sw t3, 52(sp)
.Lif_end2:
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
