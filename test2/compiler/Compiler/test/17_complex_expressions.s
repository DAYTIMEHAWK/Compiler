
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

    lw t0, 52(sp)
    li t1, 1
slt t2, t1, t0
    xori t2, t2, 1
    beqz t2, .Lif_else1
    j .Lif_then0
.Lif_else1:
    j .Lif_end2
.Lif_then0:
    li t1, 1
    mv a0, t1
.Lif_end2:
    lw t0, 52(sp)
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t1, 52(sp)
    li t2, 1
sub t3, t1, t2
    mv a0, t3    call factorial
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t1, a0
mul t2, t0, t1
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



    .globl fibonacci
fibonacci:
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
slt t2, t1, t0
    xori t2, t2, 1
    beqz t2, .Lif_else1
    j .Lif_then0
.Lif_else1:
    j .Lif_end2
.Lif_then0:
    li t1, 0
    mv a0, t1
.Lif_end2:
    lw t0, 52(sp)
    li t1, 1
sub t2, t0, t1
    seqz t2, t2
    beqz t2, .Lif_else4
    j .Lif_then3
.Lif_else4:
    j .Lif_end5
.Lif_then3:
    li t1, 1
    mv a0, t1
.Lif_end5:
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t0, 52(sp)
    li t1, 1
sub t2, t0, t1
    mv a0, t2    call fibonacci
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t0, a0
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t1, 52(sp)
    li t2, 2
sub t3, t1, t2
    mv a0, t3    call fibonacci
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t1, a0
add t2, t0, t1
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



    .globl gcd
gcd:
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
    sw a1, 56(sp)

    lw t0, 56(sp)
    li t1, 0
sub t2, t0, t1
    seqz t2, t2
    beqz t2, .Lif_else1
    j .Lif_then0
.Lif_else1:
    j .Lif_end2
.Lif_then0:
    lw t1, 52(sp)
    mv a0, t1
.Lif_end2:
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t0, 56(sp)
    mv a0, t0    lw t0, 52(sp)
    lw t1, 56(sp)
rem t2, t0, t1
    mv a1, t2    call gcd
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t0, a0
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



    .globl is_prime
is_prime:
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
    li t1, 1
slt t2, t1, t0
    xori t2, t2, 1
    beqz t2, .Lif_else1
    j .Lif_then0
.Lif_else1:
    j .Lif_end2
.Lif_then0:
    li t1, 0
    mv a0, t1
.Lif_end2:
    lw t0, 52(sp)
    li t1, 3
slt t2, t1, t0
    xori t2, t2, 1
    beqz t2, .Lif_else4
    j .Lif_then3
.Lif_else4:
    j .Lif_end5
.Lif_then3:
    li t1, 1
    mv a0, t1
.Lif_end5:
    lw t0, 52(sp)
    li t1, 2
rem t2, t0, t1
    li t1, 0
sub t2, t2, t1
    seqz t2, t2
    lw t1, 52(sp)
    li t2, 3
rem t3, t1, t2
    li t2, 0
sub t3, t3, t2
    seqz t3, t3
or t2, t2, t3
    beqz t2, .Lif_else7
    j .Lif_then6
.Lif_else7:
    j .Lif_end8
.Lif_then6:
    li t1, 0
    mv a0, t1
.Lif_end8:
    li t0, 5
    sw t0, 56(sp)
.Lloop_begin9:    lw t0, 56(sp)
    lw t1, 56(sp)
mul t2, t0, t1
    lw t1, 52(sp)
slt t2, t1, t2
    xori t2, t2, 1
    beqz t2, .Lloop_end10
    lw t1, 52(sp)
    lw t2, 56(sp)
rem t3, t1, t2
    li t2, 0
sub t3, t3, t2
    seqz t3, t3
    lw t2, 52(sp)
    lw t3, 56(sp)
    li t4, 2
add t5, t3, t4
rem t4, t2, t5
    li t3, 0
sub t4, t4, t3
    seqz t4, t4
or t3, t3, t4
    beqz t3, .Lif_else12
    j .Lif_then11
.Lif_else12:
    j .Lif_end13
.Lif_then11:
    li t2, 0
    mv a0, t2
.Lif_end13:
    lw t1, 56(sp)
    li t2, 6
add t3, t1, t2
    sw t3, 56(sp)
    j .Lloop_begin9
.Lloop_end10:
    li t0, 1
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
    lw t0, 52(sp)
    lw t1, 56(sp)
add t2, t0, t1
    lw t1, 60(sp)
mul t2, t2, t1
    lw t1, 64(sp)
    lw t2, 52(sp)
mul t3, t1, t2
add t2, t2, t3
    lw t1, 56(sp)
    lw t2, 60(sp)
add t3, t1, t2
    lw t2, 52(sp)
    lw t3, 64(sp)
neg t4, t3
add t4, t2, t4
    li t3, 2048
add t4, t4, t3
rem t3, t3, t4
    li t2, 1
add t3, t3, t2
div t2, t2, t3
    lw t1, 52(sp)
    lw t2, 56(sp)
mul t3, t1, t2
    lw t2, 60(sp)
mul t3, t3, t2
    lw t2, 64(sp)
    li t3, 2
sub t4, t2, t3
    lw t3, 60(sp)
sub t4, t4, t3
mul t3, t3, t4
add t2, t2, t3
    sw t2, 68(sp)
    li t0, 0
    sw t0, 72(sp)
    li t0, 1
    sw t0, 76(sp)
    li t0, 2
    sw t0, 80(sp)
    li t0, 0
    sw t0, 84(sp)
    lw t0, 72(sp)
    lw t1, 76(sp)
slt t2, t1, t0
    lw t1, 80(sp)
    li t2, 1
add t3, t1, t2
    li t2, 1
sub t3, t3, t2
    seqz t3, t3
and t2, t2, t3
    beqz t2, .Lif_else1
    j .Lif_then0
.Lif_else1:
    j .Lif_end2
.Lif_then0:
    li t1, 1
    sw t1, 84(sp)
.Lif_end2:
    li t0, 0
    sw t0, 88(sp)
    lw t0, 72(sp)
    lw t1, 76(sp)
slt t2, t0, t1
    lw t1, 80(sp)
    li t2, 2
add t3, t1, t2
    li t2, 2
sub t3, t3, t2
    seqz t3, t3
or t2, t2, t3
    beqz t2, .Lif_else4
    j .Lif_then3
.Lif_else4:
    j .Lif_end5
.Lif_then3:
    li t1, 1
    sw t1, 88(sp)
.Lif_end5:
    li t0, 0
    sw t0, 92(sp)
    lw t0, 72(sp)
    li t1, 0
slt t2, t1, t0
    lw t1, 76(sp)
    li t2, 0
slt t3, t1, t2
and t2, t2, t3
    lw t1, 80(sp)
    li t2, 0
slt t3, t2, t1
    lw t2, 72(sp)
    li t3, 0
slt t4, t2, t3
and t3, t3, t4
or t2, t2, t3
seqz t1, t2
    lw t1, 76(sp)
    li t2, 0
slt t3, t2, t1
    lw t2, 72(sp)
    li t3, 0
slt t4, t2, t3
or t3, t3, t4
and t2, t1, t3
    beqz t2, .Lif_else7
    j .Lif_then6
.Lif_else7:
    j .Lif_end8
.Lif_then6:
    li t1, 1
    sw t1, 92(sp)
.Lif_end8:
    li t0, 42
    sw t0, 96(sp)
    li t0, 56
    sw t0, 100(sp)
    li t0, 87
    sw t0, 104(sp)
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t0, 100(sp)
    mv a0, t0    lw t0, 104(sp)
    mv a1, t0    call gcd
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t0, a0
    mv a0, t0    call factorial
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t0, a0
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t1, 96(sp)
    li t2, 5
div t3, t1, t2
    mv a0, t3    call fibonacci
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t1, a0
add t2, t0, t1
    sw t2, 108(sp)
    li t0, 0
    sw t0, 112(sp)
    lw t0, 96(sp)
    lw t1, 100(sp)
slt t2, t1, t0
    lw t1, 96(sp)
    lw t2, 104(sp)
slt t3, t2, t1
and t2, t2, t3
    beqz t2, .Lif_else10
    j .Lif_then9
.Lif_else10:    lw t1, 100(sp)
    lw t2, 96(sp)
slt t3, t2, t1
    lw t2, 100(sp)
    lw t3, 104(sp)
slt t4, t3, t2
and t3, t3, t4
    beqz t3, .Lif_else13
    j .Lif_then12
.Lif_else13:
    lw t2, 104(sp)
    sw t2, 112(sp)
    j .Lif_end14
.Lif_then12:
    lw t2, 100(sp)
    sw t2, 112(sp)
.Lif_end14:
    j .Lif_end11
.Lif_then9:
    lw t1, 96(sp)
    sw t1, 112(sp)
.Lif_end11:
    li t0, 0
    sw t0, 116(sp)
    li t0, 1
    sw t0, 120(sp)
.Lloop_begin15:    lw t0, 120(sp)
    li t1, 10
slt t2, t1, t0
    xori t2, t2, 1
    beqz t2, .Lloop_end16
    lw t1, 120(sp)
    li t2, 2
rem t3, t1, t2
    li t2, 0
sub t3, t3, t2
    seqz t3, t3
    beqz t3, .Lif_else18
    j .Lif_then17
.Lif_else18:    lw t2, 120(sp)
    li t3, 3
rem t4, t2, t3
    li t3, 0
sub t4, t4, t3
    seqz t4, t4
    beqz t4, .Lif_else21
    j .Lif_then20
.Lif_else21:
    lw t3, 116(sp)
    lw t4, 120(sp)
add t5, t3, t4
    sw t5, 116(sp)
    j .Lif_end22
.Lif_then20:
    lw t3, 116(sp)
    lw t4, 120(sp)
    lw t5, 120(sp)
mul t6, t4, t5
    lw t5, 120(sp)
mul t6, t6, t5
add t5, t3, t6
    sw t5, 116(sp)
.Lif_end22:
    j .Lif_end19
.Lif_then17:
    lw t2, 116(sp)
    lw t3, 120(sp)
    lw t4, 120(sp)
mul t5, t3, t4
add t4, t2, t5
    sw t4, 116(sp)
.Lif_end19:
    lw t1, 120(sp)
    li t2, 1
add t3, t1, t2
    sw t3, 120(sp)
    j .Lloop_begin15
.Lloop_end16:
    li t0, 0
    sw t0, 124(sp)
    li t0, 1
    sw t0, 120(sp)
.Lloop_begin23:    lw t0, 120(sp)
    li t1, 5
slt t2, t1, t0
    xori t2, t2, 1
    beqz t2, .Lloop_end24
    li t1, 1
    sw t1, 128(sp)
    li t1, 1
    sw t1, 132(sp)
.Lloop_begin25:    lw t1, 128(sp)
    lw t2, 120(sp)
slt t3, t2, t1
    xori t3, t3, 1
    beqz t3, .Lloop_end26
    lw t2, 132(sp)
    lw t3, 128(sp)
mul t4, t2, t3
    sw t4, 132(sp)
    lw t2, 128(sp)
    li t3, 1
add t4, t2, t3
    sw t4, 128(sp)
    j .Lloop_begin25
.Lloop_end26:
    lw t1, 124(sp)
    lw t2, 132(sp)
add t3, t1, t2
    sw t3, 124(sp)
    lw t1, 120(sp)
    li t2, 1
add t3, t1, t2
    sw t3, 120(sp)
    j .Lloop_begin23
.Lloop_end24:
    li t0, 0
    sw t0, 136(sp)
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t0, 96(sp)
    mv a0, t0    call is_prime
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t0, a0
    beqz t0, .Lif_else28
    j .Lif_then27
.Lif_else28:    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t1, 100(sp)
    mv a0, t1    call is_prime
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t1, a0
    beqz t1, .Lif_else37
    j .Lif_then36
.Lif_else37:    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t2, 104(sp)
    mv a0, t2    call is_prime
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t2, a0
    beqz t2, .Lif_else43
    j .Lif_then42
.Lif_else43:
    lw t3, 96(sp)
    lw t4, 100(sp)
add t5, t3, t4
    lw t4, 104(sp)
add t5, t5, t4
    sw t5, 136(sp)
    j .Lif_end44
.Lif_then42:
    lw t3, 104(sp)
    sw t3, 136(sp)
.Lif_end44:
    j .Lif_end38
.Lif_then36:
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t2, 104(sp)
    mv a0, t2    call is_prime
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t2, a0
    beqz t2, .Lif_else40
    j .Lif_then39
.Lif_else40:
    lw t3, 100(sp)
    sw t3, 136(sp)
    j .Lif_end41
.Lif_then39:
    lw t3, 100(sp)
    lw t4, 104(sp)
mul t5, t3, t4
    sw t5, 136(sp)
.Lif_end41:
.Lif_end38:
    j .Lif_end29
.Lif_then27:
    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t1, 100(sp)
    mv a0, t1    call is_prime
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t1, a0
    beqz t1, .Lif_else31
    j .Lif_then30
.Lif_else31:    addi sp, sp, -32
    sw t0, 0(sp)
    sw t1, 4(sp)
    sw t2, 8(sp)
    sw t3, 12(sp)
    sw t4, 16(sp)
    sw t5, 20(sp)
    sw t6, 24(sp)
    lw t2, 104(sp)
    mv a0, t2    call is_prime
    lw t0, 0(sp)
    lw t1, 4(sp)
    lw t2, 8(sp)
    lw t3, 12(sp)
    lw t4, 16(sp)
    lw t5, 20(sp)
    lw t6, 24(sp)
    addi sp, sp, 32
    mv t2, a0
    beqz t2, .Lif_else34
    j .Lif_then33
.Lif_else34:
    lw t3, 96(sp)
    sw t3, 136(sp)
    j .Lif_end35
.Lif_then33:
    lw t3, 96(sp)
    lw t4, 104(sp)
mul t5, t3, t4
    sw t5, 136(sp)
.Lif_end35:
    j .Lif_end32
.Lif_then30:
    lw t2, 96(sp)
    lw t3, 100(sp)
mul t4, t2, t3
    sw t4, 136(sp)
.Lif_end32:
.Lif_end29:
    li t0, 0
    sw t0, 140(sp)
    li t0, 2345
    sw t0, 144(sp)
    li t0, 0
    sw t0, 148(sp)
.Lloop_begin45:    lw t0, 144(sp)
    li t1, 0
slt t2, t1, t0
    beqz t2, .Lloop_end46
    lw t1, 144(sp)
    li t2, 2
rem t3, t1, t2
    li t2, 1
sub t3, t3, t2
    seqz t3, t3
    beqz t3, .Lif_else48
    j .Lif_then47
.Lif_else48:
    j .Lif_end49
.Lif_then47:
    lw t2, 148(sp)
    li t3, 1
add t4, t2, t3
    sw t4, 148(sp)
.Lif_end49:
    lw t1, 144(sp)
    li t2, 2
div t3, t1, t2
    sw t3, 144(sp)
    j .Lloop_begin45
.Lloop_end46:
    lw t0, 68(sp)
    lw t1, 84(sp)
add t2, t0, t1
    lw t1, 88(sp)
add t2, t2, t1
    lw t1, 92(sp)
add t2, t2, t1
    lw t1, 108(sp)
add t2, t2, t1
    lw t1, 112(sp)
add t2, t2, t1
    lw t1, 116(sp)
add t2, t2, t1
    lw t1, 124(sp)
add t2, t2, t1
    lw t1, 136(sp)
add t2, t2, t1
    lw t1, 148(sp)
add t2, t2, t1
    sw t2, 152(sp)
    lw t0, 152(sp)
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
