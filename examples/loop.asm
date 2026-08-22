entry
li r1, 100
li r2, 1
li r0, 0
loop:
add r0, r0, r1
sub r1, r1, r2
jnz r1, loop
halt
