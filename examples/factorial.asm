entry
li r1, 10
call factorial
halt
factorial:
entry
jnz r1, recurse
li r0, 1
ret
recurse:
mov r2, r1
li r3, 1
sub r1, r1, r3
call factorial
mul r0, r0, r2
ret
