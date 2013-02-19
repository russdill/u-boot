.globl call_with_stack
call_with_stack:
	str	sp, [r2, #-4]!
	str	lr, [r2, #-4]!

	mov	sp, r2
	mov	r2, r0
	mov	r0, r1

	adr	lr, 1f
	mov	pc, r2

1:	ldr	lr, [sp]
	ldr	sp, [sp, #4]
	mov	pc, lr

