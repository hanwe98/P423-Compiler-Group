(define (length=? v x)
	(eq? (vector-length v) x))

(if (length=? (vector 1 2 3 4) 3)
	0
	42)
