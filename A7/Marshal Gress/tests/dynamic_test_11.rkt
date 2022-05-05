(define (length=? v x)
	(eq? (vector-length v) x))

(let ([x (length=? (vector 1 2 3 4) 3)])
	42)
