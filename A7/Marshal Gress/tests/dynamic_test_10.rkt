(define (f v)
	(if (vector-ref v 0)
		(vector-ref v 1)
		(vector-ref v 2)))

(f (vector 10 42 #f))
