(define (f v)
	(vector-set! v 0 42))

(if (f (vector 12)) 42 0)
