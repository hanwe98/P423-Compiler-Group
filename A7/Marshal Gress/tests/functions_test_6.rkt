(define (combine [v : (Vector Boolean Boolean)])
		: Integer
	(+ (vector-ref v 0)
	   (vector-ref v 1)))
(combine (vector #t #f))
