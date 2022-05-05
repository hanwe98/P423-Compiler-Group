(define (combine [v : (Vector Integer Integer)])
		: Integer
	(+ (vector-ref v 0)
	   (vector-ref v 1)))
(combine (vector 20 #f))
