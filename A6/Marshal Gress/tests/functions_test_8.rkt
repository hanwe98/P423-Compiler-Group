(define (add5 [x : Integer]) 
		: Integer
	(+ 5 x))
(define (combine [v : (Vector Integer Integer)])
		: Integer
	(+ (vector-ref v 0)
	   (vector-ref v 1)))

(add5 (combine (vector 20 17)))
