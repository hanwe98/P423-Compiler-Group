(define (f [x : Integer] [y : Integer]
		   [b : Boolean] [c : Boolean] [d : Boolean])
		: Integer
	(if b
		(if (and c d)
			(+ x y)
			(- x y))
		(if c
			x
			(if d
				y
				0))))
(define (g [v : (Vector Integer Integer)])
		: Integer
	(+ (vector-ref v 0) (vector-ref v 1)))
(define (h [v : (Vector Integer Integer)])
		: Integer
	(- (vector-ref v 0) (vector-ref v 1)))

(let ([v (vector 20 30)])
	(+ (f (g v) (h v) #f #t #f) ; 50
	   -8))
