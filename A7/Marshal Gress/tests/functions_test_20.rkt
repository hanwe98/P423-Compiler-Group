(define (f [a : Integer] [b : Integer] [c : Integer]
		   [d : Integer] [e : Integer])
		: Integer
	(+ a (+ b (+ c (+ d e)))))
(+ (f 1 2 3 4 5) 27)
