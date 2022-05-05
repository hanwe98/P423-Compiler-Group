(define (f [a : Integer] [b : Integer] [c : Integer]
		   [d : Integer])
		: Integer
	(+ a (+ b (+ c d))))
(+ (f 1 2 3 4) 32)
