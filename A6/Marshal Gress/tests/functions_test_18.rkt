(define (add1 [x : Integer])
		: Integer
	(+ x 1))
(define (sub1 [x : Integer])
		: Integer
	(- x 1))
(define (add2 [x : Integer])
		: Integer
	(+ x 2))
(define (sub2 [x : Integer])
		: Integer
	(- x 2))

(sub2 (add2 (sub1 (add1 42))))
