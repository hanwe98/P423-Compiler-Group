(define (add1 [x : Integer]) : Integer
	(+ x 1))
(define (sub1 [x : Integer]) : Integer
	(- x 1))
(let ([x #t])
	((if x add1 sub1) 41))
