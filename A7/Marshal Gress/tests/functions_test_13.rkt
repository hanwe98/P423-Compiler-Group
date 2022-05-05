(define (f [f : (Integer -> Integer)] [x : Integer]) : Integer
	; tests uniquify (function name and first param name are same)
	(f x))
(define (id [x : Integer]) : Integer
	x)
(f id 42)
