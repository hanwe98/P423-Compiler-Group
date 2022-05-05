(define (f [a0 : Integer] [a1 : Integer] [a2 : Integer] [a3 : Integer] [a4 : Integer]
		   [a5 : Integer] [a6 : Integer] [a7 : Integer] [a8 : Integer] [a9 : Integer])
		: Integer
	(begin (set! a9 42)
		   a9))
(f 0 1 2 3 4 5 6 7 8 9)
