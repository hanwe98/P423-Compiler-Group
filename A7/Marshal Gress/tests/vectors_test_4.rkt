;#lang racket
(let ([v1 (vector (vector 3 4) 1 2)])
	(let ([v2 (vector (vector-ref v1 1) (vector-ref v1 2))]) ; (vector 1 2)
		(begin (vector-set! v1 0 v2) ; (vector (vector 1 2) 1 2)
			   (vector-ref (vector-ref v1 0) 1)))) ; => 2
