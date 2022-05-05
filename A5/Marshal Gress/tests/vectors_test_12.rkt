;#lang racket
(let ([v (vector #t #f)])
  (begin (vector-set! v 1 #t)
  		 (if (and (vector-ref v 0)
		          (vector-ref v 1))
			 42
			 0)))
