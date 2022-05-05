(define (f b i vec)
	(and (and (boolean? b)
		 	  (integer? i))
		 (vector? vec)))

(if (f #t 10 (vector 10))
	42
	0)
