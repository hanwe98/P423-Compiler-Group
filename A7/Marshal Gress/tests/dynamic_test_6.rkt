(define (f n x y)
	(if (eq? n y)
		(not x)
		(f (+ 1 n) x y)))

(if (f 0 #f 10)
	42
	#f)
