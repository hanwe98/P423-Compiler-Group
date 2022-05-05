(define (t [x : Integer])
		: Integer
	(let ([i 0])
	(let ([sum 0])
		(begin (while (<= i x)
			   (begin (set! sum (+ sum i))
			   		  (set! i (+ i 1))))
			   sum))))
(if (eq? (t 4) 10) 42 0)
