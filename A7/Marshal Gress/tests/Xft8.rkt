(define (map [f : (Integer -> Integer)]
			 [v : (Vector Integer Integer Integer Integer Integer)])
		: (Vector Integer Integer Integer Integer Integer)
	(vector (f (vector-ref v 0))
			(f (vector-ref v 1)) 
			(f (vector-ref v 2))
			(f (vector-ref v 3))
			(f (vector-ref v 4))))

(define (add1 [x : Integer])
		: Integer
	(+ 1 x))

(define (sum-all [v : (Vector Integer Integer Integer Integer Integer)])
		: Integer
	(let ([i 0])
		(let ([sum 0])
			(begin (while (< i 5)
			   		  	  (let ([e (vector-ref v i)])
						  	(begin (set! sum (+ sum e))
			   		  			   (set! i (add1 i)))))
				   sum))))

(sum-all (map add1 (vector 5 15 25 35 45))) ; 10 + 20 + 30 + 40 + 50 = 150
