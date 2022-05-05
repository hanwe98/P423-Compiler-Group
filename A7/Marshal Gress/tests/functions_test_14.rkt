(define (add-all [a0 : Integer] [a1 : Integer] [a2 : Integer] [a3 : Integer] [a4 : Integer]
				 [a5 : Integer] [a6 : Integer] [a7 : Integer] [a8 : Integer] [a9 : Integer])
		: Integer
	(+ a0
	   (+ a1
	      (+ a2
		     (+ a3
			    (+ a4
				   (+ a5
				      (+ a6
					     (+ a7
						    (+ a8
							   a9))))))))))
(- (add-all 1 2 3 4 5 6 7 8 9 10) ; 55
   13) ; 42
