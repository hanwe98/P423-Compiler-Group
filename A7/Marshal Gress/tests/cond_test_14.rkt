(if (and (<= (let ([x 20]) x)
			 (let ([y 30]) (- y 10)))
		#t)
	42 0)
