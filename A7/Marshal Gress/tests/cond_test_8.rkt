;#lang racket
(let ([x #t])
  (let ([y 11])
    (let ([z 53])
      (if (and x (eq? (- z y) (+ 10 32)))
	      42 0))))
