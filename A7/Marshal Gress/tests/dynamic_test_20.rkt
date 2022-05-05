;#lang racket
(define (f a b c d e f g)
	(+ a (+ b (+ c (+ d (+ e (+ f g)))))))

(f 10 20 30 40 50 60 70) ; 280
