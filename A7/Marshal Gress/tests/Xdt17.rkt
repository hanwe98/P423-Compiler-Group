;#lang racket
(define (f a b c d e f g h)
	(+ a (+ b (+ c (+ d (+ e (+ f (+ g h))))))))

(f 10 20 30 40 50 60 70 80) ; 360
