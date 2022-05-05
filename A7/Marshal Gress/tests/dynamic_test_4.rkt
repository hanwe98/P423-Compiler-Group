;#lang racket
(define (f x)
	(if (not (eq? x 1)) #f 42))

(f 1)
