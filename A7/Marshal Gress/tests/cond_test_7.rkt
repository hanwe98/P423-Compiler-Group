;#lang racket
(if (if (if (>= 15 20)
        (and (eq? 1 2)
             (or #t #f))
        (< 10 20))
    (and #t (not #t))
    (eq? (- 20 10) 10))
	0
	(if (eq? 1 1) 42 0))
