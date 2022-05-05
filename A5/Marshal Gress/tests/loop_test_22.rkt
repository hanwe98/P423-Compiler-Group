;#lang racket
;(require "../utilities.rkt")
(let ([i 0])
  (let ([fact 1])
    (let ([n (read)])
  (begin (while (< i n)
         (begin (set! fact (+ fact (- n i)))
                (set! i (+ i 1))))
		fact))))
