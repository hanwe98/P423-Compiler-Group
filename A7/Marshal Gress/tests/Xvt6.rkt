;#lang racket
;(require "../utilities.rkt")
(let ([v (vector 0 1 2 3 4 5 6 7 8 9)])
  (let ([i 0])
    (begin (while (< i 10)
                  (begin (let ([x (+ 1 (vector-ref v i))])
                           (vector-set! v i x))
                         (set! i (+ i 1))))
           (if (eq? 10 (vector-ref v 9))
               42
               777))))
