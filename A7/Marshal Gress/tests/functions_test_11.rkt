;#lang racket
(define (triangular-tail [n : Integer] [acc : Integer]) : Integer
  (if (eq? n 0) acc
      (triangular-tail (- n 1) (+ n acc))))
(triangular-tail 6 0)