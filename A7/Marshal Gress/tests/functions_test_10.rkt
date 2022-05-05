;#lang racket
(define (triangular [n : Integer]) : Integer
  (if (eq? n 0) 0
      (+ n (triangular (- n 1)))))
(triangular 6)