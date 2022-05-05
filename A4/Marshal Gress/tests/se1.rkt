;#lang racket
(let ([x (read)])
  (let ([y x])
    (+ (+ (begin (set! x (read))
                 x)
          x)
       (+ y
          (begin (set! y (read))
                 y)))))