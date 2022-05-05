;#lang racket

(if (and (eq? (+ (let ([x 1]) x)
            (let ([y 41]) y))
         42)
         (eq? (+ (let ([x 1]) 2)
                 (let ([y 41]) 40))
              42))
    42
    0)
    