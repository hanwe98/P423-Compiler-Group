;#lang racket

(+ (let ([x (let ([y (- 12)])
              (- y))])
     (+ x 5))
   (+ 5 (let ([x 8])
          (- x))))