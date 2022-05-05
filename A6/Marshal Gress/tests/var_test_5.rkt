;#lang racket
(+ (let ([x 1])
     (let ([ x 2])
       (let ([x 3])
         x)))
   (let ([y 4])
     (let ([y 5])
       (let ([x 6])
         (+ x y)))))
