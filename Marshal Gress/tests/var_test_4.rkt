;#lang racket

(let ([a (let ([a 20])
           (let ([a 30])
             (+ a 10)))])
  (+ a (let ([a 25])
         (+ a (let ([b 5]) (- b))))))