;#lang racket
(let ([b 19])
  (+ b (let ([b 9])
         (- b))))