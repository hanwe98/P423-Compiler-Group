;#lang racket

(if (and (or (and #t #t)
             (and #f #f))
         (and (or #t #f)
              (or #f #t)))
    42 0)