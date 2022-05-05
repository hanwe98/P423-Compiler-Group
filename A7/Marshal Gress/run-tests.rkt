#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Ldyn.rkt")
(require "interp-Lany.rkt")
(require "interp-Lany-prime.rkt")
(require "type-check-Lany.rkt")
(require "interp-Cany.rkt")
(require "type-check-Cany.rkt")
(require "interp.rkt")
(require "compiler.rkt")

;(debug-level 1)
;(AST-output-syntax 'concrete-syntax)

;; all the files in the tests/ directory with extension ".rkt".
(define all-tests
  (map (lambda (p) (car (string-split (path->string p) ".")))
       (filter (lambda (p)
                 (string=? (cadr (string-split (path->string p) ".")) "rkt"))
               (directory-list (build-path (current-directory) "tests")))))

(define (tests-for r)
  (map (lambda (p)
         (caddr (string-split p "_")))
       (filter
        (lambda (p)
          (string=? r (car (string-split p "_"))))
        all-tests)))
(define ca (tests-for "dynamic")) ; current assignment
(define remove-xs
  (filter (λ (n)
            (not (string=? "22" n)))
          ca))
;(displayln remove-xs)

;(interp-tests "dynamic" #f compiler-passes interp-Ldyn "dynamic_test" (list 10))

(compiler-tests "if" #f compiler-passes "dynamic_test" remove-xs)
