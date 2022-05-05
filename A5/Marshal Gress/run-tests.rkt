#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Rvec.rkt")
(require "type-check-Rvec.rkt")
(require "interp-Cvec.rkt")
(require "type-check-Cvec.rkt")
(require "interp.rkt")
(require "compiler.rkt")

;(debug-level 1)
(AST-output-syntax 'concrete-syntax)

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

(interp-tests "tuples" type-check-Rvec compiler-passes interp-Rvec "vectors_test" (tests-for "vectors"))

;(compiler-tests "if" type-check-Rif compiler-passes "cond_test" (list 32))