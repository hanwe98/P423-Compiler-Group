#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Rwhile.rkt")
(require "type-check-Rwhile.rkt")
(require "interp-Cwhile.rkt")
(require "type-check-Cwhile.rkt")
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

(interp-tests "loop" type-check-Rwhile compiler-passes interp-Rwhile "loop_test" (tests-for "loop"))

;(compiler-tests "if" type-check-Rif compiler-passes "cond_test" (list 32))