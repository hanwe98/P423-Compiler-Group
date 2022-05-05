#! /usr/bin/env racket
#lang racket

(require "utilities.rkt")
(require "interp-Lfun.rkt")
(require "interp-Lfun-prime.rkt")
(require "type-check-Lfun.rkt")
(require "interp-Cfun.rkt")
(require "type-check-Cfun.rkt")
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
(define ca (tests-for "functions")) ; current assignment

;(interp-tests "functions" type-check-Lfun compiler-passes interp-Lfun "functions_test" ca)

(compiler-tests "if" type-check-Lfun compiler-passes "functions_test" (list 28))