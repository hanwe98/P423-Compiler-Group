#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Rint.rkt")
(require "interp-Rvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Cvar.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(provide (all-defined-out))


;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Group members: Marshal Gress, Weifeng Han, Garrett Robinson, Nick Irmscher
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Rint examples
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; The following compiler pass is just a silly one that doesn't change
;; anything important, but is nevertheless an example of a pass. It
;; flips the arguments of +. -Jeremy
(define (flip-exp e)
  (match e
    [(Var x) e]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (Prim '- (list (flip-exp e1)))]
    [(Prim '+ (list e1 e2)) (Prim '+ (list (flip-exp e2) (flip-exp e1)))]))

(define (flip-Rint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [(_ _) (Prim '+ (list r1 r2))]))

(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Rint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (let* ([y (gensym x)]
              [new-env (dict-set env x y)])
         (Let y
              ((uniquify-exp new-env) e)
              ((uniquify-exp new-env) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

; rco-exp : Exp -> Exp
(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Let x e body)
     (let* ([newe    (rco-exp e)]
            [newbody (rco-exp body)])
       (Let x newe newbody))]
    [(Prim op es)
     (let* ([lopoad (map (λ (e) (rco-atom e)) es)]
            [newes (map (λ (pr) (car pr)) lopoad)]
            [dict (foldl (λ (pr l) (append (cdr pr) l)) '() lopoad)])
       (update (Prim op newes) dict))]))

; rco-atom : exp -> (Pair Atom (Listof (Pair Atom Exp)))
(define (rco-atom e)
  (match e
    [(Var x)
     (let* ([atm   (Var x)]
            [alist '()])
       (cons atm alist))]
    [(Int n)
     (let* ([atm   (Int n)]
            [alist '()])
       (cons atm alist))]
    [(Let x e body)
     (let* ([s (gensym 'tmp)]
            [newe    (rco-exp e)]
            [newbody (rco-exp body)]
            [atm (Var s)]
            [alist (dict-set (dict-set '() x newe)
                             s newbody)])
       (cons atm alist))]
    [(Prim op es)
     (let* ([s (gensym 'tmp)]
            [atm   (Var s)]
            [alist (let* ([key   s]
                          [lopoad (map (λ (e) (rco-atom e)) es)]
                          [newes (map (λ (pr) (car pr)) lopoad)]
                          [dict (foldl (λ (pr l) (append (cdr pr) l)) '() lopoad)]
                          [value (Prim op newes)])
                     (dict-set dict key value))])
       (cons atm alist))]))

; update : Exp Dictionary -> Exp
(define (update e dict)
  (cond
    [(dict-empty? dict) e]
    [else (let* ([x (car (car dict))]
                 [v (cdr (car dict))]
                 [body (update e (cdr dict))])
            (Let x v body))]))

; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p
    [(Program info body)
     (let ([r (explicate-tail body)])
       (CProgram info (list (cons 'start (car r)))))]))

(define (explicate-tail e)
  (match e
    [(Var x)
     (let* ([ctail (Return (Var x))]
            [vlist '()])
       (cons ctail vlist))]
    [(Int n)
     (let* ([ctail (Return (Int n))]
            [vlist '()])
       (cons ctail vlist))]
    [(Let x rhs body)
     (match-let ([(cons bodyctail bodyvlist) (explicate-tail body)])
       (match-let ([(cons rhsctail rhsvlist) (explicate-assign rhs x bodyctail)])
         (let* ([ctail rhsctail]
                [vlist (append (cons x rhsvlist) bodyvlist)])
           (cons ctail vlist))))]
    [(Prim op es)
     (let* ([ctail (Return (Prim op es))]
            [vlist '()])
       (cons ctail vlist))]
    [else (error "explicate_tail unhandled case" e)]))

(define (explicate-assign e x cont)
  (match e
    [(Var s) 
     (let* ([ctail (Seq (Assign (Var x) (Var s)) cont)]
            [vlist '()])
       (cons ctail vlist))]
    [(Int n)
     (let* ([ctail (Seq (Assign (Var x) (Int n)) cont)]
            [vlist '()])
       (cons ctail vlist))]
    [(Let s rhs body)
     (match-let ([(cons bodyctail bodyvlist) (explicate-assign body x cont)])
       (match-let ([(cons rhsctail rhsvlist) (explicate-assign rhs s bodyctail)])
         (let* ([ctail rhsctail]
                [vlist (append (cons s rhsvlist) bodyvlist)])
           (cons ctail vlist))))]
    [(Prim op es)
     (let* ([ctail (Seq (Assign (Var x) (Prim op es)) cont)]
            [vlist '()])
       (cons ctail vlist))]
    [else (error "explicate_tail unhandled case" e)]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

#|
   C_Var Grammar
   atm ::= int | var

   exp ::= atm | (read) | (- atm) | (+ atm atm)

   stmt ::= var = exp; 

   tail ::= return exp; | stmt tail 

   C_Var ::= (label: tail)^+

   ===========================================================

   pseudo-x86 Grammar
   reg ::= rsp | rbp | rax | rbx | rcx | rdx | rsi | rdi |
           r8 | r9 | r10 | r11 | r12 | r13 | r14 | r15

   arg ::= (Imm int) | (Reg reg) | (Deref reg int) | (Var x)

   instr ::= (Instr addq (arg arg)) | (Instr subq (arg arg))
             | (Instr movq (arg arg)) | (Instr negq (arg))
             | (Callq label int) | (Retq) | (Pushq arg) | (Popq arg) | (Jmp label)

   block ::= (Block info (instr …))

   pseudo-x86 ::= (X86Program info ((label . block)…))
|#

; si-atm : atm -> pseudo-x86
(define si-atm
  (λ (atm)
    (match atm
      [(Int n) (Imm n)]
      [(Var x) (Var x)]
      [else (error "expected an atom for si-atm, instead got" atm)])))

; si-stmt : stmt -> pseudo-x86
(define si-stmt
  (λ (stmt)
    (match stmt
      [(Assign (Var x) exp)
       (match exp
         [(Prim '+ `(,atm1 ,atm2))
          (cond ; prevent needless code by seeing if x is an addend
            [(equal? (Var x) atm1)
             (list (Instr 'addq (list (si-atm atm2) (Var x))))]
            [(equal? (Var x) atm2)
             (list (Instr 'addq (list (si-atm atm1) (Var x))))]
            [else (append (si-exp exp)
                          (list (Instr 'movq (list (Reg 'rax) (Var x)))))])]
         [else (append (si-exp exp)
                       (list (Instr 'movq (list (Reg 'rax) (Var x)))))])]
      [else (error "expected a stmt for si-stmt, instead got" stmt)])))

; si-tail : tail -> pseudo-x86
(define si-tail
  (λ (tail)
    (match tail
      [(Return exp)
       (append (si-exp exp)
               (list (Jmp 'conclusion)))]
      [(Seq stmt tail)
       (append (si-stmt stmt)
               (si-tail tail))]
      [else (error "expected a tail for si-tail, instead got" tail)])))

; si-exp : exp -> pseudo-x86
(define si-exp
  (λ (exp)
    (match exp
      [(Prim read '())
       (list (Callq 'read_int 0))]
      [(Prim '- `(,atm))
       (list (Instr 'movq (list (si-atm atm)
                                (Reg 'rax)))
             (Instr 'negq (list (Reg 'rax))))]
      [(Prim '+ `(,atm1 ,atm2))
       (list (Instr 'movq (list (si-atm atm1)
                                (Reg 'rax)))
             (Instr 'addq (list (si-atm atm2)
                                (Reg 'rax))))]
      [else (list (Instr 'movq (list (si-atm exp) (Reg 'rax))))])))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match-let ([(CProgram types (list (cons label tail))) (type-check-Cvar p)])
    (X86Program types
                (list (cons label
                            (Block '() (si-tail tail)))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (match p
    [(X86Program info lopr)
     (let* ([pr (car lopr)]
            [label (car pr)]
            [block (cdr pr)])
       (match block
         [(Block binfo instructions)
          (let* ([instrs instructions]
                 [alist (refer-list (map car (cdr (car info))) -8)])
            (X86Program
             `((stack-space . ,(stack-size (dict-ref info 'locals-types))))
             (list (cons label
                         (Block binfo (assign-homes-instrs instrs alist))))))]))]))

; refer-list : Dictionary Integer -> Dicationary
(define (refer-list info counter)
  (cond
    [(empty? info) empty]
    [else
     (dict-set (refer-list (cdr info) (- counter 8))
               (car info) (Deref 'rbp counter))]))

; stack-size : Dictionary -> Integer
; make stack-size a multiple of 16
(define stack-size
  (λ (dict)
    (let ([dict-size (length dict)])
      (if (even? dict-size)
          (* dict-size 8)
          (+ (* dict-size 8) 8)))))

; assign-homes-instrs : [ListOf Instr] [ListOf [PairOf Symbol (Deref reg int)]] -> [ListOf Instr]
(define (assign-homes-instrs instrs alist)
  (cond
    [(empty? instrs) empty]
    [else (cons (assign-homes-single (car instrs) alist)
                (assign-homes-instrs (cdr instrs) alist))]))

; assign-homes-single : Instr [ListOf [PairOf Symbol (Deref reg int)]] -> Instr
(define (assign-homes-single instr alist)
  (match instr
    [(Instr op `,ls)
     (Instr op (map (λ (arg)
                      (match arg
                        [(Var var) (dict-ref alist var)]
                        [else arg]))
                    ls))]
    [else instr])) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info lopr)
     (let* ([pr (car lopr)]
            [label (car pr)]
            [block (cdr pr)])
       (match block
         [(Block binfo instructions)
          (X86Program
           info
           (list (cons label
                       (Block binfo
                              (foldr (λ (this rest) (append (patch-instructions-instr this) rest))
                                     '()
                                     instructions)))))]))]))

; patch-instructions-instr : Instr -> [ListOf Instr]
(define (patch-instructions-instr instr)
  (match instr
    [(Instr op `(,arg1 ,arg2))
     (cond
       [(or (equal? op 'addq)
            (equal? op 'movq)
            (equal? op 'subq))
        (cond
          [(both-memory? (list arg1 arg2)) (list (Instr 'movq (list arg1 (Reg 'rax)))
                                                 (Instr op (list (Reg 'rax) arg2)))] 
          [else (list instr)])]
       [else (list instr)])]
    [else (list instr)]))

; both-memory? : [ListOf Arg] -> Boolean
(define (both-memory? loa)
  (foldr (λ (a rest) (match a
                       [(Deref reg int) rest]
                       [else false]))
         true
         loa))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info lopr)
     (let* ([pr (car lopr)]
            [label (car pr)]
            [block (cdr pr)])
       (match block
         [(Block binfo instr)
          (X86Program info (list 
                            (build-main info)
                            (build-start instr)
                            (build-conclusion info)))]))]))

(define (build-main info)
  (cons 'main
        (Block '()
               (list
                (Instr 'pushq (list (Reg 'rbp)))
                (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))
                (Instr 'subq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp)))
                (Jmp 'start)))))

(define (build-start instr)
  (cons 'start
        (Block '()
               instr)))

(define (build-conclusion info)
  (cons 'conclusion
        (Block '()
               (list
                (Instr 'addq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp)))
                (Instr 'popq (list (Reg 'rbp)))
                (Retq)))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("uniquify" ,uniquify ,interp-Rvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Rvar)
     ("explicate control" ,explicate-control ,interp-Cvar)
     ("instruction selection" ,select-instructions ,interp-x86-0)
     ("assign homes" ,assign-homes ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

