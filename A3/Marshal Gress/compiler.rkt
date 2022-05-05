#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Rif.rkt")
(require "type-check-Rif.rkt")
(require "interp-Cif.rkt")
(require "type-check-Cif.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(require graph)
(require "graph-printing.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")
(provide (all-defined-out))
(require racket/trace)

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Group members: Marshal Gress, Weifeng Han, Nick Irmscher
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; shrink

; shrink : Rif -> Rif
(define (shrink p)
  (match p
    [(Program info exp)
     (Program info (shrink-exp exp))]))

; shrink-exp : exp -> exp
(define (shrink-exp e)
  (match e
    [(Prim 'and `(,e1 ,e2)) (If (shrink-exp e1) (shrink-exp e2) (Bool #f))]
    [(Prim 'or  `(,e1 ,e2)) (If (shrink-exp e1) (Bool #t) (shrink-exp e2))]
    [(Prim op ls)
     (Prim op (map shrink-exp ls))]
    [(Let x e body)
     (Let x (shrink-exp e) (shrink-exp body))]
    [(If cnd thn els)
     (If (shrink-exp cnd) (shrink-exp thn) (shrink-exp els))]
    [else e]))

;(shrink-exp (parse-exp '(and (< 10 20) (>= 30 40))))
;(shrink-exp (parse-exp '(or (< 10 20) (>= 30 40))))
#;(shrink-exp (parse-exp '(if (and (or (and #t #t)
                                     (and #f #f))
                                 (and (or #t #f)
                                      (or #f #t)))
                            42 0)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; uniquify

#| Rif
    bool ::= #t | #f

    cmp ::= eq? | < | <= | > | >=

    op ::= cmp | read | + | - | and | or | not

    exp ::= (Int int) | (Var var) | (Let var exp exp)
            | (Prim op (exp…))
            | (Bool bool) | (If exp exp exp)

    LIf ::= (Program ’() exp)
|#

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Let x e body)
       (let* ([y (gensym x)]
              [new-env (dict-set env x y)])
         (Let y
              ((uniquify-exp new-env) e)
              ((uniquify-exp new-env) body)))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))]
      [(If test then else)
       (If ((uniquify-exp env) test)
           ((uniquify-exp env) then)
           ((uniquify-exp env) else))])))

#;((uniquify-exp '())
 (parse-exp '(let ([x 20])
               (if (>= x (let ([x 10])
                       (+ x x)))
                   (< x 15)
                   (> x (let ([x 15])
                          x))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; remove complex operands

#| Rif_ANF
atm ::= (Int int) | (Var var) | (Bool bool)

exp ::= atm | (Prim read ())
| (Prim - (atm)) | (Prim + (atm atm))
| (Let var exp exp)
| (Prim not (atm))
| (Prim cmp (atm atm)) | (If exp exp exp)

Rif_ANF ::= (Program () exp)
|#

; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))

; rco-exp : Exp -> Exp
(define (rco-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Let x e body)
     (Let x (rco-exp e) (rco-exp body))]
    [(If cnd thn els)
     (If (rco-exp cnd) (rco-exp thn) (rco-exp els))]
    [(Prim op es)
     (define lod (map rco-atom es))
     (define newes (map car lod))
     (define dict (foldl (λ (pr l) (append (cdr pr) l)) '() lod))
     (update (Prim op newes) dict)]))

; rco-atom : Exp -> (list Atom [DictionaryOf Symbol Exp])
(define (rco-atom e)
  (match e
    [(Var x)
     (define atm (Var x))
     (define alist '())
     (cons atm alist)]
    [(Int n)
     (define atm (Int n))
     (define alist '())
     (cons atm alist)]
    [(Bool b)
     (define atm (Bool b))
     (define alist '())
     (cons atm alist)]
    [(If cnd thn els)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define value (If (rco-exp cnd) (rco-exp thn) (rco-exp els)))
     (define alist (dict-set '() key value))
     (cons atm alist)]
    [(Let x e body)
     (define key (gensym 'tmp))
     (define newe (rco-exp e))
     (define newbody (rco-exp body))
     (define atm (if (is-atom newbody) newbody (Var key)))
     (define alist (if (is-atom newbody) (dict-set '() x newe)
                       (dict-set (dict-set '() x newe) key newbody)))
     (cons atm alist)]
    [(Prim op es)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define lod (map rco-atom es))
     (define es^ (map car lod))
     (define dict (foldl (λ (pr l) (append (cdr pr) l)) '() lod))
     (define value (Prim op es^))
     (define alist (dict-set dict key value))
     (cons atm alist)]))

(define is-atom
  (λ (exp)
    (match exp
      [(Var x) true]
      [(Int n) true]
      [(Bool b) true]
      [else false])))

(define (update e dict)
  (cond
    [(dict-empty? dict) e]
    [else (let* ([x (car (car dict))]
                 [v (cdr (car dict))]
                 [body (update e (cdr dict))])
            (Let x v body))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; explicate control

#| Cif
atm ::= (Int int) | (Var var) | (Bool bool)

cmp ::= eq? | < | <= | > | >=

exp ::= atm | (Prim read ())
| (Prim - (atm)) | (Prim + (atm atm)) | (Prim - (atm atm))
| (Prim ’not (atm)) | (Prim ’cmp (atm atm))

stmt ::= (Assign (Var var) exp)

tail ::= (Return exp) | (Seq stmt tail) | (Goto label)
| (IfStmt (Prim cmp (atm atm)) (Goto label) (Goto label))

CIf ::= (CProgram info ((label . tail)…))
|#

;; explicate-control : Rif -> Cif
(define (explicate-control p)
  (match p
    [(Program info body)
     (let ([r (explicate-tail body)])
       (dict-set! blocks 'start r)
       (CProgram info (hash->list blocks)))]))

(define blocks (make-hash)) ; [Dictionaryof label tail]

; explicate-tail : RIf_exp -> Cif_tail
; generates code for expressions in tail position
(define (explicate-tail e)
  (match e
    [(Var x) (Return e)]
    [(Int n) (Return e)]
    [(Bool b) (Return e)]
    [(Let x rhs body)
     (let* ([bodyctail (explicate-tail body)])
       (explicate-assign rhs x bodyctail))]
    [(Prim op es) (Return e)]
    [(If test then else)
     (let* ([cthen (explicate-tail then)]
            [celse (explicate-tail else)])
       (explicate-pred test cthen celse))]
    [else (error "explicate_tail unhandled case" e)]))

; explicate-assign : RIf_exp var CIf_tail -> Cif_tail
; generates code for a `let` by cases on the right-hand side expression
(define (explicate-assign e x cont)
  (match e
    [(Var s) (Seq (Assign (Var x) e) cont)]
    [(Int n) (Seq (Assign (Var x) e) cont)]
    [(Bool b) (Seq (Assign (Var x) e) cont)]
    [(Let s rhs body)
     (let* ([bodyctail (explicate-assign body x cont)])
       (explicate-assign rhs s bodyctail))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [(If test then else)
     (let* ([cont-goto (create-block cont)]
            [then-tail (explicate-assign then x cont-goto)]
            [else-tail (explicate-assign else x cont-goto)])
       (explicate-pred test then-tail else-tail))]
    [else (error "explicate_tail unhandled case" e)]))

; explicate-pred : LIf_exp CIf_tail CIf_tail -> CIf_tail
; generates code for an `if` expression by cases on the condition.
(define (explicate-pred cnd thn els)
  (match cnd
    [(Var x)
     (let ([thn-goto (create-block thn)]
           [els-goto (create-block els)])
       (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) ; x is a bool, (and x #t) works
               thn-goto
               els-goto))]
    [(Let x rhs body) ; might be right
     (let ([body-tail (explicate-pred body thn els)])
       (explicate-assign rhs x body-tail))]
    [(Prim 'not (list e))
     (explicate-pred e els thn)] ; switched thn and els
    [(Prim op es)
     #:when (cmp? op)
     (let ([thn-goto (create-block thn)]
           [els-goto (create-block els)])
       (IfStmt cnd
               thn-goto
               els-goto))]
    [(Bool b) (if b thn els)]
    [(If cnd^ thn^ els^)
     (let* ([thn-goto (create-block thn)]
            [els-goto (create-block els)]
            [thn^-tail (explicate-pred thn^ thn-goto els-goto)]
            [els^-tail (explicate-pred els^ thn-goto els-goto)])
       (explicate-pred cnd^ thn^-tail els^-tail))]
    [else (error "explicate_pred unhandled case" cnd)]))

; create-block : Cif_tail -> (Goto label)
(define (create-block tail)
  (let ([label (gensym 'block)])
    (dict-set! blocks label tail)
    (Goto label)))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; select instructions

; si-atm : atm -> x86If
(define si-atm
  (λ (atm)
    (match atm
      [(Int n) (Imm n)]
      [(Var x) (Var x)]
      [(Bool b)
       (match b
         [#t (Imm 1)]
         [#f (Imm 0)])]
      [else (error "expected an atom for si-atm, instead got" atm)])))

; si-stmt : stmt -> x86If
(define si-stmt
  (λ (stmt)
    (match stmt
      [(Assign (Var x) exp)
       (match exp
         [(Int n) (list (Instr 'movq (list (si-atm exp) (Var x))))]
         [(Var y) (list (Instr 'movq (list (si-atm exp) (Var x))))]
         [(Bool b) (list (Instr 'movq (list (si-atm exp) (Var x))))]
         
         [(Prim '+ `(,atm1 ,atm2))
          (cond ; prevent needless code by seeing if x is an addend
            [(equal? (Var x) atm1)
             (list (Instr 'addq (list (si-atm atm2) (Var x))))]
            [(equal? (Var x) atm2)
             (list (Instr 'addq (list (si-atm atm1) (Var x))))]
            [else (append (si-exp exp)
                          (list (Instr 'movq (list (Reg 'rax) (Var x)))))])]

         [(Prim '- `(,atm1 ,atm2))
          (cond ; prevent needless code by seeing if x is an addend
            [(equal? (Var x) atm1)
             (list (Instr 'subq (list (si-atm atm2) (Var x))))]
            [else (append (si-exp exp)
                          (list (Instr 'movq (list (Reg 'rax) (Var x)))))])]

         [(Prim op `(,atm1 ,atm2))
          #:when (cmp? op)
          (let ([arg1 (si-atm atm1)]
                [arg2 (si-atm atm2)]
                [cc (set-suffix op)])
            (list (Instr 'cmpq (list arg2 arg1))
                  (Instr 'set (list cc (ByteReg 'al)))
                  (Instr 'movzbq (list (ByteReg 'al) (Var x)))))]
         
         [(Prim 'not `(,atm1))
          (cond
            [(equal? (Var x) atm1)
             (list (Instr 'xorq (list (Imm 1) (Var x))))]
            [else
             (let ([arg (si-atm atm1)])
               (list (Instr 'movq (list arg (Var x)))
                     (Instr 'xorq (list (Imm 1) (Var x)))))])]
         
         [else (append (si-exp exp)
                       (list (Instr 'movq (list (Reg 'rax) (Var x)))))])]
      [else (error "expected a stmt for si-stmt, instead got" stmt)])))

; set-suffix : cmp -> cc
(define (set-suffix cmp)
  (match cmp
    ['eq? 'e]
    ['< 'l]
    ['<= 'le]
    ['> 'g]
    ['>= 'ge]))

; cmp? : Symbol -> Boolean
(define (cmp? op)
  (or (eq? op 'eq?) (eq? op '<) (eq? op '<=)
      (eq? op '>) (eq? op '>=)))

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
      [(Goto label)
       (list (Jmp label))]
      [(IfStmt (Prim cmp `(,atm1 ,atm2))
               (Goto l1) (Goto l2))
       (let ([cc (set-suffix cmp)]
             [arg1 (si-atm atm1)]
             [arg2 (si-atm atm2)])
         (list (Instr 'cmpq (list arg2 arg1))
               (JmpIf cc l1)
               (Jmp l2)))]
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
      [(Prim '- `(,atm1 ,atm2))
       (list (Instr 'movq (list (si-atm atm2)
                                (Reg 'rax)))
             (Instr 'subq (list (si-atm atm1)
                                (Reg 'rax))))]
      [else (list (Instr 'movq (list (si-atm exp) (Reg 'rax))))])))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match-let ([(CProgram types blocks) (type-check-Cif p)])
    (X86Program types
                (for/list ([block blocks])
                  (match-let ([(cons label tail) block])
                    (cons label (Block '() (si-tail tail))))))))

#;(interp-x86-1 (select-instructions (CProgram '() `((start . ,(Seq (Assign (Var 'x)
                                                            (Int 50))
                                                    (Return (Prim '- (list (Var 'x)
                                                                           (Int 8))))))))))
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; liveness analysis

#|  x86If
bytereg ::= ah | al | bh | bl | ch | cl | dh | dl

arg ::= (Imm int) | (Reg reg) | (Deref reg int) | (ByteReg bytereg)

cc ::= e | l | le | g | ge

instr ::= (Instr addq (arg arg)) | (Instr subq (arg arg))
| (Instr ’movq (arg arg)) | (Instr negq (arg))
| (Callq label int) | (Retq) | (Instr 'popq (arg))
| (Instr 'pushq (arg)) | (Jmp label)
| (Instr xorq (arg arg)) | (Instr cmpq (arg arg))
| (Instr set (cc arg)) | (Instr movzbq (arg arg))
| (JmpIf 'cc' label)

block ::= (Block info (instr …))

x86If ::= (X86Program info ((label . block)…))
|#

(define label->live
  (make-hash))

; uncover-lives : x86Program -> x86Program
(define (uncover-lives p)
  (match p
    [(X86Program info labels-blocks)
     ; initialize label->live
     (hash-set! label->live
                'conclusion
                (list (set (Reg 'rax) (Reg 'rsp))))

     (define rtsort (block-interference labels-blocks)) ; [Listof label]
     (define rtsort-blocks
       (for/foldr ([acc '()])
         ([l rtsort]
          #:when (not (eq? l 'conclusion))) ; no conclusion block yet
         (cons (cons l (dict-ref labels-blocks l))
               acc)))
     
     (X86Program
      info
      (for/list ([label-block rtsort-blocks])
        (match label-block
          [(cons label (Block binfo loi))
           (define block-lives (uncover-live-loi loi))
           (hash-set! label->live label block-lives)
           (cons label
                 (Block `(,(cons 'lives block-lives))
                        loi))])))]))

; block-interference : [Listof [Pair label Block]] -> [Listof label]
; returns reverse topological ordering of blocks
(define (block-interference blocks)
  (define edge-list (make-hash))
  
  (for ([b blocks])
    (match b
      [(cons label (Block binfo loi))
       (for/list ([instr loi]
                  #:when (or (Jmp? instr)
                             (JmpIf? instr)))
         (match instr
           [(Jmp label^)
            (hash-set! edge-list
                       (gensym 'tmp)
                       (list label label^))]
           [(JmpIf cc label^)
            (hash-set! edge-list
                       (gensym 'tmp)
                       (list label label^))]
           [else (error "expected Jmp instruction in block-interference, got" instr)]))]
      [else (error "expected block in block-interference, got" b)]))
  
    (reverse (tsort (make-multigraph (hash-values edge-list)))))

#;(block-interference
 (X86Program-blocks
  (select-instructions
   (explicate-control
    (remove-complex-opera*
     (uniquify
      (shrink
       (read-program
        "tests/cond_test_14.rkt"))))))))

#;(block-interference
 (list (cons 'start
             (Block '()
                    (list (Callq 'read_int 0)
                          (Callq 'read_int 0)
                          (Callq 'read_int 0)
                          (JmpIf 'e 'conclusion)
                          (Jmp 'block1))))
       (cons 'block1
             (Block '()
                    (list (Callq 'read_int 0)
                          (Callq 'read_int 0)
                          (Jmp 'block3))))
       (cons 'block2
             (Block '()
                    (list (Callq 'read_int 0)
                          (Jmp 'block4))))
       (cons 'block3
             (Block '()
                    (list (Callq 'read_int 0)
                          (Callq 'read_int 0)
                          (Callq 'read_int 0)
                          (Callq 'read_int 0)
                          (Jmp 'block2))))
       (cons 'block4
             (Block '()
                    (list (Jmp 'block1))))
       (cons 'conclusion
             (Block '()
                    (list (Callq 'read_int 0))))))

; uncover-live-loi : [Listof instr] [Set arg] -> [Listof [Setof arg]]
; returns list of live-after sets
(define (uncover-live-loi loi) ; ila = initial live after
  (foldr
   (λ (instr so-far)
     (cons (set-union
            (set-subtract
             (if (empty? so-far) (set) (car so-far))
             (locations-written instr))
            (locations-read instr))
           so-far))
   '()
   loi))
     
; locations-read : instr -> [Setof arg]
(define (locations-read instr)
  (match instr
    [(Instr 'movq `(,arg1 ,arg2)) ; read 1st
     (locations-arg arg1)]
    [(Instr 'set `(,cc ,arg)) ; read 1st 
     (locations-arg arg)]
    [(Instr 'movzbq `(,arg1 ,arg2)) ; read 1st
     (locations-arg arg1)]
    [(Instr op `(,arg1 ,arg2)) ; add/subtract/cmp/xorq (read, read)
     (set-union (locations-arg arg1)
                (locations-arg arg2))]
    [(Instr op `(,arg)) ; negq, popq, pushq
     (locations-arg arg)]
    [(Callq label arity)
     (locations-call caller-save arity)]
    [(Retq)
     (set)]
    [(Jmp label)
     (car (dict-ref label->live label))] ; beginning of the block
    [(JmpIf cc label)
     (car (dict-ref label->live label))])) ; beginning of the block
      
; locations-written : instr -> [Set arg]
(define (locations-written instr)
  (match instr
    [(Instr 'cmpq `(,arg1 ,arg2)) ; read, read
     (set)]
    [(Instr op `(,arg1 ,arg2)) ; addq, subq, movq, xorq, set, movzbq (read, write)
     (locations-arg arg2)]
    [(Instr 'negq `(,arg)) ; write
     (locations-arg arg)]
    ((Instr push/pop `(,arg)) ; read
     (set))
    [(Callq label arity)
     caller-save]
    [(Retq) (set)]
    [(Jmp label) (set)]
    [(JmpIf cc label) (set)]))

; locations-arg : arg -> [Set arg]
(define (locations-arg arg)
  (match arg
    [(Imm int) (set)]
    [else (set arg)]))

; locations-call : [Listof Register] Integer -> [Set arg]
(define (locations-call regs arity)
  (cond
    [(= arity 0) (set)]
    [else (set-union (car regs)
                     (locations-call (cdr regs)
                                     (sub1 arity)))]))


(define ex
  (list (Instr 'movq (list (Imm 1) (Var 'v)))
        (Instr 'movq (list (Imm 42) (Var 'w)))
        (Instr 'movq (list (Var 'v) (Var 'x)))
        (Instr 'addq (list (Imm 7) (Var 'x)))
        (Instr 'movq (list (Var 'x) (Var 'y)))
        (Instr 'movq (list (Var 'x) (Var 'z)))
        (Instr 'addq (list (Var 'w) (Var 'z)))
        (Instr 'movq (list (Var 'y) (Var 't)))
        (Instr 'negq (list (Var 't)))
        (Instr 'movq (list (Var 'z) (Reg 'rax)))
        (Instr 'addq (list (Var 't) (Reg 'rax)))
        (Jmp 'conclusion)))
#;(uncover-live-loi
   ex
   (set))

(define ex2
  (list
   (Instr 'movq (list (Imm 10) (Var 'x13598))) ; rsp
   (Instr 'movq (list (Imm 5) (Var 'tmp13600))) ; rsp, x13598
   (Instr 'addq (list (Var 'x13598) (Var 'tmp13600))) ; rsp, tmp13600, x13598
   (Instr 'movq (list (Imm 20) (Var 'y13599))) ; rsp, tmp13600
   (Instr 'movq (list (Var 'y13599) (Var 'tmp13601))) ; rsp, tmp13600, y13599
   (Instr 'addq (list (Imm 17) (Var 'tmp13601))) ; rsp, tmp13601, tmp13600
   (Instr 'movq (list (Var 'tmp13600) (Reg 'rax))) ; rsp, tmp13601, tmp13600
   (Instr 'addq (list (Var 'tmp13601) (Reg 'rax))) ; rsp, rax, tmp13601
   (Jmp 'conclusion))) ; rsp, rax
#;(uncover-live-loi
   ex2
   (set))
#;(uncover-lives
 (X86Program '()
             (list (cons 'start
                         (Block '()
                                ex2)))))

#;(uncover-lives (select-instructions
                (CProgram '()
                          `((start . ,(Seq (Assign (Var 'x)
                                                   (Int 50))
                                           (Return (Prim '- (list (Var 'x)
                                                                  (Int 8))))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; build interference graph

; build-inter-graph : X86Program -> X86Program
(define (build-inter-graph p)
  (match p
    [(X86Program info labels-blocks)
     (define blocks (dict-values labels-blocks))
     (define all-live-sets
       (for/foldr ([acc '()])
                  ([b blocks])
         (append (dict-ref (Block-info b) 'lives)
                 acc)))
     (define all-instr
       (for/foldr ([acc '()])
                  ([b blocks])
         (append (Block-instr* b)
                 acc)))
     
     (X86Program (dict-set info
                           'conflicts
                           (big-loi all-instr all-live-sets))
                 labels-blocks)]))

#|
1. If instruction Ik is a move instruction, movq s, d, then add the edge (d, v) for
every v ∈ Lafter(k) unless v = d or v = s.
2. For any other instruction Ik, for every d ∈ W(k) add an edge (d, v) for every
v ∈ Lafter(k) unless v = d.
|#
; big-loi : [Listof instr] [Listof [Set arg]] -> [Graph arg]
(define (big-loi loi live-after)
  (define graph (undirected-graph '()))
  (for ([set live-after])
    (for ([arg (set->list set)])
      (add-vertex! graph arg)))
  
  (for ([instr loi]
        [lak live-after])
    (match instr
      [(Instr op `(,s ,d))
       #:when (or (eq? op 'movq) (eq? op 'movzbq))
       (for ([v (set->list lak)]
             #:when (not (or (arg-eq? v d)
                             (arg-eq? v s))))
         (add-edge! graph d v))]
      
      [(Instr op `(,s ,d))
       ;#:when (not (cmp? op)) ; cmp doesn't write
       (for ([v (set->list lak)]
             #:when (not (arg-eq? v d)))
         (add-edge! graph d v))]
      
      [(Instr op `(,d))
       #:when (and (not (eq? op 'pushq))
                   (not (eq? op 'popq)))
       (for ([v (set->list lak)]
             #:when (not (arg-eq? v d)))
         (add-edge! graph d v))]
      
      [(Callq label n)
       (for ([d (set->list caller-save)])
         (for ([v (set->list lak)]
               #:when (not (arg-eq? v d)))
           (add-edge! graph d v)))]
      
      [_ graph])) ; Retq doesn't write
  graph)

; arg-eq? : arg arg -> Boolean
(define (arg-eq? arg1 arg2)
  (match arg1
    [(Imm n) #f] ; won't write to an Imm
    [(Reg r)
     (match arg2
       [(Reg r1) (eq? r r1)]
       [_ #f])]
    [(Var x)
     (match arg2
       [(Var y) (eq? x y)]
       [_ #f])]
    [(Deref r n)
     (match arg2
       [(Deref r1 n1)
        (and (eq? r r1)
             (eq? n n1))]
       [_ #f])]
    [_ (error "arg-eq? : expected an arg for arg1, got" arg1)]))



;(print-graph (big-loi ex (uncover-live-loi ex (set))))
(define test-graph
 (dict-ref (X86Program-info
            (build-inter-graph
             (uncover-lives
              (select-instructions
               (explicate-control
                (remove-complex-opera*
                 (uniquify
                  (shrink
                   (read-program
                    "tests/cond_test_14.rkt")))))))))
           'conflicts))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; allocate-registers : pseudo-x86 -> pseudo-x86
(define (allocate-registers p)
  (match p
    [(X86Program info labels-blocks)
     (define graph (dict-ref info 'conflicts))
     (define dict (append (ar-regs graph) (ar-vars graph))) ; [Dictionaryof Var/Reg Number]
     (define color-map (color-to-locations dict)) ;; [DictionaryOf Var/Reg Location]
     
     (define new-info (dict-set info 'used-callee (filter callee? (set->list (list->set (map cdr color-map))))))
     (define new-info2 (dict-set new-info 'colors color-map))
     (define stack-space (stack-size (set->list (list->set (map cdr color-map)))))
     (define new-info3 (dict-set new-info2 'stack-space stack-space))
     
     (define new-blocks
       (for/list ([lb labels-blocks])
         (match (cdr lb)
           [(Block binfo instrs)
            (cons (car lb)
                  (Block binfo
                         (assign-homes-instrs instrs
                                              (dict-ref new-info3
                                                        'colors))))])))
     
     (X86Program
      new-info3
      new-blocks)]))

; An Arg is one of :
; - (Reg Symbol) ;; Register
; - (Var Symbol) ;; Var
; - (Imm Number) ;; Imm

; ar-regs : Graph -> [DictionaryOf Arg Number]
; takes a Graph and return its mapping from Registers to colors
(define (ar-regs g)
  (bond-reg (filter is-reg? (sequence->list (in-vertices g)))))

; is-reg? : Arg -> Boolean
(define (is-reg? a)
  (match a
    [(Reg reg) true]
    [else false]))

; bond-reg : [ListOf Register] -> [DictionaryOf Register Number]
(define (bond-reg lor)
  (cond
    [(empty? lor) empty]
    [else (let ([rest (bond-reg (rest lor))])
            (dict-set rest (car lor) (- 0 (add1 (dict-count rest)))))]))

; ar-graph : Graph -> [DictionaryOf Arg Number]
(define ar-vars ;; change [ListOf Color] to [SetOf Color] later
  (λ (g)
    (let* ([var-satur-list (make-hash)] ;; [DictionaryOf Var [SetOf Color]]
           [var-handle-list (make-hash)];; [DictionaryOf Var Handle]
           [ls (sequence->list (in-vertices g))]
           [lovar (filter (λ (a) (not (is-reg? a))) ls)]) 
      (begin (for/list ([var ls]) ;; initialize var-satur-list
               (dict-set! var-satur-list var (set)))
             (define pq              ;; initialize pq
               (make-pqueue (λ (n1 n2) (> (set-count (dict-ref var-satur-list n1))
                                          (set-count (dict-ref var-satur-list n2))))))
             (for/list ([var lovar]) ;; initialize var-satur-list
               (dict-set! var-handle-list var (pqueue-push! pq var)))
             ;; var-handle-list and var-satur-list and pq working properly at this point!!!

             ; find-index : [SetOf Number] Number -> Number
             (define (find-index son n)
               (cond
                 [(< n (sub1 (length lovar)))
                  (cond
                    [(not (ormap (λ (num) (= num n)) (set->list son))) n] ;; if n is not used, use n
                    [else (find-index son (add1 n))])]
                 [else n]))
             (letrec ([ar-ls ;; ar-ls : -> [DictionaryOf Arg Number]
                       (λ ()
                         (cond
                           [(zero? (pqueue-count pq)) empty]
                           [else (begin
                                   (define var (pqueue-pop! pq))
                                   (pqueue-decrease-key! pq (dict-ref var-handle-list var))
                                   (define sat-set (dict-ref var-satur-list var)) ;; [SetOf Color(Number)]
                                   (define index (find-index sat-set 0))
                                   (for/list ([neighbor (in-neighbors g var)])
                                     (dict-set! var-satur-list neighbor (set-union (set index) (dict-ref var-satur-list neighbor)))) 
                                   (define dict-rest (ar-ls))
                                   (dict-set dict-rest var index))]))])
               (ar-ls))))))

            

(define all-regs
  (list (Reg 'rbx)
        (Reg 'rcx)
        (Reg 'rdx)
        (Reg 'rsi)
        (Reg 'rdi)
        (Reg 'r8)
        (Reg 'r9)
        (Reg 'r10)
        (Reg 'r11)
        (Reg 'r12)
        (Reg 'r13)
        (Reg 'r14)))
 
(define callee?
  (λ (r)
    (or (equal? (Reg 'rsp) r)
        (equal? (Reg 'rbp) r)
        (equal? (Reg 'rbx) r)
        (equal? (Reg 'r12) r)
        (equal? (Reg 'r13) r)
        (equal? (Reg 'r14) r)
        (equal? (Reg 'r15) r))))

; color-to-locations : [ListOf [PairOf Arg Number]] -> [DictionaryOf Arg Location]
(define (color-to-locations arg-color-list)
  (cond
    [(empty? arg-color-list) empty]
    [else (dict-set (color-to-locations (cdr arg-color-list))
                    (car (car arg-color-list))
                    (map-to-loc (car arg-color-list)))]))

; A Location is one of:
; - (Reg reg)
; - (Deref reg int)

; map-to-loc : [Pair Arg Number] -> Location
(define (map-to-loc pr)
  (let* ([arg (car pr)]
         [n (cdr pr)])
    (cond
      [(< n 0) arg]
      [(< n 12) (find-ith n all-regs)]
      [else ; spill
       (Deref 'rbp (* -8 (- n 11)))])))

; find-ith : Number -> Location
(define (find-ith n ls)
  (cond
    [(zero? n) (car ls)]
    [else (find-ith (sub1 n) (cdr ls))]))

; stack-size : [Listof Location] -> Number
(define (stack-size list)
  (let ([size (length (filter Deref? list))])
    (if (even? size)
        (* size 8)
        (+ (* size 8) 8))))

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
                        [(Var var) (dict-ref alist arg)]
                        [else arg]))
                    ls))]
    [else instr])) 

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; patch instructions

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info blocks)
     (define block (dict-ref blocks 'start))
     (define instrs-after-removing-duplicate
       (match block
         [(Block binfo instructions)
          (foldr (λ (instr rest)
                   (match instr
                     [(Instr 'movq `(,arg1 ,arg2))
                      (if (equal? arg1 arg2)
                          rest ;; remove instrs in case of (movq (list -8(%rbp) -8(%rbp)))
                          (append (patch-instructions-instr instr) rest))]
                     [else (append (patch-instructions-instr instr) rest)]))                                      
                 '()
                 instructions)]))
     (define instrs-handling-cmpq-movzbq
       (foldr (λ (instr rest)
                (let ([new-instrs (match instr
                                    [(Instr 'cmpq `(,arg1 ,arg2))
                                     #:when (Imm? arg2)
                                     (list (Instr 'movq (list arg2 (Reg 'rax)))
                                           (Instr 'cmpq (list arg1 (Reg 'rax))))]
                                    [(Instr 'movzbq `(,arg1 ,arg2))
                                     #:when (not (Reg? arg2))
                                     (list (Instr 'movzbq (list arg1 (Reg 'rax)))
                                           (Instr 'movq (list (Reg 'rax) arg2)))]
                                    [_ (list instr)])])
                  (append new-instrs rest)))
              '() instrs-after-removing-duplicate))
     (X86Program
      info
      (dict-set blocks 'start (Block '() instrs-handling-cmpq-movzbq)))]))

; patch-instructions-instr : Instr -> [ListOf Instr]
(define (patch-instructions-instr instr)
  (match instr
    [(Instr op `(,arg1 ,arg2))
     (cond
       [(both-memory? (list arg1 arg2)) (list (Instr 'movq (list  arg1 (Reg 'rax)))
                                              (Instr op (list (Reg 'rax) arg2)))] 
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
; p&c

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info labels-blocks)
     (X86Program
      info
      (append labels-blocks
              (list (build-main info))
              (list (build-conclusion info))))]))

;;stack-adj -(align (+ callee-space spill-space ) 16) callee-space))
(define (build-main info)
  (define reg-pushes
    (map (lambda (i)
           (Instr 'pushq (list i)))         
         (dict-ref info 'used-callee)))
  (define callee-space
    (* 8 (length (dict-ref info 'used-callee))))
  (cons 'main
        (Block '()
               (append
                (list
                 (Instr 'pushq (list (Reg 'rbp)))
                 (Instr 'movq (list (Reg 'rsp) (Reg 'rbp))))
                reg-pushes
                (list
                 (Instr 'subq (list (Imm (- (align (+ callee-space (dict-ref info 'stack-space)) 16) callee-space)) (Reg 'rsp)))
                 (Jmp 'start))))))

(define (build-start instr)
  (cons 'start (Block '() instr)))

(define (build-conclusion info)
  (define reg-pops
    (reverse
     (map (lambda (i)
            (Instr 'popq (list i)))
          (dict-ref info 'used-callee))))
  (cons 'conclusion
        (Block '()
               (append
                (list
                 (Instr 'addq (list (Imm (dict-ref info 'stack-space)) (Reg 'rsp))))
                reg-pops
                (list (Instr 'popq (list (Reg 'rbp)))
                      (Retq))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;(print-graph test-graph)
#;(set->list
 (list->set
  (map cdr (color-to-locations
   (append (ar-regs test-graph)
                    (ar-vars test-graph))))))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("shrink" ,shrink ,interp-Rif ,type-check-Rif)
     ("uniquify" ,uniquify ,interp-Rif)
     ("remove complex opera*" ,remove-complex-opera* ,interp-Rif)
     ("explicate control" ,explicate-control ,interp-Cif)
     ("instruction selection" ,select-instructions ,interp-pseudo-x86-1)
     ("liveness analysis" ,uncover-lives ,interp-pseudo-x86-1)
     ("build interference graph" ,build-inter-graph ,interp-pseudo-x86-1)
     ("allocate registers" ,allocate-registers ,interp-x86-1)
     ("patch instructions" ,patch-instructions ,interp-x86-1)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-1)
     ))