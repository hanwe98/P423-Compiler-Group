#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Rwhile.rkt")
(require "type-check-Rwhile.rkt")
(require "interp-Cwhile.rkt")
(require "type-check-Cwhile.rkt")
(require "interp.rkt")
(require "utilities.rkt")
(require graph)
(require "graph-printing.rkt")
(require "priority_queue.rkt")
(require "multigraph.rkt")
(require data/queue)
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
    [(SetBang x e)
     (SetBang x (shrink-exp e))]
    [(Begin es end)
     (Begin (map shrink-exp es)
            (shrink-exp end))]
    [(WhileLoop cnd body)
     (WhileLoop (shrink-exp cnd)
                (shrink-exp body))]
    [else e])) ; atom

;(shrink (read-program "tests/loop_test_17.rkt"))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; uniquify

#| Rwhile

exp ::= (Int int) | (Var var) | (Let var exp exp)| (Prim op (exp…))
      | (Bool bool) | (If exp exp exp)
      | (SetBang var exp) | (Begin (exp…) exp) | (WhileLoop exp exp)

LWhile ::= (Program ’() exp)

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
           ((uniquify-exp env) else))]
      [(SetBang x e)
       (SetBang (dict-ref env x) ((uniquify-exp env) e))]
      [(Begin es end)
       (Begin (map (uniquify-exp env) es)
              ((uniquify-exp env) end))]
      [(WhileLoop cnd body)
       (WhileLoop ((uniquify-exp env) cnd)
                  ((uniquify-exp env) body))])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; remove complex operands

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
     (define dict (foldr (λ (pr l) (append (cdr pr) l)) '() lod))
     (update (Prim op newes) dict)]
    [(SetBang x e)
     (SetBang x (rco-exp e))]
    [(Begin es end)
     (Begin (map rco-exp es)
            (rco-exp end))]
    [(WhileLoop cnd body)
     (WhileLoop (rco-exp cnd)
                (rco-exp body))]))

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
     (define atm (if (is-atom newbody)
                     newbody
                     (Var key)))
     (define alist (if (is-atom newbody)
                       (dict-set '() x newe)
                       (dict-set (dict-set '() x newe) key newbody)))
     (cons atm alist)]
    [(Prim op es)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define lod (map rco-atom es))
     (define es^ (map car lod))
     (define dict (foldr (λ (pr l) (append (cdr pr) l)) '() lod))
     (define value (Prim op es^))
     (define alist (dict-set dict key value))
     (cons atm alist)]
    [(SetBang x e)
     (define tmp (gensym 'tmp))
     (define val (SetBang x (rco-exp e)))
     (define alist (dict-set '() tmp val))
     (cons (Var tmp) alist)]
    [(Begin es end)
     (define tmp (gensym 'tmp))
     (define val
       (Begin (map rco-exp es)
              (rco-exp end)))
     (define alist (dict-set '() tmp val))
     (cons (Var tmp) alist)]
    [(WhileLoop cnd body)
     (define tmp (gensym 'tmp))
     (define val
       (WhileLoop (rco-exp cnd)
                  (rco-exp body)))
     (define alist (dict-set '() tmp val))
     (cons (Var tmp) alist)]))

; is-atom : exp -> Boolean
(define is-atom
  (λ (exp)
    (match exp
      [(Var x) true]
      [(Int n) true]
      [(Bool b) true]
      [else false])))

; update : exp Dicitonary -> (Let var exp exp)
(define (update e dict)
  (cond
    [(dict-empty? dict) e]
    [else (let* ([x (car (car dict))]
                 [v (cdr (car dict))]
                 [body (update e (cdr dict))])
            (Let x v body))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; explicate control

#| Cloop
atm ::= (Int int) | (Var var) | (Bool bool) | (Void)

cmp ::= eq? | < | <= | > | >=

exp ::= atm
      | (Prim read ())
      | (Prim - (atm))
      | (Prim + (atm atm))
      | (Prim not (atm))
      | (Prim cmp (atm atm))

stmt ::= (Assign (Var var) exp)
       | (Prim read ())

tail ::= (Return exp)
       | (Seq stmt tail)
       | (Goto label)
       | (IfStmt (Prim cmp (atm atm)) (Goto label) (Goto label))

CWhile ::= (CProgram info ((label . tail) ... ))
|#

;; explicate-control : Rwhile -> Cwhile
(define (explicate-control p)
  (match p
    [(Program info body)
     (hash-clear! blocks)
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
    [(Prim op es) (Return e)]

    [(Let x rhs body)
     (let* ([bodyctail (explicate-tail body)])
       (explicate-assign rhs x bodyctail))]

    [(If test then else)
     (let* ([cthen (explicate-tail then)]
            [celse (explicate-tail else)])
       (explicate-pred test cthen celse))]

    [(SetBang x e)
     (explicate-assign e x (Return (Void)))]

    [(Begin es end)
     (foldl (λ (e cont)
              (explicate-effect e cont))
            (explicate-tail end)
            es)]

    [(WhileLoop cnd body)
     (let ([body-tail (explicate-tail body)])
       (explicate-pred cnd body-tail (Return (Void))))]

    [else (error "explicate-tail unhandled case" e)]))

; explicate-assign : RIf_exp var CIf_tail -> Cif_tail
; generates code for a `let` by cases on the right-hand side expression
(define (explicate-assign e x cont)
  (match e
    [(Var s) (Seq (Assign (Var x) e) cont)]
    [(Int n) (Seq (Assign (Var x) e) cont)]
    [(Bool b) (Seq (Assign (Var x) e) cont)]
    [(Prim op es) (Seq (Assign (Var x) e) cont)]

    [(Let s rhs body)
     (let* ([bodyctail (explicate-assign body x cont)])
       (explicate-assign rhs s bodyctail))]

    [(If test then else)
     (let* ([cont-goto (create-block cont (gensym 'block))]
            [then-tail (explicate-assign then x cont-goto)]
            [else-tail (explicate-assign else x cont-goto)])
       (explicate-pred test then-tail else-tail))]

    [(SetBang x e)
     (Seq (Assign (Var x) e) cont)]

    [(Begin es end)
     (foldl (λ (e cont^)
              (explicate-effect e cont^))
            (explicate-assign end x cont)
            es)]

    [(WhileLoop cnd body)
     (let ([body-tail (explicate-assign body x cont)])
       (explicate-pred cnd body-tail (Return (Void))))]

    [else (error "explicate-assign unhandled case" e)]))

; explicate-pred : RIf_exp CIf_tail CIf_tail -> CIf_tail
; generates code for an `if` expression by cases on the condition.
(define (explicate-pred cnd thn els)
  (match cnd
    [(Var x)
     (let ([thn-goto (create-block thn (gensym 'block))]
           [els-goto (create-block els (gensym 'block))])
       (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) ; x is a bool, (and x #t) works
               thn-goto
               els-goto))]

    [(Bool b) (if b thn els)]

    [(Prim 'not (list e))
     (explicate-pred e els thn)] ; switched thn and els

    [(Prim op es)
     #:when (cmp? op)
     (let ([thn-goto (create-block thn (gensym 'block))]
           [els-goto (create-block els (gensym 'block))])
       (IfStmt cnd
               thn-goto
               els-goto))]

    [(Let x rhs body) ; might be right
     (let ([body-tail (explicate-pred body thn els)])
       (explicate-assign rhs x body-tail))]

    [(If cnd^ thn^ els^)
     (let* ([thn-goto (create-block thn (gensym 'block))]
            [els-goto (create-block els (gensym 'block))]
            [thn^-tail (explicate-pred thn^ thn-goto els-goto)]
            [els^-tail (explicate-pred els^ thn-goto els-goto)])
       (explicate-pred cnd^ thn^-tail els^-tail))]

    [(Begin es end)
     (foldl (λ (e cont)
              (explicate-effect e cont))
            (explicate-pred end thn els)
            es)]

    [else (error "explicate-pred unhandled case" cnd)]))

; explicate-effect : exp tail -> tail
(define (explicate-effect e tail)
  (match e
    [(Var x) tail]
    [(Int n) tail]
    [(Bool b) tail]
    [(Prim op es)
     (if (eq? op 'read)
         (Seq (Prim 'read '()) tail)
         tail)]

    [(Let x rhs body)
     (explicate-assign rhs x (explicate-effect body tail))]

    [(If test then else)
     (let* ([cthen (explicate-effect then tail)]
            [celse (explicate-effect else tail)])
       (explicate-pred test cthen celse))]

    [(SetBang x e)
     (explicate-assign e x tail)]

    [(Begin es end)
     (foldl (λ (e cont)
              (explicate-effect e cont))
            (explicate-effect end tail)
            es)]

    [(WhileLoop cnd body)
     (let* ([label (gensym 'loop)]
            [body^ (explicate-effect body (Goto label))]
            [loop-body (explicate-pred cnd body^ tail)])
       (create-block loop-body label))]

    [else (error "explicate-effect unhandled case" e)]))

; create-block : Cif_tail Symbol -> (Goto label)
(define (create-block tail label)
  (dict-set! blocks label tail)
  (Goto label))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; select instructions

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
      
      [(Prim 'read '())
      (si-exp stmt)]
              
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
       (list (Instr 'movq (list (si-atm atm1)
                                (Reg 'rax)))
             (Instr 'subq (list (si-atm atm2)
                                (Reg 'rax))))]
      [else (list (Instr 'movq (list (si-atm exp) (Reg 'rax))))])))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match-let ([(CProgram types blocks) (type-check-Cwhile p)])
    (X86Program types
                (for/list ([block blocks])
                  (match-let ([(cons label tail) block])
                    (cons label (Block '() (si-tail tail))))))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; liveness analysis

; now contains liveness for all of a block's insturctions, not just Lbefore
(define label->live
  (make-hash))

; uncover-lives : x86Program -> x86Program
(define (uncover-lives p)
  (match p
    [(X86Program info labels-blocks)
     ; initialize label->live
     (hash-clear! label->live)
     (for ([label (map car labels-blocks)])
       (hash-set! label->live label (list (set))))
     (hash-set! label->live
                'conclusion
                (list (set (Reg 'rax) (Reg 'rsp))))

     (define bg (block-graph labels-blocks))
     (analyze-dataflow bg (transfer labels-blocks) (set) set-union)
            ; side effects for jmp instrs during uncover-live-loi

     (X86Program
      info
      (for/list ([label-block labels-blocks])
        (match label-block
          [(cons label (Block binfo loi))
           (define lives (uncover-live-loi loi))
           (cons label
                 (Block (dict-set binfo 'lives lives)
                        loi))])))]))

; analyze-dataflow : Graph Transfer Bottomm Join -> [Dictionaryof label live-before]
(define (analyze-dataflow G transfer bottom join)
  (define mapping (make-hash))
  (remove-vertex! G 'conclusion)
  ;(print-graph G)
  (for ([v (in-vertices G)])
    (dict-set! mapping v bottom))
  (define worklist (make-queue))
  (for ([v (in-vertices G)])
    (enqueue! worklist v))
  (define trans-G (transpose G))
  ;(displayln "trans-G:")
  ;(print-graph trans-G)
  (while (not (queue-empty? worklist))
         (define node (dequeue! worklist))
         (define input (for/fold ([state bottom])
                                 ([pred (in-neighbors trans-G node)])
                         (join state (dict-ref mapping pred))))
         (define output (transfer node input))
         (cond [(not (equal? output (dict-ref mapping node)))
                (dict-set! mapping node output)
                (for ([v (in-neighbors G node)])
                  (enqueue! worklist v))]))
  mapping)

; transfer : [DictionaryOf label Block] -> [label [Setof arg] -> [Setof arg]]
(define (transfer blocks)
  (λ (label live-after)
    (let ([block (dict-ref blocks label)])
      (match block
        [(Block binfo loi)
         (define lives
           (for/foldr ([acc (list live-after)])
                      ([instr loi])
               (cons (set-union 
                      (set-subtract (car acc)
                                    (locations-written instr))
                      (locations-read instr))
                     acc)))
         (hash-set! label->live label lives)
         (car lives)] ; return live before

        [else (error "transfer expected a block, got" block)]))))

; block-graph : [Listof [Pair label Block]] -> [DirectedGraph label label]
; returns graph of blocks according to their jumps
(define (block-graph blocks)
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
           [else (void)]))]
      [else (error "expected block in block-interference, got" b)]))
  (make-multigraph (hash-values edge-list)))

; uncover-live-loi : [Listof instr] [Set arg] -> [Listof [Setof arg]]
; returns list of live-after sets
(define (uncover-live-loi loi) ; ila = initial live after
  (foldr
   (λ (instr acc)
     (cons (set-union
            (set-subtract
             (car acc)
             (locations-written instr))
            (locations-read instr))
           acc))
   (list (set))
   loi))

; locations-read : instr -> [Setof arg]
(define (locations-read instr)
  (match instr
    [(Instr op `(,arg1 ,arg2)) ; read 1st
     #:when (or (eq? op 'movq)
                (eq? op 'movzbq))
     (locations-arg arg1)]
    [(Instr 'set `(,cc ,arg)) ; read 2nd
     (locations-arg arg)]
    [(Instr op `(,arg1 ,arg2)) ; add/subtract/cmp/xorq (read both)
     #:when (or (eq? op 'addq)
                (eq? op 'subq)
                (eq? op 'cmpq)
                (eq? op 'xorq))
     (set-union (locations-arg arg1)
                (locations-arg arg2))]
    [(Instr op `(,arg)) ; negq, popq, pushq
     (locations-arg arg)]
    [(Callq label arity) ; !!!!!!!!!
     (locations-call (set->list caller-save) arity)]
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
    [(Instr op `(,arg1 ,arg2)) ; write 2nd
     #:when (or (eq? op 'addq)
                (eq? op 'subq)
                (eq? op 'movq)
                (eq? op 'xorq)
                (eq? op 'set)
                (eq? op 'movzbq))
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; build interference graph

;; build-inter-graph : pseudo-x86 -> pseudo-x86
(define (build-inter-graph p)
  (match p
    [(X86Program info blocks)
     (define locals (map car (dict-ref info 'locals-types)))
     (define edges (foldr (λ (pair rest)
                            (append (match (cdr pair)
                                      [(Block binfo instructions)
                                       (bi instructions (cdar binfo))])
                                    rest))
                          '() blocks))
     (define graph (undirected-graph edges))
     (for/list ([local locals])
       (add-vertex! graph (Var local)))
     (define info-remove-label-live (dict-remove info 'label->live))
     (define newblocks ;; remove-liveness in info
       (for/list ([pair blocks])
         (cons (car pair)  (match (cdr pair)
                             [(Block binfo instrs)
                              (Block '() instrs)]))))
     (X86Program (dict-set info-remove-label-live 'conflicts graph) newblocks)]))

;; bi : [ListOf Instructions] [ListOf [SetOf Location]] -> [ListOf Edge]
(define (bi loi los)
  (cond
    [(empty? loi) empty]
    [else (append
           (match (car loi)
             [(Callq label int) (foldr (λ (reg rest) (append (map (λ (loc) (list reg loc)) (set->list (car los))) rest)) '()
                                       (set->list available-caller))]
             [else
              (filter (λ (e) (not (equal? 0 e)))
                      (map (λ (loc) (bi-single (car loi) loc))
                           (set->list (car los))))])
           (bi (cdr loi) (cdr los)))]))

; A [Maybe Edge] is one of:
; - Edge
; - zero

; bi-single : Instruction Location -> [Maybe Edge]
(define bi-single
  (λ (i loc)
    (match i
      [(Instr 'negq `(,arg1))
       (let ([notTarget (not (equal? loc arg1))])
         (cond
           [notTarget (list loc arg1)]
           [else 0]))]
      [(Instr 'set `(,cc ,arg1))
       (let ([notTarget (not (equal? loc arg1))])
         (cond
           [notTarget (list loc arg1)]
           [else 0]))]
      ;; for every caller-saved register, create an edge between the register
      ;; and the given location unless they are the same. create an edge between
      ;; every pair of differernt caller-saved registers. Is this right?? yes!!!
      [(Instr op `(,arg1 ,arg2))
       #:when (equal? op 'cmpq)
       0]
      [(Instr 'movq `(,arg1 ,arg2))
       (let ([notSource (not (equal? loc arg1))]
             [notTarget (not (equal? loc arg2))])
         (cond
           [(and notSource notTarget)
            (list loc arg2)]
           [else 0]))]
      [(Instr 'movzbq `(,arg1 ,arg2))
       (let ([notSource (not (equal? loc (Reg 'rax)))]
             [notTarget (not (equal? loc arg2))])
         (cond
           [(and notSource notTarget)
            (list loc arg2)]
           [else 0]))]
      [(Instr op `(,arg1 ,arg2))
       #:when (or (equal? op 'addq)
                  (equal? op 'subq)
                  (equal? op 'xorq))
       (let ([notTarget (not (equal? loc arg2))])
         (cond
           [notTarget (list loc arg2)]
           [else 0]))]
      [else 0])))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
; allocate registers

(define pre-coloring
  (λ (loreg n)
    (cond
      [(empty? loreg) empty]
      [else (dict-set (pre-coloring (cdr loreg) (add1 n)) (car loreg) n)])))

(define available-caller
  (set (Reg 'rcx) (Reg 'rdx) (Reg 'rsi) (Reg 'rdi) (Reg 'r8) (Reg 'r9) (Reg 'r10) (Reg 'r11)))

(define available-callee
  (set (Reg 'rbx) (Reg 'r12) (Reg 'r13) (Reg 'r14)))

; init-satur-list : [ListOf Var] Graph [DictionaryOf Reg Number(Color)] -> [SetOf Color]
(define (init-satur-list var g dict)
  (foldr (λ (pair rest)
           (cond
             [(list? (member (car pair) (sequence->list (in-neighbors g var))))
              (set-union (set (cdr pair)) rest)]
             [else rest])) 
         (set) 
         dict))

(define pre-color (append
                   (list (cons (Reg 'rax) -1)
                         (cons (Reg 'rsp) -2))
                   (pre-coloring (set->list available-caller) 0)
                   (pre-coloring (set->list available-callee) 8)))

;; allocate-registers : pseudo-x86 -> pseudo-x86
(define (allocate-registers p)
  (match p
    [(X86Program info blocks)
     (define graph (dict-ref info 'conflicts))
     (define color-mapping (ar-vars graph)) ; [DictionaryOf Var/Reg Number(Color)]
     (define var-mapping (color-to-location color-mapping)) ; [DictionaryOf Var Reg/Deref]
     (define used-callee (filter available-callee? (set->list (list->set (map cdr var-mapping))))) ; [ListOf Reg]
     (define num-spill (num-spilled (set->list (list->set (map cdr var-mapping)))))
     (define info^ (dict-set (dict-set (dict-set (dict-set (dict-remove info 'conflicts)
                                                           'color (append pre-color color-mapping))
                                                 'home var-mapping)
                                       'used-callee used-callee)
                             'num-spill num-spill))
     (define newblocks
       (for/list ([pair blocks])
         (define label (car pair))
         (define block (cdr pair))
         (define new-instrs
           (match block
             [(Block binfo instrs)
              (assign-homes-instrs instrs var-mapping)]))
         (cons label (Block '() new-instrs))))
     (X86Program info^ newblocks)]))

; An Arg is one of :
; - (Reg Symbol) ;; Register
; - (Var Symbol) ;; Var
; - (Imm Number) ;; Imm

; is-reg? : Arg -> Boolean
(define (is-reg? a)
  (match a
    [(Reg reg) true]
    [else false]))


; ar-graph : Graph -> [DictionaryOf Var Number(Color)]
(define ar-vars ;; change [ListOf Color] to [SetOf Color] later
  (λ (g)
    (let* ([var-satur-list (make-hash)] ;; [DictionaryOf Var [SetOf Color]]
           [var-handle-list (make-hash)];; [DictionaryOf Var Handle]
           [ls (sequence->list (in-vertices g))]
           [lovar (filter (λ (a) (not (is-reg? a))) ls)]) ;; [DictionaryOf Reg Number(Color)]
      (begin (for/list ([var ls]) ;; initialize var-satur-list
               (dict-set! var-satur-list var (init-satur-list var g pre-color)))
             (define pq              ;; initialize pq
               (make-pqueue (λ (n1 n2) (> (set-count (dict-ref var-satur-list n1))
                                          (set-count (dict-ref var-satur-list n2))))))
             (for/list ([var lovar]) ;; initialize var-handle-list
               (dict-set! var-handle-list var (pqueue-push! pq var)))
             ;; var-handle-list and var-satur-list and pq working properly at this point!!!

             ; find-index : [SetOf Number] Number -> Number
             (define (find-index son n)
               (cond
                 [(< n (sub1 (length ls)))
                  (cond
                    [(not (ormap (λ (num) (= num n)) (set->list son))) n] ;; if n is not used, use n
                    [else (find-index son (add1 n))])]
                 [else n]))
             (letrec ([ar-ls ;; ar-ls : -> [DictionaryOf Number Var]
                       (λ ()
                         (cond
                           [(zero? (pqueue-count pq)) empty]
                           [else (begin
                                   (define var (pqueue-pop! pq))
                                   (pqueue-decrease-key! pq (dict-ref var-handle-list var))
                                   (define sat-set (dict-ref var-satur-list var)) ;; [SetOf Color(Number)]
                                   (define index (find-index sat-set 0))
                                   (for/list ([neighbor (sequence->list (in-neighbors g var))])
                                     (dict-set! var-satur-list neighbor (set-union (set index) (dict-ref var-satur-list neighbor))))
                                   (define dict-rest (ar-ls))
                                   (dict-set dict-rest var index))]))])
               (ar-ls))))))

(define available-callee?
  (λ (r)
    (or (equal? (Reg 'rbx) r)
        (equal? (Reg 'r12) r)
        (equal? (Reg 'r13) r)
        (equal? (Reg 'r14) r)
        #;(equal? (Reg 'r15) r))))

; color-to-location : [ListOf [PairOf Var Number]] -> [DictionaryOf Arg Location]
(define (color-to-location var-color-list)
  (cond
    [(empty? var-color-list) empty]
    [else (dict-set (color-to-location (cdr var-color-list))
                    (car (car var-color-list))
                    (map-to-loc (car var-color-list)))]))

; A Location is one of:
; - (Reg reg)
; - (Deref reg int)

; map-to-loc : [PairOf Var Number] -> Location
(define (map-to-loc pr)
  (let* ([var (car pr)]
         [n (cdr pr)])
    (cond
      [(< n 12) (find-ith n pre-color)]
      [else ; spill
       (Deref 'rbp (* -8 (- n 11)))])))

; find-ith : Number [DictionaryOf Reg Number(Color)] -> Location
(define (find-ith n ls)
  (cond
    [(empty? ls) (Reg 'r15)] ; shouldn't happen
    [else (cond
            [(= n (cdar ls)) (caar ls)]
            [else (find-ith n (rest ls))])]))

; num-spilled : [Listof Location] -> Number
(define (num-spilled list)
  (length (filter Deref? list)))

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
      (append (list (build-main info))
              labels-blocks
              (list (build-conclusion info))))]))

; build-main : info -> (cons label Block)
(define (build-main info)
  (let ([setup
         (append
          (list (Instr 'pushq (list (Reg 'rbp)))
                (Instr 'movq (list (Reg 'rsp) (Reg'rbp))))
          (foldr (λ (s rest) (cons (Instr 'pushq (list s)) rest))
                 '() (set->list (dict-ref info 'used-callee)))
          (list (Instr 'subq (list (compute-rsp info) (Reg 'rsp))) ;; relating to num-spill
                (Jmp 'start)))])
    (cons 'main (Block '() setup))))

; compute-rsp : info -> (Imm Number)
(define (compute-rsp info)
  (let* ([callees (length (dict-ref info 'used-callee))]
         [spills (dict-ref info 'num-spill)])
    (Imm (- (align (+ (* 8 callees) (* 8 spills)) 16) (* 8 callees)))))

; build-conclusion : info -> (cons label Block)
(define (build-conclusion info)
  (let ([setup
         (cons (Instr 'addq (list (compute-rsp info) (Reg 'rsp))) ;; relating to num-spill
               (append (foldl (λ (s rest) (cons (Instr 'popq (list s)) rest))
                              '() (set->list (dict-ref info 'used-callee)))
                       (list (Instr 'popq (list (Reg 'rbp)))
                             (Retq))))])
    (cons 'conclusion (Block '() setup))))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ("shrink" ,shrink ,interp-Rwhile ,type-check-Rwhile)
    ("uniquify" ,uniquify ,interp-Rwhile)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Rwhile)
    ("explicate control" ,explicate-control ,interp-Cwhile)
    ("instruction selection" ,select-instructions ,interp-pseudo-x86-1)
    ("liveness analysis" ,uncover-lives ,interp-pseudo-x86-1)
    ("build interference graph" ,build-inter-graph ,interp-pseudo-x86-1)
    ("allocate registers" ,allocate-registers ,interp-x86-1)
    ("patch instructions" ,patch-instructions ,interp-x86-1)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-1)
    ))