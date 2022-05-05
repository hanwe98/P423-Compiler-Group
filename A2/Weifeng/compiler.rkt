; Collaborators :
; - Nick Irmscher
; - Garrett Robinson
; - Marshal Gress

#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Rint.rkt")
(require "interp-Rvar.rkt")
(require "interp-Cvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(provide (all-defined-out))
(require "priority_queue.rkt")
(require graph)


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
      [(Let x e body)
       (let* ([newe ((uniquify-exp env) e)]
              [newx (gensym x)]
              [newbody ((uniquify-exp (dict-set env x newx)) body)])
         (Let newx newe newbody))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))


; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info (rco-exp e))]))

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
            [atm (if (is-var newbody) newbody (Var s))]
            [alist (cond
                     [(is-var newbody) (dict-set '() x newe)]
                     [else (dict-set (dict-set '() x newe)
                                     s newbody)])])
       (cons atm alist))]
    [(Prim op es)
     (let* ([s (gensym 'tmp)]
            [atm   (Var s)]
            [alist (let* ([key   s]
                          [lopoad (map (λ (e) (rco-atom e)) es)]
                          [newes (map (λ (pr) (car pr)) lopoad)]
                          [dict (foldl (λ (pr l) (append (cdr pr) l)) '() lopoad)] ;; use foldr?
                          [value (Prim op newes)])
                     (dict-set dict key value))])
       (cons atm alist))]))

(define is-var
  (λ (exp)
    (match exp
      [(Var var) true]
      [else false])))

(define (update e dict)
  (cond
    [(dict-empty? dict) e]
    [else (let* ([x (car (car dict))]
                 [v (cdr (car dict))]
                 [body (update e (cdr dict))])
            (Let x v body))]))




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



;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match-let
      ([(CProgram info blocks) (type-check-Cvar p)])
    (define tail (dict-ref blocks 'start)) ; tail : tail
    (define newblock (Block '() (si-tail tail)))
    (X86Program info (dict-set blocks 'start newblock))))

; si-tail : tail -> [ListOf Instr]
(define si-tail
  (λ (tail)
    (match tail
      [(Return exp)
       (define instrs
         (match exp
           [(Int n) (list (Instr 'movq (list (si-atm (Int n)) (Reg 'rax))))]
           [(Var x) (list (Instr 'movq (list (si-atm (Var x)) (Reg 'rax))))]
           [(Prim '+ `(,atm1 ,atm2)) (list (Instr 'movq (list (si-atm atm1) (Reg 'rax)))
                                           (Instr 'addq (list (si-atm atm2) (Reg 'rax))))]
           [(Prim '- `(,atm1)) (list (Instr 'movq (list (si-atm atm1) (Reg 'rax)))
                                     (Instr 'negq (list (Reg 'rax))))]
           [(Prim 'read ls) (list (Callq 'read_int 0))]))
       (append instrs
               (list (Jmp 'conclusion)))]
      [(Seq stmt tail)
       (append (si-stmt stmt)
               (si-tail tail))]
      [else (error "expected a tail for si-tail, instead got" tail)])))

; si-atm : atm -> arg
(define si-atm
  (λ (atm)
    (match atm
      [(Int n) (Imm n)]
      [(Var x) (Var x)]
      [else (error "expected an atom for si-atm, instead got" atm)])))

; si-stmt : stmt -> [ListOf Instr]
(define (si-stmt stmt)
  (match stmt
    [(Assign (Var var) exp)
     (match exp
       [(Int n) (list (Instr 'movq (list (si-atm (Int n)) (Var var))))]
       [(Var x) (list (Instr 'movq (list (si-atm (Var x)) (Var var))))]
       [(Prim '+ `(,atm1 ,atm2))
        (define arg1 (si-atm atm1))
        (define arg2 (si-atm atm2))
        (cond
          [(equal? (Var var) arg2) (list (Instr 'addq (list arg1 arg2)))]
          [(equal? (Var var) arg1) (list (Instr 'addq (list arg2 arg1)))]
          [else 
           (list (Instr 'movq (list arg1 (Var var)))
                 (Instr 'addq (list arg2 (Var var))))])]
       [(Prim '- `(,atm1)) (list (Instr 'movq (list (si-atm atm1) (Var var)))
                                 (Instr 'negq (list (Var var))))]
       [(Prim 'read ls) (list (Callq 'read_int 0)
                              (Instr 'movq (list (Reg 'rax) (Var var))))])]))

;; uncover-live : pseudo-x86 -> pseudo-x86
(define (uncover-live p)
  (match p
    [(X86Program info blocks)
     (define block (dict-ref blocks 'start))
     (define newblock (match block
                        [(Block binfo instructions) 
                         (Block (ul-instrs instructions (set)) instructions)]))
     (X86Program info (dict-set blocks 'start newblock))])) ; binfo is a list of sets of liveness
; ul-instrs : [ListOf Instr] [SetOf Location] -> [ListOf [SetOf Location]]
(define (ul-instrs loi after)
  (cond
    [(empty? loi) (list after)]
    [else (let* ([nlist (ul-instrs (cdr loi) after)]
                 [nafter (car nlist)]
                 [curset (set-union (set-subtract nafter (written (car loi)))
                                    (read (car loi)))])
            (cons curset nlist))]))

; written : Instr -> [SetOf Location]
(define (written i)
  (match i
    [(Instr 'addq `(,arg1 ,arg2)) (loc-in-arg arg2)]
    [(Instr 'neg `(,arg1)) (loc-in-arg arg1)]
    [(Instr 'movq `(,arg1 ,arg2)) (loc-in-arg arg2)]
    [(Callq 'label int) (set (Reg 'rax) (Reg 'rdx) (Reg 'rcx)
                             (Reg 'rsi) (Reg 'rdi) (Reg 'r8)
                             (Reg 'r9)  (Reg 'r10) (Reg 'r11))]
    [else (set)]))

; read : Instr -> [Setof Location]
(define (read i)
  (match i
    [(Instr 'addq `(,arg1 ,arg2)) (set-union (loc-in-arg arg1) (loc-in-arg arg2))]
    [(Instr 'neg `(,arg1)) (loc-in-arg arg1)]
    [(Instr 'movq `(,arg1 ,arg2)) (loc-in-arg arg1)]
    [(Callq 'label int) (set)] ; the only call is read_int which takes no args
    [else (set)]))

; loc-in-arg : Arg -> [SetOf Location]
(define (loc-in-arg arg)
  (match arg
    [(Reg reg) (set (Reg reg))]
    [(Var var) (set (Var var))]
    [else (set)]))

(define t1 (ul-instrs (list (Instr 'movq (list (Imm 5) (Var 'a)))
                            (Instr 'movq (list (Imm 30) (Var 'b)))
                            (Instr 'movq (list (Var 'a) (Var 'c)))
                            (Instr 'movq (list (Imm 10) (Var 'b)))
                            (Instr 'addq (list (Var 'b) (Var 'c))))
                      (set)))

;; build-interference : pseudo-x86 -> pseudo-x86
(define (build-interference p)
  (match p
    [(X86Program info blocks)
     (define locals (map car (dict-ref info 'locals-types)))
     (define graph (match (dict-ref blocks 'start)
                     [(Block binfo instructions)
                      (undirected-graph (bi instructions (cdr binfo)))]))
     (for/list ([local locals])
       (add-vertex! graph (Var local)))
     (X86Program (dict-set info 'conflict graph) blocks)]))

;; bi : [ListOf Instructions] [ListOf [SetOf Location]] -> [ListOf Edge]
(define (bi loi los)
  (cond
    [(empty? loi) empty]
    [else (append
           (filter (λ (e) (not (equal? 0 e)))
                   (map (λ (loc) (bi-single (first loi) loc))
                        (set->list (first los))))
           (bi (rest loi) (rest los)))]))

; A [Maybe Edge] is one of:
; - Edge
; - zero

; bi-single : Instruction Location -> [Maybe Edge]
(define bi-single
  (λ (i loc)
    (match i
      [(Instr 'movq `(,arg1 ,arg2))
       (let ([notSource (not (equal? loc arg1))]
             [notTarget (not (equal? loc arg2))])
         (cond
           [(and notSource notTarget)
            (list loc arg2)]
           [else 0]))]
      [(Instr 'addq `(,arg1 ,arg2))
       (let ([notTarget (not (equal? loc arg2))])
         (cond
           [notTarget (list loc arg2)]
           [else 0]))]
      [(Instr 'negq `(,arg))
       (let ([notTarget (not (equal? loc arg))])
         (cond
           [notTarget (list loc arg)]
           [else 0]))]
      [(Callq 'label int) 0]
      [else 0])))

;; allocate-registers : pseudo-x86 -> pseudo-x86
(define (allocate-registers p)
  (match p
    [(X86Program info blocks)
     (define graph (dict-ref info 'conflict))
     (define block (dict-ref blocks 'start))
     (match block
       [(Block binfo instructions)
        (define dict (append (ar-regs graph) (ar-vars graph)))
        (define new-binfo (color-to-locations dict)) ;; [DictionaryOf Var/Reg Reg/Deref]
        (define new-info (dict-set info 'used-callee (filter callee? (set->list (list->set (map cdr new-binfo))))))
        (define newblocks (dict-set blocks 'start (Block new-binfo instructions)))
        (X86Program new-info newblocks)])]))

; An Arg is one of :
; - (Reg Symbol) ;; Register
; - (Var Symbol) ;; Var
; - (Imm Number) ;; Imm

; ar-regs : Graph -> [DictionaryOf Number Arg]
; takes a Graph and return its mapping from Registers to colors
(define (ar-regs g)
  (bond-reg (filter is-reg? (sequence->list (in-vertices g)))))

; is-reg? : Arg -> Boolean
(define (is-reg? a)
  (match a
    [(Reg reg) true]
    [else false]))

; bond-reg : [ListOf Register] -> [DictionaryOf Number Register]
(define (bond-reg lor)
  (cond
    [(empty? lor) empty]
    [else (let ([rest (bond-reg (rest lor))])
            (dict-set rest (car lor) (- 0 (add1 (dict-count rest)))))]))

; ar-graph : Graph -> [DictionaryOf Number Arg]
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
                    (map-to-loc (cdr (car arg-color-list))))]))

; A Location is one of:
; - (Reg reg)
; - (Deref reg int)

; map-to-loc : Number(Color) -> Location
(define (map-to-loc n)
  (cond
    [(= -1 n) (Reg 'rax)]
    [(= -2 n) (Reg 'rsp)]
    [(< n 12) (find-ith n all-regs)]
    [else ; spill
     (Deref 'rbp (* -8 (- n 11)))]))

; find-ith : Number -> Location
(define (find-ith n ls)
  (cond
    [(zero? n) (car ls)]
    [else (find-ith (sub1 n) (cdr ls))]))

;(define instructions (list (Instr 'movq (list (Imm 1) (Var 'v)))
;                           (Instr 'movq (list (Imm 42) (Var 'w)))
;                           (Instr 'movq (list (Var 'v) (Var 'x)))
;                           (Instr 'addq (list (Imm 7) (Var 'x)))
;                           (Instr 'movq (list (Var 'x) (Var 'y)))
;                           (Instr 'movq (list (Var 'x) (Var 'z)))
;                           (Instr 'addq (list (Var 'w) (Var 'z)))
;                           (Instr 'movq (list (Var 'y) (Var 't)))
;                           (Instr 'negq (list (Var 't)))
;                           (Instr 'movq (list (Var 'z) (Reg 'rax)))
;                           (Instr 'addq (list (Var 't) (Reg 'rax)))
;                           (Jmp 'conclusion)))
;(define losol2 (ul-instrs instructions (set (Reg 'rsp) (Reg 'rax))))
;(define graph (undirected-graph (bi instructions losol2)))
;(define result (ar-vars graph))
;
;(define dict (append (ar-regs graph) (ar-vars graph)))
;(define new-binfo (color-to-locations dict))
;(define new-info (dict-set empty 'used-callee (filter callee? (set->list (list->set (map cdr new-binfo))))))
;(define newblocks (dict-set empty 'start (Block new-binfo instructions)))
;(define p1-after-ar (X86Program new-info newblocks))



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

(define (refer-list locals counter)
  (cond
    [(empty? locals) empty]
    [else
     (dict-set (refer-list (cdr locals) (- counter 8))
               (car locals) (Deref 'rbp counter))]))

; stack-size : Dictionary -> Number
(define (stack-size dict)
  (let ([dict-size (length dict)])
    (if (even? dict-size)
        (* dict-size 8)
        (+ (* dict-size 8) 8))))

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



;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info blocks)
     (define block (dict-ref blocks 'start))
     (match block
       [(Block binfo instructions)
        (define new-instrs (foldr (λ (instr rest)
                                    (match instr
                                      [(Instr 'movq `(,arg1 ,arg2))
                                       (if (equal? arg1 arg2)
                                           rest ;; remove instrs in case of (movq (list -8(%rbp) -8(%rbp)))
                                           (append (patch-instructions-instr instr) rest))]
                                      [else (append (patch-instructions-instr instr) rest)]))                                      
                                  '()
                                  instructions))
        (X86Program
         info
         (dict-set blocks 'start (Block binfo new-instrs)))])]))

; patch-instructions-instr : Instr -> [ListOf Instr]
(define (patch-instructions-instr instr)
  (match instr
    [(Instr op `(,arg1 ,arg2))
     (cond
       [(both-memory? (list arg1 arg2)) (list (Instr 'movq (list arg1 (Reg 'rax)))
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


;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("uniquify" ,uniquify ,interp-Rvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Rvar)
     ("explicate control" ,explicate-control ,interp-Cvar)
     ("instruction selection" ,select-instructions ,interp-x86-0)
     ("uncover live" ,uncover-live ,interp-x86-0)
     ("build interference" ,build-interference ,interp-x86-0)
     ("allocate registers" ,allocate-registers ,interp-x86-0)
     ("assign homes" ,assign-homes ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))
