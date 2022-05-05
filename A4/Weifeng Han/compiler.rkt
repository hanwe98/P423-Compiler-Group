; Collaborators :
; - Nick Irmscher
; - Marshal Gress

#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Rwhile.rkt")
(require "interp-Cwhile.rkt")
(require "type-check-Rwhile.rkt")
(require "type-check-Cwhile.rkt")
(require "utilities.rkt")
(require "interp.rkt")
(require "multigraph.rkt")
(provide (all-defined-out))
(require "priority_queue.rkt")
(require data/queue)
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

; shrink : Rif -> Rif
(define (shrink p)
  (match p
    [(Program info e) (Program info (shrink-exp e))]))

; shrink-exp : Exp -> Exp
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
    [(SetBang var rhs)
     (SetBang var (shrink-exp rhs))]
    [(Begin es body)
     (Begin (map (λ (e) (shrink-exp e)) es) (shrink-exp body))]
    [(WhileLoop cnd body)
     (WhileLoop (shrink-exp cnd) (shrink-exp body))]
    [else e]))     

;; uniquify : R1 -> R1 
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

; uniquify-exp : [Dictionaryof Symbol Symbol] -> [Exp -> Exp]
(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (dict-ref env x))] 
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(If cnd thn els)
       (If ((uniquify-exp env) cnd) ((uniquify-exp env) thn) ((uniquify-exp env) els))]
      [(Let x e body)
       (define e^ ((uniquify-exp env) e))
       (define x^ (gensym x))
       (define body^ ((uniquify-exp (dict-set env x x^)) body))
       (Let x^ e^ body^)]
      [(SetBang var rhs)
       (SetBang (dict-ref env var) ((uniquify-exp env) rhs))]
      [(Begin es body)
       (Begin (map (uniquify-exp env) es) ((uniquify-exp env) body))]
      [(WhileLoop cnd body)
       (WhileLoop ((uniquify-exp env) cnd) ((uniquify-exp env) body))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

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
    [(Void) (Void)]
    [(SetBang var rhs)
     (SetBang var (rco-exp rhs))]
    [(Begin es body)
     (Begin (map rco-exp es) (rco-exp body))]
    [(WhileLoop cnd body)
     (WhileLoop (rco-exp cnd) (rco-exp body))]
    [(Let x e body)
     (Let x (rco-exp e) (rco-exp body))]
    [(If cnd thn els)
     (If (rco-exp cnd) (rco-exp thn) (rco-exp els))]
    [(Prim op es)
     (define lod (map rco-atom es))
     (define newes (map car lod))
     (define dict (foldr (λ (pr l) (append (cdr pr) l)) '() lod))
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
    [(Void)
     (define atm (Void))
     (define alist '())
     (cons atm alist)]
    [(Begin es body)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define value (Begin (map rco-exp es) (rco-exp body)))
     (define alist (dict-set '() key value))
     (cons atm alist)]
    [(SetBang var rhs)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define value (SetBang var (rco-exp rhs)))
     (define alist (dict-set '() key value))
     (cons atm alist)]
    [(WhileLoop cnd body)
     (define key (gensym 'tmp))
     (define atm (Var key))
     (define value (WhileLoop (rco-exp cnd) (rco-exp body)))
     (define alist (dict-set '() key value))
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
     (define atm (if (atm? newbody) newbody (Var key)))
     (define alist (if (atm? newbody) (dict-set '() x newe)
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
     (cons atm alist)]))


(define (update e dict)
  (cond
    [(dict-empty? dict) e]
    [else (let* ([x (car (car dict))]
                 [v (cdr (car dict))]
                 [body (update e (cdr dict))])
            (Let x v body))]))

;; explicate-control : R1 -> C0
(define blocks (make-hash))
(define (explicate-control p)
  (match p
    [(Program info body)
     (dict-clear! blocks)
     (define bodyctail (explicate-tail body))
     (dict-set! blocks 'start bodyctail)
     (CProgram info (hash->list blocks))]))
    
; explicate-pred : Exp(Rif) Tail(Cif) Tail(Cif) -> Tail(Cif) 
(define (explicate-pred cnd thn els)
  (match cnd
    [(Var x) (IfStmt (Prim 'eq? (list (Var x) (Bool #t)))
                     (create-block thn)
                     (create-block els))]
    [(Begin (list) body)
     (explicate-pred body thn els)]
    [(Begin (cons exp exp*) body)
     (explicate-effect exp (explicate-pred (Begin exp* body) thn els))]
    [(Let x rhs body)
     (define cont (explicate-pred body thn els))
     (explicate-assign rhs x cont)]
    [(Prim 'not (list e)) (explicate-pred e els thn)]
    [(Prim op es) #:when (or (eq? op 'eq?) (eq? op '<) (eq? op '>) (eq? op '>=) (eq? op '<=))
                  (IfStmt (Prim op es) (create-block thn)
                          (create-block els))]
    [(Bool b) (if b thn els)]
    [(If cnd^ thn^ els^)
     (define thn-block (create-block thn))
     (define els-block (create-block els))
     (explicate-pred cnd^
                     (explicate-pred thn^ thn-block els-block)
                     (explicate-pred els^ thn-block els-block))]
    [else (error "explicate_pred unhandled case" cnd)]))

; explicate-tail : Exp(Rif) -> Tail(Cif)
(define (explicate-tail e)
  (match e
    [(Var x)
     (Return (Var x))]
    [(Int n)
     (Return (Int n))]
    [(Bool b)
     (Return (Bool b))]
    [(Void)
     (Return (Void))]
    [(If cnd thn els)
     (define thn^ (explicate-tail thn))
     (define els^ (explicate-tail els))
     (explicate-pred cnd thn^ els^)]
    [(Let x rhs body)
     (define bodyctail (explicate-tail body))
     (explicate-assign rhs x bodyctail)]
    [(Prim op es)
     (Return (Prim op es))]
    [(Begin es body)
     (foldl (λ (exp cont)
              (explicate-effect exp cont))
            (explicate-tail body) es)]
    [(SetBang var exp)
     (explicate-effect (SetBang var exp) (explicate-tail (Void)))]
    [(WhileLoop cnd body)
     (explicate-effect (WhileLoop cnd body) (explicate-tail (Void)))]
    [else (error "explicate_tail unhandled case" e)]))

; explicate-assign : Exp(Rif) Symbol Tail(Cif) -> Tail(Cif)
(define (explicate-assign e x cont)
  (match e
    [(Var s) 
     (Seq (Assign (Var x) (Var s)) cont)]
    [(Int n)
     (Seq (Assign (Var x) (Int n)) cont)]
    [(Bool b)
     (Seq (Assign (Var x) (Bool b)) cont)]
    [(If cnd thn els)
     (define cont^ (create-block cont)) ; (Goto label)
     (define thn^ (explicate-assign thn x cont^)) ; Tail(Cif) 
     (define els^ (explicate-assign els x cont^)) ; Tail(Cif)
     (explicate-pred cnd thn^ els^)]
    [(Let s rhs body)
     (define bodyctail (explicate-assign body x cont))
     (explicate-assign rhs s bodyctail)]
    [(Prim op es)
     (Seq (Assign (Var x) (Prim op es)) cont)]
    [(Begin es body)
     (foldl (λ (exp cont)
              (explicate-effect exp cont))
            (explicate-assign body x cont) es)]
    [(SetBang var exp)
     (explicate-effect (SetBang var exp) (explicate-assign (Void) x cont))]
    [(WhileLoop cnd body)
     (explicate-effect (WhileLoop cnd body) (explicate-assign (Void) x cont))]
    [else (error "explicate_tail unhandled case" e)]))

; explicate-effect : Exp(R) Tail(C) -> Tail(C)
(define (explicate-effect e cont)
  (match e
    [(Prim 'read ls) (Seq e cont)]
    [(Let s rhs body)
     (define bodyctail (explicate-effect body cont))
     (explicate-assign rhs s bodyctail)]
    [(Begin es body) (foldl (λ (exp cont)
                              (explicate-effect exp cont))
                            (explicate-effect body cont) es)] 
    [(SetBang var exp)
     (explicate-assign exp var cont)]
    [(WhileLoop cnd body)
     (define loop (gensym 'loop_))
     (define cont^ (Goto loop)) 
     (define body^ (explicate-effect body cont^))
     (dict-set! blocks loop (explicate-pred cnd body^ cont))
     cont^]
    [else cont]))

; create-block : Tail(Cif) -> (Goto label)
; dict-set! the input tail and return a goto to this tail
(define (create-block t)
  (match t
    [_ (define key (gensym 'block_))
       (dict-set! blocks key t)
       (Goto key)]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match-let
      ([(CProgram info blocks) (type-check-Cwhile p)])
    (X86Program info (for/list ([pair blocks])
                       (define label (car pair))
                       (define tail  (cdr pair))
                       (cons label (Block '() (si-tail tail)))))))

; si-tail : tail -> [ListOf Instr]
(define si-tail
  (λ (tail)
    (match tail
      [(Return exp)
       (define instrs (si-exp exp (Reg 'rax)))
       (append instrs
               (list (Jmp 'conclusion)))]
      [(Seq stmt tail)
       (append (si-stmt stmt)
               (si-tail tail))]
      [(Goto label) (list (Jmp label))]
      [(IfStmt cnd (Goto thn) (Goto els))
       (match cnd
         [(Prim cmp `(,atm1 ,atm2)) (list (Instr 'cmpq (list (si-atm atm2) (si-atm atm1)))
                                          (JmpIf
                                           (cond
                                             [(equal? cmp 'eq?) 'e]
                                             [(equal? cmp '<) 'l]
                                             [(equal? cmp '<=) 'le]
                                             [(equal? cmp '>) 'g]
                                             [(equal? cmp '>=) 'ge]
                                             [else (error "jmpif")])
                                           thn)
                                          (Jmp els))])]
      [else (error "expected a tail for si-tail, instead got" tail)])))

; si-atm : atm -> arg
(define si-atm
  (λ (atm)
    (match atm
      [(Int n) (Imm n)]
      [(Var x) (Var x)]
      [(Bool b) (match b
                  [#t (Imm 1)]
                  [#f (Imm 0)])]
      [else (error "expected an atom for si-atm, instead got" atm)])))

; si-exp : Exp x86Arg -> [ListOf Instr]
(define si-exp
  (λ (exp arg)
    (match exp
      [(Int n) (list (Instr 'movq (list (si-atm (Int n)) arg)))]
      [(Var x) (list (Instr 'movq (list (si-atm (Var x)) arg)))]
      [(Bool b) (list (Instr 'movq (list (si-atm (Bool b)) arg)))]
      [(Prim 'not `(,atm))
       (define arg1 (si-atm atm))
       (match arg1
         [(Var x)
          #:when (equal? arg1 arg)
          (list (Instr 'xorq (list (Imm 0) arg)))]
         [else (list (Instr 'movq (list arg1 arg)) ; why not xor first, then movq?
                     (Instr 'xorq (list (Imm 1) arg)))])]
      [(Prim op `(,atm1 ,atm2))
       #:when (or (equal? op '+) (equal? op '-))
       (define arg1 (si-atm atm1))
       (define arg2 (si-atm atm2))
       (define instr (if (equal? '+ op) 'addq 'subq))
       (abstraction instr arg arg1 arg2)]
      [(Prim '- `(,atm1)) (list (Instr 'movq (list (si-atm atm1) arg))
                                (Instr 'negq (list arg)))]
      [(Prim cmp `(,atm1 ,atm2))
       #:when (or (equal? 'eq? cmp) (equal? '< cmp) (equal? '<= cmp) (equal? '> cmp) (equal? '>= cmp))
       (define arg1 (si-atm atm1))
       (define arg2 (si-atm atm2))
       (append (cmp-to-instrs cmp arg1 arg2)
               (list (Instr 'movzbq (list (ByteReg 'al) arg))))]
      [(Prim 'read ls) (list (Callq 'read_int 0)
                             (Instr 'movq (list (Reg 'rax) arg)))])))

; abstraction : Symbol(op) -> [ListOf Instrs]
(define (abstraction op arg arg1 arg2)
  (cond
    [(equal? arg arg2) (list (Instr op (list arg1 arg2)))]
    [(equal? arg arg1) (list (Instr op (list arg2 arg1)))]
    [else 
     (list (Instr 'movq (list arg1 arg))
           (Instr op (list arg2 arg)))]))


; si-stmt : stmt -> [ListOf Instr]
(define (si-stmt stmt)
  (match stmt
    [(Assign (Var var) exp)
     (si-exp exp (Var var))]
    [(Prim 'read ls)
     (list (Callq 'read_int 0))]))

; cmp-to-instrs : Symbol Arg(x86Var) Arg(x86Arg) -> [ListOf Instr](cmpq and sete, movzbq handled in the si-stmt)
(define (cmp-to-instrs cmp arg1 arg2)
  (list (Instr 'cmpq (list arg2 arg1))
        (Instr 'set (list (match cmp
                            ['eq? 'e]
                            ['< 'l]
                            ['<= 'le]
                            ['> 'g]
                            ['>= 'ge])
                          (ByteReg 'al)))))

(define label->live (make-hash)) ;; needs to be global because we use them in read and write

(define (analyze_dataflow G transfer bottom join)
  (for ([v (in-vertices G)])
    (dict-set! label->live v bottom))
  (dict-set! label->live 'conclusion (set (Reg 'rax) (Reg 'rsp)))
  (define worklist (make-queue))
  (for ([v (in-vertices G)])
    (enqueue! worklist v))
  (define trans-G (transpose G))
  (while (not (queue-empty? worklist))
         (define node (dequeue! worklist))
         (define input (for/fold ([state bottom])
                                 ([pred (in-neighbors trans-G node)])
                         (join state (dict-ref label->live pred))))
         (define output (transfer node input))
         (cond [(not (equal? output (dict-ref label->live node)))
                (dict-set! label->live node output)
                (for ([v (in-neighbors G node)])
                  (enqueue! worklist v))])))

; transfer : [ListOf Instrs] [SetOf Location] -> [SetOf Location]
(define (transfer-helper loi input)
  (cond
    [(empty? loi) input]
    [else (let ([liveafterset (transfer-helper (cdr loi) input)])
            (set-union (set-subtract liveafterset (written (car loi)))
                       (read (car loi))))]))

;; uncover-live : pseudo-x86 -> pseudo-x86
(define (uncover-live p)
  (match p
    [(X86Program info blocks)
     (hash-clear! label->live) ;; clean up the global variable
     (define edge-list (create-edges blocks)) ;; create all edges
     (define graph (make-multigraph edge-list)) ;; create the graph from the edges
     (remove-vertex! graph 'conclusion)
     (define (trans block-label live-after)
       (define block (dict-ref blocks block-label))
       (match block
         [(Block binfo instrs)
          (transfer-helper instrs live-after)]))
     (analyze_dataflow graph trans (set) set-union)          
     (define blocks^ (sequence->list (in-vertices graph))) ; [ListOf Label] without 'conclusion
     (define newblocks
       (for/list ([label blocks^])
         (match (dict-ref blocks label)
           [(Block binfo instrs)
            (cons label (Block (ul-instrs instrs) instrs))])))
     (X86Program info newblocks)]))

; create-edges : [DictionaryOf Label Block] -> [ListOf Edge]
; Create an edge pointing from a to b if block a has a jmp or jmpif to block b
(define (create-edges blocks)
  (foldr (λ (pair rest)
           (let ([current-edges (match (cdr pair)
                                  [(Block binfo instrs)
                                   (create-edges-helper (car pair) instrs)])])
             (append current-edges rest)))
         '() blocks))

; create-edges-helper : Label [ListOf Instr] -> [ListOf Edge]
; Create an edge pointing from the given label to b if the given [ListOf Instr] has a jmp or a jmpif to block b
(define (create-edges-helper label loi)
  (cond
    [(empty? loi) empty]
    [(cons? loi) (let* ([rest (create-edges-helper label (rest loi))])
                   (match (first loi)
                     [(Jmp destination) (cons (list label destination) rest)]
                     [(JmpIf cc destination) (cons (list label destination) rest)]
                     [_ rest]))]))


; ul-instrs : [ListOf Instr] -> [ListOf [SetOf Location]]
(define (ul-instrs loi)
  (cond
    [(empty? loi) (list (set))]
    [else (let* ([nlist (ul-instrs (cdr loi))]
                 [nafter (car nlist)]
                 [curset (set-union (set-subtract nafter (written (car loi)))
                                    (read (car loi)))])
            (cons curset nlist))]))

; written : Instr -> [SetOf Location]
(define (written i)
  (match i
    [(Instr 'negq `(,arg1)) (loc-in-arg arg1)]
    [(Instr 'set `(,cc ,arg1)) (loc-in-arg arg1)]
    [(Callq label int) (set (Reg 'rax) (Reg 'rdx) (Reg 'rcx)
                            (Reg 'rsi) (Reg 'rdi) (Reg 'r8)
                            (Reg 'r9)  (Reg 'r10) (Reg 'r11))]
    [(Instr op `(,arg1 ,arg2))
     #:when (equal? op 'cmpq)
     (set)]
    [(Instr op `(,arg1 ,arg2))
     #:when (or (equal? op 'addq)
                (equal? op 'movq)
                (equal? op 'subq)
                (equal? op 'xorq))
     (loc-in-arg arg2)]
    [(Instr 'movzbq `(,arg1 ,arg2))
     (set (Reg 'rax))]
    [else (set)]))

; read : Instr -> [Setof Location]
(define (read i)
  (match i
    [(Instr op `(,arg1 ,arg2))
     #:when (or (equal? op 'movq)
                (equal? op 'movzbq))
     (loc-in-arg arg1)]
    [(Instr op `(,arg1 ,arg2))
     #:when (or (equal? op 'addq)
                (equal? op 'cmpq)
                (equal? op 'subq)
                (equal? op 'xorq))
     (set-union (loc-in-arg arg1) (loc-in-arg arg2))]
    [(Instr 'negq `(,arg1)) (loc-in-arg arg1)]
    [(Instr 'set `(,cc ,arg1)) (set)]
    [(Callq label int) (set)] ; the only call is read_int which takes no args
    [(Jmp label) (dict-ref label->live label)] ;; maybe not found, so we need tsort
    [(JmpIf cc label) (dict-ref label->live label)]
    [else (error "read does not handle" i)]))

; loc-in-arg : Arg -> [SetOf Location]
(define (loc-in-arg arg)
  (match arg
    [(Reg reg) (set (Reg reg))]
    [(Var var) (set (Var var))]
    [else (set)]))

;; build-interference : pseudo-x86 -> pseudo-x86
(define (build-interference p)
  (match p
    [(X86Program info blocks)
     (define locals (map car (dict-ref info 'locals-types)))
     (define edges (foldr (λ (pair rest)
                            (append (match (cdr pair)
                                      [(Block binfo instructions)
                                       (bi instructions (cdr binfo))])
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
     (X86Program (dict-set info-remove-label-live 'conflict graph) newblocks)]))

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
             [else rest])) (set) dict))

(define pre-color (append
                   (list (cons (Reg 'rax) -1)
                         (cons (Reg 'rsp) -2))
                   (pre-coloring (set->list available-caller) 0)
                   (pre-coloring (set->list available-callee) 8)))

;; allocate-registers : pseudo-x86 -> pseudo-x86
(define (allocate-registers p)
  (match p
    [(X86Program info blocks)
     (define graph (dict-ref info 'conflict))
     (define color-mapping (ar-vars graph)) ; [DictionaryOf Var/Reg Number(Color)]
     (define var-mapping (color-to-location color-mapping)) ; [DictionaryOf Var Reg/Deref]
     (define used-callee (filter available-callee? (set->list (list->set (map cdr var-mapping))))) ; [ListOf Reg]
     (define num-spill (num-spilled (set->list (list->set (map cdr var-mapping)))))
     (define info^ (dict-set (dict-set (dict-set (dict-set (dict-remove info 'conflict)
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
        (equal? (Reg 'r15) r))))

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

; assign-homes-single : Instr [ListOf [PairOf Var/Reg Reg/Deref]] -> Instr
(define (assign-homes-single instr alist)
  (match instr
    [(Instr op `,ls)
     (Instr op (map (λ (arg)
                      (match arg
                        [(Var var) (dict-ref alist (Var var))]
                        [else arg]))
                    ls))]
    [else instr])) 



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
                (let ([new-instrs
                       (match instr
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


;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info blocks)
     (define prelude-block (build-prelude info)) ; (cons label Block)
     (define conclusion-block (build-conclusion info)) ; (cons label Block)
     (X86Program info (cons prelude-block
                            (cons conclusion-block blocks)))]))

; build-prelude : info -> (cons label Block)
(define (build-prelude info)
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


;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("shrink" ,shrink ,interp-Rwhile ,type-check-Rwhile)
     ("uniquify" ,uniquify ,interp-Rwhile ,type-check-Rwhile)
     ("remove-complex" ,remove-complex-opera* ,interp-Rwhile ,type-check-Rwhile) 
     ("explicate-control" ,explicate-control ,interp-Cwhile ,type-check-Cwhile)
     ("select-instructions" ,select-instructions ,interp-pseudo-x86-1)
     ("uncover live" ,uncover-live ,interp-pseudo-x86-1)
     ("build interference" ,build-interference ,interp-pseudo-x86-1)
     ("allocate registers" ,allocate-registers ,interp-x86-1)
     ("patch instructions" ,patch-instructions ,interp-x86-1)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-1)
     ))
