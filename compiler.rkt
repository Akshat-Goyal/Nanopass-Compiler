#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require racket/promise)
;(require "interp-Lint.rkt")
;(require "interp-Lvar.rkt")
;(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "interp-Lwhile.rkt")
(require "interp-Cwhile.rkt")
(require "type-check-Lwhile.rkt")
(require "type-check-Cwhile.rkt")
;(require "interp-Lif.rkt")
;(require "interp-Cif.rkt")
;(require "type-check-Lif.rkt")
;(require "type-check-Cif.rkt")
;(require "type-check-Lvar.rkt")
;(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require graph)
(require "./priority_queue.rkt")
(require "./multigraph.rkt")
(provide (all-defined-out))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; Lint examples
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

(define (flip-Lint e)
  (match e
    [(Program info e) (Program info (flip-exp e))]))


(define basic-blocks (list))

(define (display-pq pq)
  (cond
    [(equal? 0 (pqueue-count pq))
     (displayln "-----")]
    [else
     (define top (pqueue-pop! pq))
     (displayln (color_priority_node-name top))
     (display-pq pq)]))

(define caller-saved-registers (list
                                (Reg 'rax)
                                (Reg 'rcx)
                                (Reg 'rdx)
                                (Reg 'rsi)
                                (Reg 'rdi)
                                (Reg 'r8)
                                (Reg 'r9)
                                (Reg 'r10)
                                (Reg 'r11)))

(define argument-registers (list
                            (Reg 'rdi)
                            (Reg 'rsi)
                            (Reg 'rdx)
                            (Reg 'rcx)
                            (Reg 'r8)
                            (Reg 'r9)))


(define all-registers (list
                       (Reg 'rcx)
                       (Reg 'rdx)
                       (Reg 'rsi)
                       (Reg 'rdi)
                       (Reg 'r8)
                       (Reg 'r9)
                       (Reg 'r10)
                       (Reg 'r11)
                       (Reg 'rbx)
                       (Reg 'r12)
                       (Reg 'r13)
                       (Reg 'r14)
                       (Reg 'rax)
                       (Reg 'rsp)
                       (Reg 'rbp)
                       (Reg 'r15)))


(define registers-for-coloring (list
                                (Reg 'rcx)
                                (Reg 'rdx)
                                (Reg 'rsi)
                                (Reg 'rdi)
                                (Reg 'r8)
                                (Reg 'r9)
                                (Reg 'r10)
                                (Reg 'r11)
                                (Reg 'rbx)
                                (Reg 'r12)
                                (Reg 'r13)
                                (Reg 'r14)))


(define unavailable-registers-for-coloring (list
                                            (Reg 'rax)
                                            (Reg 'rsp)
                                            (Reg 'rbp)
                                            (Reg 'r15)))

(define-values (color-to-register register-to-color-prev) (for/fold ([color-to-register '()]
                                                                     [register-to-color '()])
                                                                    ([reg registers-for-coloring]
                                                                     [cur-color (in-range 0 12)])
                                                            (values (dict-set color-to-register cur-color reg) (dict-set register-to-color reg cur-color))))

(define register-to-color (for/fold ([register-to-color register-to-color-prev])
                                    ([reg unavailable-registers-for-coloring]
                                     [cur-color (in-range -1 -5 -1)])
                            (dict-set register-to-color reg cur-color)))


;(displayln "hallo")
;(displayln color-to-register)
;(displayln register-to-color)

(struct color_priority_node (name saturation move_bias))

;; Next we have the partial evaluation pass described in the book.
(define (pe-neg r)
  (match r
    [(Int n) (Int (fx- 0 n))]
    [(Let var rhs body) (Let var rhs (pe-neg body))]
    [(Prim '- (list e)) e]
    [(Prim '+ (list e1 e2)) (pe-add (pe-neg e1) (pe-neg e2))]
    [else (Prim '- (list r))]))

(define (pe-add r1 r2)
  (match* (r1 r2)
    [((Int n1) (Int n2)) (Int (fx+ n1 n2))]
    [((Prim '+ (list (Int n1) e)) (Int n2)) (Prim '+ (list (Int (fx+ n1 n2)) e))]
    [((Int n1) (Prim '+ (list (Int n2) e))) (Prim '+ (list (Int (fx+ n1 n2)) e))]
    [((Prim '+ (list (Int n1) e1)) (Prim '+ (list (Int n2) e2))) (Prim '+ (list (Int (fx+ n1 n2)) (pe-add e1 e2)))]
    [(e (Int n)) (Prim '+ (list (Int n) e))]
    [((Prim '+ (list (Int n) e1)) e2) (Prim '+ (list (Int n) (pe-add e1 e2)))]
    [(e1 (Prim '+ (list (Int n) e2))) (Prim '+ (list (Int n) (pe-add e1 e2)))]
    [(_ _) (Prim '+ (list r1 r2))]))


(define (pe-exp e)
  (match e
    [(Int n) (Int n)]
    [(Var x) (Var x)]
    [(Let var rhs body) (Let var (pe-exp rhs) (pe-exp body))]
    [(Prim 'read '()) (Prim 'read '())]
    [(Prim '- (list e1)) (pe-neg (pe-exp e1))]
    [(Prim '+ (list e1 e2)) (pe-add (pe-exp e1) (pe-exp e2))]))

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

(define (shrink-exp e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(Let x rhs body)
     (Let x (shrink-exp rhs) (shrink-exp body))]
    [(If cnd thn els)
     (If (shrink-exp cnd) (shrink-exp thn) (shrink-exp els))]
    [(SetBang x rhs)
     (SetBang x (shrink-exp rhs))]
    [(Begin es body)
     (Begin (for/list ([e es]) (shrink-exp e)) (shrink-exp body))]
    [(WhileLoop cnd body)
     (WhileLoop (shrink-exp cnd) (shrink-exp body))]
    [(Prim 'and (list e1 e2))
     (If (shrink-exp e1) (shrink-exp e2) (Bool #f))]
    [(Prim 'or (list e1 e2))
     (If (shrink-exp e1) (Bool #t) (shrink-exp e2))]
    [(Prim '- (list e1 e2))
     (Prim '+ (list (shrink-exp e1) (Prim '- (list (shrink-exp e2)))))]
    [(Prim op es)
     (Prim op (for/list ([e es]) (shrink-exp e)))]))

(define (shrink p)
  (match p
    [(Program info e) (Program info (shrink-exp e))]))

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Void) (Void)]
      [(Let x e body)
       (define new-e ((uniquify-exp env) e))
       (define new-x (gensym x))
       (define new-env (dict-set env x new-x))
       (define new-body ((uniquify-exp new-env) body))
       (Let new-x new-e new-body)]
      [(If cnd thn els)
       (If ((uniquify-exp env) cnd) ((uniquify-exp env) thn) ((uniquify-exp env) els))]
      [(SetBang x rhs)
       (define new-x (dict-ref env x))
       (define new-rhs ((uniquify-exp env) rhs))
       (SetBang new-x new-rhs)]
      [(Begin es body)
       (Begin (for/list ([e es]) ((uniquify-exp env) e)) ((uniquify-exp env) body))]
      [(WhileLoop cnd body)
       (WhileLoop ((uniquify-exp env) cnd) ((uniquify-exp env) body))]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (collect-set! e)
  (match e
    [(Var x) (set)]
    [(Int n) (set)]
    [(Bool b) (set)]
    [(Void) (set)]
    [(Let x rhs body)
     (set-union (collect-set! rhs) (collect-set! body))]
    [(If cnd thn els)
     (set-union (collect-set! cnd) (collect-set! thn) (collect-set! els))]
    [(SetBang x rhs)
     (set-union (set x) (collect-set! rhs))]
    [(Begin es body)
     (define set!-es-vars (for/fold ([set!-vars (set)]) ([e es]) (set-union set!-vars (collect-set! e))))
     (set-union set!-es-vars (collect-set! body))]
    [(WhileLoop cnd body)
     (set-union (collect-set! cnd) (collect-set! body))]
    [(Prim op es)
     (for/fold ([set!-vars (set)]) ([e es]) (set-union set!-vars (collect-set! e)))]))

(define ((uncover-get!-exp set!-vars) e)
  (match e
    [(Var x)
     (if (set-member? set!-vars x)
        (GetBang x)
        (Var x))]
    [(Int n) (Int n)]
    [(Bool b) (Bool b)]
    [(Void) (Void)]
    [(Let x rhs body)
     (Let x ((uncover-get!-exp set!-vars) rhs) ((uncover-get!-exp set!-vars) body))]
    [(If cnd thn els)
     (If ((uncover-get!-exp set!-vars) cnd) ((uncover-get!-exp set!-vars) thn) ((uncover-get!-exp set!-vars) els))]
    [(SetBang x rhs)
     (SetBang x ((uncover-get!-exp set!-vars) rhs))]
    [(Begin es body)
     (Begin (for/list ([e es]) ((uncover-get!-exp set!-vars) e)) ((uncover-get!-exp set!-vars) body))]
    [(WhileLoop cnd body)
     (WhileLoop ((uncover-get!-exp set!-vars) cnd) ((uncover-get!-exp set!-vars) body))]
    [(Prim op es)
     (Prim op (for/list ([e es]) ((uncover-get!-exp set!-vars) e)))]))

(define (uncover-get! p)
  (match p
    [(Program info e) (Program info ((uncover-get!-exp (collect-set! e)) e))]))

(define (rco-atom env)
  (lambda (e)
    (gensym 'tmp)))

(define (Atm? e)
  (match e
    [(Int n) #t]
    [(Var x) #t]
    [(Bool b) #t]
    [(Void) #t]
    [_ #f]))

(define (rco-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Bool b) (Bool b)]
      [(Void) (Void)]
      [(GetBang x) (Var x)]
      [(Prim 'read '()) (Prim 'read '())]
      [(Let x e body) 
       (Let x ((rco-exp env) e) ((rco-exp env) body))]
      [(If cnd thn els)
       (If ((rco-exp env) cnd) ((rco-exp env) thn) ((rco-exp env) els))]
      [(SetBang x rhs)
       (SetBang x ((rco-exp env) rhs))]
      [(Begin es body)
       (Begin (for/list ([e es]) ((rco-exp env) e)) ((rco-exp env) body))]
      [(WhileLoop cnd body)
       (WhileLoop ((rco-exp env) cnd) ((rco-exp env) body))]
      [(Prim op (list e1))
       (cond
         [(Atm? e1) (Prim op (list e1))]
         [else
          (define tmp-var ((rco-atom env) e1))
          (Let tmp-var ((rco-exp env) e1) (Prim op (list (Var tmp-var))))])]
      [(Prim op (list e1 e2))
       (cond
         [(not (Atm? e1))
          (define tmp-var ((rco-atom env) e1))
          (Let tmp-var ((rco-exp env) e1) ((rco-exp env) (Prim op (list (Var tmp-var) e2))))]
         [(not (Atm? e2))
          (define tmp-var ((rco-atom env) e2))
          (Let tmp-var ((rco-exp env) e2) ((rco-exp env) (Prim op (list e1 (Var tmp-var)))))]
         [else (Prim op (list e1 e2))])])))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info ((rco-exp '()) e))]))

(define (create_block tail)
  (delay
    (define t (force tail))
    (match t
      [(Goto label) (Goto label)]
      [else
       (let ([label (gensym 'block)])
         (set! basic-blocks (cons (cons label t) basic-blocks))
         (Goto label))])))

(define (Cmp? op)
  (match op
    ['eq? #t]
    ['< #t]
    ['<= #t]
    ['> #t]
    ['>= #t]
    [_ #f]))

(define (explicate_pred cnd thn els)
  (match cnd
    [(Var x)
     (delay (IfStmt (Prim 'eq? (list (Var x) (Bool #t))) (force (create_block thn)) (force (create_block els))))]
    [(Let x rhs body)
     (explicate-assign rhs x (explicate_pred body thn els))]
    [(Prim 'not (list e))
     (match e
       [(Bool b)
        (if b els thn)]
       [(Var x)
        (delay (IfStmt (Prim 'eq? (list (Var x) (Bool #f))) (force (create_block thn)) (force (create_block els))))])]
    [(Prim op es) #:when (Cmp? op)
                  (delay (IfStmt (Prim op es) (force (create_block thn))
                                 (force (create_block els))))]
    [(Bool b) (if b thn els)]
    [(If cnd^ thn^ els^)
     (delay 
       (define thn-block (create_block thn))
       (define els-block (create_block els))
       (define B1 (explicate_pred thn^ thn-block els-block))
       (define B2 (explicate_pred els^ thn-block els-block))
       (force (explicate_pred cnd^ B1 B2)))]
    [(Begin es body)
     (explicate-effect (Begin es (Void)) (explicate_pred body thn els))]
    [else (error "explicate_pred unhandled case" cnd)]))

; (let ([x (if (let ([x #t]) (if x x (not x))) #t #f)]) (if x 10 (- 10)))

(define (explicate-effect e cont)
  (match e
    [(Var x) cont]
    [(Int n) cont]
    [(Bool b) cont]
    [(Void) cont]
    [(Prim 'read '()) (Seq (Prim 'read '()) cont)]
    [(Prim op es) cont]
    [(Let x rhs body) (explicate-assign rhs x (explicate-effect body cont))]
    [(If cnd thn els)
     (define cont-block (create_block cont))
     (define B1 (explicate-effect thn cont-block))
     (define B2 (explicate-effect els cont-block))
     (explicate_pred cnd B1 B2)]
    [(SetBang x rhs) (explicate-assign rhs x cont)]
    [(Begin es body)
     (match es
      [(list) (explicate-effect body cont)]
      [(cons e rest) (explicate-effect e (explicate-effect (Begin rest body) cont))])]
    [(WhileLoop cnd body)
     (define loop-label (gensym 'block))
     (define thn (explicate-effect body (Goto loop-label)))
     (define els cont)
     (define loop (explicate_pred cnd thn els))
     (set! basic-blocks (cons (cons loop-label loop) basic-blocks))
     (Goto loop-label)]
    [else (error "explicate-effect unhandled case" e)]))

(define (explicate-tail e)
  (match e
    [(Var x) (delay (Return (Var x)))]
    [(Int n) (delay (Return (Int n)))]
    [(Bool b) (delay (Return (Bool b)))]
    [(Void) (delay (Return (Void)))]
    [(Let x rhs body) (explicate-assign rhs x (explicate-tail body))]
    [(Prim op es) (delay (Return (Prim op es)))]
    [(If cnd exp1 exp2)
     (define B1 (explicate-tail exp1))
     (define B2 (explicate-tail exp2))
     (explicate_pred cnd B1 B2)]
    [(SetBang x rhs) (explicate-assign rhs x (Return (Void)))]
    [(Begin es body) (explicate-effect (Begin es (Void)) (explicate-tail body))]
    [(WhileLoop cnd body)
     (define loop-label (gensym 'block))
     (define thn (explicate-effect body (Goto loop-label)))
     (define els (Return (Void)))
     (define loop (explicate_pred cnd thn els))
     (set! basic-blocks (cons (cons loop-label loop) basic-blocks))
     (Goto loop-label)]
    [else (error "explicate-tail unhandled case" e)]))

(define (explicate-assign e x cont)
  (match e
    [(Var y) (delay (Seq (Assign (Var x) (Var y)) (force cont)))]
    [(Int n) (delay (Seq (Assign (Var x) (Int n)) (force cont)))]
    [(Bool b) (delay (Seq (Assign (Var x) (Bool b)) (force cont)))]
    [(Void) (delay (Seq (Assign (Var x) (Void)) (force cont)))]
    [(Let y rhs body) (explicate-assign rhs y (explicate-assign body x cont))]
    [(Prim op es) (delay (Seq (Assign (Var x) (Prim op es)) (force cont)))]
    [(If cnd exp1 exp2)
     (delay
       (define tail-block (create_block cont))
       (define B1 (explicate-assign exp1 x tail-block))
       (define B2 (explicate-assign exp2 x tail-block))
       (force (explicate_pred cnd B1 B2)))]
    [(SetBang y rhs) 
     (explicate-assign rhs y (explicate-assign (Void) x cont))]
    [(Begin es body)
     (explicate-effect (Begin es (Void)) (explicate-assign body x cont))]
    [(WhileLoop cnd body)
     (define loop-label (gensym 'block))
     (define thn (explicate-effect body (Goto loop-label)))
     (define els (Seq (Assign (Var x) (Void)) cont))
     (define loop (explicate_pred cnd thn els))
     (set! basic-blocks (cons (cons loop-label loop) basic-blocks))
     (Goto loop-label)]
    [else (error "explicate-assign unhandled case" e)]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p 
    [(Program info e)
     (set! basic-blocks (list))
     (define tail (force (explicate-tail e)))
     (set! basic-blocks (cons (cons 'start tail) basic-blocks))
     (CProgram info basic-blocks)]))

(define (si-atm e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Imm n)]
    [(Bool #t) (Imm 1)]
    [(Bool #f) (Imm 0)]
    [(Void) (Imm 0)]))

(define (si-exp v e cont [op-x86-dict '((+ . addq) (- . subq))])
  (match e
    [(Var y) (cons (Instr 'movq (list (si-atm e) v)) cont)]
    [(Int n) (cons (Instr 'movq (list (si-atm e) v)) cont)]
    [(Bool b) (cons (Instr 'movq (list (si-atm e) v)) cont)]
    [(Void) (cons (Instr 'movq (list (si-atm e) v)) cont)]
    [(Prim 'not (list e1))
     (cond
       [(equal? v e1)
        (cons (Instr 'xorq (list (Imm 1) v)) cont)]
       [else
        (append (list (Instr 'movq (list (si-atm e1) v)) (Instr 'xor (list (Imm 1) v))) cont)])]
    [(Prim 'eq? (list e1 e2))
     (append (list (Instr 'cmpq (list (si-atm e1) (si-atm e2))) (Instr 'set (list 'e (ByteReg 'al))) (Instr 'movzbq (list (ByteReg 'al) v))) cont)]
    [(Prim '< (list e1 e2))
     (append (list (Instr 'cmpq (list (si-atm e1) (si-atm e2))) (Instr 'set (list 'l (ByteReg 'al))) (Instr 'movzbq (list (ByteReg 'al) v))) cont)]
    [(Prim '<= (list e1 e2))
     (append (list (Instr 'cmpq (list (si-atm e1) (si-atm e2))) (Instr 'set (list 'le (ByteReg 'al))) (Instr 'movzbq (list (ByteReg 'al) v))) cont)]
    [(Prim '> (list e1 e2))
     (append (list (Instr 'cmpq (list (si-atm e1) (si-atm e2))) (Instr 'set (list 'g (ByteReg 'al))) (Instr 'movzbq (list (ByteReg 'al) v))) cont)]
    [(Prim '>= (list e1 e2))
     (append (list (Instr 'cmpq (list (si-atm e1) (si-atm e2))) (Instr 'set (list 'ge (ByteReg 'al))) (Instr 'movzbq (list (ByteReg 'al) v))) cont)]
    [(Prim 'read '()) 
     (append (list (Callq 'read_int 0) (Instr 'movq (list (Reg 'rax) v))) cont)]
    [(Prim '- (list e1))
     #:when (equal? e1 v) (append (Instr 'negq (list v)) cont)]
    [(Prim '- (list e1)) 
     (append (list (Instr 'movq (list (si-atm e1) v)) (Instr 'negq (list v))) cont)]
    [(Prim op (list e1 e2))
     #:when (equal? e1 v) (cons (Instr (dict-ref op-x86-dict op) (list (si-atm e2) v)) cont)]
    [(Prim '+ (list e1 e2))
     #:when (equal? e2 v) (cons (Instr 'addq (list (si-atm e1) v)) cont)]
    [(Prim op (list e1 e2))
     (append (list (Instr 'movq (list (si-atm e1) v)) (Instr (dict-ref op-x86-dict op) (list (si-atm e2) v))) cont)]))

(define (si-stmt e cont)
  (match e
    [(Assign (Var x) exp) (si-exp (Var x) exp cont)]
    [(Prim 'read '()) (cons (Callq 'read_int 0) cont)]))

(define (si-tail e)
  (match e
    [(Return exp) (si-exp (Reg 'rax) exp (list (Jmp 'conclusion)))]
    [(Seq stmt tail) (si-stmt stmt (si-tail tail))]
    [(Goto label)
     (list (Jmp label))]
    [(IfStmt (Prim 'eq? (list atm1 atm2)) (Goto thn) (Goto els))
     (list (Instr 'cmpq (list (si-atm atm2) (si-atm atm1))) (JmpIf 'e thn) (Jmp els))]
    [(IfStmt (Prim '< (list atm1 atm2)) (Goto thn) (Goto els))
     (list (Instr 'cmpq (list (si-atm atm2) (si-atm atm1))) (JmpIf 'l thn) (Jmp els))]
    [(IfStmt (Prim '<= (list atm1 atm2)) (Goto thn) (Goto els))
     (list (Instr 'cmpq (list (si-atm atm2) (si-atm atm1))) (JmpIf 'le thn) (Jmp els))]
    [(IfStmt (Prim '> (list atm1 atm2)) (Goto thn) (Goto els))
     (list (Instr 'cmpq (list (si-atm atm2) (si-atm atm1))) (JmpIf 'g thn) (Jmp els))]
    [(IfStmt (Prim '>= (list atm1 atm2)) (Goto thn) (Goto els))
     (list (Instr 'cmpq (list (si-atm atm2) (si-atm atm1))) (JmpIf 'ge thn) (Jmp els))]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info e)
     (define partial-x86-blocks (for/fold ([partial-x86-blocks '()]) ([block e]) (dict-set partial-x86-blocks (car block) (Block '() (si-tail (cdr block))))))
     (X86Program info partial-x86-blocks)]))

(define (constant-propagation-instrs instrs env)
  (match instrs
    [(cons instr rest)
     (match instr
      [(Instr 'movq (list (Var x) (Var y)))
       (define const (dict-ref env (Var x) #f))
       (if (equal? const #f)
          (cons instr (constant-propagation-instrs rest (dict-remove env (Var y))))
          (cons (Instr 'movq (list const (Var y))) (constant-propagation-instrs rest (dict-set env (Var y) const))))]
      [(Instr 'movq (list (Imm n) (Var y)))
       (cons instr (constant-propagation-instrs rest (dict-set env (Var y) (Imm n))))]
      [(Instr 'cmpq (list arg1 arg2)) 
       (cons (Instr 'cmpq (list (dict-ref env arg1 arg1) arg2)) (constant-propagation-instrs rest env))]
      [(Instr x86-op (list arg1 arg2)) 
       (cons (Instr x86-op (list (dict-ref env arg1 arg1) arg2)) (constant-propagation-instrs rest (dict-remove env arg2)))]
      [(Instr x86-op (list arg)) 
       (cons (Instr x86-op (list (dict-ref env arg arg))) (constant-propagation-instrs rest (dict-remove env arg)))]
      [_ (cons instr (constant-propagation-instrs rest env))])]
    [_ instrs]))

(define (constant-propagation p)
  (match p
    [(X86Program info e)
     (define partial-x86-blocks (for/list ([label-block-pair e]) 
                                  (define label (car label-block-pair))
                                  (define block (cdr label-block-pair))
                                  (define updated-instrs (constant-propagation-instrs (Block-instr* block) '()))
                                  (define updated-block (Block (Block-info block) updated-instrs))
                                  (cons label updated-block)))
     (X86Program info partial-x86-blocks)]))

(define (compute-write-locations instr)
  ; TODO: handle retq instruction: not needed
  (match instr
    [(Instr 'cmpq es) (set)] ;TODO: prolly return empty set here: DONE, before we were returning rax
    [(Instr 'set es) (set (Reg 'rax))]
    [(Instr x86-op (list arg1 arg2)) (set arg2)] ; arg2 cannot be immediate since we are writing into arg2
    [(Instr x86-op (list arg1)) (set arg1)] ; arg1 cannot be immediate, x86-op should only be negq
    [(Callq func-name n) (list->set caller-saved-registers)]
    [_ (set)]))

(define (compute-read-locations instr)
  ; TODO: handle retq instruction: no need to because it will never be used before this pass
  (match instr
    [(Instr 'movq (list arg1 arg2))
     (match arg1
       [(Imm n) (set)]
       [else (set arg1)])]
    [(Instr 'set es) (set)]
    [(Instr 'movzbq es) (set (Reg 'rax))]
    [(Instr x86-op (list arg1 arg2))
     ; handles xorq cmpq addq subq 
     (match* (arg1 arg2)
       [((Imm n1) (Imm n2)) (set)]
       [((Imm n1) arg2) (set arg2)]
       [(arg1 (Imm n2)) (set arg1)]
       [(_ _) (set arg1 arg2)])]
    [(Instr x86-op (list arg1)) (set arg1)] ; arg1 cannot be immediate, x86-op should only be negq
    [(Callq func-name n)
     (cond
       [(<= n 6) (list->set (take argument-registers n))]
       [else (list->set (take argument-registers 6))])]
    [_ (set)]))

(define (find-live-sets instrs live-sets)
  (match instrs
    [(cons instr rest)
     (define read-locations (compute-read-locations instr))
     (define write-locations (compute-write-locations instr))
     (define live-after-cur (cond
                              [(empty? live-sets) (set)]
                              [else (car live-sets)]))
     (define live-before (set-union (set-subtract live-after-cur write-locations) read-locations))
     (find-live-sets rest (cons live-before live-sets))]
    [else live-sets]))
    
;; uncover_live: pseudo-x86 -> pseudo-x86
(define (generate-label-graph e graph)
  (match e
    [(cons cur rest)
     (match cur
       [(cons label (Block sinfo instrs))
        (add-vertex! graph label)
        (define reverse-instrs (reverse instrs))
        (define last-instr (car reverse-instrs))

        ; last instruction is always a jmp instruction
        (define label1 (Jmp-target last-instr))
        (cond
          [(not (eq? label1 'conclusion))
           (add-vertex! graph label1)
           (add-directed-edge! graph label1 label)]
          [else
           #f])
       
        ; second last instruction might be a JmpIf instruction
        (define rem-instr (cdr reverse-instrs))
        (cond
          [(not (empty? rem-instr))
           (define second-last-instr (car (cdr reverse-instrs)))
           (match second-last-instr
             [(JmpIf cc l)
              (add-vertex! graph l)
              (add-directed-edge! graph l label)]
             [else
              #f])]
          [else
           #f])
        (generate-label-graph rest graph)])]

    [else
     graph]))

(define (uncover_live_after_per_block e live-afters blocks label-graph topo-order)
  (match topo-order
    [(cons label rest)
     (define cur-block (dict-ref e label))
     (define instrs (Block-instr* cur-block))
     (define initial-live-after (dict-ref live-afters label))
     ;(displayln initial-live-after)
     (define live-sets (find-live-sets (reverse instrs) initial-live-after))
     (define updated-cur-block (Block `((live-sets . ,(cdr live-sets))) instrs))
     (define updated-blocks (dict-set blocks label updated-cur-block))
     (define updated-live-afters (for/fold ([updated-live-afters live-afters])
                                           ([adj (in-neighbors label-graph label)])
                                   (dict-set updated-live-afters adj (list (set-union (car live-sets) (car (dict-ref live-afters adj))))))) 
     (uncover_live_after_per_block e updated-live-afters updated-blocks label-graph rest)]
    [else
     blocks]))

(define (analyze_dataflow blocks live-afters label-graph)
  (define-values (updated-blocks updated-live-afters) 
    (for/fold ([updated-blocks blocks] [updated-live-afters live-afters]) 
              ([label-block-pair blocks])
      (define label (car label-block-pair)) 
      (define block (cdr label-block-pair)) 
      (define instrs (Block-instr* block))
      (define live-after (dict-ref live-afters label))
      (define live-sets (find-live-sets (reverse instrs) (list live-after)))
      (define updated-block (Block `((live-sets . ,(cdr live-sets))) instrs))
      (define updated-blocks^ (dict-set updated-blocks label updated-block))
      (define updated-live-afters^ 
        (for/fold ([updated-live-afters^ updated-live-afters])
                  ([adj (in-neighbors label-graph label)])
          (dict-set updated-live-afters^ adj (set-union (car live-sets) (dict-ref updated-live-afters adj)))))
      (values updated-blocks^ updated-live-afters^)))
  (cond
    [(equal? live-afters updated-live-afters) updated-blocks]
    [else (analyze_dataflow updated-blocks updated-live-afters label-graph)]))

(define (uncover_live p)
  (match p
    [(X86Program info e)
     (define label-graph (generate-label-graph e (make-multigraph '())))
     (define label-list (for/list ([block e]) (car block)))
     (define initial-live-afters (for/fold ([initial-live-afters '()]) ([label label-list]) (dict-set initial-live-afters label (set))))
     (define updated-blocks (analyze_dataflow e initial-live-afters label-graph))
     (X86Program info updated-blocks)]))

(define (print-graph graph)
  (for ([u (in-vertices graph)])
    (for ([v (in-neighbors graph u)])
      (display (format "~a -> ~a;\n" u v)))))

(define (build-intereference-graph-block instrs live-sets cur-graph)
  (for ([live-set live-sets]
        [instr instrs])
    (match instr
      [(Instr 'movq (list arg1 arg2))
       (for ([live-location (set->list live-set)])
         (cond
           [(not (or (equal? arg1 live-location) (equal? arg2 live-location)))
            (add-edge! cur-graph arg2 live-location)]))]
      [(Instr 'movzbq (list arg1 arg2))
       (for ([live-location (set->list live-set)])
         (cond
           [(not (or (equal? arg1 live-location) (equal? arg2 live-location)))
            (add-edge! cur-graph arg2 live-location)]))]
      [else
       (define write-locations (compute-write-locations instr))
       (for* ([live-location live-set]
              [write-location write-locations])
         (cond
           [(not (equal? live-location write-location))
            (add-edge! cur-graph live-location write-location)]))]))
  cur-graph)

(define (build-interference-graph blocks locals)
  (define interference-graph (undirected-graph '()))

  (for ([reg all-registers]) ;TODO: do we need to add vertices of all registers or only caller saved ones or none at all here?
    (add-vertex! interference-graph reg))

  (for ([var locals]) ;need to do this otherwise error on var_test 6 or something
    (add-vertex! interference-graph (Var var)))
  
  (for ([block_key (dict-keys blocks)])
    (define block (dict-ref blocks block_key))
    (match block
      [(Block sinfo instrs)
       (define live-sets (dict-ref sinfo 'live-sets))
       (set! interference-graph (build-intereference-graph-block instrs live-sets interference-graph))
       ;(print-graph interference-graph)
       ]))
  
  ;(print-graph interference-graph)
  interference-graph)
 
;; build_interference: pseudo-x86 -> pseudo-x86
(define (build_interference p)
  (match p
    [(X86Program info blocks)
     (define locals (dict-keys (dict-ref info 'locals-types)))
     (define interference-graph (build-interference-graph blocks locals))
     (X86Program (dict-set info 'conflicts interference-graph) blocks)]))

(define graph-coloring-comparator                         
  (lambda (node1 node2)
    (cond
      [(= (color_priority_node-saturation node1) (color_priority_node-saturation node2))
       (> (color_priority_node-move_bias node1) (color_priority_node-move_bias node2))]
      [else
       (> (color_priority_node-saturation node1) (color_priority_node-saturation node2))])))

(define (build-move-graph blocks locals)
  (define graph (undirected-graph '()))

  (for ([reg all-registers])
    (add-vertex! graph reg))
 
  (for ([var locals])
    (add-vertex! graph (Var var)))

  (for ([block_key (dict-keys blocks)])
    (define block (dict-ref blocks block_key))
    (match block
      [(Block sinfo instrs)
       (for ([instr instrs])
         (match instr
           ;no need to handle movzbq because it always moves al (rax) to something and no need of move biasing for rax
           [(Instr 'movq (list arg1 arg2))
            (match* (arg1 arg2)
              [((Var x) (Var y))
               (add-edge! graph arg1 arg2)]
              [((Var x) (Reg r))
               (cond
                 [(>= (dict-ref register-to-color arg2) 0) (add-edge! graph arg1 arg2)])]
              [((Reg r) (Var x))
               (cond
                 [(>= (dict-ref register-to-color arg1) 0) (add-edge! graph arg1 arg2)])]
              [(_ _) (void)])]
           [_ (void)]))
       ]))
  graph)

(define (find-mex s cur)
  (cond
    [(set-member? s cur)
     (find-mex s (+ cur 1))]
    [else
     cur]))

(define (find-correct-color potential-colors interfering-colors)
  (define allowed-colors (set-subtract potential-colors interfering-colors))
  (define mex (find-mex interfering-colors 0))
  (cond
    [(set-empty? allowed-colors)
     mex]
    [else
     (let ([move-bias-color (set-first allowed-colors)])
       (cond
         [(< move-bias-color 13)
          move-bias-color]
         [(< mex 13)
          mex]
         [else
          move-bias-color]))]))

; conflicts is a set of neighbors of node in interference graph
(define (find-move-biasing-colors move-graph node color conflicts visited)
  (for/set ([v (in-neighbors move-graph node)]
            #:when (equal? (dict-ref visited v) #t)
            #:when (not (set-member? conflicts node))
            #:when (not (< (dict-ref color v) 0))) ; check if node is visited or not (we can set registers to be visited): DONE
    (dict-ref color v)))

(define (find-interfering-colors color conflicts visited)
  (for/set ([u conflicts]
            #:when (equal? (dict-ref visited u) #t)) ; should be visited: DONE 
    (dict-ref color u)))

(define (update-saturation saturation color neighbors)
  (match neighbors
    [(cons cur rest)
     (match cur
       [(Var x)
        (let* ([my-saturation (dict-ref saturation cur)]
               [my-saturation-updated (set-add my-saturation color)]
               [updated-saturation (dict-set saturation cur my-saturation-updated)])
          (update-saturation updated-saturation color rest))]
       [_ (update-saturation saturation color rest)])]
    [_ saturation]))

(define (update-move-bias move-bias neighbors)
  ;(displayln "update-move-bias")
  ;(displayln move-bias)
  ;(displayln neighbors)
  (match neighbors
    [(cons cur rest) ;TODO: check if we need to check if cur is variable or not: DONE
     (match cur
       [(Var x)
        (let* ([my-bias (dict-ref move-bias cur)]
               [my-bias-updated (+ my-bias 1)]
               [updated-move-bias (dict-set move-bias cur my-bias-updated)])
          (update-move-bias updated-move-bias rest))]
       [_ (update-move-bias move-bias rest)])]
    [_ move-bias]))

(define (update-pq pq saturation move-bias neighbors)
  (for ([cur neighbors])
    (match cur
      [(Var x)
       (let* ([my-saturation (dict-ref saturation cur)]
              [my-bias (dict-ref move-bias cur)]
              [new-node (color_priority_node cur (set-count my-saturation) my-bias)])
         (pqueue-push! pq new-node))]
      [_ (void)]))
  pq)
         
        
; CANT DO THIS BECAUSE PROLLY pqueue-push DOESNT RETURN NEW PQ BUT UPDATES IN THE OLD PQ ITSELF       
;  (match neighbors
;    [(cons cur rest)
;     (match cur
;       [(Var x)
;        (display "update-pq: ")
;        (displayln cur)
;        (displayln rest)
;        (displayln saturation)
;        (let* ([my-saturation (dict-ref saturation cur)]
;               [my-bias (dict-ref move-bias cur)]
;               [new-node (color_priority_node cur (set-count my-saturation) my-bias)]
;               [updated-pq (pqueue-push! pq new-node)])
;          (update-pq updated-pq saturation move-bias rest))]
;       [_ (update-pq pq saturation move-bias rest)])]
;    [_ pq]))
  

(define (color-recur interference-graph move-graph saturation move-bias visited color pq)
  (cond
    [(equal? (pqueue-count pq) 0)
     color]
    [else
     (let* ([cur-node (color_priority_node-name (pqueue-pop! pq))] ; check if pq is modified here or if we need to set it to a new pq: NOT NEEDED
            [vis (dict-ref visited cur-node)])
       (match vis
         [#t
          (color-recur interference-graph move-graph saturation move-bias visited color pq)]
         [#f
          (define neighbors (for/list ([u (in-neighbors interference-graph cur-node)]) u)) ; maybe modify here to return only variables that are interfering: NOT NEEDED
          (define potential-colors (find-move-biasing-colors move-graph cur-node color (list->set neighbors) visited)) ; returns a set
          (define interfering-colors (find-interfering-colors color neighbors visited)); returns a set
          (define cur-color (find-correct-color potential-colors interfering-colors))
          ;(displayln "cur-node neighbors potential-colors interfering-colors cur-color")
          ;(displayln cur-node)
          ;(displayln neighbors)
          ;(displayln potential-colors)
          ;(displayln interfering-colors)
          ;(displayln cur-color)
          (define updated-saturation (update-saturation saturation cur-color neighbors))
          ;(display "updated-saturation: ")
          ;(displayln updated-saturation)
          (define updated-move-bias (update-move-bias move-bias (for/list ([u (in-neighbors move-graph cur-node)]) u)))
          ;(displayln "old and updated-move-bias: ")
          ;(displayln move-bias)
          ;(displayln updated-move-bias)
          (define updated-visited (dict-set visited cur-node #t))
          (define updated-color (dict-set color cur-node cur-color))
          (define updated-pq (update-pq pq updated-saturation updated-move-bias neighbors))
          (color-recur interference-graph move-graph updated-saturation updated-move-bias updated-visited updated-color updated-pq)]))]))

(define (get-initial-saturation-helper cur-saturation u u-color v-list)
  (match v-list
    [(cons v rest)
     (match v
       [(Var x)
        (define old-saturation (dict-ref cur-saturation v))
        (define new-saturation (set-add old-saturation u-color))
        (get-initial-saturation-helper (dict-set cur-saturation v new-saturation) u u-color rest)]
       [_ (get-initial-saturation-helper cur-saturation u u-color rest)])]
    [_ cur-saturation]))
  
(define (get-initial-saturation cur-saturation u-list interference-graph)
  ;(displayln "u-list")
  ;(displayln u-list)
  (match u-list
    [(cons u rest)
     ;(displayln "u")
     ;(displayln u)
     (match u
       [(Reg r)
        (define v-list (for/list ([v (in-neighbors interference-graph u)]) v))
        ;(displayln "v-list")
        ;(displayln v-list)
        (define updated-saturation (get-initial-saturation-helper cur-saturation u (dict-ref register-to-color u) v-list))
        (get-initial-saturation updated-saturation rest interference-graph)]
       [_ (get-initial-saturation cur-saturation rest interference-graph)])]
    [_ cur-saturation]))

(define (get-initial-move-bias-helper cur-move-bias u v-list)
  (match v-list
    [(cons v rest)
     (match v
       [(Var x)
        (define old-move-bias (dict-ref cur-move-bias v))
        (define new-move-bias (+ 1 old-move-bias))
        (get-initial-move-bias-helper (dict-set cur-move-bias v new-move-bias) u rest)]
       [_ (get-initial-move-bias-helper cur-move-bias u rest)])]
    [_ cur-move-bias]))
  
(define (get-initial-move-bias cur-move-bias u-list move-graph)
  (match u-list
    [(cons u rest)
     (match u
       [(Reg r)
        (define v-list (for/list ([v (in-neighbors move-graph u)]) v))
        (define updated-move-bias (get-initial-move-bias-helper cur-move-bias u v-list))
        (get-initial-move-bias updated-move-bias rest move-graph)]
       [_ (get-initial-move-bias cur-move-bias rest move-graph)])]
    [_ cur-move-bias]))


(define (color-graph interference-graph locals move-graph)

  ;(display "locals: ")
  ;(displayln locals)

  ; set default saturation, visited and move-bias of ONLY variables.
  (define-values (prev-saturation visited-prev move-bias-prev) (for/fold ([saturation '()]    
                                                                          [visited '()]
                                                                          [move-bias '()])
                                                                         ([var locals])
                                                                 (values (dict-set saturation (Var var) (set)) (dict-set visited (Var var) #f) (dict-set move-bias (Var var) 0))))

  ;TODO: update move-bias for register to variable or vive versa move operations: DONE
                                              
  ; set default of color of ONLY registers. locals are not present as keys of color right now
  (define color (for/fold ([color '()]) ([reg all-registers]) (dict-set color reg (dict-ref register-to-color reg))))
  ; set registers as visited. locals were set as unvisited before
  (define visited (for/fold ([visited visited-prev]) ([reg all-registers]) (dict-set visited reg #t)))
  (define u-list (for/list ([u (in-vertices interference-graph)]) u))
  ; sets saturtation for variables adjacent to registers. This step is performed because registers can be ignored from the graph after this step
  (define saturation (get-initial-saturation prev-saturation u-list interference-graph))
  (define u-list-move-graph (for/list ([u (in-vertices move-graph)]) u))

  ; IS THIS STEP REQUIRED ??
  (define move-bias (get-initial-move-bias move-bias-prev u-list-move-graph move-graph))

  ; (displayln "old and updated move-bias")
  ; (displayln move-bias-prev)
  ; (displayln move-bias)
 
  ;(displayln prev-saturation)
  ;(displayln "new-saturation")
  ;(displayln saturation)

  (define pq (make-pqueue graph-coloring-comparator))     
  (for ([var locals])
    (define cur-saturation (set-count (dict-ref saturation (Var var))))
    (define cur-move-bias (dict-ref move-bias (Var var))) ; TODO: update move bias here using 'move-bias' ??
    (define cur-node (color_priority_node (Var var) cur-saturation cur-move-bias))
    (pqueue-push! pq cur-node))
  (color-recur interference-graph move-graph saturation move-bias visited color pq))

(define (get-used-callee-registers locals cur-used-callee variable-colors)
  (match locals
    [(cons var rest)
     (define var-color (dict-ref variable-colors (Var var)))
     (cond
       [(and (>= var-color 8) (<= var-color 11)) (get-used-callee-registers rest (set-add cur-used-callee (dict-ref color-to-register var-color)) variable-colors)] ;TODO: change this hardcoded colors to something more general
       [else (get-used-callee-registers rest cur-used-callee variable-colors)])] 
    [_ cur-used-callee]))


(define (assign-home-to-locals locals variable-colors used-callee cur-locals-homes)
  (match locals
    [(cons var rest)
     (define var-color (dict-ref variable-colors (Var var)))
     (cond
       [(<= var-color 11)
        (assign-home-to-locals rest variable-colors used-callee (dict-set cur-locals-homes var (dict-ref color-to-register var-color)))]
       [else
        (define offset (* -8 (- (+ var-color used-callee) 11)))
        (assign-home-to-locals rest variable-colors used-callee (dict-set cur-locals-homes var (Deref 'rbp offset)))])]
    [_ cur-locals-homes]))

(define (get-stack-colors locals variable-colors cur-stack-colors)
  (match locals
    [(cons var rest)
     (define var-color (dict-ref variable-colors (Var var)))
     (cond
       [(<= var-color 11)
        (get-stack-colors rest variable-colors cur-stack-colors)]
       [else
        (get-stack-colors rest variable-colors (set-add cur-stack-colors var-color))])]
    [_ cur-stack-colors]))

(define (assign-homes-instr instrs locals-home)
  (match instrs
    [(cons (Instr x86-op args) ss)
     (cons (Instr x86-op (for/list ([arg args]) 
                           (if (Var? arg) (dict-ref locals-home (Var-name arg)) arg))) 
           (assign-homes-instr ss locals-home))]
    [(cons instr ss) (cons instr (assign-homes-instr ss locals-home))]
    [else instrs]))

(define (get-stack-space stack-color-size used-callee-size)
  (define stack-size (+ (* 8 stack-color-size) (* 8 used-callee-size)))
  (if (zero? (remainder stack-size 16)) stack-size (+ 8 stack-size)))
     
;; allocate_registers: pseudo-x86 -> pseudo-x86
(define (allocate_registers p)
  (match p
    [(X86Program info blocks)
     (define locals (dict-keys (dict-ref info 'locals-types)))
     (define interference-graph (dict-ref info 'conflicts))
     (define move-graph (build-move-graph blocks locals))
     ;(display "move-graph: ")
     ;(print-graph move-graph)
     ;(displayln "move-graph end")
     (define variable-colors (color-graph interference-graph locals move-graph))
     ;(display "variable-colors: ")
     ;(displayln variable-colors)
     (define used-callee (get-used-callee-registers locals (set) variable-colors))
     (define new-info (dict-set info 'used_callee used-callee))
     (define locals-homes (assign-home-to-locals locals variable-colors (set-count used-callee) '()))
     (define stack-variable-colors (get-stack-colors locals variable-colors (set)))
     (define stack-size (get-stack-space (set-count stack-variable-colors) (set-count used-callee)))

     (for ([block_key (dict-keys blocks)])
       (define block (dict-ref blocks block_key))
       (match block
         [(Block sinfo instrs)
          (set! blocks (dict-set blocks block_key (Block sinfo (assign-homes-instr instrs locals-homes))))
          ]))
       
     (X86Program (dict-set new-info 'stack-space stack-size) blocks)]))

; assign homes of R1
;(define (assign-home-to-locals locals-types)
;  (define-values (stack-space locals-home) 
;    (for/fold ([offset 0]
;               [locals-home '()])
;              ([(local type) (in-dict locals-types)])
;      (values (- offset 8) (dict-set locals-home local (Deref 'rbp (- offset 8))))))
;  (if (zero? (remainder stack-space 16)) 
;    (values (abs stack-space) locals-home)
;    (values (abs (- stack-space 8)) locals-home)))



;; assign-homes : pseudo-x86 -> pseudo-x86
;(define (assign-homes p)
;  (match p
;    [(X86Program info e)
;     (match e
;      [`((start . ,(Block sinfo instrs)))
;        (define-values (stack-space locals-home) (assign-home-to-locals (dict-ref info 'locals-types)))
;        (X86Program (dict-set info 'stack-space stack-space) `((start . ,(Block sinfo (assign-homes-instr instrs locals-home)))))])]))

(define (remove-jumps-each-block e label-graph topo-order)
  (match topo-order
    [(cons label rest)
     (define neighbors (get-neighbors label-graph label))
     (define count (length neighbors))
     (cond
       [(eq? count 1)
        (define parent-label (car neighbors))
        (define parent-instructions (Block-instr* (dict-ref e parent-label)))
        (define last-instruction (car (reverse parent-instructions)))
        (match last-instruction
          [(Jmp jmp-label)
           (cond
             [(eq? jmp-label label)
              ;(displayln "removing label:")
              ;(displayln label)
              (define parent-instr-rev (reverse parent-instructions))
              ;(displayln parent-instr-rev)
              (define jmp-removed (reverse (cdr parent-instr-rev)))
              ;(displayln jmp-removed)
              (define updated-instrs (append jmp-removed (Block-instr* (dict-ref e label))))
              ;(displayln updated-instrs)
              (define parent-info (Block-info (dict-ref e parent-label)))
              (define updated-e (dict-set e parent-label (Block parent-info updated-instrs)))
              (remove-jumps-each-block updated-e label-graph rest)]
             [else
              (remove-jumps-each-block e label-graph rest)])]
          [else
           (remove-jumps-each-block e label-graph rest)])]
       [else
        (remove-jumps-each-block e label-graph rest)])]
    [else
     e]))

(define (remove-jumps p)
  (match p
    [(X86Program info e)
     (define label-graph (generate-label-graph e (make-multigraph '())))
     (define topo-order (tsort label-graph))
     ;(print-graph label-graph)
     ;(displayln topo-order)
     (define updated-e (remove-jumps-each-block e label-graph topo-order)) 
     (X86Program info updated-e)]))

(define (pi-instr instrs)
  (match instrs
    [(cons (Instr 'movq (list arg1 arg2)) ss)
     #:when (equal? arg1 arg2) (pi-instr ss)]
    [(cons (Instr 'movzbq (list arg1 (Deref arg2 n2))) ss)
     (append (list (Instr 'movzbq (list arg1 (Reg 'rax))) (Instr 'movq (list (Reg 'rax) (Deref arg2 n2)))) (pi-instr ss))]
    [(cons (Instr 'cmpq (list arg1 (Imm n2))) ss)
     (append (list (Instr 'movq (list (Imm n2) (Reg 'rax))) (Instr 'cmpq (list arg1 (Reg 'rax)))) (pi-instr ss))]
    [(cons (Instr x86-op (list (Deref arg1 n1) (Deref arg2 n2))) ss)
     (append (list (Instr 'movq (list (Deref arg1 n1) (Reg 'rax))) (Instr x86-op (list (Reg 'rax) (Deref arg2 n2)))) (pi-instr ss))]
    [(cons instr ss) (cons instr (pi-instr ss))]
    [else instrs]))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info blocks)

     (for ([block_key (dict-keys blocks)])
       (define block (dict-ref blocks block_key))
       (match block
         [(Block sinfo instrs)
          (set! blocks (dict-set blocks block_key (Block sinfo (pi-instr instrs))))
          ]))

     (X86Program info blocks)]))

(define (pac-main stack-space used-callee)
  (define part-1 (list
                  (Instr 'pushq (list (Reg 'rbp)))
                  (Instr 'movq (list (Reg 'rsp) (Reg 'rbp)))))
  (define part-2 (for/list ([reg used-callee])
                   (Instr 'pushq (list reg))))
  (define part-3 (list
                  (Instr 'subq (list (Imm stack-space) (Reg 'rsp)))
                  (Jmp 'start)))
  (append part-1 part-2 part-3))

(define (pac-conclusion stack-space reversed-used-callee)
  (define part-1 (list
                  (Instr 'addq (list (Imm stack-space) (Reg 'rsp)))))
  (define part-2 (for/list ([reg reversed-used-callee])
                   (Instr 'popq (list reg))))
  (define part-3 (list
                  (Instr 'popq (list (Reg 'rbp)))
                  (Retq)))
  (append part-1 part-2 part-3))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (match p
    [(X86Program info blocks)
     (define used-callee (set->list (dict-ref info 'used_callee)))
     (define stack-space (- (dict-ref info 'stack-space) (* 8 (length used-callee))))
     ;(define start (dict-ref blocks 'start))
     (define main (Block '() (pac-main stack-space used-callee)))
     (define conclusion (Block '() (pac-conclusion stack-space (reverse used-callee))))
     (set! blocks (dict-set blocks 'main main))
     (set! blocks (dict-set blocks 'conclusion conclusion))
     (X86Program info blocks)]))


;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `(
    ;("partial evaluator", pe-Lint, interp-Lvar)
    ("shrink" ,shrink ,interp-Lwhile ,type-check-Lwhile)
    ("uniquify" ,uniquify ,interp-Lwhile ,type-check-Lwhile)
    ("uncover get" ,uncover-get! ,interp-Lwhile ,type-check-Lwhile)
    ("remove complex opera*" ,remove-complex-opera* ,interp-Lwhile ,type-check-Lwhile)
    ("explicate control" ,explicate-control ,interp-Cwhile ,type-check-Cwhile)
    ("instruction selection" ,select-instructions ,interp-pseudo-x86-1)
    ("constant propagation" ,constant-propagation ,interp-pseudo-x86-1)
    ("liveness analysis" ,uncover_live ,interp-pseudo-x86-1)
    ("build interference graph" ,build_interference ,interp-pseudo-x86-1)
    ("register allocation" ,allocate_registers ,interp-x86-1)
    ("remove jumps" ,remove-jumps ,interp-x86-1)
    ("patch instructions" ,patch-instructions ,interp-x86-1)
    ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-1)
    ))

