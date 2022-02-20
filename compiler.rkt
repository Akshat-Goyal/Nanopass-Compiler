#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "utilities.rkt")
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

(define (pe-Lint p)
  (match p
    [(Program info e) (Program info (pe-exp e))]))

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (update-env env x)
  (define cnt (dict-ref env x #f))
  (match cnt
    [#f (update-env (dict-set env x 0) x)]
    [else (dict-set env x (+ cnt 1))]))

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (string->symbol (~a x "." (dict-ref env x))))]
      [(Int n) (Int n)]
      [(Let x e body)
       (define new-e ((uniquify-exp env) e))
       (define new-env (update-env env x))
       (define new-x (string->symbol (~a x "." (dict-ref new-env x))))
       (define new-body ((uniquify-exp new-env) body))
       (Let new-x new-e new-body)]
      [(Prim op es)
       (Prim op (for/list ([e es]) ((uniquify-exp env) e)))])))

;; uniquify : R1 -> R1
(define (uniquify p)
  (match p
    [(Program info e) (Program info ((uniquify-exp '()) e))]))

(define (rco-atom env)
  (lambda (e)
    (define tmp-var (string->symbol (~a 'tmp "$" (dict-ref env 'tmp))))
    (values tmp-var (dict-set '() tmp-var e))))

(define (rco-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var x)]
      [(Int n) (Int n)]
      [(Prim 'read '()) (Prim 'read '())]
      [(Let x e body) 
       (Let x ((rco-exp env) e) ((rco-exp env) body))]
      [(Prim '- (list e1))
       (cond
        [(or (Var? e1) (Int? e1)) (Prim '- (list e1))]
        [else
         (define new-env (update-env env 'tmp))
         (define-values (tmp-var exp-dict) ((rco-atom new-env) e1))
         (Let tmp-var ((rco-exp new-env) (dict-ref exp-dict tmp-var)) (Prim '- (list (Var tmp-var))))])]
      [(Prim op (list e1 e2))
       (cond
        [(not (or (Var? e1) (Int? e1)))
         (define new-env (update-env env 'tmp))
         (define-values (tmp-var exp-dict) ((rco-atom new-env) e1))
         (Let tmp-var ((rco-exp new-env) (dict-ref exp-dict tmp-var)) ((rco-exp new-env) (Prim op (list (Var tmp-var) e2))))]
        [(not (or (Var? e2) (Int? e2)))
         (define new-env (update-env env 'tmp))
         (define-values (tmp-var exp-dict) ((rco-atom new-env) e2))
         (Let tmp-var ((rco-exp new-env) (dict-ref exp-dict tmp-var)) ((rco-exp new-env) (Prim op (list e1 (Var tmp-var)))))]
        [else (Prim op (list e1 e2))])])))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info ((rco-exp '()) e))]))

(define (explicate-tail e)
  (match e
    [(Var x) (Return (Var x))]
    [(Int n) (Return (Int n))]
    [(Let x rhs body) (explicate-assign rhs x (explicate-tail body))]
    [(Prim op es) (Return (Prim op es))]
    [else (error "explicate-tail unhandled case" e)]))

(define (explicate-assign e x cont)
  (match e
    [(Var y) (Seq (Assign (Var x) (Var y)) cont)]
    [(Int n) (Seq (Assign (Var x) (Int n)) cont)]
    [(Let y rhs body) (explicate-assign rhs y (explicate-assign body x cont))]
    [(Prim op es) (Seq (Assign (Var x) (Prim op es)) cont)]
    [else (error "explicate-assign unhandled case" e)]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (match p 
    [(Program info e) (CProgram info `((start . ,(explicate-tail e))))]))

(define (si-atm e)
  (match e
    [(Var x) (Var x)]
    [(Int n) (Imm n)]))

(define (si-exp v e cont [op-x86-dict '((+ . addq) (- . subq))])
  (match e
    [(Var y) (cons (Instr 'movq (list (si-atm e) v)) cont)]
    [(Int n) (cons (Instr 'movq (list (si-atm e) v)) cont)]
    [(Prim 'read '()) 
      (append (list (Callq 'read_int '()) (Instr 'movq (list (Reg 'rax) v))) cons)]
    [(Prim '- (list e1))
      #:when (equal? e1 v) (append (Instr 'negq (list v)) cont)]
    [(Prim '- (list e1)) 
      (append (list (Instr 'movq (list (si-atm e1) v)) (Instr 'negq (list v))) cont)]
    [(Prim op (list e1 e2))
      #:when (equal? e1 v) (cons (Instr (dict-ref op-x86-dict op) (list (si-atm e2) v)) cont)]
    [(Prim op (list e1 e2))
      #:when (equal? e2 v) (cons (Instr (dict-ref op-x86-dict op) (list (si-atm e1) v)) cont)]
    [(Prim op (list e1 e2))
      (append (list (Instr 'movq (list (si-atm e1) v)) (Instr (dict-ref op-x86-dict op) (list (si-atm e2) v))) cont)]))

(define (si-stmt e cont)
  (match e
    [(Assign (Var x) exp) (si-exp (Var x) exp cont)]))

(define (si-tail e)
  (match e
    [(Return exp) (si-exp (Reg 'rax) exp (list (Jmp 'conclusion)))]
    [(Seq stmt tail) (si-stmt stmt (si-tail tail))]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info label-tail-dict) 
     (X86Program info `((start . ,(Block info (si-tail (dict-ref label-tail-dict 'start))))))]))

;; assign-homes : pseudo-x86 -> pseudo-x86
(define (assign-homes p)
  (error "TODO: code goes here (assign-homes)"))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (error "TODO: code goes here (patch-instructions)"))

;; prelude-and-conclusion : x86 -> x86
(define (prelude-and-conclusion p)
  (error "TODO: code goes here (prelude-and-conclusion)"))

;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ("uniquify" ,uniquify ,interp-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar)
     ("instruction selection" ,select-instructions ,interp-x86-0)
     ;; ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

