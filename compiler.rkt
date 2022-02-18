#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
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
    [else 
      (define new-x-str (~a x (+ cnt 1)))
      (match (member new-x-str (for/list ([(k v) (in-dict env)]) (~a k v)))
        [#f (dict-set env x (+ cnt 1))]
        [else (update-env (dict-set env x (+ cnt 1)) x)])]))

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x)
       (Var (string->symbol (~a x (dict-ref env x))))]
      [(Int n) (Int n)]
      [(Let x e body)
       (define new-e ((uniquify-exp env) e))
       (define new-env (update-env env x))
       (define new-x (string->symbol (~a x (dict-ref new-env x))))
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
    (define temp-var (string->symbol (~a 'tmp (dict-ref env 'tmp))))
    (values temp-var (dict-set '() temp-var e))))

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
         (define-values (temp-var exp-dict) ((rco-atom new-env) e1))
         (Let temp-var ((rco-exp new-env) (dict-ref exp-dict temp-var)) (Prim '- (list (Var temp-var))))])]
      [(Prim '+ (list e1 e2))
       (cond
        [(not (atm? e1))
         (define new-env (update-env env 'tmp))
         (define-values (temp-var exp-dict) ((rco-atom new-env) e1))
         (Let temp-var ((rco-exp new-env) (dict-ref exp-dict temp-var)) ((rco-exp new-env) (Prim '+ (list (Var temp-var) e2))))]
        [(not (atm? e2))
         (define new-env (update-env env 'tmp))
         (define-values (temp-var exp-dict) ((rco-atom new-env) e2))
         (Let temp-var ((rco-exp new-env) (dict-ref exp-dict temp-var)) ((rco-exp new-env) (Prim '+ (list e1 (Var temp-var)))))]
        [else (Prim '+ (list e1 e2))])])))

;; remove-complex-opera* : R1 -> R1
(define (remove-complex-opera* p)
  (match p
    [(Program info e) (Program info ((rco-exp '()) e))]))

;; explicate-control : R1 -> C0
(define (explicate-control p)
  (error "TODO: code goes here (explicate-control)"))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (error "TODO: code goes here (select-instructions)"))

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
     ;; ("explicate control" ,explicate-control ,interp-Cvar)
     ;; ("instruction selection" ,select-instructions ,interp-x86-0)
     ;; ("assign homes" ,assign-homes ,interp-x86-0)
     ;; ("patch instructions" ,patch-instructions ,interp-x86-0)
     ;; ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

