#lang racket
(require racket/set racket/stream)
(require racket/fixnum)
(require "interp-Lint.rkt")
(require "interp-Lvar.rkt")
(require "interp-Cvar.rkt")
(require "interp.rkt")
(require "type-check-Lvar.rkt")
(require "type-check-Cvar.rkt")
(require "utilities.rkt")
(require graph)
(require "./priority_queue.rkt")
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

;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;
;; HW1 Passes
;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;;

(define (uniquify-exp env)
  (lambda (e)
    (match e
      [(Var x) (Var (dict-ref env x))]
      [(Int n) (Int n)]
      [(Let x e body)
       (define new-e ((uniquify-exp env) e))
       (define new-x (gensym x))
       (define new-env (dict-set env x new-x))
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
    (gensym 'tmp)))

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
         (define tmp-var ((rco-atom env) e1))
         (Let tmp-var ((rco-exp env) e1) (Prim '- (list (Var tmp-var))))])]
      [(Prim op (list e1 e2))
       (cond
        [(not (or (Var? e1) (Int? e1)))
         (define tmp-var ((rco-atom env) e1))
         (Let tmp-var ((rco-exp env) e1) ((rco-exp env) (Prim op (list (Var tmp-var) e2))))]
        [(not (or (Var? e2) (Int? e2)))
         (define tmp-var ((rco-atom env) e2))
         (Let tmp-var ((rco-exp env) e2) ((rco-exp env) (Prim op (list e1 (Var tmp-var)))))]
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
    [(Assign (Var x) exp) (si-exp (Var x) exp cont)]))

(define (si-tail e)
  (match e
    [(Return exp) (si-exp (Reg 'rax) exp (list (Jmp 'conclusion)))]
    [(Seq stmt tail) (si-stmt stmt (si-tail tail))]))

;; select-instructions : C0 -> pseudo-x86
(define (select-instructions p)
  (match p
    [(CProgram info e) 
     (X86Program info `((start . ,(Block '() (si-tail (dict-ref e 'start))))))]))

(define (compute-locations instr)
  (match instr
    [(Instr x86-op (list arg1 arg2))
     ; arg2 cannot be immediate since we are writing into arg2
     (match arg1
       [(Imm n) (set arg2)]
       [else (set arg1 arg2)])]
    [(Instr 'negq (list arg1)) (set arg1)] ; arg1 cannot be immediate
    [else (set)])) ;; for callq

(define (compute-write-locations instr)
  ; TODO: handle retq instruction
  (match instr
    [(Instr x86-op (list arg1 arg2)) (set arg2)] ; arg2 cannot be immediate since we are writing into arg2
    [(Instr 'negq (list arg1)) (set arg1)] ; arg1 cannot be immediate
    [(Callq func-name n) (list->set caller-saved-registers)]
    [else (set)]))

(define (compute-read-locations instr)
  ; TODO: handle retq instruction
  (match instr
    [(Instr 'movq (list arg1 arg2))
     (match arg1
       [(Imm n) (set)]
       [else (set arg1)])]
    [(Instr x86-op (list arg1 arg2))
     ; arg2 cannot be immediate since we are writing into arg2
     (match arg1
       [(Imm n) (set arg2)]
       [else (set arg1 arg2)])]
    [(Instr 'negq (list arg1)) (set arg1)] ; arg1 cannot be immediate
    [(Callq func-name n)
     (cond
       [(<= n 6) (list->set (take argument-registers n))]
       [else (list->set (take argument-registers 6))])]
    [else (set)]))

(define (find-live-sets instrs live-after)
  (match instrs
    [(cons instr rest)
     (define locations (compute-locations instr))
     (define read-locations (compute-read-locations instr))
     (define write-locations (compute-write-locations instr))
     (define live-after-cur (cond
       [(empty? live-after) (set)]
       [else (car live-after)]))
     (define live-before (set-union (set-subtract live-after-cur write-locations) read-locations))
     (find-live-sets rest (cons live-before live-after))]
    [else live-after]))
    
;; uncover_live: pseudo-x86 -> pseudo-x86
(define (uncover_live p)
  (match p
    [(X86Program info e)
     (match e
      [`((start . ,(Block sinfo instrs)))
        (X86Program info `((start . ,(Block `((live-sets . ,(cdr (find-live-sets (reverse instrs) (list (set)))))) instrs))))])]))

(define (print-graph graph)
  (for ([u (in-vertices graph)])
    (for ([v (in-neighbors graph u)])
      (display (format "~a -> ~a;\n" u v)))))

(define (build-graph instrs live-sets locals)
  (define graph (undirected-graph '()))
  (for ([reg all-registers]) ;TODO: do we need to add vertices of all registers or only caller saved ones or none at all here?
    (add-vertex! graph reg))
  (for ([var locals]) ;need to do this otherwise error on var_test 6 or something
    (add-vertex! graph (Var var)))
  (for ([live-set live-sets]
        [instr instrs])
    (match instr
      [(Instr 'movq (list arg1 arg2))
       (for ([live-location (set->list live-set)])
         (cond
           [(not (or (equal? arg1 live-location) (equal? arg2 live-location)))
            (add-edge! graph arg2 live-location)]))]
      [else
       (define write-locations (compute-write-locations instr))
       (for* ([live-location live-set]
              [write-location write-locations])
         (cond
           [(not (equal? live-location write-location))
            (add-edge! graph live-location write-location)]))]))
  graph)
       
 
;; build_interference: pseudo-x86 -> pseudo-x86
(define (build_interference p)
  (match p
    [(X86Program info e)
     (match e
      [`((start . ,(Block sinfo instrs)))
       (define live-sets (dict-ref sinfo 'live-sets))
       (define locals (dict-keys (dict-ref info 'locals-types)))
       (define interference-graph (build-graph instrs live-sets locals))
       (print-graph interference-graph)
       (X86Program (dict-set info 'conflicts interference-graph) e)])]))

(define graph-coloring-comparator                         
  (lambda (node1 node2)
    (cond
      [(= (color_priority_node-saturation node1) (color_priority_node-saturation node2))
       (< (color_priority_node-move_bias node1) (color_priority_node-move_bias node2))]
      [else
       (< (color_priority_node-saturation node1) (color_priority_node-saturation node2))])))

(define (build-move-graph instrs locals)
  (define graph (undirected-graph '()))

  (for ([reg all-registers])
    (add-vertex! graph reg))
 
  (for ([var locals])
    (add-vertex! graph (Var var)))
  
  (for ([instr instrs])
    (match instr
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
          (displayln "cur-node neighbors potential-colors interfering-colors cur-color")
          (displayln cur-node)
          (displayln neighbors)
          (displayln potential-colors)
          (displayln interfering-colors)
          (displayln cur-color)
          (define updated-saturation (update-saturation saturation cur-color neighbors))
          (display "updated-saturation: ")
          (displayln updated-saturation)
          (define updated-move-bias (update-move-bias move-bias (for/list ([u (in-neighbors move-graph cur-node)]) u)))
          (displayln "old and updated-move-bias: ")
          (displayln move-bias)
          (displayln updated-move-bias)
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

  ; set color of registers to their actual color: DONE
  ; set visited of registers to true: DONE
  (define-values (prev-saturation visited-prev move-bias-prev) (for/fold ([saturation '()]    
                                                                          [visited '()]
                                                                          [move-bias '()])
                                                                         ([var locals])
                                                                 (values (dict-set saturation (Var var) (set)) (dict-set visited (Var var) #f) (dict-set move-bias (Var var) 0))))

  ;TODO: update move-bias for register to variable or vive versa move operations: DONE
                                              
  (define color (for/fold ([color '()]) ([reg all-registers]) (dict-set color reg (dict-ref register-to-color reg))))
  (define visited (for/fold ([visited visited-prev]) ([reg all-registers]) (dict-set visited reg #t)))
  
  ;(display "color: ")
  ;(displayln color)

  ;(display "visited: ")
  ;(displayln visited)
  
;  (displayln (dict-keys register-to-color))
;  (displayln (dict-values register-to-color))
;  (displayln locals)

  (define u-list (for/list ([u (in-vertices interference-graph)]) u))
  (define saturation (get-initial-saturation prev-saturation u-list interference-graph))
  (define u-list-move-graph (for/list ([u (in-vertices move-graph)]) u))
  (define move-bias (get-initial-move-bias move-bias-prev u-list-move-graph move-graph))

  (displayln "old and updated move-bias")
  (displayln move-bias-prev)
  (displayln move-bias)

  ;(displayln prev-saturation)
  ;(displayln "new-saturation")
  ;(displayln saturation)
    
;  (for ([u (in-vertices interference-graph)])
;    (match u
;      [(Reg r)
;       (define color (dict-ref register-to-color u))
;       (for ([v (in-neighbors interference-graph u)])
;         (match v
;           [(Var x)
;            (define old-saturation (dict-ref saturation v))
;            (define new-saturation (set-add old-saturation color))
;            (dict-set saturation v new-saturation)]))])) ; do this with recursion as 'saturation' will not be modified here: DONE

  (define pq (make-pqueue graph-coloring-comparator))     
  (for ([var locals])
    (define cur-saturation (set-count (dict-ref saturation (Var var))))
    (define cur-move-bias 0)
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
    [(X86Program info e)
     (match e
      [`((start . ,(Block sinfo instrs)))
       (define locals (dict-keys (dict-ref info 'locals-types)))
       (define interference-graph (dict-ref info 'conflicts))
       (define move-graph (build-move-graph instrs locals))
       (define variable-colors (color-graph interference-graph locals move-graph))
       (display "variable-colors: ")
       (displayln variable-colors)
       (define used-callee (get-used-callee-registers locals (set) variable-colors))
       (define new-info (dict-set info 'used_callee used-callee))
       (define locals-homes (assign-home-to-locals locals variable-colors (set-count used-callee) '()))
       (define stack-variable-colors (get-stack-colors locals variable-colors (set)))
       (define stack-size (get-stack-space (set-count stack-variable-colors) (set-count used-callee)))
       
       (X86Program (dict-set new-info 'stack-space stack-size) `((start . ,(Block sinfo (assign-homes-instr instrs locals-homes)))))])]))

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
(define (assign-homes p)
  (match p
    [(X86Program info e)
     (match e
      [`((start . ,(Block sinfo instrs)))
        (define-values (stack-space locals-home) (assign-home-to-locals (dict-ref info 'locals-types)))
        (X86Program (dict-set info 'stack-space stack-space) `((start . ,(Block sinfo (assign-homes-instr instrs locals-home)))))])]))

(define (pi-instr instrs)
  (match instrs
    [(cons (Instr 'movq (list arg1 arg2)) ss)
     #:when (equal? arg1 arg2) (pi-instr ss)]
    [(cons (Instr x86-op (list (Deref arg1 n1) (Deref arg2 n2))) ss)
     (append (list (Instr 'movq (list (Deref arg1 n1) (Reg 'rax))) (Instr x86-op (list (Reg 'rax) (Deref arg2 n2)))) (pi-instr ss))]
    [(cons instr ss) (cons instr (pi-instr ss))]
    [else instrs]))

;; patch-instructions : psuedo-x86 -> x86
(define (patch-instructions p)
  (match p
    [(X86Program info e)
     (match e
      [`((start . ,(Block sinfo instrs)))
        (X86Program info `((start . ,(Block sinfo (pi-instr instrs)))))])]))

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
     (define start (dict-ref blocks 'start))
     (define main (Block '() (pac-main stack-space used-callee)))
     (define conclusion (Block '() (pac-conclusion stack-space (reverse used-callee))))
     (X86Program info `((start . ,start) (main . ,main) (conclusion . ,conclusion)))]))


;; Define the compiler passes to be used by interp-tests and the grader
;; Note that your compiler file (the file that defines the passes)
;; must be named "compiler.rkt"
(define compiler-passes
  `( ;("partial evaluator", pe-Lint, interp-Lvar)
     ("uniquify" ,uniquify ,interp-Lvar ,type-check-Lvar)
     ;; Uncomment the following passes as you finish them.
     ("remove complex opera*" ,remove-complex-opera* ,interp-Lvar ,type-check-Lvar)
     ("explicate control" ,explicate-control ,interp-Cvar ,type-check-Cvar)
     ("instruction selection" ,select-instructions ,interp-x86-0)
     ("liveness analysis" ,uncover_live ,interp-x86-0)
     ("build interference graph" ,build_interference ,interp-x86-0)
     ("register allocation" ,allocate_registers ,interp-x86-0)
     ("patch instructions" ,patch-instructions ,interp-x86-0)
     ("prelude-and-conclusion" ,prelude-and-conclusion ,interp-x86-0)
     ))

