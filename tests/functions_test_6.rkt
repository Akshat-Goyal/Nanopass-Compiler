;(define (inc [a : Integer] [b : Integer] [c : Integer] [d: Integer] [e : Integer] [f : Integer] [g : Integer] [h : Integer]) : Integer
  ;(+ a (+ b (+ c (+ e (+ f (- g (+ h 22))))))))
;  1)
;(inc 1 2 3 4 5 6 7 8)

(define (mult [x : Integer] [y : Integer] [a : Integer] [b : Integer] [c : Integer] [d : Integer] [e : Integer] [f : Integer]) : Integer
  (if (eq? 0 x)
      0
      (+ y (mult (+ (- 1) x) y))))
(mult 6 7 1 2 3 4 5 6)