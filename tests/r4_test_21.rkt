(define (tailsum [n : Integer] [r : Integer]) : Integer
  (if (eq? n 0) r
      (tailsum (- n 1) (+ n r))))

(+ (tailsum 5 0) 27)
