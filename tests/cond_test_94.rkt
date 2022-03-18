(let ([x (if (and #t (or #f #t)) (- 9 6) (+ 4 2))])
  (let ([x (+ x x)])
    (+ x 10)))
