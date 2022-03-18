(let ([x (if (let ([x #t]) (if x x 10)) #t #f)]) (if x 10 (- 10)))
