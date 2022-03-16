(let ([x (if (let ([x #t]) (if x x (not x))) #t #f)]) (if x 10 (- 10)))
