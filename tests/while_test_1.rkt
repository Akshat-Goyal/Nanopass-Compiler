(let ([x2 10])
    (let ([y3 0])
        (+ (+ (begin
                (set! y3 20)
                x2)
            (begin
                (set! x2 40)
                y3))
         x2)))
