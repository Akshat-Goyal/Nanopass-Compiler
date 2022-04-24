(define (useless [a : Integer] [b : Integer] [c : Integer] [d : Integer] [e : Integer] [f : Integer] [g : Integer] [h : (Integer -> Integer)]) : Integer
	(begin
		(set! a (+ a 1))
		(set! b (+ b 2))
		(let ([a 10])
			(begin
				(- 20 a)
				(set! a 20)
			)
		)
        (set! f (inc-2 7))
		(if (< f g) 10 20)
		(set! f (+ f 5))
		(set! g (- g 5))
		(h 7)
		(+ a (+ f g))
	)
)

(define (inc-2 [a : Integer]) : Integer
	(+ a 2)
)

(+ 10 (useless 1 2 3 4 5 6 7 inc-2))
