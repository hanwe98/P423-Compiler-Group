(let ([x 42])
  (let ([i 2])
    (begin
      (while (< i 0)
        (begin
          (set! x (+ x 1))
          (set! i (+ x 1))))
      x)))
