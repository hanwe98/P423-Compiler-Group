(let ([x 0])
  (let ([y (set! x 1)])
    (begin
      (set! y (set! x 42))
      x)))
