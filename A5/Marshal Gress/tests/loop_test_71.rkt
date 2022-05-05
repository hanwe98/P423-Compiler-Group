(let ([x 0])
      (begin
        (while (< x 1)
          (begin
            (set! x (+ x 1))))
        x))
