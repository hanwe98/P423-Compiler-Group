(let ([x 1])
  (let ([i 0])
    (begin
      (while (if (eq? x 1)
                 (eq? i 0)
                 (eq? i 1))
        (set! x 42))
      x)))
