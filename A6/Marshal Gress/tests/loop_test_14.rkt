(begin
  (let ([x 1])
    (begin
      (set! x 2)
      (if (eq? x 2)
          42
          0))))
