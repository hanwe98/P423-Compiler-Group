(let ([x 1])
  (begin
    (if #t
        (set! x 42)
        (set! x 0))
    x))
