(let ([x #f])
  (begin
    (set! x #t)
    (if x
        42
        0)))
