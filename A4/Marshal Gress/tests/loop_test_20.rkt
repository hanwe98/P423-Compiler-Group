(let ([x 5])
  (begin
    (while
     (< x 10)
     (set! x (+ x 1)))
    (if (< x 10) 0 42)))