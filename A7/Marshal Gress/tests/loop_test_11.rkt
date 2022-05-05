(let ([x (read)])
  (begin
    (while (> x 0)
      (set! x (- x 2)))
    (+ x 42)))
