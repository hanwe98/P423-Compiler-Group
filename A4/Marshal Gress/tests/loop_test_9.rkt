(let ([i 5])
  (begin
    (while (> i 0)
      (set! i (- i 1)))
    (+ i 42)))
