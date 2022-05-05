(let ([units 15])
  (let ([i 5])
    (begin
      (while (> i 0)
        (begin
          (set! units (- units i))
          (set! i (- i 1))))
      (+ units 42))))
