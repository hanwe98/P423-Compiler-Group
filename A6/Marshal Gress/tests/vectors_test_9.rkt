(let ([z 3])
  (if (eq? z 2)
      (vector-ref (vector #t 0) 1)
      (vector-ref (vector #f 42) 1)))
