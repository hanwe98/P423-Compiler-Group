(let ([v (vector #t #f)])
  (if (and (vector-ref v 0)
           (vector-ref v 1))
      0
      42))
