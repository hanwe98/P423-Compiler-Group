(let ([M00 1])
  (let ([M01 0])
    (let ([M10 0])
      (let ([M11 0])
        (let ([i 1])
          (let ([j 1])
            (begin
              (while (< i 2)
                (begin
                  (while (< j 2)
                    (begin
                      (if (eq? i j)
                          (set! M11 1)
                          (set! M11 M11))
                      (set! j (+ j 1))))
                  (set! i (+ i 1))))
              (+ (+ (+ (+ M00 M01) M10) M11) 40))))))))
