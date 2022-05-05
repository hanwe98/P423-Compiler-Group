Jeremy said to use FunRefArity because it was introduced in Llambda, but right now I'm thinking FunRef should be fine.  I added FunRef AST node to interp-Lfun.rkt (interp-exp)

Limit functions has issue where I believe the type within a `(ValueOf v t)` that refers to a function needs to change if the arguments are excessive.  This changes the value produced by `'procedure-arity`, which makes the `(Prim eq? ...` comparing that and the flatType produced from `reveal-casts` return false, causing the program to exit.  See `Xdt17.rkt` and `Xdt20.rkt`
