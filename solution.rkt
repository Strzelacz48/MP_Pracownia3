#lang plait
(module+ test
  (print-only-errors #t))

(define-type Exp
  (defE [args : (Listof Exp)] [e : Exp])
  (funE [name : Exp] [args : (Listof Exp)] [body : Exp])
  (numE [n : Number])
  (varE [x : Symbol])
  (ifzE [e0 : Exp] [e1 : Exp] [e2 : Exp])
  (letE [x : Exp] [e1 : Exp] [e2 : Exp])
  (appE [f : Exp] [args : (Listof Exp)])
  (opE  [op : (Number Number -> Number)] [l : Exp] [r : Exp]))

;(ifzE [bool : Number] [e1 : Exp] [e2 : Exp])
;==============================================================
;parser 

(define (parse [s : S-Exp]) : Exp
  (if (s-exp-match? `{define {ANY ...} for ANY} s)
      (defE (parse-list (s-exp->list (second (s-exp->list s))))
            (parse-exp (fourth (s-exp->list s))))
      (parse-exp s)))

(define (parse-exp [s : S-Exp]) : Exp
  (cond
    [(s-exp-match? `{fun SYMBOL {ANY ...} = ANY} s)
     (funE (parse-exp (second (s-exp->list s)))
           (parse-list (s-exp->list (third (s-exp->list s))))
           (parse-exp (fifth (s-exp->list s))))]
    [(s-exp-match? `{let SYMBOL be ANY in ANY} s)
     (letE (parse-exp (second (s-exp->list s)))
           (parse-exp (fourth (s-exp->list s)))
           (parse-exp (sixth (s-exp->list s))))]
    [(s-exp-match? `{ifz ANY then ANY else ANY} s)
     (ifzE (parse-exp (second (s-exp->list s)))
           (parse-exp (fourth (s-exp->list s)))
           (parse-exp (sixth (s-exp->list s))))]
    [(s-exp-match? `{SYMBOL {ANY ...}} s)
     (appE (parse-exp (first (s-exp->list s)))
           (parse-list (s-exp->list (second (s-exp->list s)))))]
    [(s-exp-match? `NUMBER s)
     (numE (s-exp->number s))]
    [(s-exp-match? `SYMBOL s)
     (varE (s-exp->symbol s))]
    [(s-exp-match? `{ANY SYMBOL ANY} s)
     (opE (parse-op (s-exp->symbol (second (s-exp->list s))))
          (parse-exp (first (s-exp->list s)))
          (parse-exp (third (s-exp->list s))))]
    [else (error 'parse "input not supported")]))

(define (<= [x : Number] [y : Number]) : Number
  (if (or (< x y) (= x y))
      0
      69));najs

(define (parse-op [op : Symbol]) : (Number Number -> Number)
  (cond
    [(symbol=? op '+)  +]
    [(symbol=? op '-)  -]
    [(symbol=? op '*)  *]
    [(symbol=? op '<=) <=]
    [else (error 'parse (string-append "unknown operator: " (symbol->string op)))]))

(define (parse-list [xs : (Listof S-Exp)]) : (Listof Exp)
  (type-case (Listof S-Exp) xs
    [empty empty]
    [(cons x xs)
     (cons (parse-exp x) (parse-list xs))]))

(define (fifth [xs : (Listof 'a)]) : 'a
  (list-ref xs 4))

(define (sixth [xs : (Listof 'a)]) : 'a
  (list-ref xs 5))
;=============================================================
;eval

;; Values:

(define-type-alias Value Number)

;; Environments:

(define-type Storable
  (valS [v : 'a]))

(define-type Binding
  (bind [name : Symbol]
        [ref : (Boxof Storable)]))

(define-type-alias Env (Listof Binding))

(define mt-env empty)

(define (extend-env [env : Env] [x : Symbol] [v : 'a]) : Env
  (cons (bind x (box (valS v))) env))

(define (extend-env-with-vars [env : Env] [vars : (Listof Exp)] [args : (Listof Value)]) : Env
  (type-case (Listof Exp) vars
    [(cons fun funs)
     (type-case Exp fun
       [(varE x)
        (if (find env x)
            (error 'eval (string-append "the function argument "
                                             (string-append (symbol->string x) " already taken")))
            (extend-env-with-vars (extend-env env x (first args)) funs (rest args)))]
       [else (error 'eval "the function variables must be of type Symbol")])]
    [empty env]))

(define (extend-env-with-funs [env : Env] [funs : (Listof Exp)]) : Env
  (type-case (Listof Exp) funs
    [(cons fun funs)
     (type-case Exp fun
       [(funE name args body)
        (type-case Exp name
          [(varE x)
           (if (find env x)
               (error 'define (string-append "identifier "
                                             (string-append (symbol->string x) " already defined")))
               (extend-env-with-funs (extend-env env x fun) funs))]
          [else (error 'define "the function name must be of type Symbol")])]
       [else (error 'define "only functions can be in the define")])]
    [empty env]))

(define (find-var [env : Env] [x : Symbol]) : (Boxof Storable)
  (type-case (Listof Binding) env
    [empty (error 'lookup (string-append "unbound expression: " (symbol->string x)))]
    [(cons b rst-env) (cond
                        [(eq? x (bind-name b))
                         (bind-ref b)]
                        [else
                         (find-var rst-env x)])]))

(define (find [env : Env] [f : Symbol]) : Boolean ;do znajdowania w środowisku
  (type-case (Listof Binding) env
    [(cons x xs)
     (if (symbol=? (bind-name x) f)
         #t
         (find xs f))]
    [empty #f]))

(define (lookup-env [x : Symbol] [env : Env]) : 'a
  (type-case Storable (unbox (find-var env x))
    [(valS v) v]))

;; Evaluation function (eval/apply/eval-list):

(define (eval [e : Exp] [env-var : Env] [env-fun : Env]) : Value
  (type-case Exp e
    [(defE args e)
     (eval e env-var (extend-env-with-funs env-fun args))]
    [(numE n) n]
    [(varE x)
     (lookup-env x env-var)]
    [(ifzE e0 e1 e2)
     (if (= (eval e0 env-var env-fun) 0)
         (eval e1 env-var env-fun)
         (eval e2 env-var env-fun))]
    [(letE x e1 e2)
     (type-case Exp x
       [(varE x)
        (let ([v1 (eval e1 env-var env-fun)])
          (eval e2 (extend-env env-var x v1) env-fun))]
       [else (error 'let "variable must be of type Symbol")])]
    [(opE op l r)
     (op (eval l env-var env-fun) (eval r env-var env-fun))]
    [(appE f args)
     (type-case Exp f
       [(varE x)
        (apply x args env-var env-fun)]
       [else (error 'eval "the function name must be of type Symbol")])]
    [(funE name args body)
     (type-case Exp name
       [(varE x)
        (error 'eval (string-append "the function (in this case: "
                                    (string-append (symbol->string x)
                                                   ") cannot be evaluated to Value")))]
       [else (error 'eval "the function name must be of type Symbol")])]))

(define (apply [f : Symbol] [args : (Listof Exp)] [env-var : Env] [env-fun : Env]) : Value
  (type-case Exp (lookup-env f env-fun)
    [(funE name vars body)
     (if (= (length vars) (length args))
         (eval body (extend-env-with-vars mt-env vars (eval-list args env-var env-fun)) env-fun)
         (error 'apply "wrong number of argument"))]
    [else (error 'apply "not a function")]))

(define (eval-list [vars : (Listof Exp)] [env-var : Env] [env-fun : Env]) : (Listof Value)
  (type-case (Listof Exp) vars
    [(cons var vars)
     (cons (eval var env-var env-fun) (eval-list vars env-var env-fun))]
    [empty empty]))

(define (run [program : S-Exp]) : Value
  (eval (parse program) mt-env mt-env))
;==============================================================
;printer
;(define (value->string [v : Value]) : String
;  (type-case Value v
;    [(numV n) (to-string n)]
;    [(funV x e env) "#<procedure>"])

;(define (print-value [v : Value]) : Void
;  (display (value->string v)))

(define (print-value [v : Value]) : Void
  (display v))

(define (main [e : S-Exp]) : Void
  (print-value (eval (parse e) mt-env mt-env)))

;==============================================================
;testy


;testy parsera

(module+ test
  (test (parse `7)
        (numE 7))
  (test (parse `x)
        (varE 'x))
  (test (parse `{1 + 2})
        (opE + (numE 1) (numE 2)))
  (test (parse `{-34 - -5})
        (opE - (numE -34) (numE -5)))
  (test (parse `{3 * 3})
        (opE * (numE 3) (numE 3)))
  (test (parse `{-67 <= -99})
        (opE <= (numE -67) (numE -99)))
  (test/exn (parse `{{* 4 2}})
            "input not supported")
  (test/exn (parse `{+ 1})
            "input not supported")
  (test/exn (parse `{1 % 2})
            "unknown operator: %")
  (test (parse `{ifz {8 - 5} then 3 else 14})
        (ifzE (opE - (numE 8) (numE 5)) (numE 3) (numE 14)))
  (test (parse `{let x be {2 - 3} in {42 * {x * x}}})
        (letE (varE 'x) (opE - (numE 2) (numE 3))
              (opE * (numE 42) (opE * (varE 'x) (varE 'x)))))
  (test (parse `{f {x1 x2 x3}})
        (appE (varE 'f) (list (varE 'x1) (varE 'x2) (varE 'x3))))
  (test (parse `{f {}})
        (appE (varE 'f) (list)))
  (test (parse `{fun f {x1 x2 x3} = {x1 + (x2 - x3)}})
        (funE (varE 'f)
              (list (varE 'x1) (varE 'x2) (varE 'x3))
              (opE + (varE 'x1) (opE - (varE 'x2) (varE 'x3)))))
  (test (parse `{define {{fun f {x1 x2} = {x1 * x2}} {fun g {x1} = {x1 * x1}}}
                  for {{f {x1 x2}} + {g {x1}}}})
        (defE (list (funE (varE 'f)
                          (list (varE 'x1) (varE 'x2))
                          (opE * (varE 'x1) (varE 'x2)))
                    (funE (varE 'g)
                          (list (varE 'x1))
                          (opE * (varE 'x1) (varE 'x1))))
          (opE + (appE (varE 'f) (list (varE 'x1) (varE' x2)))
               (appE (varE 'g) (list (varE 'x1)))))))
;=========================================================================
;testy evaluatora

;; Testy z pliku pdf:

(module+ test
  (test (run `{define
                {[fun fact (n) = {ifz n then 1 else {n * {fact ({n - 1})}}}]}
                for {fact (5)}})
        120)
  (test (run `{define
                {[fun even (n) = {ifz n then 0 else {odd ({n - 1})}}]
                 [fun odd (n) = {ifz n then 42 else {even ({n - 1})}}]}
                for {even (1024)}})
        0)
  (test (run `{define
                {[fun gcd (m n) = {ifz n then m else
                                       {ifz {m <= n}
                                            then {gcd (m {n - m})}
                                            else {gcd ({m - n} n)}}}]}
                for {gcd (81 63)}})
        9))

;; Testy błędów:

(module+ test
          (test/exn (run `{define
                    {[fun sum (x y x) = {{x + y} + x}]}
                    for {sum (81 63 9)}})
            "the function argument x already taken")
  (test/exn (run `{define
                    {[fun sum (x y {1 + 2}) = {{x + y} + x}]}
                    for {sum (81 63 9)}})
            "the function variables must be of type Symbol")
  (test/exn (run `{define
                    {[fun sub (x y) = {x - y}]
                     [fun sub (x y) = {x - y}]}
                    for {sum (81 63)}})
            "identifier sub already defined")
  (test/exn (run `{define
                    {let sub be 1 in {sub + 1}}
                    for {sub (81 63)}})
            "only functions can be in the define")
  (test/exn (run `{define
                     {[fun fact (n) = {ifz n then 1 else {n * {fact ({n - 1})}}}]}
                     for {exponential (5)}})
            "unbound expression: exponential")
  (test/exn (run `{define
                    {[fun even (n) = {ifz n then 0 else {odd ({n - 1})}}]
                     [fun odd (n) = {ifz x then 42 else {even ({n - 1})}}]}
                    for {even (1024)}})
            "unbound expression: x")
  (test/exn (run `{define
                    {[fun f (x) = {x + y}]}
                    for {let y be 5 in {f (3)}}}) 
            "unbound expression: y")
  (test/exn (run `{fun error (x) = {{x * x} + 1}})
            "the function (in this case: error) cannot be evaluated to Value")
  (test/exn (run `{define
                    {[fun gcd (m n) = {ifz n then m else
                                           {ifz {m <= n}
                                                then {gcd (m {n - m})}
                                                else {gcd ({m - n} n)}}}]}
                    for {gcd (81 63 9)}})
            "wrong number of argument"))

;;testy operatorów:

(module+ test
  (test (run `2)
        2)
  (test (run `{2 - 1})
        1)
  (test (run `{3 * 1})
        3)
  (test (run `{4 + 3})
        7)
  (test (run `{3 <= 14})
        0)
  (test (run `{8934 <= -1})
        69)
  (test (run `{{2 - 3}+{3 * {5 + 8}}})
        38)
  (test (run `{ifz {1 <= 0} then {2 * 4} else 64})
        64)
  (test (run `{let x be 1 in {x + 1}})
        2)
  (test (run `{let x be 1 in {x + {let y be 2 in {x * y}}}})
        3)
  (test (run `{let x be 1 in {x + {let x be {x + 1} in {x * 4}}}})
        9))
