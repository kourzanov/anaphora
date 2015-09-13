; foo
(cond-expand (bigloo-eval
(module main
   (library slib);for debug
   (import (synrules "synrules.sch")
	   (ascript "cases.scm")
	   helpers))
)(else
(module main
   (library slib);for debug
)
(load "synrules.sch")
(load "dodger.sch")
(load "helpers.scm")
))

(def-syntax λ lambda)
(def-syntax + $+)(def-syntax - $-)
(def-syntax * $*)(def-syntax / $/)
(def-syntax _ rcurry)

(call-with-values (delay (apply [_ + 1] '(3))) (λ args
(call-with-values (delay (apply [_ * 2] args)) [_ / 4])
))

((circ
    [_ / 4]
    [_ * 2]
    [_ + 1]
    )
 3)

((circ*
    [_ / 4]
    [_ * 2]
    [_ + 1]
    )
 3)

(def (/+% a b)
  (values (/ a b) (modulo a b))
  )
(def (foo a b)
  (values (/ a 2) (- b 1))
  )
((circ*
    cons
    foo
    /+%
    ;(delay (values 2 3))
    ;(kurry* apply values _)
    values
    )
  2 3
  )

([kurry - 4 _ 1] 2)

#'(circ' $- $*)
((circ' $- $*) 1 2 3)



(def (range n) (unfold  [_ >= n] values [_ + 1] 0))
(def add1 [_ + 1])

;; non-manifest anaphoric pronouns
(->' (range 10)  
     (map add1)  
     (apply +)  
     (printf "the sum is: ~a\n"))
(-> 1
     (/ 2)
     (+ 1)  
     (pp))

;; manifest versions are the easiest
[~>> _
  (+ 123 234)
  (* _ 345)
  (- _ 5)
  (cons _ _)
]
[->> _
  (+ 123 234)
  (begin (pp 'HERE) (* _ 345))
  456
  (- _ 5)
  (cons _ _)
]
;; check pre-emption
[=>> _
  (+ 123 234)
  (begin (pp 'HERE) (* _ 345))
  456
  (- _ 5)
  (cons _ _)
]



;; check auto-manifest versions
(>>-
   (range 10)  
   (map add1 _)  
   (apply + _)  
   (printf "the sum is: ~a\n" _))
(>>=
   (range 10)  
   (map add1 _)  
   (apply + _)  
   (printf "the sum is: ~a\n" _))

;; we can stick it anywhere
(>>-
   (range 10)  
   (map add1 _)
   (take _ 5) 
   (apply + _))
(>>=
   (range 10)  
   (map add1 _)
   (take _ 5) 
   (apply + _))

;; can even duplicate
[>>~
  (+ 123 234)
  (* _ 345)
  (- _ 5)
  (cons _ _)
]

;; check pre-emption
[>>-
  (+ 123 234)
  (begin (pp 'HERE) (* _ 345))
  456
  (- _ 5)
  (cons _' _)
]
[>>=
  (+ 123 234)
  (begin (pp 'HERE) (* _ 345))
  456
  (- _ 5)
  (cons _' _)
]

;; check nesting
(>>-
   (range 10)  
   (map add1 _)
   (take _ (>>- (>>- (>>- 1 (+ _ 1))
		     (/ _ _))
	      (+ _ 4))) 
   (apply + _))
(>>-
   (range 10)  
   (map add1 _)
   (take _ (>>= 1 (+ 4 _))) 
   (apply + _))
(>>=
   (range 10)  
   (map add1 _)
   (take _ (>>= 1 (+ _ 4))) 
   (apply + _))
(>>=
   (range 10)  
   (map add1 _)
   (take _ (>>- (>>- (>>- 3 (- _ 1))
		     (/ _ _))
	      (+ _ (>>- 2 (* _ _)))))
   (apply + _))
(>>~
   (range 10)  
   (map add1 _)
   (take _ (>>~ 1 (+ _ 4))) 
   (apply + _))



(def (array-slice a s e)
   (make-shared-array a
      (fn y x =>
	 (list y (+ x s)))
      10
      [+ (- e s) 1]
      ))
(def (list-rank l)
   (if [list? l]
       (+ 1 (apply max (map list-rank l)))
       0
       ))


(TYPES (Λ types (member?? string: types #true #false)))

((Λ (foo:) #true) :foo)

(Def [foo x :array]
   (type x quote)
   )
(map (\>>~ (+ _ 1) (* 2 _)) '(1 2 3))

#|
123

(Let ([c 1] :flo)
 (pp (type c quote))
 (Let* (fix:
	[a 1] ;:fix
	[b #l2] :llong
	[c #z0] :bignum
       )
   (printf "~a ~a ~a~n" (type a quote) (type b quote) (type c quote))
   (+ 1 a)
   (+ a 2)
   (Let ([a :flo 3.] 
	 [ch #\a] :char
	 [wc #u0042] :wchar
	 [in 42] :int
	 )
      (pp (type a quote))
      (+ a .0)
      (+ b #l2)
      (+ b a)
      (+ #z1 c)
      (printf "~a ~a ~a~n" (type ch quote) (type wc quote) (type in quote))
      (int ch) (wchar ch)
      (int wc) (char wc)
      (int in) (char in) (wchar in)
   )
   
   (Let ([b 2.] :flo
	 [c #e33] :elong
	 )
      (+ a 1)
      (+ 2. b)
      (printf "~a ~a~n" (type b quote) (type c quote))
      (+ c #e1)
      (+ c b)
      (Let ([c 3] :fix
	    [l '(1 2 3)] :list
	    [v '#f64(1. 2. 3.)] :f64vector
	    [m '#(#(1 2) #(3 4))] :matrix
	    [A (make-array '#(#false) 10 10)] :array)
	 (pp (type c quote))
	 (+ a 0)
	 (+ .2 b)
	 (+ c 1)
	 
	 (printf "~a ~a ~a ~a~n"
	     (type l quote) (copy l) (clone l) (length l))
	 (ref l 1)
	 (set! l 2 3)
	 ;(let ([clone 'xxx])
	 {l} {l .copy} {l .clone} {l .length}
	 {l(1)}
	 (pp {l(.. 2)})
	 (pp {l(2 ..)})
	 (pp {l(1 .. 2)})
	 {l(1):= 2}
	 
	 (printf "~a ~a ~a ~a~n"
	    (type v quote) (copy v) (clone v (length v)) (length v))
	 (ref v 1)
	 (set! v 2 3.)
	 {v} {v .copy} {v .clone 2} {v .length}
	 (pp {v(1)})
	 {v(1):= 20.}
	 (pp {v(1 .. 1)})
	 (pp (map (λ (x) (>>- x (+ _ 1))) v))
	 (pp (for-each pp v))

	 {m} {m .rows} {m .cols} {m .cols 1}
	 (length m)
	 (ref m 0 0)
	 (set! m 1 0 1)
	 {m((0 1)):= 3}
	 {m((0 1))}
	 {m(0 1):= 3}
	 {m(0 1)}
	 ;)
	 (pp 'here)
	 {A} {A .dim} {A .dim 1} {A .length} {A .clone}
	 (pp {A .rank})
	 {A(1 1)}
	 {A(5 5):= 1}
	 (pp (ref A 5 6))
	 (pp (set! A 5 6 7))
	 )
      )
   )
)

(Let ([x 1] :bignum)
(Let ([y 2] :elong)
(Let ([z 3] :llong)
(Let ([A :array (make-array '#(#false) 10 10)])
   (ref A 5 5)
   (set! A 5 5 1)
   
(
(Lambda (x :fix sl :array)
   (type x quote)
   (type sl quote)
   ;(map (\>>~ (+ _ 1)) sl)
   ;
   (Let (array: [s sl] [x x] :fix)
      (type s quote)
      (+ x x)
      (Let ([s :array (map (fn x => (>>~ x (+ _ 1))) s)])
	 ;(map (λ (x) (>>~ x (+ _ 1))) s)
	 (pp {s .dim})
	 (pp {s[5 0]})
	 (pp {s[5 1]})
	 (pp {s[5 {s[5 1]}]})
	 123
	 ))
   (Let ([l :list (list sl)])
      (pp (type l quote))
      (pp (list-rank l))
      (pp l)
      (Let ([a :array (array l)])
	 ;(pp (array a))
	 (pp {sl[5 1]})
	 (pp {a[5 1]})
	 (pp (list a))
	 1
	 ))
   (Let ([v :vector (vector sl)])
      ;(printf "~a~n" v)
      (pp (type v quote))
      ;(pp v)
      (Let ([a :array (array v 10 3)])
	 ;(printf "~a~n" (array a))
	 ;(pp (vector a))
	 (pp {sl[5 1]})
	 (pp {a[5 1]})
	 (pp (list a))
	 1
	 ))
   )
12
{A(4 .. 6)})
))))

;; check nesting

; (Lambda (fix: a b d)
;   (Lambda (b :flo c)
;     (Lambda (c :bignum)
;        (Lambda (d :fix)
;     (loop (type a quote)
;          (type b quote)
; 	 (type c quote)
; 	 (type d quote))))))
; (Let (fix: [a 1] [b 1] [d 5])
;   (Let ([b 3] :flo [c 4])
;     (Let ([c :bignum 5])
;       (Let ([d 4] :fix)
; 	 (loop (type a quote)
; 	    (type b quote)
; 	    (type c quote)
; 	    (type d quote))
; 	 ))))
; (Let (fix: [a 1] [b 1] [d 5])
;   (Let ([b 3] :flo [c 4])
;    (Lambda (c :bignum)
;       (Let ([a flo: 1])
; 	(Let ([d :fix 4])
; 	 (loop (type a quote)
; 	    (type b quote)
; 	    (type c quote)
; 	    (type d quote))
; 	 )))))
; (Define [x flo: c d]
;   (Let (fix: [a 1] [b 1]);[d 5])
;      (Let ([b 3] :flo [c 4] :bignum)
;        (Let ([d 4]); :fix)
;   (define xx 1)
;   (define yy 1)
; 	 (loop (type a quote)
; 	    (type b quote)
; 	    (type c quote)
; 	    (type d quote))
; 	 ))))
; (pp (list-rank '((1 2) ((3)))))



(display (Let (fix: [z 300] [y 200] [x 100] [l :list '()])
(Do (fix: (i 0 (+ i 1))
          (x x (rsh x 1)))
    ((<= x 0) #f)
    (display (+ i 1))
    (display " ")
    (display (lsh x 1))
    (newline))
(+ y x)
(map [list] (list(list l)))
))

(printf "~s~n" (>-> (+ 1 2 3) :fix
   (* _ 2) 
   (+ _ _)
   (max 23 _ 25)
   (* 2 _)
   (flo _) :flo
   (+ _ .1)))

(Member?? 12 (a b x c) #true #false)

;(nth (a (b (c d))) 1 1 1)
(>-> 012 :fix
     123 
     234 ;:flo
     (+ _;[nth _']
	;[nth _' 1]
	#,[Nth 2];[nth _' 1 1] ;_
	;[nth _' 1 1 1]
	;[nth _' 1 1 1 1]
	)
     )

(>=> 012 :fix
     123 
     234 ;:flo
     (+ _;[nth _']
	;[nth _' 1]
	[nth _' 1 1] ;_
	;[nth _' 1 1 1]
	;[nth _' 1 1 1 1]
	)
     )

(>~> 012 :fix
     123 
     234 ;:flo
     (+ _;[nth _']
	;[nth _' 1]
	[nth _' 1 1] ;_
	;[nth _' 1 1 1]
	;[nth _' 1 1 1 1]
	)
     )

;; irreflexive letrec_ does not really make sense,
;; since the bindings must be initialized in order
(def-syntax letrec_ (syntax-rules ()
 ([_ 1 (t ...) (o ...) (n ...) (v ...) [] . body]
  (let-syntax ([o n] ...)
   (let ([n '#?] ...)
     (letrec-syntax ([rec (syntax-rules .. ()
	([_ (t1 ..) () () () (n1 v1) ..]
	 (let ([t1 v1] ..)
	    (set! n1 t1) ..
	    ))
	([_ ts (o1 . os) (n1 . ns) (v1 . vs) rs ..]
	  (let-syntax ([baz
	    (let-syntax ([n1 o1])
	       v1
	       )])
	    (rec ts os ns vs rs .. (n1 baz))
	    ))
       )])
	(rec (t ...) (o ...) (n ...) (v ...))
	. body
	))
     ))
 ([_ 1 (t ...) (o ...) (n ...) (v ...) ([n1 v1] . rest) . body]
  (letrec_ 1 (t ... foo) (o ... bar) (n ... n1) (v ... v1) rest . body)
  )
 ([_ ([n v] . rest) . body]
  (letrec_ 1 [] [] [] [] ([n v] . rest) . body)
  )
))

(def-syntax letrec*_ (syntax-rules ()
 ([_ 1 (t ...) (o ...) (n ...) (v ...) [] . body]
  (let-syntax ([o n] ...)
   (let ([n '#?] ...)
     (letrec-syntax ([rec (syntax-rules .. ()
	([_ () () ()]
	 #false)
	([_ (o1 . os) (n1 . ns) (v1 . vs)]
	 (begin
	  (set! n1
	    (let-syntax ([n1 o1])
	       v1
	       ))
	    (rec os ns vs)
	    ))
       )])
	(rec (o ...) (n ...) (v ...))
	. body
	))
     ))
 ([_ 1 (t ...) (o ...) (n ...) (v ...) ([n1 v1] . rest) . body]
  (letrec*_ 1 (t ... foo) (o ... bar) (n ... n1) (v ... v1) rest . body)
  )
 ([_ ([n v] . rest) . body]
  (letrec*_ 1 [] [] [] [] ([n v] . rest) . body)
  )
))
;

(letrec_ ([a (+ 0 1)][b (+ 1 2)])   (list a b))
(letrec*_ ([a (+ 0 1)][b (+ a 2)])   (list a b))

(>>= (cons 1 2) 10
   (begin (set-car! _' _)
	  _'))


(def-syntax hah (syntax-rules ()
 ;(_ 'wow
 ([_] 'hah)
))
;(define-syntax trf 'trf)


(defs-syntax [Hah 'wow] [] ([_ . args] (symbol->keyword #'Hah)))
(defs-syntax [Hoo 'woo] [] ([_ . args] 'hoo))

; (begin
;    (define-identifier-syntax Hah
;       'wow)
;    (define-syntax syntax (let-syntax ([stx syntax])
; 	(syntax-rules (Hah)
; 	   ([_ (Hah . args)] 'hah)
; 	   ([_ . args] (stx . args))
; 	   )))
;    )
; (begin
;    (define-identifier-syntax Hoo
;       'woo)
;    (define-syntax syntax (let-syntax ([stx syntax])
; 	(syntax-rules (Hoo)
; 	   ([_ (Hoo . args)] 'hoo)
; 	   ([_ . args] (stx . args))
; 	   )))
;    )

#'Hah
;(let-syntax ([Hah Hoo])
[Hah]
;)

(as (a :fix b :flo u64vector: c d)
  (as (c :bignum e :elong)
     (as (f)
	(Define x 1)
	(Define y 2)
   (type a quote)
   (type b quote)
   (type c quote)
   (type d quote)
   (type e quote)
   (type f quote))))
;(let-syntax ([_ 'foobar])
 (>-> 321
    432
  (>-> 012 ;:fix
     123 
     234 ;:flo
     (list _
	;[nth _']
	[nth _' 1]
	[nth _' 1 1] ;_
	[nth _' 1 1 1]
	[nth _' 1 1 1 1]
	[nth _' 1 1 1 1 1]
	)
     ));)

(>~> 1
   2
   (> [nth _' 1] [nth _' 1 1])     ;; expands to (> 2 1)
   (- [nth _' 1 1] [nth _' 1 1 1]) ;; expands (- 2 1)
)
(>-> 1
  (>~> 2
     (> [nth _' 1] [nth _' 1 1])     ;; expands to (> 2 1)
     (- [nth _' 1 1] [nth _' 1 1 1]) ;; expands (- 2 1)
))
(>-> (list 1 2 3) ;; _ binds to whatever was in the outer scope
     (filter (lambda (x) (> x 1)) _) ;; _ binds to '(1 2 3)
     (list-ref _ 1)                  ;; _ binds to '(2 3)
)
|#

(->> _
   25
   (- _ 1) 
   (/ _ (->> _ 1 (+ 1 _)))
   (+ _ _)
   (* _ (->> _ 2 (+ 1 _)))
   )

(kurry' _ ((kurry' _ _) +) (* _ 2) 3)

(>->
   1
   (+ 1 _)
   ;[kurry  + _ x]
   )

#|
(Let (fix: [x 25]); [y .1] :flo)
;(Let (bignum: [z #z1])
 (type x quote)
 (type (- x 1) quote)
 (type (/ x 2) quote)
 ;;(- type quote x 1)
 ;;(/ type quote fail x 2)
 ;;(/ type quote fail y 2)
 (type y quote)
 (type (- y 1) quote)
 (type (/ y 2) quote)
 (>-> x ;:fix
  (begin
     (pp (type x quote))
     (- _ 1)
     ) ;:fix
  ;(>->
   (begin
      (pp (type _ quote))
      (pp (type (/ _ 2) quote))
      (/ _ (>-> 1 (+ _ 1)))
      );:flo
   (begin
      (pp (type _ quote))
      ;(pp [nth _'])
      ;(pp (+ type quote + _ 10))
      (+ _ _)
      )
   (* _ (>-> 2 (+ _ 1)))
   ))
(>-> 25 :fix
  (begin
     (pp (type _ quote))
     (- _ 1)
     ) ;:fix
  ;(>->
   (begin
      (pp (type _ quote))
      (pp (type (/ _ 2) quote))
      (/ _ (>-> 1 (+ _ 1)))
      );:flo
   (begin
      (pp (type _ quote))
      ;(pp [nth _'])
      ;(pp (+ type quote + _ 10))
      (+ _ _)
      )
   (* _ (>-> 2 (+ _ 1)))
   )
|#

;#|
(let-syntax (;[_ cons]
	     [c (Λ (a b) (cons a b))]
	     )
   (>-> (λ (x) (+ x 1))
        (_ 2)
	(c 3 _)))

(>-> 1
    (let ([_ 2])
       (+ _ _)
       )
    (* [nth _' 1 1] _))

(let ([_ 2])
  (>-> 1
     (+ _ _)
     (* [nth _' 1 1] [nth _' 1] _)))

(Let ([p :pair '(1 . a)])
   {p[0]:= 2}
   {p[1]:= 'b}
   (pp {p[0]})
   (pp {p[1]})
   (pp {p .length})
   (pp {p .copy})
   )


(Let ([v :vector '#(.1 .2 .3 .4 .5 .6 .7 .8 .9 .10)])
   (pp (Do ([i :fix 1 (+ i 1)]
	    [s :flo 0. (+ s (>-> (expt 2 i):fix
				 (flo _):flo
				 {v[(- i 1)]}
				 (* #,[Nth 2] _)
				 ;(* #,[Nth 2] _))
			       ))])
       ((> i 10) s)
       (pp s))
      ))
;|#

(def-syntax r (syntax-rules ()
 ([_ () k] (k ()))
 ([_ (t . ts) k]
  (r t (Λ (v)
  (r ts (Λ (vs)
     (k (v . vs))))
  )))
 ([_ t k]
  (k t))
 ))

;(r () (Λ [x] x))
(r 1 (Λ [x] x))
(r (1 2) (Λ [x] x))
(r ((1 2) 3) (Λ [x] x))
(r (1 (2 3)) (Λ [x] x))
(r (1 2 a 3 4) (Λ [x] x))


(def-syntax affine (syntax-rules ()
  ([_ th () k] (k ()))
  ([_ th (t . ts) k]
   (let-syntax ([eq?? (syntax-rules (th)
	([_ th kt kf] kt)
	([_ tt kt kf] kf)
	)])
     (eq?? t
	(affine th t (Λ [t']
         (let-syntax ([th syntax-error])
	  (affine th ts (Λ [ts']
	   (k (t' . ts'))
	   ))
	)))
	(affine th t (Λ [t']
	 (affine th ts (Λ [ts']
	  (k (t' . ts'))
	   ))
	))
      )))
  ([_ th t k] (k t))
  ))
(def-syntax strict (syntax-rules ()
  ([_ th bad () k] (k ()))
  ([_ th bad (t . ts) k]
   (let-syntax ([eq?? (syntax-rules (th)
	([_ th kt kf] kt)
	([_ tt kt kf] kf)
	)])
     (eq?? t
	(strict th bad t (Λ [t']
         (let-syntax ([bad ident])
	  (strict th bad ts (Λ [ts']
	   (k (t' . ts'))
	   ))
	  )))
	(strict th bad t (Λ [t']
	 (strict th bad ts (Λ [ts']
	  (k (t' . ts'))
	  ))
	 ))
      )))
  ([_ th bad t k] (k t))
  ))
(def-syntax linear (syntax-rules ()
  ([_ th bad () k] (k ()))
  ([_ th bad (t . ts) k]
   (let-syntax ([eq?? (syntax-rules (th)
	([_ th kt kf] kt)
	([_ tt kt kf] kf)
	)])
     (eq?? t
	(linear th bad t (Λ [t']
         (let-syntax ([bad ident]
		      [th syntax-error])
	  (linear th bad ts (Λ [ts']
	   (k (t' . ts'))
	   ))
	  )))
	(linear th bad t (Λ [t']
	 (linear th bad ts (Λ [ts']
	  (k (t' . ts'))
	  ))
	 ))
      )))
  ([_ th bad t k] (k t))
  ))
(define-anaphora (_ _' syntax-error)
   ;; ensure affine λ-calculus
   (>- rec0 (syntax-rules ()
		([_ (thy thy' . _0) x fa] (affine thy fa (Λ [a] a)))
		([_ (thy thy' . _0) slfs fa . fb]
		 (let-syntax ([thy' thy]
			      [thy (affine thy fa (Λ [a] a))])
		     (redefine-thyself* (thy thy' . _0) [] slfs (rec0 rec1 rec2)
		       (rec0 (thy thy' . _0) slfs . fb)
		       ))
		    )
		))
   ;; ensure strict λ-calculus
   (>= rec1 (syntax-rules ()
		([_ "next" (thy thy' bad) x fa]
		 (strict thy bad fa (Λ a (bad . a))))
		([_ "next" (thy thy' bad) slfs fa . fb]
		 (let-syntax ([thy' thy]
			      [thy (strict thy bad fa (Λ a (bad . a)))])
		     (redefine-thyself* (thy thy' bad) [] slfs (rec0 rec1 rec2)
		       (rec1 "next" (thy thy' bad) slfs . fb)
		       ))
		    )
		;; first
		([_ (thy thy' bad) x fa]
		 (strict thy bad fa (Λ [a] a)))
		([_ (thy thy' bad) slfs fa . fb]
		 (let-syntax ([thy' thy]
			      [thy (strict thy bad fa (Λ [a] a))])
		     (redefine-thyself* (thy thy' bad) [] slfs (rec0 rec1 rec2)
		       (rec1 "next" (thy thy' bad) slfs . fb)
		       ))
		    )
		))
      ;; ensure linear λ-calculus
   (>! rec2 (syntax-rules ()
		([_ "next" (thy thy' bad) x fa]
		 (linear thy bad fa (Λ a (bad . a))))
		([_ "next" (thy thy' bad) slfs fa . fb]
		 (let-syntax ([thy' thy]
			      [thy (linear thy bad fa (Λ a (bad . a)))])
		     (redefine-thyself* (thy thy' bad) [] slfs (rec0 rec1 rec2)
		       (rec2 "next" (thy thy' bad) slfs . fb)
		       ))
		    )
		;; first
		([_ (thy thy' bad) x fa]
		 (linear thy bad fa (Λ [a] a)))
		([_ (thy thy' bad) slfs fa . fb]
		 (let-syntax ([thy' thy]
			      [thy (linear thy bad fa (Λ [a] a))])
		     (redefine-thyself* (thy thy' bad) [] slfs (rec0 rec1 rec2)
		       (rec2 "next" (thy thy' bad) slfs . fb)
		       ))
		    )
		))
   )

(>- 22 _)
(>- 22
    (+ 00 _ 33 44 55))
(>- 22
    (+ 00 (+ _ 33) 55 44))
(>- 22
    (+ 00 _ 33 (+ 55 44)))
(>- 11
    (* 2 _)
    (+ 00 _ 33 (+ 55 _' 44)))


(>= abc)
(>= a (begin _))
;(>= a (+ 1 2))
(>= a (+ 1 _ 2))
(>= a (+ 1 _ 2 _))

(>! 123)
(>! 123 (begin _))
(>! 123 (+ _ 321))

;(>! 123 234)
;(>! 123 (+ 1 _ 2 _))

(>-> 1 2 3
   (+ #,(Nth 1) #,(Nth 2) #,(Nth 3))
   )

(>-> 1 (>-> 2 3
   (+ #,(Nth 1) #,(Nth 2) #,(Nth 3))
   ))

'(let-syntax ([foo '(+ #,(Nth 1) #,(Nth 2) #,(Nth 3))])
   (>-> 1 2 3
   foo
   ))

(define-anaphora (_ _')
   (<<- rec1 (syntax-rules ()
		([_ _ x fa] fa)
		([_ (thy thy') slfs fb ... fa]
		 (let-syntax ([thy' thy]
			      [thy fa])
		    ;(recursive-bindings
		     (redefine-thyself* (thy thy') [] slfs (rec1 rec2 rec3);[]
		       (rec1 (thy thy') slfs fb ...)
		       );)
		    ))
		))
   (<<= rec2 (syntax-rules ()
		([_ _ x fa] fa)
		([_ (thy thy') slfs fb ... fa]
		 (let ([thy' thy]
		       [thy fa])
		    (redefine-thyself* (thy thy') [] slfs (rec1 rec2 rec3) ;recursive-bindings
		       (rec2 (thy thy') slfs fb ... fa)
		       )
		    ))
		))
   (<<~ rec3 (syntax-rules ()
		([_ _ x fa] fa)
		([_ (thy thy') slfs fb ... fa]
		 (let ([thy' thy]
		       [thy fa])
		    (redefine-thyself* (thy thy') [] slfs (rec1 rec2 rec3) ;recursive-bindings
		       (and thy (rec3 (thy thy') slfs fb ...))
		       )
		    ))
		))
   )

(<<- (+ 2 _) (* _ 3) 1)