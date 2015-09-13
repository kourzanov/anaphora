(code;;bones
(define-syntax define-syntax-rule (syntax-rules ()   
   ([_ (syn . args) . body]
    (define-syntax syn (syntax-rules () ([syn . args] . body))))
   ([_ syn . forms]
    (define-syntax syn . forms))
   ))
(define-syntax-rule [let-syntax-rule ((t . pat) . expr) . body]
   (let-syntax ([t (syntax-rules () ([t . pat] . expr))]) . body))
(define-syntax-rule [let-syntax-rule' ell ((t . pat) . expr) . body]
   (let-syntax ([t (syntax-rules ell () ([t . pat] . expr))]) . body))
(define-syntax-rule [letrec-syntax-rule ((t . pat) . expr) . body]
   (letrec-syntax ([t (syntax-rules () ([t . pat] . expr))]) . body))

(define-syntax-rule [Lam forms . body]
  (let-syntax ([foo (syntax-rules () ([_ . forms] . body))])
    foo
))

(define-syntax-rule [extract symb body _k]
   (letrec-syntax ([tr (syntax-rules (symb)
     ([_ x symb tail (k symb-l . args)]
      (k (x . symb-l) . args)) 
     ([_ d (x . y) tail k]  
      (tr x x (y . tail) k)) 
     ([_ d1 d2 () (k  symb-l . args)]
      (k (symb . symb-l) . args))
     ([_ d1 d2 (x . y) k]
      (tr x x y k)))])
      (tr body body () _k)
   ))

(define-syntax extract* (syntax-rules ()
    ([_ (symb) body k]
     (extract symb body k))
    ([_ _symbs _body _k]
     (letrec-syntax ([ex-aux
	   (syntax-rules ()
	     ([_ found-symbs () body k]
	      (reverse () found-symbs k))
	     ([_ found-symbs (symb . symb-others) body k]
	      (extract symb body
		       (ex-aux found-symbs symb-others body k)))
	     )]
	  (reverse	
	   (syntax-rules ()
	     ([_ res () (kp () . args)]
	      (kp res . args))
	     ([_ res (x . tail) k]
	      (reverse (x . res) tail k)))))
       (ex-aux () _symbs _body _k)))))


(define-syntax split (syntax-rules (XXX)
 ([_ (k fst [snd ...] . r) XXX  . rest] (k fst [snd ... . rest] . r))
 ([_ (k [fst ...] snd . r) x . rest]   (split (k [fst ... x] snd . r) . rest))
 ))

(define-syntax redefine-thyself* (syntax-rules ()
 ([_ 1 ids (slf ...) (rec ...) . body]
  (letrec-syntax ([slf (syntax-rules () ([_ . ts]
   (let-syntax-rule ([K all terms] (split (rec [] [] . terms) . all))
    (extract* ids ts [K [] ts])
    ))
   )] ...) . body
  ))
 ([_ (ids ...) [] (slf ...) recs . body]
  (redefine-thyself* 1 (ids ... XXX slf ...) (slf ...) recs . body))
 ))

(define-syntax-rule [define-anaphora (thy ...) (n rd rl) ...]
 (let-syntax-rule' .. ([K (rb) names ([name rdef rules] ..)]
    ;; this is where it begins
    (letrec-syntax ([rdef rules] ..)
      (begin
	 (define-syntax-rule [name . fs]
           (let-syntax-rule ([K all body] (split (rdef [] [] . body) . all))
	      (extract* (thy ... XXX . names) fs
		 [K
                  [] fs]
		 ))) ..
	)));)
    (extract* (recursive-bindings) (rl ...)
       [K [] (n ...) ([n rd rl] ...)])
 )))