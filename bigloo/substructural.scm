; substructural logic
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

(def-syntax [eq?? th t kt kf]
   ((syntax-rules (th)
	([_ th] kt)
	([_ tt] kf)
	) t))

(def-syntax membr?? (syntax-rules ()
      ([_ id () kt kf] kf)
      ([_ (x . y) z kt kf] kf)
      ([_ id (x . r) kt kf]
       (eq?? id x
	  kt
	  (membr?? id r kt kf)
       ))
      ))


(def-syntax expand-let (syntax-rules (let let*)
  ([_ (let ([n v] ...) . ts) k]
   (k ((lambda (n ...) . ts) v ...)))
  ([_ (let* [] . ts) k]         (k ts))
  ([_ (let* ([n v] . rest) . ts) k]
   (expand-let (let* rest . ts) (Λ [a]
	(k ((lambda (n) . a) v))
	)))
  ))

(def-syntax expand-cond (syntax-rules (cond else case =>)
  ([_ (cond) k]                      (k #false))
  ([_ (cond [else . body] . rest) k] (k (begin . body)))
  ([_ (cond [check => fn] . rest) k]
   (expand-cond (cond . rest) (Λ [a]
    (k (let ([tmp check])
	  (if tmp
	      (fn tmp)
	      a
	      )))
    )))
  ([_ (cond [check . body] . rest) k]
   (expand-cond (cond . rest) (Λ [a]
    (k (if check
	   (begin . body)
	   a
	   )))
      ))
  ;; CASE needs to pass the binding for T up the continuation
  ;; since the wrapping by a LET is done in the outer handler,
  ;; which has to "unhygienically" bind the previously unbound T
  ([_ 1 (case t) k]                      (k t #false))
  ([_ 1 (case t [else . body] . rest) k] (k t (begin . body)))
  ([_ 1 (case t [check => fn] . rest) k]
   (expand-cond 1 (case t . rest) (Λ [t a]
	(k t (let ([tmp (memv t 'check)])
	      (if tmp
		  (fn tmp)
		  a)
	      )))
      ))
  ([_ 1 (case t [check . body] . rest) k]
   (expand-cond 1 (case t . rest) (Λ [t a]
	(k t (if (memv t 'check)
	       (begin . body)
	       a)))
      ))
  ;; outer handler
  ([_ (case term . rest) k]
   (expand-cond 1 (case t . rest) (Λ [t a]
	(k (let ([t term]) a))
	)))
  ))

;; WARM UP
(def-syntax affine (syntax-rules ()
  ([_ th () k] (k ()))
  ([_ th (t . ts) k]
     (eq?? th t
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
      ))
  ([_ th t k] (k t))
  ))
(def-syntax strict (syntax-rules ()
  ([_ th bad () k] (k ()))
  ([_ th bad (t . ts) k]
   (eq?? th t
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
      ))
  ([_ th bad t k] (k t))
  ))
;; check for occurrence of identifier [[th]]
(def-syntax check (syntax-rules (let let* letrec letrec* lambda)
  ([_ db () k] (k ()))
  ;; expand binding forms inplace (taking care of shadowing)
  ([_ [spec th bad] (lambda (n) . ts) k]
   (eq?? th n
      ;; we are shadowing thy. check that value does not use it
      ;; reset while checking the body, since thy is shadowed
      (k (lambda (n) (check [spec th bad] (begin . ts) (Λ [a] a))))
      (check [spec th bad] ts (Λ [ts']
	(extract* (n) ts'
	   [(Λ (nn tt) (k (lambda nn . tt)))
            [] ts'])
      	))))
  ([_ db (let . ts) k] (expand-let (let . ts) (Λ [f] (check db f k))))
  ([_ db (let* . ts) k] (expand-let (let* . ts) (Λ [f] (check db f k))))
  ([_ db (t . ts) k]
   (check db t (Λ [t']
    (check db ts (Λ [ts']
     (k (t' . ts'))
     )))))
  ([_ [affine: th bad] t k] (eq?? th t
      ((let-syntax ([th syntax-error]) k) t)
      (k t)))
  ([_ [strict: th bad] t k] (eq?? th t
      ((let-syntax ([bad ident]) k) t)
      (k t)))
  ([_ [linear: th bad] t k] (eq?? th t
      ((let-syntax ([bad ident] [th syntax-error]) k) t)
      (k t)))
  ))

(define-anaphora (_ _' syntax-error)
   ;; ensure affine λ-calculus
   (>- rec0 (syntax-rules ()
		([_ (thy thy' . _0) x fa] (check [affine: thy . _0] fa (Λ [a] a)))
		([_ (thy thy' . _0) slfs fa . fb]
		 (let-syntax ([thy' thy]
			      [thy (check [affine: thy . _0] fa (Λ [a] a))])
		     (redefine-thyself* (thy thy' . _0) [] slfs (rec0 rec1 rec2)
		       (rec0 (thy thy' . _0) slfs . fb)
		       ))
		    )
		))
   ;; ensure strict λ-calculus
   (>= rec1 (syntax-rules ()
		([_ "next" (thy thy' bad) x fa]
		 (check [strict: thy bad] fa (Λ a (bad . a))))
		([_ "next" (thy thy' bad) slfs fa . fb]
		 (let-syntax ([thy' thy]
			      [thy (check [strict: thy bad] fa (Λ a (bad . a)))])
		     (redefine-thyself* (thy thy' bad) [] slfs (rec0 rec1 rec2)
		       (rec1 "next" (thy thy' bad) slfs . fb)
		       ))
		    )
		;; first
		([_ (thy thy' bad) x fa]
		 (check [strict: thy bad] fa (Λ [a] a)))
		([_ (thy thy' bad) slfs fa . fb]
		 (let-syntax ([thy' thy]
			      [thy (check [strict: thy bad] fa (Λ [a] a))])
		     (redefine-thyself* (thy thy' bad) [] slfs (rec0 rec1 rec2)
		       (rec1 "next" (thy thy' bad) slfs . fb)
		       ))
		    )
		))
      ;; ensure linear λ-calculus
   (>! rec2 (syntax-rules ()
		([_ "next" (thy thy' bad) x fa]
		 (check [linear: thy bad] fa (Λ a (bad . a))))
		([_ "next" (thy thy' bad) slfs fa . fb]
		 (let-syntax ([thy' thy]
			      [thy (check [linear: thy bad] fa (Λ a (bad . a)))])
		     (redefine-thyself* (thy thy' bad) [] slfs (rec0 rec1 rec2)
		       (rec2 "next" (thy thy' bad) slfs . fb)
		       ))
		    )
		;; first
		([_ (thy thy' bad) x fa]
		 (check [linear: thy bad] fa (Λ [a] a)))
		([_ (thy thy' bad) slfs fa . fb]
		 (let-syntax ([thy' thy]
			      [thy (check [linear: thy bad] fa (Λ [a] a))])
		     (redefine-thyself* (thy thy' bad) [] slfs (rec0 rec1 rec2)
		       (rec2 "next" (thy thy' bad) slfs . fb)
		       )))
		)))

;; check for occurrence of a form (r0 r1 ...)
(def-syntax check* (syntax-rules (lambda λ let let* if cond case begin
			q quote quasiquote unquote unquote-splicing)
  ;; handle (quasi) quotation
  ([_ qq db (quote ts) k]                  (k 'ts))
  ([_ qq db (quasiquote ts) k]             (check* [q . qq] db ts (Λ [a] (k (quasiquote a)))))
  ([_ [q . qq] db (unquote ts) k]          (check* qq db ts (Λ [a] (k (unquote a)))))
  ([_ [q . qq] db (unquote-splicing ts) k] (check* qq db ts (Λ [a] (k (unquote-splicing a)))))
  ;; base case (reflection point, results starts to build from here
  ([_ qq db () k] (k ()))
  ;; we basically support a language with λs and IFs (with some syntactic sugar)
  ([_ [] [spec (r0 r1) bad] (lambda ns . ts) k]
   (membr?? r0 ns
      ;; shadowing r0
      (k (lambda ns (check* [] [spec (r0 r1) bad] (begin . ts) (Λ [a] a))))
      (membr?? r1 ns
	 ;; shadowing r1
	 (k (lambda ns (check* [] [spec (r0 r1) bad] (begin . ts) (Λ [a] a))))
	 (check* [] [spec (r0 r1) bad] ts (Λ [ts']
	  (extract* ns ts'
	   [(Λ (nn tt)
	       (k (lambda nn . tt)))
            [] ts'])
	  )))
    ))
  ([_ [] db (let . ts) k] (expand-let (let . ts) (Λ [f] (check* [] db f k))))
  ([_ [] db (let* . ts) k] (expand-let (let* . ts) (Λ [f] (check* [] db f k))))
  ([_ [] db (λ . ts) k] (check* [] db (lambda . ts) k))
  ;; conditionals
  ([_ [] db (if a ts) k]
   (check* [] db (if a ts #false) k))
  ([_ [] [spec (r0 r1) bad] (if a ts es) k]
   ;; assume check* does not modify the terms
   ;; here we are expanding for checking only
   (check* [] [spec (r0 r1) bad] a (Λ [a']
    ;; check ts and es in parallel, in the context provided
    ;; by the whole code chunk represented by k. Ignore the (big) result
    (let-syntax ([check-context-with-ts (check* [] [spec (r0 r1) bad] ts k)]
		 [check-context-with-es (check* [] [spec (r0 r1) bad] es k)])
      ;; we've checked compliance in a, ts and es
      ;; disable the syntax-error wrapper now
     (check* [] [] ts (Λ [ts'] ;; these are run to fully
     (check* [] [] es (Λ [es'] ;; expand syntactic sugar
      ((let-syntax ([bad (Λ* [] ([(r0 r1) msg v] v) (rs (bad . rs)))])
	  k) (if a' ts' es'))
      ))
     ))
    ))
   ))
  ([_ [] db (cond . ts) k] (expand-cond (cond . ts) (Λ [f] (check* [] db f k))))
  ([_ [] db (case . ts) k] (expand-cond (case . ts) (Λ [f] (check* [] db f k))))
  ([_ [] db (begin . ts) k] (check* [] db (BEGIN . ts) k))
  ;; substructural handlers
  ([_ [] [affine: (r0 r1) bad] (t0 t1 . ts) k]
   (eq?? r0 t0
      (eq?? r1 t1
	 ((let-syntax (;; disable this effect for the rest of the block
           [r0 (Λ* [r1]
		  ([r1 . rs]
		   (syntax-error ["\nNon-affine usage of"
                                  (r0 r1 . rs) "in block\n"]))
		  (rs (r0 . rs)))])
	     k) (t0 t1 . ts))
	 (check* (traverse:) [affine: (r0 r1) bad] (t0 t1 . ts) k))
      (check* (traverse:) [affine: (r0 r1) bad] (t0 t1 . ts) k)
     )) 
  ([_ [] [strict: (r0 r1) bad] (t0 t1 . ts) k]
   (eq?? r0 t0
      (eq?? r1 t1
	 ((let-syntax ([bad (Λ* [] ([(r0 r1) msg v] v) (rs (bad . rs)))])
	     k) (t0 t1 . ts))
	 (check* (traverse:) [strict: (r0 r1) bad] (t0 t1 . ts) k))
      (check* (traverse:) [strict: (r0 r1) bad] (t0 t1 . ts) k)
     ))
  ([_ [] [linear: (r0 r1) bad] (t0 t1 . ts) k]
   (eq?? r0 t0
      (eq?? r1 t1
	 ((let-syntax (;; combine handling of affine: and strict:
	    [bad (Λ* [] ([(r0 r1) msg v] v) (rs (bad . rs)))]
            [r0 (Λ* [r1]
		   ([r1 . rs]
		    (syntax-error ["\nNon-affine usage of"
                                   (r0 r1 . rs) "in block\n"]))
		   (rs (r0 . rs)))])
	     k) (t0 t1 . ts))
	 (check* (traverse:) [linear: (r0 r1) bad] (t0 t1 . ts) k))
      (check* (traverse:) [linear: (r0 r1) bad] (t0 t1 . ts) k)
     ))
  ([_ (traverse: . qq) db (t . ts) k]
   (check* qq db t (Λ [t']
    (check* qq db ts (Λ [ts']
     (k (t' . ts'))
     ))
    )))
  ([_ qq db (t . ts) k]
   (check* (traverse: . qq) db (t . ts) k))
  ;; catch all
  ([_ qq db t k] (k t))
  ))


(def-syntax with-effects (syntax-rules ()
 ([_ () . ts] (begin . ts))
 ([_ (spec [rator rand] . rest) . terms]
   (extract* (rator rand syntax-error) terms
      [(Λ ([r0 r1 bad] ts)
	  (let-syntax ([chk (check* [] (spec [r0 r1] bad) (begin . ts)
	     (Λ a (eq?? affine: spec
		(begin . a)
		(bad (r0 r1) ["\nEffect" (r0 r1) "required in block:\n"] . a)
		))
	     )])
	       ((Λ* []
		   ([] (begin . terms))
		   (rs (with-effects rs . terms)))
		. rest)
	  ))
        [] terms]
      ))
 ))

;; check for occurrence of a form [[r0]]
(def-syntax check'
   (syntax-rules (lambda λ let let* if cond case begin
	   q quote quasiquote unquote unquote-splicing
	   letrec
	   let-syntax)
  ;; handle (quasi) quotation
  ([_ qq db 'ts k]        (k 'ts))
  ([_ qq db `ts k]        (check' [q . qq] db ts (Λ [a] (k `a))))
  ([_ [q . qq] db ,ts k]  (check' qq db ts (Λ [a] (k ,a))))
  ([_ [q . qq] db ,@ts k] (check' qq db ts (Λ [a] (k ,@a))))
  ;; base case (reflection point, results starts to build from here
  ([_ qq db () k] (k ()))
  ;;
  ;; we basically support a language with λs and IFs (with some syntactic sugar)
  ;;
  ([_ [] [spec (r0) bad] (lambda ns . ts) k]
   ;(eq?? r0 ns
   (membr?? r0 ns
      ;; shadowing r0
      (k (λ ns . ts))
         ;(λ ns (check' [] [spec (r0) bad] (begin . ts) (Λ [a] a))))
      (check' [] [spec (r0) bad] ts (Λ [ts']
	 (extract* ns ts'
	   [(Λ (nn tt) (k (λ nn . tt)))
            [] ts'])
	  ))
    ))
  ;([_ [] db (let ([n v] ...) . ts) k] (check' [] db ((lambda (n ...) . ts) v ...) k))
  ([_ [] db (let . ts) k]  (expand-let (let . ts)  (Λ [f] (check' [] db f k))))
  ([_ [] db (let* . ts) k] (expand-let (let* . ts) (Λ [f] (check' [] db f k))))
  ([_ [] db (λ . ts) k] (check' [] db (lambda . ts) k))
  ;;
  ;; conditionals
  ;;
  ([_ [] db (if a ts) k]
   (check' [] db (if a ts #false) k))
  ([_ [] [spec (r0) bad] (if a ts es) k]
   ;; assume check' does not modify the terms
   ;; here we are expanding for checking only
   (check' [] [spec (r0) bad] a (Λ [a']
    ;; check ts and es in parallel, in the context provided
    ;; by the whole code chunk represented by k. Ignore the (big) result
    (let-syntax ([check-context-with-ts (check' [] [spec (r0) bad] ts k)]
		 [check-context-with-es (check' [] [spec (r0) bad] es k)])
      ;; we've checked compliance in a, ts and es
      ;; disable the syntax-error wrapper now
     ;(check' [] [] ts (Λ [ts'] ;; these are run to fully
     ;(check' [] [] es (Λ [es'] ;; expand syntactic sugar
      ((let-syntax ([bad (Λ* [] ([r0 msg v] v) (rs (bad . rs)))])
	  k) (if a' ts es))
      ;))
     ;))
    ))
   ))
  ([_ [] db (cond . ts) k] (expand-cond (cond . ts) (Λ [f] (check' [] db f k))))
  ([_ [] db (case . ts) k] (expand-cond (case . ts) (Λ [f] (check' [] db f k))))
  ;([_ [] db (begin . ts) k] (check' [] db (BEGIN . ts) k))
  ;;
  ;; structural handler
  ;;
  ([_ (traverse: . qq) db (t . ts) k]
   (check' qq db t (Λ [t']
    (check' qq db ts (Λ [ts']
     (k (t' . ts'))
     ))
    )))
  ([_ qq db (t . ts) k]
   (check' (traverse: . qq) db (t . ts) k))
  ;; substructural handlers
  ([_ [] [affine: (r0) bad] t0 k]
   (eq?? r0 t0
      ((let-syntax (;; disable this effect for the rest of the block
           [r0 (Λ rs (syntax-error "\nNon-affine usage of"
                                  [r0 . rs] "in block\n"))])
	  k) t0)
      (k t0)
     ))
  ([_ [] [strict: (r0) bad] t0 k]
   (eq?? r0 t0
      ((let-syntax ([bad (Λ* [] ([r0 msg v] v) (rs (bad . rs)))])
	     k) t0)
      (k t0)
     ))
  ([_ [] [linear: (r0) bad] t0 k]
   (eq?? r0 t0
      ((let-syntax (;; combine handling of affine: and strict:
	    [bad (Λ* [] ([r0 msg v] v) (rs (bad . rs)))]
            [r0 (Λ rs (syntax-error "\nNon-affine usage of"
                                   [r0 . rs] "in block\n"))])
	  k) t0)
      (k t0)
     ))
  ;; catch all (REALLY NEEDED FOR QUOTED DATA)
  ([_ qq db t k] (k t))
  ))

(def-syntax ensure (syntax-rules ()
 ([_ (_) . ts] (begin . ts))
 ([_ (spec term . rest) . terms]
   (extract* (term syntax-error) terms
      [(Λ ([r0 bad] ts)
	  (let-syntax ([chk (check' [] (spec [r0] bad) (begin . ts) 
	     (Λ a (eq?? affine: spec
		(begin . a)
		(bad r0 ("\nTerm" r0 "required in block:\n") . a)
		))
	     )])
	     ((Λ* []
		 ([] (begin . terms))
		 (rs (ensure (spec . rs) . terms)))
	      . rest)
	     ))
        [] terms]
      ))
 ))

(def-syntax [λK args . body] (λ args . body))
(def-syntax [λI args . body] (λ args (ensure [strict: . args] . body)))
(def-syntax [λA args . body] (λ args (ensure [affine: . args] . body)))
(def-syntax [λL args . body] (λ args (ensure [linear: . args] . body)))

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


(>= 'abc)
(>= 'a (begin _))
;(>= a (+ 1 2))
(>= 3 (+ 1 _ 2))
(>= 3 (+ 1 _ 2 _))

(>! 123)
(>! 123 (begin _))
(>! 123 (+ _ 321))
;(>! 123 234)
;(>! 123 (+ 1 2 (let ([_x 1][_ 2]) _) _))
(>! 123 (+ 1 _ 2 ((lambda (y) y) 1)))
(>! 123 (+ 1 2 (let* ([_x _] [_ 2]) _x)))
;(>! 123 (+ 1 _ (>! 2 (+ _ 3))))

(expand-cond (cond (b a) (c d)) quote);(Λ [a] a))
(expand-cond (case t ((1 2 3) => a) ((a b c) => d)) quote);(Λ [a] a))

; (cases t
;    (a => b)
;    (c => d)
;    (else e))
(
 (λL (k a)
      ;(k 1)
      ;(lambda (kk z)
      (let ([k 1][z 2])
	    ;z 
	    ;k;(k 1)
	    z
	    (k k)
	    ;
	    z
      ); aa)
      ;k
      ;a
      (case kk
	  ((a b) kk)
	  ((1 2) kk)
	  (else kk))

      (k 2)
      ;(k k)
      ;a
      `(a b ,'k)
      (if 2
	  (identity a)
	  (value a))
      ;k
      )
 identity 2)

(let ([a 1][b '#?][c '#?][d '#?])
;(with-effect [linear: (set! b)]
(as (a :fix)
 (with-effects [linear: (set! a)
                linear: (set! b)]
   (pp a)
   ;(set! b 1)
   (pp (+ a 1))
   ;(if b (set! a 33))
   ;(if b (set! b 33) #false)
   (if b
       (begin (set! b 22)
   	      (set! d 4)
	      )
       (set! b 21)
       )
   (cond (b => (λ (x) (set! c 2)))
	 (c => (λ (x) (set! c 3)))
       (else (set! c 3))
       )
   ((λ (x) (if a
	       (set! b 1)
	       (set! c 2))
	)
    (set! a 0))
   
   ;(let ([t (set! a 0)]) ;#false)
    (case (set! a 0)
      ((1 2 3) (set! a 1));=> (λ (x) (set! a 1)))
      ((a b c) (set! a 2));=> (λ (x) (set! a 2)))
      (else (set! a 3))
      )
    ;#false)

   `(begin ,'(set! a 99))

   (pp a)

   (let ([foo (λ (dd)
		 (set! d 1)
		 )])
      ;(foo d)
      #false
      )
   (let ([a '#?])
      (set! a 3))
   )))

;)


