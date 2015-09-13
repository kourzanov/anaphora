; the beginning
(module synrules)



(define-syntax define-syntax-rule (syntax-rules ()   
   ([_ (syn . args) . body]
    (define-syntax syn (syntax-rules () ([syn . args] . body))))
   
   ([_ syn (form ...)]
    (define-syntax syn (form ...)))
   
   ([_ ell (syn . args) . body]
    (define-syntax syn (syntax-rules ell () ([syn . args] . body))))
   ([_ syn . forms]
    (define-syntax syn . forms))
   ))

(define-syntax def-syntax define-syntax-rule)


(def-syntax [Λ forms . body]
   (syntax-rules .. () ([_ . forms] . body)
))
(def-syntax [Λ… forms . body]
   (syntax-rules … () ([_ . forms] . body)
))

(def-syntax [Λ' (forms . body) ...]
   (syntax-rules .. () ([_ . forms] . body) ...
))

(def-syntax let-syntax-rule (syntax-rules ()
 ([_ ((t . pat) . expr) . body]
   (let-syntax ([t (syntax-rules () ([t . pat] . expr))]) . body))
 ([_ ell ((t . pat) . expr) . body]
   (let-syntax ([t (syntax-rules ell () ([t . pat] . expr))]) . body))
 ))

(def-syntax letrec-syntax-rule (syntax-rules ()
 ([_ ((t . pat) . expr) . body]
   (letrec-syntax ([t (syntax-rules () ([t . pat] . expr))]) . body))
 ([_ ell ((t . pat) . expr) . body]
   (letrec-syntax ([t (syntax-rules ell () ([t . pat] . expr))]) . body))
 ))




(def-syntax define-immutable
   (syntax-rules ()
      ((_ (var . args) . body)
       (begin
	  (define (var . args) . body)
	  (def-syntax var var)))
      ((_ var expr)
       (begin
	  (define var expr)
	  (def-syntax var var)))
      ((_ var)
       (begin
	  (define var #?)
	  (def-syntax var var)))
      ))

(def-syntax def define-immutable)

(def-syntax define-identifier-syntax
  (syntax-rules (set!)
    ((_ id e)
     (def-syntax id e))
    ((_ id (id* e1) ((set! id** pat) tmpl)) ;; id* and id** are ignored
     (begin
       (def-syntax id e1)
       (def-syntax set!
         (let-syntax ((real-set! set!))
           (syntax-rules (id)
             ((set! id pat) tmpl)
             ((set! . whatever)
              (real-set! . whatever)))))))))

(def-syntax with-immutable (syntax-rules ()
  ([_ () . body] (begin . body))
  ([_ (id . rest) . body]
   (let-syntax ([id id])
      (with-immutable rest . body)))
  ))

; redefine [[f]] to [[bottom]] just for the body itself
(def-syntax defn (syntax-rules ()
 ;; recursive functions
 ([_ (f . args) . body]
   (define f (lambda args
	(let-syntax ([f (syntax-rules ())])
	   (let () . body)))
      ))
 ;; recursive CAFs
 ([_ f . exprs]
     (define f 
	(let-syntax ([f (syntax-rules ())])
	   (let () . exprs))
	))
))



; Thanks Oleg & Al
(def-syntax [extract sym body _k]
   (letrec-syntax ([tr (syntax-rules .. (sym)
     ([_ x sym tail (k (syms ..) . args)]
      (k (syms .. x) . args)) ; symb has occurred
     ([_ d (x . y) tail k]   ; if body is a composite form,
      (tr x x (y . tail) k)) ; look inside
     ([_ d1 d2 () (k (syms ..) . args)]
      (k (syms .. sym) . args)) ; symb does not occur
     ([_ d1 d2 (x . y) k]
      (tr x x y k)))])
      (tr body body () _k))
   )
(def-syntax extract* (syntax-rules ()
    ([_ (sym) body k]      ; only one symbol: use extract to do the job
     (extract sym body k))
    ([_ _syms _body _k]
     (letrec-syntax ([ex-aux		; extract symbol-by-symbol
       (syntax-rules ()
	  ([_ syms () body (k () . args)] (k syms . args))
	  ([_ syms (sym . sym*) body k]
	   (extract sym body (ex-aux syms sym* body k)))
	  )])
       (ex-aux () _syms _body _k)))))



(def-syntax [syntax-error] (syntax-error Bad syntax))
;(syntax-error)



;; syntactic composition and currying operators
(def-syntax [circ . fs]
  (lambda args
      (letrec-syntax ([compose
         (syntax-rules ()
	    ([_ g] (apply g args))
	    ([_ f . gs]
	     (f (compose . gs)))
	    )])
	 (compose . fs)
	 )))
;; return a syntax transformer
(def-syntax [circ' . fs]
   (Λ args
      (letrec-syntax ([compose
         (syntax-rules ()
	    ([_ g] (g . args))
	    ([_ f . gs]
	     (f (compose . gs)))
	    )])
	 (compose . fs)
	 )))

;; bring composition down to the value level
(def-syntax syntax (let-syntax ([stx syntax])
       (syntax-rules (circ')
	  ([_ (circ' . args)]
	   (circ . args))
	  ([_ . rest] (stx . rest))
	  )))

;; f o g = λ as. f g as = cwv {apply g as} f
;; f o g o h = λ as. f g h as = cwv {apply h as} λ as. cwv {apply g as} f.
(def-syntax [circ* . fs]
   (letrec-syntax ([compose
      (syntax-rules .. ()
	([_ f] f)
	([_ gs .. f] (λ args
	    (call-with-values (λ () (apply f args))
			      (compose gs ..))
	    ))
	)])
      (compose . fs)
      ))

;; syntactic currying
;; a varargs versions
(def-syntax [kurry* . exps]
   (extract* (_) exps [
         (Λ ((x) terms)
	   (λ x  terms))
             []  exps]
))

;; version that can nest
(def-syntax [kurry' _ . exps]
   (extract* (_) exps [
         (Λ ((x) terms)
          (λ (x) terms))
             []  exps]
))

(def-syntax [kurry . exps]
   (kurry' _ . exps))

;; define reifiable syntax-rules object (via LISP's #'=syntax)
(def-syntax define-syntax-rules (syntax-rules (syntax)
 ;; exp0 is a syntax transformer
 ([_ (id0 #'trf) (lit ...) ([id . args] . exps) ...]
  (begin (def-syntax id0 (syntax-rules (lit ...)
	   ([id . args] . exps) ...))
   (def-syntax syntax (let-syntax ([stx syntax])
	(syntax-rules (id0 lit ...)
	   ;; return it as a syntax object
	   ([syntax id0] trf)
	   ;; reify it as a value, assume
	   ;; SYNTAX is redefined to handle it
	   ([syntax (id0)] #'trf)
	   ([syntax . r] (stx . r))
	   )))
   ))
 ([_ (id0 exp0) (lit ...) ([id . args] . exps) ...]
  (begin (def-syntax id0 (syntax-rules (lit ...)
	   ([id . args] . exps) ...))
   (def-syntax syntax (let-syntax ([stx syntax])
	(syntax-rules (id0 lit ...)
	   ([syntax id0] exp0)
	   ([syntax . r] (stx . r))
	   )))
   ))
 ([_ (id0 exp0) ell lits ([id . args] . exps) ...]
  (begin (def-syntax id0 (syntax-rules ell lits
	   ([id . args] . exps) ...))
   (def-syntax syntax (let-syntax ([stx syntax])
	(syntax-rules (id0 . lits)
	   ([syntax id0] exp0)
	   ([syntax . r] (stx . r))
	   )))
   ))
 ))
(define-syntax defs-syntax define-syntax-rules)



;; ala Clojure, stick _ at the end, is not manifest
(def-syntax ->' (syntax-rules ()
 ([_ fa] fa)
 ([_ f (fa ...) . fb]
  (->' (fa ... f) . fb))
 ))
;; ala Clojure, stick _ as the first arg, is not manifest
(def-syntax -> (syntax-rules ()
 ([_ fa] fa)
 ([_ f (fa args ...) . fb]
  (-> (fa f args ...) . fb))
 ))

;; explicitly-named anaphora versions of the above
;; three macros th is duplicated
(def-syntax ->> (syntax-rules ()
 ([_ th fa] fa)
 ([_ th fa . fb]
     (let-syntax ([th fa])
	(->> th . fb)))
   ))
(def-syntax =>> (syntax-rules ()
 ([_ th fa] fa)
 ([_ th fa . fb]
     (let ([th fa])
	(=>> th . fb)))
   ))
(def-syntax ~>> (syntax-rules ()
 ([_ th fa] fa)
 ([_ th fa . fb]
     (let ([th fa])
	(and th (~>> th . fb))))
   ))



;; split the rest argument list into two lists, one part coming
;; before the || and the other part coming after. stick each part
;; into first and second argument of [[k]], respectively
(def-syntax split (syntax-rules (XXX)
 ([_ (k fst [snd ...] . r) XXX  . rest] (k fst [snd ... . rest] . r))
 ([_ (k [fst ...] snd . r) x . rest]   (split (k [fst ... x] snd . r) . rest))
 ))

;; auto-manifest, properly nesting versions
;; redefine identifiers from slfs (third argument)
;; to refer to the recursive definitions  (fourth argument)
;; scoped under anaphoric redefinitions from the first argument (ids)

;; GOOD VERSION
(def-syntax redefine-thyself* (syntax-rules ()
 ([_ 2 ids syms (slf0 slf ...) (rec0 rec ...) (recx 1 _ . body)]
  (letrec-syntax ([slf0 (Λ ts
    (extract* ids ts [(Λ (all terms) (split (rec0 [] [] . terms) . all)) [] ts])
   )]
		  [slf (Λ ts
    (extract* ids ts [(Λ (all terms) (split (rec [] [] . terms) . all)) [] ts])
   )] ...)
    (extract* syms (body rec ...) ([Λ (ss (ts . tt))
                                  (rec0 1 ss . ts)]
    		() (body rec ...)))
    ;(rec0 1 syms . body)
    ; ((syntax-rules (rec0)
    ;   ([_ (rec0 1 _ . as)] (rec0 1 syms . as))
    ;   ([_ . bs] (begin . bs))
    ;   ) . body)
  ))
 ([_ 2 ids syms (slf ...) (rec ...) . body]
  (letrec-syntax ([slf (Λ ts
    (extract* ids ts [(Λ (all terms) (split (rec [] [] . terms) . all)) [] ts])
   )] ...)
  ;(let-syntax ([rec (Λ' ;([1 _ . r] '(rec 1 syms . r))
  ;		        (args (rec . args))
  ;			)] ...)
     . body;)
  ))
 ([_ 1 ids (slf ...) (rec ...) . body]
  ;; XXX redefine self, must be letrec-syntax here, contrary to Oleg
  (letrec-syntax ([slf (Λ ts
    (extract* ids ts
       ;; capture anaphoric pronouns
       [(Λ (all terms)
	   (split (rec [] [] . terms) . all))
        [] ts])
   )] ...) . body))
 ([_ (ids ...) 2 slfs recs . body]
  (redefine-thyself* 2 (ids ... XXX . slfs) (ids ...) slfs recs . body))
 ([_ (ids ...) [] slfs recs . body]
  (redefine-thyself* 1 (ids ... XXX . slfs) slfs recs . body))
 ))

;; define a set of 3 macros that are aware of several common
;; anaphoric pronouns, which are lexically scoped by each
;; of the macros. a key insight is the [redefine-thyself*]
;; which redefines the macro itself to refer to the new,
;; redefined occurrence of the anaphoric pronouns.
(def-syntax [define-anaphora (thy ...) (n rd rl) ...]
 (let-syntax ([K (syntax-rules .. ()
 ([_ (rb) names rdefs ([name rdef rules] ..)]
   (let-syntax-rule ([rb (k a b c _ . d)]
		         (k a b c rdefs . d))
   ;(let-syntax ([rb rdefs])
    ;; this is where it begins
    (letrec-syntax ([rdef rules] ..)
      (begin
	 (def-syntax [name . fs]
	      (extract* (thy ... XXX . names) fs
		 [(Λ (all body)
		    (split (rdef [] [] . body) . all))
                  [] fs]
		 )) ..
	))
      ))
    )])
    (extract* (recursive-bindings) (rl ...)
       [K [] (n ...) (rd ...) ([n rd rl] ...)])
 ))

;; simple version of threading
(define-anaphora (_ _')
   (>>- rec1 (syntax-rules ()
		([_ _ x fa] fa)
		([_ (thy thy') slfs fa . fb]
		 (let-syntax ([thy' thy]
			      [thy fa])
		    ;(recursive-bindings
		     (redefine-thyself* (thy thy') [] slfs (rec1 rec2 rec3);[]
		       (rec1 (thy thy') slfs . fb)
		       );)
		    ))
		))
   (>>= rec2 (syntax-rules ()
		([_ _ x fa] fa)
		([_ (thy thy') slfs fa . fb]
		 (let ([thy' thy]
		       [thy fa])
		    (redefine-thyself* (thy thy') [] slfs (rec1 rec2 rec3) ;recursive-bindings
		       (rec2 (thy thy') slfs . fb)
		       )
		    ))
		))
   (>>~ rec3 (syntax-rules ()
		([_ _ x fa] fa)
		([_ (thy thy') slfs fa . fb]
		 (let ([thy' thy]
		       [thy fa])
		    (redefine-thyself* (thy thy') [] slfs (rec1 rec2 rec3) ;recursive-bindings
		       (and thy (rec3 (thy thy') slfs . fb))
		       )
		    ))
		))
   )

(def-syntax [\>>- . body] (λ (arg) (>>- arg . body)))
(def-syntax [\>>= . body] (λ (arg) (>>= arg . body)))
(def-syntax [\>>~ . body] (λ (arg) (>>~ arg . body)))



(def-syntax type (syntax-rules ()
 ([_ 3 n k] (k type :unknown))
 ([_ n k] (k :unknown))
 ))

(def-syntax [ty-trf type ty' n]
   (syntax-rules (n)
      ;([_ (op . args) k] (op ty' k . args))
      ([_ n k] (k type))
      ([_ . r] (ty' . r))
      ))
; generate an algebraic operator transformer [[op]] that
; recognizes [[x]] in its arguments and rewrites into
; [[opo]] if found, or else rewrites into [[opd]]
(def-syntax [op-trf opo opd x]
  (letrec-syntax ([op (syntax-rules .. (x)
     ([_ "1" (c ..) x . y] (opo c .. x . y))     ; x is found
     ([_ "1" (c ..) y . z] (op "1" (c .. y) . z))  ; x not found - save y
     ([_ "1" c] (opd . c))                       ; no x at all
     ([_ a . as] (op "1" [] a . as))             ; start it
     ([_] opd)                                 ; no args: default
     )])
     op))

(def-syntax [ty-trf' typ ty pty n]
   (syntax-rules .. (n begin)
      ([_ 3 n k]               (k ty typ))
      ([_ 3 (begin bs .. b) k] (ty 3 b k))
      ([_ 3 (op . os) k]       (op ty 5 k op . os))
      ([_ 3 . r]               (pty 3 . r))
      ([_ n k]               (k typ))
      ([_ (begin bs .. b) k] (ty b k))
      ([_ (op . os) k]       (op ty 4 k op . os))
      ([_ . r]        [pty . r])
      ))
(def-syntax [op-trf' opo opd typ ty pty n]
  (letrec-syntax ([op (syntax-rules .. (n ty)
     ([_ 1 (c ..) n . y] (opo c .. n . y))
     ([_ 1 (c ..) y . z] (op 1 (c .. y) . z))
     ([_ 1 cs]           (opd . cs))
     ;retrieve the type
     ([_ 2 k cs n . y]     (k typ))
     ([_ 2 k (c ..) y . z] (op 2 k (c .. y) . z))
     ([_ 2 k cs]           (pty cs k))
     ;([_ 2 k (c . cs)]      (opd ty k opd . cs));(k unknown:)
     ([_ 3 k cs n . y]     (k ty typ))
     ([_ 3 k (c ..) y . z] (op 3 k (c .. y) . z))
     ([_ 3 k cs]           (pty 3 cs k))
     ; dispatch
     ([_ ty 5 k o . os]     (op 3 k [] o . os))
     ([_ ty 4 k o . os]     (op 2 k [] o . os))
     ([_ o . os]            (op 1 [] o . os))
     ([_] opd)
     )])
     op))

(def-syntax [with-protocol (syntax n) ell liter rules . body]
   (let-syntax ([syntax (syntax-rules (n)
	([_ (n . args)] ((syntax-rules ell liter . rules) . args))
	([_ . a] (syntax . a))
	)])
      . body))

(def-syntax [ident v] v)

;; DONE: make this extensible, library-style
(def-syntax [extend-ty-sugar lits clause ...]
  (def-syntax ty-sugar (let-syntax ([tysugar ty-sugar])
    (syntax-rules lits
       clause ...
       ([_ . args] (tysugar . args))
       ))
     ))

;; default: fail
(def-syntax [ty-sugar . args]
   (syntax-error ty-sugar: . args))

;; support vacuous type declarations
(extend-ty-sugar (redefine-thyself*)
([_ unknown: n _ (redefine-thyself* _ _ _ _ . ts)]
  (let () . ts))
)

;; fix/flo numbers
(extend-ty-sugar ()
 ([_ fix: n (ty syntax o+ o- o* o/
	       = < > <= >= 
	       neg min max ;minval maxval
	       zero? even? odd? positive? negative?
	       and lsh not or rsh xor
	       _ _ _ _ _
	       _ _
	       tofix toflo
	       toelong tollong tobignum
	       _ _ _
	       _ _ tostring
	       . _)
       . rs]
  (let-syntax ([ty (ty-trf fix: ty n)]
	       [o+ (op-trf +fx o+ n)]
	       [o- (op-trf -fx o- n)]
	       [o* (op-trf *fx o* n)]
	       [o/ (op-trf /fx o/ n)]
	       [=  (op-trf =fx = n)]
	       [<  (op-trf <fx < n)]
	       [>  (op-trf >fx > n)]
	       [<= (op-trf <=fx <= n)]
	       [>= (op-trf >=fx >= n)]
	       [neg (op-trf negfx neg n)]
	       [min (op-trf minfx min n)]
	       [max (op-trf maxfx max n)]
	       ;[minval (op-trf minvalfx minval n)]
	       ;[maxval (op-trf maxvalfx maxval n)]
	       [zero? (op-trf zerofx? zero? n)]
	       [even? (op-trf evenfx? even? n)]
	       [odd? (op-trf oddfx? odd? n)]
	       [positive? (op-trf positivefx? positive? n)]
	       [negative? (op-trf negativefx? negative? n)]
	       [and (op-trf bit-and and n)]
	       [lsh (op-trf bit-lsh lsh n)]
	       [not (op-trf bit-not not n)]
	       [or (op-trf bit-or or n)]
	       [rsh (op-trf bit-rsh rsh n)]
	       [xor (op-trf bit-xor xor n)]
	       [tofix (op-trf ident tofix n)]
	       [toflo (op-trf fixnum->flonum toflo n)]
	       [toelong (op-trf fixnum->elong toelong n)]
	       [tollong (op-trf fixnum->llong tollong n)]
	       [tobignum (op-trf fixnum->bignum tobignum n)]
	       [tostring (op-trf number->string tostring n)]
	       )
     . rs))
 ([_ flo: n (ty syntax o+ o- o* o/
	       = < > <= >=
	       neg min max ;_ _
	       zero? even? odd? positive? negative?
	       _ _ _ _ _ _
	       _ _ _ _ _
	       _ _
	       tofix toflo
	       toelong tollong tobignum
	       _ _ _
	       _ _ tostring
	       . _)
       . rs]
  (let-syntax ([ty (ty-trf flo: ty n)]
	       [o+ (op-trf +fl o+ n)]
	       [o- (op-trf -fl o- n)]
	       [o* (op-trf *fl o* n)]
	       [o/ (op-trf /fl o/ n)]
	       [=  (op-trf =fl = n)]
	       [<  (op-trf <fl < n)]
	       [>  (op-trf >fl > n)]
	       [<= (op-trf <=fl <= n)]
	       [>= (op-trf >=fl >= n)]
	       [neg (op-trf negfl neg n)]
	       [min (op-trf minfl min n)]
	       [max (op-trf maxfl max n)]
	       ;[minval (op-trf minvalfx minfl n)]
	       ;[maxval (op-trf maxvalfx maxvalfl n)]
	       [zero? (op-trf zerofl? zero? n)]
	       [even? (op-trf evenfl? even? n)]
	       [odd? (op-trf oddfl? odd? n)]
	       [positive? (op-trf positivefl? positive? n)]
	       [negative? (op-trf negativefl? negative? n)]
	       [tofix (op-trf flonum->fixnum tofix n)]
	       [toflo (op-trf ident toflo n)]
	       [toelong (op-trf flonum->elong toelong n)]
	       [tollong (op-trf flonum->llong tollong n)]
	       [tobignum (op-trf flonum->bignum tobignum n)]
	       [tostring (op-trf real->string tostring n)]
	       )
     . rs))
 )
;; a version supporting type info propagation
#;(extend-ty-sugar (redefine-thyself*)  ;; TODO not working yet
 ([_ fix: n (ty syntax o+ o- o* o/
	       = < > <= >=
	       neg min max 
	       zero? even? odd? positive? negative?
	       and lsh not or rsh xor
	       _1 _2 _3 _4 _5
	       _6 _7
	       tofix toflo
	       toelong tollong tobignum
	       _11 _12 _13
	       _14 _15 tostring
	       . _0)
        (redefine-thyself* _ [] slfs recs . ts)]
  (let-syntax ([pty ty])
  (letrec-syntax ([ty (ty-trf' fix: ty pty n)])
  (let-syntax ([o+ (op-trf' +fx o+ fix: ty pty n)]
	       [o- (op-trf' -fx o- fix: ty pty n)]
	       [o* (op-trf' *fx o* fix: ty pty n)]
	       [o/ (op-trf' /fx o/ flo: ty pty n)]
	       [=  (op-trf =fx = n)]
	       [<  (op-trf <fx < n)]
	       [>  (op-trf >fx > n)]
	       [<= (op-trf <=fx <= n)]
	       [>= (op-trf >=fx >= n)]
	       [neg (op-trf negfx neg n)]
	       [min (op-trf minfx min n)]
	       [max (op-trf maxfx max n)]
	       [zero? (op-trf zerofx? zero? n)]
	       [even? (op-trf evenfx? even? n)]
	       [odd? (op-trf oddfx? odd? n)]
	       [positive? (op-trf positivefx? positive? n)]
	       [negative? (op-trf negativefx? negative? n)]
	       [and (op-trf bit-and and n)]
	       [lsh (op-trf bit-lsh lsh n)]
	       [not (op-trf bit-not not n)]
	       [or (op-trf bit-or or n)]
	       [rsh (op-trf bit-rsh rsh n)]
	       [xor (op-trf bit-xor xor n)]
	       [tofix (op-trf ident tofix n)]
	       [toflo (op-trf fixnum->flonum toflo n)]
	       [toelong (op-trf fixnum->elong toelong n)]
	       [tollong (op-trf fixnum->llong tollong n)]
	       [tobignum (op-trf ident tobignum n)]
	       [tostring (op-trf number->string tostring n)]
	       )
     (redefine-thyself* (ty syntax o+ o- o* o/
	       = < > <= >=
	       neg min max
	       zero? even? odd? positive? negative?
	       and lsh not or rsh xor
	       _1 _2 _3 _4 _5
	       _6 _7
	       tofix toflo
	       toelong tollong tobignum
	       _11 _12 _13
	       _14 _15 tostring
	       . _0)
	2 slfs recs . ts))
  )))
 ([_ flo: n (ty syntax o+ o- o* o/
	       = < > <= >=
	       neg min max
	       zero? even? odd? positive? negative?
	       _1 _2 _3 _4 _5 _6
	       _11 _12 _13 _14 _15
	       _16 _17
	       tofix toflo
	       toelong tollong tobignum
	       _21 _22 _23
	       _24 _25 tostring
	       . _0)
       (redefine-thyself* _ [] slfs recs . ts)]
  (let-syntax ([pty ty])
  (letrec-syntax ([ty (ty-trf' flo: ty pty n)])
  (let-syntax ([o+ (op-trf' +fl o+ flo: ty pty n)]
	       [o- (op-trf' -fl o- flo: ty pty n)]
	       [o* (op-trf' *fl o* flo: ty pty n)]
	       [o/ (op-trf' /fl o/ flo: ty pty n)]
	       [=  (op-trf =fl = n)]
	       [<  (op-trf <fl < n)]
	       [>  (op-trf >fl > n)]
	       [<= (op-trf <=fl <= n)]
	       [>= (op-trf >=fl >= n)]
	       [neg (op-trf negfl neg n)]
	       [min (op-trf minfl min n)]
	       [max (op-trf maxfl max n)]
	       [zero? (op-trf zerofl? zero? n)]
	       [even? (op-trf evenfl? even? n)]
	       [odd? (op-trf oddfl? odd? n)]
	       [positive? (op-trf positivefl? positive? n)]
	       [negative? (op-trf negativefl? negative? n)]
	       [tofix (op-trf flonum->fixnum tofix n)]
	       [toflo (op-trf ident toflo n)]
	       [toelong (op-trf flonum->elong toelong n)]
	       [tollong (op-trf flonum->llong tollong n)]
	       [tobignum (op-trf inexact->exact tobignum n)]
	       [tostring (op-trf real->string tostring n)]
	       )
     (redefine-thyself* (ty syntax o+ o- o* o/
	       = < > <= >=
	       neg min max
	       zero? even? odd? positive? negative?
	       _1 _2 _3 _4 _5 _6
	       _11 _12 _13 _14 _15
	       _16 _17
	       tofix toflo
	       toelong tollong tobignum
	       _21 _22 _23
	       _24 _25 tostring
	       . _0)
	 2 slfs recs . ts))
  )))
 )

;; Bigloo fixpoint numbers
(extend-ty-sugar ()
 ([_ elong: n (ty syntax o+ o- o* o/
		 = < > <= >=
		 neg _ _ ;minval maxval
		 zero? even? odd? positive? negative?
		 and lsh not or rsh xor
		 _ _ _ _ _
		 _ _
		 tofix toflo
		 toelong tollong tobignum
		 _ _ _
		 _ _ tostring
		 . _)
         . rs]
  (let-syntax ([ty (ty-trf elong: ty n)]
	       [o+ (op-trf +elong o+ n)]
	       [o- (op-trf -elong o- n)]
	       [o* (op-trf *elong o* n)]
	       [o/ (op-trf /elong o/ n)]
	       [=  (op-trf =elong = n)]
	       [<  (op-trf <elong < n)]
	       [>  (op-trf >elong > n)]
	       [<= (op-trf <=elong <= n)]
	       [>= (op-trf >=elong >= n)]
	       [neg (op-trf negelong neg n)]
	       ;[min (op-trf minelong min n)]
	       ;[max (op-trf maxelong max n)]
	       ;[minval (op-trf minvalelong minval n)]
	       ;[maxval (op-trf maxvalelong maxval n)]
	       [zero? (op-trf zeroelong? zero? n)]
	       [even? (op-trf evenelong? even? n)]
	       [odd? (op-trf oddelong? odd? n)]
	       [positive? (op-trf positiveelong? positive? n)]
	       [negative? (op-trf negativeelong? negative? n)]
	       [and (op-trf bit-andelong and n)]
	       [lsh (op-trf bit-lshelong lsh n)]
	       [not (op-trf bit-notelong not n)]
	       [or (op-trf bit-orelong or n)]
	       [rsh (op-trf bit-rshelong rsh n)]
	       [xor (op-trf bit-xorelong xor n)]
	       [tofix (op-trf elong->fixnum tofix n)]
	       [toflo (op-trf elong->flonum toflo n)]
	       [toelong (op-trf ident toelong n)]
	       [tollong (op-trf elong->llong tollong n)]
	       [tobignum (op-trf elong->bignum tobignum n)]
	       [tostring (op-trf elong->string tostring n)]
	       )
     . rs))
 ([_ llong: n (ty syntax o+ o- o* o/
		 = < > <= >=
		 neg _ _ ;minval maxval
		 zero? even? odd? positive? negative?
		 and lsh not or rsh xor
		 _ _ _ _ _
		 _ _
		 tofix toflo
		 toelong tollong tobignum
		 _ _ _
		 _ _ tostring
		 . _)
      . rs]
  (let-syntax ([ty (ty-trf llong: ty n)]
	       [o+ (op-trf +llong o+ n)]
	       [o- (op-trf -llong o- n)]
	       [o* (op-trf *llong o* n)]
	       [o/ (op-trf /llong o/ n)]
	       [=  (op-trf =llong = n)]
	       [<  (op-trf <llong < n)]
	       [>  (op-trf >llong > n)]
	       [<= (op-trf <=llong <= n)]
	       [>= (op-trf >=llong >= n)]
	       [neg (op-trf negllong neg n)]
	       ;[min (op-trf minllong min n)]
	       ;[max (op-trf maxllong max n)]
	       ;[minval (op-trf minvalllong minval n)]
	       ;[maxval (op-trf maxvalllong maxval n)]
	       [zero? (op-trf zerollong? zero? n)]
	       [even? (op-trf evenllong? even? n)]
	       [odd? (op-trf oddllong? odd? n)]
	       [positive? (op-trf positivellong? positive? n)]
	       [negative? (op-trf negativellong? negative? n)]
	       [and (op-trf bit-andllong and n)]
	       [lsh (op-trf bit-lshllong lsh n)]
	       [not (op-trf bit-notllong not n)]
	       [or (op-trf bit-orllong or n)]
	       [rsh (op-trf bit-rshllong rsh n)]
	       [xor (op-trf bit-xorllong xor n)]
	       [tofix (op-trf llong->fixnum tofix n)]
	       [toflo (op-trf llong->flonum toflo n)]
	       [toelong (op-trf llong->elong toelong n)]
	       [tollong (op-trf ident tollong n)]
	       [tobignum (op-trf llong->bignum tobignum n)]
	       [tostring (op-trf llong->string tostring n)]
	       )
     . rs))
 ([_ bignum: n (ty syntax o+ o- o* o/
		  = < > <= >=
		  neg min max ;_ _
		  zero? even? odd? positive? negative?
		  and lsh not or rsh xor
		  _ _ _ _ _
		  _ _
		  tofix toflo
		  toelong tollong tobignum
		  _ _ _
		  _ _ tostring
		  . _)
      . rs]
  (let-syntax ([ty (ty-trf bignum: ty n)]
	       [o+ (op-trf +bx o+ n)]
	       [o- (op-trf -bx o- n)]
	       [o* (op-trf *bx o* n)]
	       [o/ (op-trf /bx o/ n)]
	       [=  (op-trf =bx = n)]
	       [<  (op-trf <bx < n)]
	       [>  (op-trf >bx > n)]
	       [<= (op-trf <=bx <= n)]
	       [>= (op-trf >=bx >= n)]
	       [neg (op-trf negbx neg n)]
	       [min (op-trf minbx min n)]
	       [max (op-trf maxbx max n)]
	       ;[minval (op-trf minvalllong minval n)]
	       ;[maxval (op-trf maxvalllong maxval n)]
	       [zero? (op-trf zerobx? zero? n)]
	       [even? (op-trf evenbx? even? n)]
	       [odd? (op-trf oddbx? odd? n)]
	       [positive? (op-trf positivebx? positive? n)]
	       [negative? (op-trf negativebx? negative? n)]
	       [tofix (op-trf bignum->fixnum tofix n)]
	       [toflo (op-trf bignum->flonum toflo n)]
	       [toelong (op-trf bignum->elong toelong n)]
	       [tollong (op-trf bignum->llong tollong n)]
	       [tobignum (op-trf ident tobignum n)]
	       [tostring (op-trf bignum->string tostring n)]
	       )
     . rs))
 )
;; a version supporting type info propagation
#;(extend-ty-sugar (redefine-thyself*)
 ([_ elong: n (ty syntax o+ o- o* o/
		 = < > <= >=
		 neg _1 _2
		 zero? even? odd? positive? negative?
		 and lsh not or rsh xor
		 _3 _4 _5 _6 _7
		 _8 _9
		 tofix toflo
		 toelong tollong tobignum
		 _10 _11 _12
		 _13 _14 tostring
		 . _0)
         (redefine-thyself* _ [] slfs recs . ts)]
  (let-syntax ([pty ty])
  (letrec-syntax ([ty (ty-trf' elong: ty pty n)])
  (let-syntax ([o+ (op-trf' +elong o+ elong: ty pty n)]
	       [o- (op-trf' -elong o- elong: ty pty n)]
	       [o* (op-trf' *elong o* elong: ty pty n)]
	       [o/ (op-trf' /elong o/ elong: ty pty n)]
	       [=  (op-trf =elong = n)]
	       [<  (op-trf <elong < n)]
	       [>  (op-trf >elong > n)]
	       [<= (op-trf <=elong <= n)]
	       [>= (op-trf >=elong >= n)]
	       [neg (op-trf negelong neg n)]
	       [zero? (op-trf zeroelong? zero? n)]
	       [even? (op-trf evenelong? even? n)]
	       [odd? (op-trf oddelong? odd? n)]
	       [positive? (op-trf positiveelong? positive? n)]
	       [negative? (op-trf negativeelong? negative? n)]
	       [and (op-trf' bit-andelong and elong: ty pty n)]
	       [lsh (op-trf' bit-lshelong lsh elong: ty pty n)]
	       [not (op-trf' bit-notelong not elong: ty pty n)]
	       [or (op-trf' bit-orelong or elong: ty pty n)]
	       [rsh (op-trf' bit-rshelong rsh elong: ty pty n)]
	       [xor (op-trf' bit-xorelong xor elong: ty pty n)]
	       [tofix (op-trf elong->fixnum tofix n)]
	       [toflo (op-trf elong->flonum toflo n)]
	       [toelong (op-trf ident toelong n)]
	       [tollong (op-trf elong->llong tollong n)]
	       [tostring (op-trf elong->string tostring n)]
	       )
     (redefine-thyself* (ty syntax o+ o- o* o/
		 = < > <= >=
		 neg _1 _2
		 zero? even? odd? positive? negative?
		 and lsh not or rsh xor
		 _3 _4 _5 _6 _7
		 _8 _9
		 tofix toflo
		 toelong tollong tobignum
		 _10 _11 _12
		 _13 _14 tostring
		 . _0)
	2 slfs recs . ts))
  )))
 ([_ llong: n (ty syntax o+ o- o* o/
		 = < > <= >=
		 neg _1 _2 
		 zero? even? odd? positive? negative?
		 and lsh not or rsh xor
		 _3 _4 _5 _6 _7
		 _8 _9
		 tofix toflo
		 toelong tollong tobignum
		 _10 _11 _12
		 _13 _14 tostring
		 . _0)
       (redefine-thyself* _ [] slfs recs . ts)]
  (let-syntax ([ty pty])
  (letrec-syntax ([ty (ty-trf' llong: ty pty n)])
  (let-syntax ([o+ (op-trf' +llong o+ llong: ty pty n)]
	       [o- (op-trf' -llong o- llong: ty pty n)]
	       [o* (op-trf' *llong o* llong: ty pty n)]
	       [o/ (op-trf' /llong o/ llong: ty pty n)]
	       [=  (op-trf =llong = n)]
	       [<  (op-trf <llong < n)]
	       [>  (op-trf >llong > n)]
	       [<= (op-trf <=llong <= n)]
	       [>= (op-trf >=llong >= n)]
	       [neg (op-trf negllong neg n)]
	       [zero? (op-trf zerollong? zero? n)]
	       [even? (op-trf evenllong? even? n)]
	       [odd? (op-trf oddllong? odd? n)]
	       [positive? (op-trf positivellong? positive? n)]
	       [negative? (op-trf negativellong? negative? n)]
	       [and (op-trf' bit-andllong and llong: ty pty n)]
	       [lsh (op-trf' bit-lshllong lsh llong: ty pty n)]
	       [not (op-trf' bit-notllong not llong: ty pty n)]
	       [or (op-trf' bit-orllong or llong: ty pty n)]
	       [rsh (op-trf' bit-rshllong rsh llong: ty pty n)]
	       [xor (op-trf' bit-xorllong xor llong: ty pty n)]
	       [tofix (op-trf llong->fixnum tofix n)]
	       [toflo (op-trf llong->flonum toflo n)]
	       [toelong (op-trf' llong->elong toelong elong: ty pty n)]
	       [tollong (op-trf ident tollong n)]
	       [tostring (op-trf llong->string tostring n)]
	       )
     (redefine-thyself* (ty syntax o+ o- o* o/
		 = < > <= >=
		 neg _1 _2
		 zero? even? odd? positive? negative?
		 and lsh not or rsh xor
		 _3 _4 _5 _6 _7
		 _8 _9
		 tofix toflo
		 toelong tollong tobignum
		 _10 _11 _12
		 _13 _14 tostring
		 . _0)
	2 slfs recs . ts))
  )))
 ([_ bignum: n (ty syntax o+ o- o* o/
		  = < > <= >=
		  neg min max
		  zero? even? odd? positive? negative?
		  and lsh not or rsh xor
		  _1 _2 _3 _4 _5
		  _6 _7
		  tofix toflo
		  toelong tollong tobignum
		  _8 _9 _10
		  _11 _12 tostring
		  . _0)
      (redefine-thyself* _ [] slfs recs . ts)]
  (let-syntax ([ty pty])
  (letrec-syntax ([ty (ty-trf' bignum: ty pty n)]
  (let-syntax ([o+ (op-trf' +bx o+ bignum: ty pty n)]
	       [o- (op-trf' -bx o- bignum: ty pty n)]
	       [o* (op-trf' *bx o* bignum: ty pty n)]
	       [o/ (op-trf' /bx o/ bignum: ty pty n)]
	       [=  (op-trf =bx = n)]
	       [<  (op-trf <bx < n)]
	       [>  (op-trf >bx > n)]
	       [<= (op-trf <=bx <= n)]
	       [>= (op-trf >=bx >= n)]
	       [neg (op-trf negbx neg n)]
	       [min (op-trf minbx min n)]
	       [max (op-trf maxbx max n)]
	       [zero? (op-trf zerobx? zero? n)]
	       [even? (op-trf evenbx? even? n)]
	       [odd? (op-trf oddbx? odd? n)]
	       [positive? (op-trf positivebx? positive? n)]
	       [negative? (op-trf negativebx? negative? n)]
	       [tostring (op-trf bignum->string tostring n)]
	       )
     (redefine-thyself* (ty syntax o+ o- o* o/
		  = < > <= >=
		  neg min max
		  zero? even? odd? positive? negative?
		  and lsh not or rsh xor
		  _1 _2 _3 _4 _5
		  _6 _7
		  tofix toflo
		  toelong tollong tobignum
		  _8 _9 _10
		  _11 _12 tostring
		  . _0)
	2 slfs recs . ts))
  )))
 ))

;; extended arithmetic
(extend-ty-sugar ()
 ([_ rat: n (ty syntax o+ o- o* o/
		  = < > <= >=
		  neg min max ;_ _
		  zero? even? odd? positive? negative?
		  and lsh not or rsh xor
		  _ _ _ _ _
		  _ _
		  tofix toflo
		  toelong tollong tobignum
		  _ _ _
		  _ _ tostring
		  . _)
      . rs]
  (let-syntax ([ty (ty-trf rat: ty n)]
	       [o+ (op-trf +rat o+ n)]
	       [o- (op-trf -rat o- n)]
	       [o* (op-trf *rat o* n)]
	       [o/ (op-trf /rat o/ n)]
	       [=  (op-trf $=r = n)]
	       [<  (op-trf $<r < n)]
	       [>  (op-trf $>r > n)]
	       [<= (op-trf $<=r <= n)]
	       [>= (op-trf $>=r >= n)]
	       [neg (op-trf r$neg neg n)]
	       [min (op-trf r$min min n)]
	       [max (op-trf r$max max n)]
	       [zero? (op-trf r$zero? zero? n)]
	       [even? (op-trf r$even? even? n)]
	       [odd? (op-trf r$odd? odd? n)]
	       [positive? (op-trf r$positive? positive? n)]
	       [negative? (op-trf r$negative? negative? n)]
	       [tofix (op-trf ratio->integer tofix n)];TODO
	       [toflo (op-trf ratio->number toflo n)]
	       [toelong (op-trf ratio->integer toelong n)];TODO
	       [tollong (op-trf ratio->integer tollong n)];TODO
	       [tobignum (op-trf ratio->integer tobignum n)];TODO
	       [tostring (op-trf ratio->string tostring n)];TODO
	       )
     . rs))
 ([_ cx: n (ty syntax o+ o- o* o/
		  = < > <= >=
		  neg min max ;_ _
		  zero? even? odd? positive? negative?
		  and lsh not or rsh xor
		  _ _ _ _ _
		  _ _
		  tofix toflo
		  toelong tollong tobignum
		  _ _ _
		  _ _ tostring
		  . _)
      . rs]
  (let-syntax ([ty (ty-trf cx: ty n)]
	       [o+ (op-trf +cx o+ n)]
	       [o- (op-trf -cx o- n)]
	       [o* (op-trf *cx o* n)]
	       [o/ (op-trf /cx o/ n)]
	       [=  (op-trf $=c = n)]
	       [<  (op-trf $<c < n)]
	       [>  (op-trf $>c > n)]
	       [<= (op-trf $<=c <= n)]
	       [>= (op-trf $>=c >= n)]
	       [neg (op-trf c$neg neg n)]
	       [min (op-trf c$min min n)]
	       [max (op-trf c$max max n)]
	       [zero? (op-trf c$zero? zero? n)]
	       [even? (op-trf c$even? even? n)]
	       [odd? (op-trf c$odd? odd? n)]
	       [positive? (op-trf c$positive? positive? n)]
	       [negative? (op-trf c$negative? negative? n)]
	       [tofix (op-trf complex->integer tofix n)];TODO
	       [toflo (op-trf complex->real toflo n)];TODO
	       [toelong (op-trf complex->integer toelong n)];TODO
	       [tollong (op-trf complex->integer tollong n)];TODO
	       [tobignum (op-trf complex->integer tobignum n)];TODO
	       [tostring (op-trf complex->string tostring n)];TODO
	       )
     . rs))
 ([_ dx: n (ty syntax o+ o- o* o/
		  = < > <= >=
		  neg min max ;_ _
		  zero? even? odd? positive? negative?
		  and lsh not or rsh xor
		  _ _ _ _ _
		  _ _
		  tofix toflo
		  toelong tollong tobignum
		  _ _ _
		  _ _ tostring
		  . _)
      . rs]
  (let-syntax ([ty (ty-trf dx: ty n)]
	       [o+ (op-trf +dx o+ n)]
	       [o- (op-trf -dx o- n)]
	       [o* (op-trf *dx o* n)]
	       [o/ (op-trf /dx o/ n)]
	       [=  (op-trf $=d = n)]
	       [<  (op-trf $<d < n)]
	       [>  (op-trf $>d > n)]
	       [<= (op-trf $<=d <= n)]
	       [>= (op-trf $>=d >= n)]
	       [neg (op-trf d$neg neg n)]
	       [min (op-trf d$min min n)]
	       [max (op-trf d$max max n)]
	       [zero? (op-trf d$zero? zero? n)]
	       [even? (op-trf d$even? even? n)]
	       [odd? (op-trf d$odd? odd? n)]
	       [positive? (op-trf d$positive? positive? n)]
	       [negative? (op-trf d$negative? negative? n)]
	       [tofix (op-trf dual->integer tofix n)];TODO
	       [toflo (op-trf dual->real toflo n)];TODO
	       [toelong (op-trf dual->integer toelong n)];TODO
	       [tollong (op-trf dual->integer tollong n)];TODO
	       [tobignum (op-trf dual->integer tobignum n)];TODO
	       [tostring (op-trf dual->string tostring n)];TODO
	       )
     . rs))
 )

;; Characters and ordinals
(extend-ty-sugar ()
 ([_ char: n (ty syntax _ _ _ _
		= < > <= >=
		_ _ _
		_ _ _ _ _
		_ _ _ _ _ _
		_ _ _ _ _
		_ _
		_ _
		_ _ _
		tochar towchar toint
		. _) . rs]
  (let-syntax ([ty (ty-trf char: ty n)]
	       [toint (op-trf char->integer toint n)]
	       [tochar (op-trf ident tochar n)]
	       [towchar (op-trf char->ucs2 towchar n)]
	       [=  (op-trf char=? = n)]
	       [<  (op-trf char<? < n)]
	       [>  (op-trf char>? > n)]
	       [<= (op-trf char<=? <= n)]
	       [>= (op-trf char>=? >= n)]) . rs)) 
 ([_ wchar: n (ty syntax _ _ _ _
		 = < > <= >=
		 _ _ _
		 _ _ _ _ _
		 _ _ _ _ _ _
		 _ _ _ _ _
		 _ _
		 _ _
		 _ _ _
		 tochar towchar toint
		 . _) . rs]
  (let-syntax ([ty (ty-trf wchar: ty n)]
	       [toint (op-trf ucs2->integer toint n)]
	       [tochar (op-trf ucs2->char tochar n)]
	       [towchar (op-trf ident towchar n)]
	       [=  (op-trf ucs2=? = n)]
	       [<  (op-trf ucs2<? < n)]
	       [>  (op-trf ucs2>? > n)]
	       [<= (op-trf ucs2<=? <= n)]
	       [>= (op-trf ucs2>=? >= n)]) . rs)) 
 ([_ int: n (ty syntax _ _ _ _
		   = < > <= >=
		   _ _ _
		   _ _ _ _ _
		   and lsh not or rsh xor
		   _ _ _ _ _
		   _ _
		   _ _
		   _ _ _
		   tochar towchar toint
		   _ _ tostring
		   . _) . rs]
  (let-syntax ([ty (ty-trf int: ty n)]
	       [toint (op-trf ident toint n)]
	       [tochar (op-trf integer->char tochar n)]
	       [towchar (op-trf integer->ucs2 towchar n)]
	       [and (op-trf bit-and and n)]
	       [lsh (op-trf bit-lsh lsh n)]
	       [not (op-trf bit-not not n)]
	       [or (op-trf bit-or or n)]
	       [rsh (op-trf bit-rsh rsh n)]
	       [xor (op-trf bit-xor xor n)]
	       [tostring (op-trf integer->string tostring n)]
	       ) . rs))
 )
;; Basic collection types
(extend-ty-sugar ()
 ([_ list: n (ty syntax _ _ _ _
		_ _ _ _ _
		_ _ _
		_ _ _ _ _
		_ _ _ _ _ _
		_copy _clone _length set! ref
		map for-each
		_ _
		_ _ _
		_ _ _
		tolist tovector tostring
		tostruct toucs2string toutf8string
		tomatrix toarray . _) . rs]
  (let-syntax ([ty (ty-trf list: ty n)]
	       [_copy (op-trf list-copy _copy n)]
	       [_clone (op-trf tree-copy _clone n)]
	       [_length (op-trf length _length n)]
	       [set! (op-trf list-set! set! n)]
	       [ref (op-trf list-ref ref n)]
	       ;[map (op-trf map map n)]
	       ;[for-each (op-trf for-each for-each n)]
	       [tolist (op-trf ident tolist n)]
	       [tovector (op-trf list->vector tovector n)]
	       [tostring (op-trf list->string tostring n)]
	       [tomatrix (op-trf (Λ (m)
			(list->vector (map list->vector m))
		) tomatrix n)]
	       [tostruct (op-trf list->struct tostruct n)]
	       [toucs2string (op-trf list->ucs2-string toucs2string n)]
	       [toutf8string (op-trf (Λ (l)
		   (ucs2-string->utf8-string (list->ucs2-string l))
		 ) toutf8string n)]
	       [toarray (op-trf (Λ (l)
		   (list->array (list-rank l) '#() l)
		 ) toarray n)]
	       )
     (with-protocol #'n … (:= .copy .clone .length ..)
	  [([_] n)
	   ([_ .copy] (_copy n))
	   ([_ .clone] (_clone n))
	   ([_ .length] (_length n))
	   ([_ (0)] (car n))
	   ([_ (1)] (cadr n))
	   ([_ (2)] (caddr n))
	   ([_ (3)] (cadddr n))
	   ([_ (idx)] (ref n idx))
	   ([_ (.. idx)] (take n (+ idx 1)))
	   ([_ (1 ..)] (cdr n))
	   ([_ (2 ..)] (cddr n))
	   ([_ (3 ..)] (cdddr n))
	   ([_ (4 ..)] (cddddr n))
	   ([_ (idx ..)] (list-tail n idx))
	   ([_ (s .. e)] (take (list-tail n s) (+ (- e s) 1)))
	   ([_ (idx):= val] (set! n idx val))
	   ] . rs)))
 ([_ vector: n (ty syntax _ _ _ _
	       _ _ _ _ _
	       _ _ _
	       _ _ _ _ _
	       _ _ _ _ _ _
	       _copy _clone _length set! ref
	       map for-each
	       _ _
	       _ _ _
	       _ _ _
	       tolist tovector _
	       _ _ _
	       tomatrix toarray . _) . rs]
  (let-syntax ([ty (ty-trf vector: ty n)]
	       [_copy (op-trf vector-copy _copy n)]
	       [_clone (op-trf copy-vector _clone n)] ;; TODO: deep copy
	       [_length (op-trf vector-length _length n)]
	       [set! (op-trf vector-set! set! n)]
	       [ref (op-trf vector-ref ref n)]
	       [map (op-trf vector-map map n)]
	       [for-each (op-trf vector-for-each for-each n)]
	       [tolist (op-trf vector->list tolist n)]
	       [tovector (op-trf ident tovector n)]
	       [tomatrix (op-trf ident tomatrix n)] ;; TODO add rank
	       [toarray (op-trf (Λ (v . dims)
		   (vector->array v '#() . dims)
		 ) toarray n)]
	       )
     (with-protocol #'n … (:= .copy .clone .length ..)
	  [([_] n)
	   ([_ .copy] (_copy n))
	   ([_ .clone] (_clone n (_length n)))
	   ([_ .clone s] (_clone n s))
	   ([_ .length] (_length n))
	   ([_ (idx)] (ref n idx))
	   ([_ (idx .. . end)] (_copy n idx . end))
	   ([_ (idx):= val] (set! n idx val))
	   ] . rs)))
 ([_ string: n (ty syntax _ _ _ _
	       = < > <= >=
	       _ _ _
	       _ _ _ _ _
	       _ _ _ _ _ _
	       _copy _clone _length set! ref
	       map for-each
	       tofix toflo
	       toelong tollong tobignum
	       _ _ _
	       tolist _ tostring
	       . _) . rs]
  (let-syntax ([ty (ty-trf string: ty n)]
	       [_copy (op-trf string-copy _copy n)]
	       ;[_clone (op-trf TODO _clone n)] ;; TODO: deep copy
	       [=  (op-trf string=? = n)]
	       [<  (op-trf string<? < n)]
	       [>  (op-trf string>? > n)]
	       [<= (op-trf string<=? <= n)]
	       [>= (op-trf string>=? >= n)]
	       [_length (op-trf string-length _length n)]
	       [set! (op-trf string-set! set! n)]
	       [ref (op-trf string-ref ref n)]
	       [map (op-trf string-map map n)]
	       [for-each (op-trf string-for-each for-each n)]
	       [tolist (op-trf string->list tolist n)]
	       [tofix (op-trf string->number tofix n)]
	       [toflo (op-trf string->real toflo n)]
	       [toelong (op-trf string->elong toelong n)]
	       [tollong (op-trf string->llong tollong n)]
	       [tobignum (op-trf string->bignum tobignum n)]
	       [tostring (op-trf ident tostring n)]
	       )
     (with-protocol #'n … (:= .copy .clone .length ..)
	  [([_] n)
	   ([_ .copy] (_copy n))
	   ;([_ .clone] (clone n))
	   ([_ .length] (_length n))
	   ([_ (idx)] (ref n idx))
	   ([_ (idx .. . end)] (substring n idx . end))
	   ([_ (idx):= val] (set! n idx val))
	   ] . rs)))
 )
;; SRFI-4 vectors
(def-syntax [extend-ty-sugar-vector tag _len _set _ref _tol _tov]
 (extend-ty-sugar ()
 ([_ tag n (ty syntax _1 _2 _3 _4
	       _5 _6 _7 _8 _9
	       _81 _82 _83
	       _91 _92 _93 _94 _95
	       _11 _12 _13 _14 _15 _16
	       _copy _clone _length set! ref
	       map for-each
	       _31 _32
	       _41 _42 _43
	       _51 _52 _53
	       tolist tovector _61
	       _71 _72 _73
	       tomatrix . _0) . rs]
  (let-syntax ([ty (ty-trf tag ty n)]
	       [_copy (op-trf (syntax-rules ()
		 ([_ v] (_tov (_tol v)))
		 ([_ v s e] (_tov (take
				  (list-tail
				     (_tol v)
				     s)
				  (+ s (- e) +1))
			       ))
		 ) _copy n)]
	       [_clone (op-trf (Λ (v n)
				  (_tov (take
				      (_tol v)
				      n
				    ))
				  ) _clone n)] ;; TODO: deep copy

	       [_length (op-trf _len _length n)]
	       [set! (op-trf _set set! n)]
	       [ref (op-trf _ref ref n)]
	       [map (op-trf (Λ (f v) (_tov (map f (_tol v)))
			    ) map n)]
	       [for-each (op-trf (Λ (f v)
				    (do ([i 0 (+1+ i)])
					((>= i (_len v)) '#?)
					(f (_ref v i))
					)) for-each n)]
	       [tolist (op-trf _tol tolist n)]
	       [tovector (op-trf ident tovector n)]
	       [tomatrix (op-trf ident tomatrix n)] ;; TODO add rank
	       )
     (with-protocol #'n … (:= .copy .clone .length ..)
	  [([_] n)
	   ([_ .copy] (_copy n))
	   ([_ .clone] (_clone n (_length n)))
	   ([_ .clone s] (_clone n s))
	   ([_ .length] (_length n))
	   ([_ (idx)] (ref n idx))
	   ([_ (idx .. . end)] (_copy n idx . end))
	   ([_ (idx):= val] (set! n idx val))
	   ] . rs)))
 ))

(extend-ty-sugar-vector s8vector:
   s8vector-length
   s8vector-set!
   s8vector-ref
   s8vector->list
   list->s8vector)

(extend-ty-sugar-vector u8vector:
   u8vector-length
   u8vector-set!
   u8vector-ref
   u8vector->list
   list->u8vector)

(extend-ty-sugar-vector s16vector:
   s16vector-length
   s16vector-set!
   s16vector-ref
   s16vector->list
   list->s16vector)

(extend-ty-sugar-vector u16vector:
   u16vector-length
   u16vector-set!
   u16vector-ref
   u16vector->list
   list->u16vector)

(extend-ty-sugar-vector s32vector:
   s32vector-length
   s32vector-set!
   s32vector-ref
   s32vector->list
   list->s32vector)

(extend-ty-sugar-vector u32vector:
   u32vector-length
   u32vector-set!
   u32vector-ref
   u32vector->list
   list->u32vector)

(extend-ty-sugar-vector s64vector:
   s64vector-length
   s64vector-set!
   s64vector-ref
   s64vector->list
   list->s64vector)

(extend-ty-sugar-vector u64vector:
   u64vector-length
   u64vector-set!
   u64vector-ref
   u64vector->list
   list->u64vector)

(extend-ty-sugar-vector f32vector:
   f32vector-length
   f32vector-set!
   f32vector-ref
   f32vector->list
   list->f32vector)

(extend-ty-sugar-vector f64vector:
   f64vector-length
   f64vector-set!
   f64vector-ref
   f64vector->list
   list->f64vector)


;; 2-dimensional arrays, built out of vectors
(extend-ty-sugar ()
 ([_ matrix: n (ty syntax _ _ _ _
	       _ _ _ _ _
	       _ _ _
	       _ _ _ _ _
	       _ _ _ _ _ _
	       _copy _clone _length set! ref
	       map for-each
	       _ _
	       _ _ _
	       _ _ _
	       tolist tovector _
	       _ _ _
	       tomatrix . _) . rs]
  (let-syntax ([ty (ty-trf matrix: ty n)]
	       [_copy (op-trf vector-copy _copy n)]
	       [_clone (op-trf copy-vector _clone n)]
	       [_length (op-trf (Λ (x) (reduce $+ 0
					  (map vector-length
					     (vector->list x))))
			   _length n)]
	       [ref (op-trf (Λ (x i j)
			       (if [and (>= i 0) (>= j 0)
                                        (< j (vector-length x))
				        (< i (vector-length (vector-ref x j)))]
			       (vector-ref (vector-ref x j) i)
			       '#?))
		       ref n)]
	       [set! (op-trf (Λ (x i j val)
				(if [and (>= i 0) (>= j 0)
					 (< j (vector-length x))
					 (< i (vector-length (vector-ref x j)))]
			       (vector-set! (vector-ref x j) i val)
			       '#?))
			set! n)]
	       ;[map (op-trf vector-map map n)]
	       ;[for-each (op-trf vector-for-each for-each n)]
	       [tolist (op-trf (Λ (m)
			(vector->list (vector-map vector->list m))
		) tolist n)]
	       [tovector (op-trf (Λ (m)
			(list->vector
			   (apply append
			      (vector->list
				 (vector-map vector->list m))))
		) tovector n)]
	       [tomatrix (op-trf ident tomatrix n)]
	       )
     (with-protocol #'n … (:= .copy .clone .length .. .rows .cols)
	  [([_] n)
	   ([_ .copy] (_copy n))
	   ([_ .clone] (_clone n (_length n)))
	   ([_ .clone s] (_clone n s))
	   ([_ .length] (_length n))
           ([_ .rows] (vector-length n))
           ([_ .cols] (vector-length (vector-ref n 0)))
           ([_ .cols i] (vector-length (vector-ref n i)))
	   ([_ (idx .. . end)] (_copy n idx . end))
	   ([_ ((i j))] (ref n i j))
	   ([_ ((i j)):= val] (set! n i j val))
	   ([_ (i j)] (vector-ref (vector-ref n i) j))
	   ([_ (i j):= val] (vector-set! (vector-ref n i) j val))
	   ([_ ((i))] (if (< i (vector-length n))
			  (vector-ref n i)
			  #false))
	   ([_ ((i)):= val] (if (< i (vector-length n))
				(vector-set! n i val)
				#false))
	   ([_ (i)] (vector-ref n i))
	   ([_ (i):= val] (vector-set! n i val))
	   ] . rs)))
 )

;; Bigloo structs
(extend-ty-sugar ()
  ([_ struct: n (ty syntax _ _ _ _
	       _ _ _ _ _
	       _ _ _
	       _ _ _ _ _
	       _ _ _ _ _ _
	       _copy _clone _length set! ref
	       map for-each
	       _ _
	       _ _ _
	       _ _ _
	       tolist _ _
	       tostruct . _) . rs]
  (let-syntax ([ty (ty-trf struct: ty n)]
	       ;[_copy (op-trf TODO _copy n)]
	       ;[_clone (op-trf TODO _clone n)] ;; TODO: deep copy
	       [_length (op-trf struct-length _length n)]
	       [set! (op-trf struct-set! set! n)]
	       [ref (op-trf struct-ref ref n)]
	       [map (op-trf struct-map map n)]
	       [for-each (op-trf struct-for-each for-each n)]
	       [tolist (op-trf struct->list tolist n)]
	       [tostruct (op-trf ident tostruct n)]
	       )
     (with-protocol #'n … (:= .copy .clone .length .. .key)
	  [([_] n)
	   ;([_ .copy] (_copy n))
	   ;([_ .clone] (_clone n))
	   ([_ .length] (_length n))
	   ([_ .key] (struct-key n))
	   ([_ (idx)] (ref n idx))
	   ;([_ (idx ..)] (list-tail n idx))
	   ([_ (idx):= val] (set! n idx val))
	   ] . rs)))
  ([_ pair: n (ty syntax _ _ _ _
	       _ _ _ _ _
	       _ _ _
	       _ _ _ _ _
	       _ _ _ _ _ _
	       _copy _clone _length set! ref
	       map for-each
	       _ _
	       _ _ _
	       _ _ _
	       tolist _ _
	       tostruct . _) . rs]
  (let-syntax ([ty (ty-trf pair: ty n)])
     (with-protocol #'n … (:= .copy .clone .length ..)
	  [([_] n)
	   ([_ .copy] (cons (car n) (cdr n)))
	   ([_ .clone] (cons (car n) (cdr n)))
	   ([_ .length] 2)
	   ([_ (0)] (car n))
	   ([_ (1)] (cdr n))
	   ([_ (0):= val] (set-car! n val))
	   ([_ (1):= val] (set-cdr! n val))
	   ] . rs)))
  )
;; Bigloo hashes
(extend-ty-sugar ()
  ([_ hashtable: n (ty syntax _ _ _ _
	       _ _ _ _ _
	       _ _ _
	       _ _ _ _ _
	       _ _ _ _ _ _
	       _copy _clone _length set! ref
	       map for-each
	       _ _
	       _ _ _
	       _ _ _
	       tolist tovector . _) . rs]
  (let-syntax ([ty (ty-trf hashtable: ty n)]
	       ;[_copy (op-trf TODO _copy n)]
	       ;[_clone (op-trf TODO _clone n)] ;; TODO: deep copy
	       [_length (op-trf hashtable-size _length n)]
	       [set! (op-trf hashtable-put! set! n)]
	       [ref (op-trf hashtable-get ref n)]
	       [map (op-trf (Λ (f ht)
		 (hashtable-map ht f)) map n)]
	       [for-each (op-trf (Λ (f ht)
		 (hashtable-for-each ht f)) for-each n)]
	       [tolist (op-trf hashtable->list tolist n)]
	       [tovector (op-trf hashtable->vector tovector n)]
	       )
     (with-protocol #'n … (:= .copy .clone .length .. .keys)
	  [([_] n)
	   ;([_ .copy] (_copy n))
	   ;([_ .clone] (_clone n))
	   ([_ .length] (_length n))
	   ([_ .keys] (hashtable-key-list n))
	   ([_ (idx)] (ref n idx))
	   ;([_ (idx ..)] (list-tail n idx))
	   ([_ (idx):= val] (set! n idx val))
	   ] . rs)))
  )
;; TODO: add treap
;; Bigloo strings
(extend-ty-sugar ()
 ([_ ucs2string: n (ty syntax _ _ _ _
	       _ _ _ _ _
	       _ _ _
	       _ _ _ _ _
	       _ _ _ _ _ _
	       _copy _clone _length set! ref
	       map for-each
	       _ _
	       _ _ _
	       _ _ _
	       tolist _ _
	       _ toucs2string toutf8string . _) . rs]
  (let-syntax ([ty (ty-trf ucs2string: ty n)]
	       [_copy (op-trf ucs2-string-copy _copy n)]
	       ;[_clone (op-trf TODO _clone n)] ;; TODO: deep copy
	       [_length (op-trf ucs2-string-length _length n)]
	       [set! (op-trf ucs2-string-set! set! n)]
	       [ref (op-trf ucs2-string-ref ref n)]
	       ;[map (op-trf string-map map n)]
	       ;[for-each (op-trf string-for-each for-each n)]
	       [tolist (op-trf ucs2-string->list tolist n)]
	       [toucs2string (op-trf ident toucs2string n)]
	       [toutf8string (op-trf ucs2-string->utf8-string toucs2string n)]
	       )
     (with-protocol #'n … (:= .copy .clone .length ..)
	  [([_] n)
	   ([_ .copy] (_copy n))
	   ;([_ .clone] (_clone n))
	   ([_ .length] (_length n))
	   ([_ (idx)] (ref n idx))
	   ([_ (idx .. . end)] (subucs2-string n idx . end))
	   ([_ (idx):= val] (set! n idx val))
	   ] . rs)))
 ([_ utf8string: n (ty syntax _ _ _ _
	       _ _ _ _ _
	       _ _ _
	       _ _ _ _ _
	       _ _ _ _ _ _
	       _copy _clone _length set! ref
	       map for-each
	       _ _
	       _ _ _
	       _ _ _
	       _ _ _
	       _ toucs2string toutf8string . _) . rs]
  (let-syntax ([ty (ty-trf utf8string: ty n)]
	       ;[_copy (op-trf string-copy _copy n)]
	       ;[_clone (op-trf TODO _clone n)] ;; TODO: deep copy
	       [_length (op-trf utf8-string-length _length n)]
	       ;[set! (op-trf ucs2-string-set! set! n)]
	       [ref (op-trf utf8-string-ref ref n)]
	       ;[map (op-trf string-map map n)]
	       ;[for-each (op-trf string-for-each for-each n)]
	       [toucs2string (op-trf utf8-string->ucs2-string toucs2string n)]
	       [toutf8string (op-trf ident toutf8string n)]
	       )
     (with-protocol #'n … (:= .copy .clone .length ..)
	  [([_] n)
	   ;([_ .copy] (_copy n))
	   ;([_ .clone] (_clone n))
	   ([_ .length] (_length n))
	   ([_ (idx)] (ref n idx))
	   ;([_ (idx):= val] (set! n idx val))
	   ([_ (idx .. . end)] (utf8-substring n idx . end))
	   ] . rs)))
 )

;; SLIB Arrays
(extend-ty-sugar ()
([_ array: n (ty syntax _ _ _ _
	       _ _ _ _ _
	       _ _ _
	       _ _ _ _ _
	       _ _ _ _ _ _
	       _copy _clone _length set! ref
	       map for-each
	       _ _
	       _ _ _
	       _ _ _
	       tolist tovector _
	       _ _ _
	       tomatrix toarray . _) . rs]
  (let-syntax ([ty (ty-trf array: ty n)]
	       ;[_copy (op-trf vector-copy _copy n)]
	       [_clone (op-trf (Λ (x)
		  (let ([a (apply make-array `(#() . ,[array-dimensions x]))])
		     (array:copy! a x)
		     a)) _clone n)]
	       [_length (op-trf (Λ (x)
		  (reduce $* 1 [array-dimensions x]))
			   _length n)]
	       [ref (op-trf array-ref ref n)]
	       [set! (syntax-rules .. ()
			([_ n ind .. v] (array-set! n v ind ..))
			([_ . args] (set! . args)))]
	       [map (op-trf (Λ (f x)
			       (array-map '#() f x)) map n)]
	       [for-each (op-trf array-for-each for-each n)]
	       [tolist (op-trf array->list tolist n)]	       
	       [tovector (op-trf array->vector tovector n)]	       
	       [tomatrix (op-trf ident tomatrix n)] ;; TODO
	       [toarray (op-trf ident toarray n)]	       
               )
     (with-protocol #'n … (:= .copy .clone .length .. .dim .rank)
	  [([_] n)
	   ;([_ .copy] (_copy n))
	   ([_ .clone] (_clone n))
	   ([_ .length] (_length n))
           ([_ .rank] (array-rank n))
           ([_ .dim] (array-dimensions n))
           ([_ .dim x] (list-ref (array-dimensions n) x))
	   ([_ (s .. . e)] (array-slice n s . e))
	   ([_ idx] (ref n . idx))
	   ([_ (idx …) := val] (set! n idx … val))
	   ] . rs))
  ))

(def-syntax [head (x . y)  (k . r)] (k x . r))
(def-syntax [head2 (x . y) (k a [] . r)] (k a x . r))
(def-syntax [tail (x . y) (k . r)] (k y . r))

(def-syntax [TYPES k]
 (k :unknown
    :fix :flo
    :elong :llong :bignum
    :rat :cx :dx
    :char :wchar :int
    :list :vector :string
    :s8vector :u8vector :s16vector :u16vector
    :s32vector :u32vector :s64vector :u64vector
    :f32vector :f64vector
    :struct :pair
    :hashtable :ucs2string :utf8string
    :matrix :array
    ))
;(def-syntax Lambda lambda)

(def-syntax memb?? (syntax-rules ()
      ([_ id () kt kf] kf)
      ([_ (x . y) z kt kf] kf)
      ([_ id (x . r) kt kf]
       (let-syntax ([test (syntax-rules ()
			     ([_ id t f] t)
			     ([_ xx t f] f))])
	  (test x kt (memb?? id r kt kf))))))

(def-syntax [Member?? id db kt kf]
   (symbol?? id
      (memb?? id db kt kf)
      kf))

(def-syntax [nth db . spec]
  (letrec-syntax ([rec (syntax-rules .. ()
			  ([_ (y .. x)] x)
			  ([_ (y .. x) 1 . r] (rec (y ..) . r))
			  )])
     (db (rec ['#?] . spec))
     ))

(def-syntax [_' x] x)

(define-anaphora (type syntax  + - * /
		  = < > <= >=
		  neg min max ;minval maxval
		  zero? even? odd? positive? negative?
		  and lsh not or rsh xor
		  copy clone length set! ref
		  map for-each
		  fix flo
		  elong llong bignum
		  char wchar int
		  list vector string
		  struct ucs2string utf8string
		  matrix array
		  _ _')
   (>-> rec0 (syntax-rules ()
		([_ 1 _ _ _ fa] fa)
		([_ 1 (typ x ... thy thy') slfs ct fa ta . fb]
		 (let-syntax ([thy fa])
		   (let-syntax-rule ([thy' (k db . as)]
				     (thy' (k (thy . db) . as)))
		   (TYPES (Λ types
		     (memb?? ta types
			(rec3 (typ x ... thy thy') slfs (thy ta)
			 (redefine-thyself* (typ x ... thy thy') [] slfs
			    (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			    (rec0 1 (typ x ... thy thy') slfs ta . fb)
			    ))
			(typ fa (Λ'
			([:unknown]
			 (rec3 (typ x ... thy thy') slfs (thy ct)
			  (redefine-thyself* (typ x ... thy thy') [] slfs
			    (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			    (rec0 1 (typ x ... thy thy') slfs ct ta . fb)
			    )))
			([ty]
			 (rec3 (typ x ... thy thy') slfs (thy ty)
			   (redefine-thyself* (typ x ... thy thy') [] slfs
			    (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			    (rec0 1 (typ x ... thy thy') slfs ty ta . fb)
			    ))
			 )))
		     )))
		 )))
		([_ o s . rest]
		 (rec0 1 o s unknown: . rest))
		))
   (>=> rec1 (syntax-rules ()
		([_ 1 _ _ _ fa] fa)
		([_ 1 (typ x ... thy thy') slfs ct fa ta . fb]
		 (let ([thy fa])
		   (let-syntax-rule ([thy' (k db . as)]
				     (thy' (k (thy . db) . as)))
		   (TYPES (Λ types
		     (memb?? ta types
			(rec3 (typ x ... thy thy') slfs (thy ta)
			 (redefine-thyself* (typ x ... thy thy') [] slfs
			    (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			    (rec1 1 (typ x ... thy thy') slfs ta . fb)
			    ))
			; (typ fa (Λ'
			; ([:unknown]
			 (rec3 (typ x ... thy thy') slfs (thy ct)
			  (redefine-thyself* (typ x ... thy thy') [] slfs
			    (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			    (rec1 1 (typ x ... thy thy') slfs ct ta . fb)
			    ));)
			; ([ty]
			 ; (rec3 (typ x ... thy thy') slfs (thy ty)
			 ;   (redefine-thyself* (typ x ... thy thy') [] slfs
			 ;    (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			 ;    (rec1 1 (typ x ... thy thy') slfs ty ta . fb)
			 ;    ))
			 ;)))
		     )))
		 )))
		([_ o s . rest]
		 (rec1 1 o s unknown: . rest))
		))
   (>~> rec2 (syntax-rules ()
		([_ 1 _ _ _ fa] fa)
		([_ 1 (typ x ... thy thy') slfs ct fa ta . fb]
		 (let ([thy fa])
		   (let-syntax-rule ([thy' (k db . as)]
				     (thy' (k (thy . db) . as)))
		   (TYPES (Λ types
		     (memb?? ta types
			(rec3 (typ x ... thy thy') slfs (thy ta)
			 (redefine-thyself* (typ x ... thy thy') [] slfs
			    (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			    (and thy (rec2 1 (typ x ... thy thy') slfs ta . fb))
			    ))
			; (typ fa (Λ'
			; ([:unknown]			
			 (rec3 (typ x ... thy thy') slfs (thy ct)
			    (redefine-thyself* (typ x ... thy thy') [] slfs
			       (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			       (and thy (rec2 1 (typ x ... thy thy') slfs ct ta . fb))
			       ));)
			; ([ty]			
			 ; (rec3 (typ x ... thy thy') slfs (thy ty)
			 ;    (redefine-thyself* (typ x ... thy thy') [] slfs
			 ;       (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			 ;       (and thy (rec2 1 (typ x ... thy thy') slfs ty ta . fb))
			 ;       ))
			 ;)))
		     )))
		 )))
		([_ o s . rest]
		 (rec2 1 o s unknown: . rest))
		))
   (as rec3 (syntax-rules ()
	       ;; end
	       ([_ 1 os slfs ct () . k] (begin . k))
	       ;; there is a binding
	       ([_ 1 os slfs ct (n m . rest) . ts]
		(TYPES (Λ types
	          (member?? n types
		    (rec3 1 os slfs n (m . rest) . ts)
	            (member?? m types
		     (rec3 1 os slfs ct rest
			(ty-sugar m n os 
			   (redefine-thyself* os [] slfs
			      (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			      . ts)))
		     (rec3 1 os slfs ct (m . rest)
			(ty-sugar ct n os 
			   (redefine-thyself* os [] slfs
			      (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			      . ts)))
		     ))
		   )))
	       ;; last binding
	       ([_ 1 os slfs ct (n . rest) . ts]
		(TYPES (Λ types
	          (member?? n types
		    (rec3 1 os slfs n rest . ts)
	            (rec3 1 os slfs ct rest
			(ty-sugar ct n os 
			   (redefine-thyself* os [] slfs
			      (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			      . ts))))
		    )))
	       ;; catch the error (will loop otherwise)
	       ([_ 1 _ . r]
		(syntax-error as: . r))	       
	       ;; start
	       ([_ os slfs ns . body]
		(rec3 1 os slfs unknown: ns . body))
	       ))
   (Lambda rec4 (syntax-rules ()
	       ;; end
	       ([_ 1 os slfs ct () . k] k)
	       ;; there is a binding
	       ([_ 1 os slfs ct (n m . rest) lt (bs ...) . ts]
		(TYPES (Λ types
	          (member?? n types
		    (rec4 1 os slfs n (m . rest) lt (bs ...) . ts)
	            (member?? m types
		     (rec4 1 os slfs ct rest
			lt (bs ... n)
			(ty-sugar m n os 
			   (redefine-thyself* os [] slfs
			      (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			      . ts)))
		     (rec4 1 os slfs ct (m . rest)
			lt (bs ... n)
			(ty-sugar ct n os 
			   (redefine-thyself* os [] slfs
			      (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			      . ts)))
		     ))
		   )))
	       ;; last binding
	       ([_ 1 os slfs ct (n . rest) lt (bs ...) . ts]
		(TYPES (Λ types
	          (member?? n types
		    (rec4 1 os slfs n rest lt (bs ...) . ts)
	            (rec4 1 os slfs ct rest
			lt (bs ... n)
			(ty-sugar ct n os 
			   (redefine-thyself* os [] slfs
			      (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			      . ts))))
		    )))
	       ;; catch the error (will loop otherwise)
	       ([_ 1 _ . r]
		(syntax-error Lambda: . r))	       
	       ;; start
	       ([_ os slfs nvs . body]
		(rec4 1 os slfs unknown: nvs lambda () . body))
	       ))
   (Let rec5 (syntax-rules ()
	       ;; finish
               ([_ 1 o s [loop: name . ns] vs () . body]
		((letrec ([name (rec4 o s ns . body)])
		    name) . vs))
	       ([_ 1 o s ns vs () . body]
		((rec4 o s ns . body) . vs))
	       ;; engine
	       ([_ 1 o s (ns ...) (vs ...) ([n ... v] . rest) . body]
		(rec5 1 o s (ns ... n ...) (vs ... v) rest . body))
	       ([_ 1 o s (ns ...) vs (a . rest) . body]
		(rec5 1 o s (ns ... a) vs rest . body))
	       ;; start
	       ([_ o s (nvs ...) . body]
		(rec5 1 o s [] [] (nvs ...) . body))
	       ([_ o s name (nvs ...) . body]
		(rec5 1 o s [loop: name] [] (nvs ...) . body))
	       ))
   (Let* rec6 (syntax-rules ()
	       ;; finish
	       ([_ 1 o s ct () . body]
		(let () . body))
	       ;; engine
	       ([_ 1 o s ct ([n ... v] t . rest) . body]
		(TYPES (Λ types
	          (member?? t types	
		     ((rec4 o s (ct n ... t)
			  (rec6 1 o s ct rest . body))
		      v)
		     ((rec4 o s (ct n ...)
			  (rec6 1 o s ct (t . rest) . body))
		      v)
		     ))
		   ))
	       ([_ 1 o s ct ([n ... v] . rest) . body]
		((rec4 o s (ct n ...)
		    (rec6 1 o s ct rest . body))
		 v))
	       ([_ 1 o s ct (nv . rest) . body]
		(rec6 1 o s nv rest . body))
	       ;; start
	       ([_ o s nvs . body]
		(rec6 1 o s unknown: nvs . body))
	       ))
   (Letrec* rec7 (syntax-rules ()
	       ;; finish
	       ([_ 1 o s as (n ...) (v ...) ds () . body]
		((rec4 o s as
		    (set! n v) ...
		    (let () . body))
		 . ds))
	       ;; engine
	       ([_ 1 o s (as ...) (ns ...) (vs ...) ds ([n t ... v] . rest) . body]
		(rec7 1 o s (as ... n t ...)
		   (ns ... n) (vs ... v) ('#? . ds)
		   rest . body))
	       ([_ 1 o s (as ...) ns vs ds (a . rest) . body]
		(rec7 1 o s (as ... a)
		   ns vs ds2
		   rest . body))
	       ;; start
	       ([_ o s (nvs ...) . body]
		(rec7 1 o s [] [] [] [] (nvs ...) . body))
	       ))
   (Letrec rec8 (syntax-rules ()
	       ;; finish
	       ([_ 1 o s (t ...) as (n ...) vs ds () . body]
		((rec4 o s as
		   ((rec4 o s (t ...)
		     (set! n t) ...)
		    . vs)
		   (let () . body))
		 . ds))
	       ;; engine
	       ([_ 1 o s (ts ...) (as ...) (ns ...) (vs ...) ds ([n t ... v] . rest) . body]
		(rec8 1 o s (ts ... tmp) (as ... n t ...)
		   (ns ... n) (vs ... v) ('#? . ds)
		   rest . body)
		  )
	       ([_ 1 o s ts (as ...) ns vs ds (a . rest) . body]
		(rec8 1 o s ts (as ... a)
		   ns vs ds
		   rest . body))
	       ;; start
	       ([_ o s (nvs ...) . body]
		(rec8 1 o s [] [] [] [] [] (nvs ...) . body))
	       ))
   (Do rec9 (syntax-rules ()
	       ((_ o s ([var type init step ...] ...)
		   (test expr ...)
		   command ...)
		(let-syntax ([do-step (syntax-rules () ((_ x) x) ((_ x y) y))])
		   (rec5 o s loop ([var type init] ...)
		      (if test
			  (begin #f expr ...)
			  (let () command ...
			       (loop (do-step var step ...) ...)
			       ))
		      ))
		)
	       ((_ o s (typ [var . rest] ...) . r)
		(rec9 o s ([var typ . rest] ...) . r))
	       ))
   
   )

;; redefine a few derived forms to use new LAMBDA
(def-syntax Define (syntax-rules ()
      ((_ (var . args) . body) (define var (Lambda args . body)))
      ((_ var expr) (define var expr))
      ((_ var) (define var #?))
      ))
(def-syntax Define-immutable (syntax-rules ()
      ((_ (var . args) . body) (begin
	  (define var (Lambda args . body))
	  (def-syntax var var)))
      ((_ var expr) (begin
	  (define var expr)
	  (def-syntax var var)))
      ((_ var) (begin
	  (define var #?)
	  (def-syntax var var)))
      ))

(def-syntax Def Define-immutable)

(def-syntax Defn (syntax-rules ()
 ;; recursive functions
 ([_ (f . args) . body]
   (define f (Lambda args
	(let-syntax ([f (syntax-rules ())])
	   (let () . body)))
      ))
 ;; recursive CAFs
 ([_ f . exprs]
     (define f 
	(let-syntax ([f (syntax-rules ())])
	   (let () . exprs))
	))
))

; the end
