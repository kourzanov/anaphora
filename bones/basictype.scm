(code;;bones
(define-syntax-rule [type n k] (k :unknown))
(define-syntax-rule [ty-trf type ty n]
   (syntax-rules (n)
      ([_ n k] (k type))
      ([_ . r] (ty . r))
      ))
(define-syntax-rule [op-trf opo opd x]
(syntax-rules (x)
   ([_ x . r] (opo x . r))
   ([_ . r] (opd . r))
  ))
(define-syntax-rule [op2-trf opo opd x]
(syntax-rules (x)
   ([_ x . r] (opo x . r))
   ([_ y x . r] (opo y x . r))
   ([_ . r] (opd . r))
  ))
(define-syntax-rule [op3-trf opo opd x]
(syntax-rules (x)
   ([_ x . r] (opo x . r))
   ([_ y x . r] (opo y x . r))
   ([_ z y x . r] (opo z y x . r))
   ([_ . r] (opd . r))
  ))
(define-syntax-rule [op*-trf opo opd x]
  (letrec-syntax ([op (syntax-rules .. (x)
     ([_ 'int (c ..) x . y] (opo c .. x . y))
     ([_ 'int (c ..) y . z] (op 'int (c .. y) . z))
     ([_ 'int c] (opd . c))
     ([_ . rest] (op 'int [] . rest)))])
   (syntax-rules (op)
     ([_ . args] (op . args)))
   ))

;(define-syntax-rule [syntax . a] (syntax-error "syntax" . a))
; (define-syntax with-protocol' (syntax-rules ()
;  ([_ (syntax n) liter rules . body]
;    (let-syntax ([syntax (syntax-rules (n)
; 	([_ (n . args)] (let-syntax ([proc (syntax-rules liter . rules)])
; 			   (proc . args)))
; 	([_ . a] (syntax . a))
; 	)])
;       . body))
;  ))
(define-syntax-rule [with-protocol #'n liter rules . body]
   (let-syntax ([syntax (syntax-rules (n)
	([_ (n . args)] (let-syntax ([proc (syntax-rules liter . rules)])
			   (proc . args)))
	([_ . a] (syntax . a))
	)])
      . body))

(define-syntax-rule [syntax-error] (syntax-error Bad syntax))

(define-syntax-rule [extend-ty-sugar lits clause ...] 
 (define-syntax ty-sugar 
   (let-syntax ([tysugar ty-sugar])
    (syntax-rules lits     
       clause ...
       ([_ . as] (tysugar . as))
       ))
     ))

;(define-syntax let_ let)
;(define-syntax letrec_ letrec)
(define-syntax-rule [ty-sugar . args] (syntax-error ty-sugar: . args))

(extend-ty-sugar (:unknown)
([_ :unknown n _ (redefine-thyself* _1 _2 _3 _4 . ts)]
  (let () . ts))
)

(define-syntax-rule [id v] v)

;(define-syntax ty-sugar
(extend-ty-sugar (:fix :flo)
([_ :fix n (ty syntax o+ o- o* o/
	       = < > <= >=
	       neg min max
	       zero? even? odd? positive? negative?
	       and lsh not or rsh xor
	       _1 _2 length _4 _5
	       _11 _12
	       tofix toflo
	       ;toelong tollong tobignum
	       _31 _32 _33
	       _21 _22 tostring
	       . _0) . rs]
  (let-syntax ([ty (ty-trf :fix ty n)]
	       [o+ (op2-trf fx+ o+ n)]
	       [o- (op2-trf fx- o- n)]
	       [o* (op2-trf fx* o* n)]
	       [o/ (op2-trf fx/ o/ n)]
	       [=  (op2-trf fx= = n)]
	       [<  (op2-trf fx< < n)]
	       [>  (op2-trf fx> > n)]
	       [<= (op2-trf fx<= <= n)]
	       [>= (op2-trf fx>= >= n)]
	       [neg (op-trf fxneg neg n)]
	       [min (op2-trf fxmin min n)]
	       [max (op2-trf fxmax max n)]
	       [zero? (op-trf fxzero? zero? n)]
	       [even? (op-trf fxeven? even? n)]
	       [odd? (op-trf fxodd? odd? n)]
	       [positive? (op-trf fxpositive? positive? n)]
	       [negative? (op-trf fxnegative? negative? n)]
	       [not (op-trf fxnot not n)]
	       [and (op2-trf fxand and n)]
	       [or (op2-trf fxior or n)]
	       [xor (op2-trf fxxor xor n)]
	       [lsh (op2-trf fxarithmetic-shift-left lsh n)]
	       [rsh (op2-trf fxarithmetic-shift-right rsh n)]
	       [length (op-trf fxlength length n)]
	       [tofix (op-trf id tofix n)]
	       [toflo (op-trf exact->inexact toflo n)]
	       [tostring (op-trf number->string tostring n)]
	       ) . rs))
 ([_ :flo n (ty syntax o+ o- o* o/
	       = < > <= >=
	       neg min max
	       zero? even? odd? positive? negative?
	       _41 _42 _43 _44 _45 _46
	       _1 _2 _3 _4 _5
	       _11 _12
	       tofix toflo
	       ;toelong tollong tobignum
	       _31 _32 _33
	       _21 _22 tostring
	       . _0) . rs]
  (let-syntax ([ty (ty-trf :flo ty n)]
	       [o+ (op2-trf fl+ o+ n)]
	       [o- (op2-trf fl- o- n)]
	       [o* (op2-trf fl* o* n)]
	       [o/ (op2-trf fl/ o/ n)]
	       [=  (op2-trf fl= = n)]
	       [<  (op2-trf fl< < n)]
	       [>  (op2-trf fl> > n)]
	       [<= (op2-trf fl<= <= n)]
	       [>= (op2-trf fl>= >= n)]
	       [neg (op-trf flneg neg n)]
	       [min (op2-trf flmin min n)]
	       [max (op2-trf flmax max n)]
	       [zero? (op-trf flzero? zero? n)]
	       [even? (op-trf fleven? even? n)]
	       [odd? (op-trf flodd? odd? n)]
	       [positive? (op-trf flpositive? positive? n)]
	       [negative? (op-trf flnegative? negative? n)]
	       [tofix (op-trf inexact->exact tofix n)]
	       [toflo (op-trf id toflo n)]
	       [tostring (op-trf number->string tostring n)]
	       ) . rs))
)

(extend-ty-sugar (:char :int)
([_ :char n (ty syntax _1 _2 _3 _4
		= < > <= >=
		_21 _22 _23
		_31 _32 _33 _34 _35
		_41 _42 _43 _44 _45 _46
		_51 _52 _53 _54 _55
		_61 _62
		_71 _72
		_81 _82 _83
		tochar towchar toint
		. _0) . rs]
  (let-syntax ([ty (ty-trf :char ty n)]
	       [toint (op-trf char->integer toint n)]
	       [tochar (op-trf id tochar n)]
	       ;[towchar (op-trf char->ucs2 towchar n)]
	       [=  (op2-trf char=? = n)]
	       [<  (op2-trf char<? < n)]
	       [>  (op2-trf char>? > n)]
	       [<= (op2-trf char<=? <= n)]
	       [>= (op2-trf char>=? >= n)]
	       ) . rs))
([_ :int n (ty syntax _1 _2 _3 _4
		   = < > <= >=
		   _11 _12 _13
		   _21 _22 _23 _24 _25
		   and lsh not or rsh xor
		   _31 _32 _33 _34 _35
		   _41 _42
		   _51 _52
		   tochar towchar toint
		   _71 _72 tostring
		   . _0) . rs]
  (let-syntax ([ty (ty-trf :int ty n)]
	       [toint (op-trf id toint n)]
	       [tochar (op-trf integer->char tochar n)]
	       ;[wchar (op-trf integer->ucs2 wchar n)]
	       [not (op-trf bitwise-not not n)]
	       [and (op2-trf bitwise-and and n)]
	       [or (op2-trf bitwise-ior or n)]
	       [xor (op2-trf bitwise-xor xor n)]
	       [lsh (op2-trf bitwise-arithmetic-shift-left lsh n)]
	       [rsh (op2-trf bitwise-arithmetic-shift-right rsh n)]
	       [tostring (op-trf number->string tostring n)]
	       ) . rs))
)

(extend-ty-sugar (:list :vector :string)
 ([_ :list n (ty syntax _1 _2 _3 _4
		_11 _12 _13 _14 _15
		_31 _32 _33
		_41 _42 _43 _44 _45
		_21 _22 _23 _24 _25 _26
		copy clone length set! ref
		map for-each
		_51 _52
		_61 _62 _63
		tolist tovector tostring
		. _0) . rs]
  (let-syntax ([ty (ty-trf :list ty n)]
	       [copy (op-trf list-copy copy n)]
	       [clone (op-trf tree-copy clone n)]
	       [length (op-trf length length n)]
	       [set! (op-trf list-set! set! n)]
	       [ref (op-trf list-ref ref n)]
	       ;[map (op-trf map map n)]
	       ;[for-each (op-trf for-each for-each n)]
	       [tolist (op-trf id tolist n)]
	       [tovector (op-trf list->vector tovector n)]
	       [tostring (op-trf list->string tostring n)]	       
	       )
     (with-protocol #'n (:= copy clone length ..)
	  [([_] n)
	   ([_ copy] (copy n))
	   ([_ clone] (clone n))
	   ([_ length] (length n))
	   ([_ (idx)] (ref n idx))
	   ([_ (idx ..)] (list-tail n idx))
	   ([_ (idx):= val] (set! n idx val))
	   ] . rs)))
 ([_ :vector n (ty syntax _1 _2 _3 _4
		  _11 _12 _13 _14 _15
		  _31 _32 _33
		  _41 _42 _43 _44 _45
		  _21 _22 _23 _24 _25 _26
		  copy clone length set! ref
		  map for-each
		  _51 _52
		  _61 _62 _63
		  tolist tovector _81
		  . _0) . rs]
  (let-syntax ([ty (ty-trf :vector ty n)]
	       [copy (op-trf vector-copy copy n)]
	       [clone (op-trf copy-vector clone n)] ;; TODO: deep copy
	       [length (op-trf vector-length length n)]
	       [set! (op-trf vector-set! set! n)]
	       [ref (op-trf vector-ref ref n)]
	       [map (op2-trf vector-map map n)]
	       [for-each (op2-trf vector-for-each for-each n)]
	       [tolist (op-trf vector->list tolist n)]
	       [tovector (op-trf id tovector n)]
	       )
     (with-protocol #'n (:= copy clone length ..)
	  [([_] n)
	   ([_ copy] (copy n))
	   ([_ clone] (clone n (length n)))
	   ([_ clone s] (clone n s))
	   ([_ length] (length n))
	   ([_ (idx)] (ref n idx))
	   ([_ (idx .. . end)] (copy n idx . end))
	   ([_ (idx):= val] (set! n idx val))
	   ] . rs)))
 ([_ :string n (ty syntax _1 _2 _3 _4
		  _11 _12 _13 _14 _15
		  _31 _32 _33
		  _41 _42 _43 _44 _45
		  _21 _22 _23 _24 _25 _26
		  copy clone length set! ref
		  map for-each
		  tofix toflo
		  ;toelong tollong tobignum
		  _51 _52 _53
		  tolist _ tostring
		  . _0) . rs]
  (let-syntax ([ty (ty-trf :string ty n)]
	       [copy (op-trf string-copy copy n)]
	       ;[clone (op-trf TODO clone n)] ;; TODO: deep copy
	       [length (op-trf string-length length n)]
	       [set! (op-trf string-set! set! n)]
	       [ref (op-trf string-ref ref n)]
	       [map (op2-trf string-map map n)]
	       [for-each (op2-trf string-for-each for-each n)]
	       [tofix (op-trf string->number tofix n)]
	       [toflo (op-trf string->number toflo n)]
	       [tolist (op-trf string->list tolist n)]
	       [tostring (op-trf id tostring n)]
	       )
     (with-protocol #'n (:= copy clone length ..)
	  [([_] n)
	   ([_ copy] (copy n))
	   ;([_ clone] (clone n))
	   ([_ length] (length n))
	   ([_ (idx)] (ref n idx))
	   ([_ (idx .. . end)] (substring n idx . end))
	   ([_ (idx):= val] (set! n idx val))
	   ] . rs)))
 )

(define-syntax-rule [extend-ty-sugar-vector tag _len _set _ref _tol _tov]
 (extend-ty-sugar (tag)
 ([_ tag n (ty syntax _1 _2 _3 _4
	       _5 _6 _7 _8 _9
	       _81 _82 _83
	       _91 _92 _93 _94 _95
	       _11 _12 _13 _14 _15 _16
	       copy clone length set! ref
	       map for-each
	       _31 _32
	       _41 _42 _43
	       tolist tovector _61
	       . _0) . rs]
  (let-syntax ([ty (ty-trf tag ty n)]
	       [copy (op-trf (syntax-rules ()
		 ([_ v] (_tov (_tol v)))
		 ([_ v s e] (_tov (take
				  (list-tail
				     (_tol v)
				     s)
				  (+ s (- e) +1))
			       ))
		 ) copy n)]
	       [clone (op-trf (Lam (v n)
				  (_tov (take
				      (_tol v)
				      n
				    ))
				  ) clone n)] ;; TODO: deep copy

	       [length (op-trf _len length n)]
	       [set! (op-trf _set set! n)]
	       [ref (op-trf _ref ref n)]
	       [map (op2-trf (Lam (f v) (_tov (map f (_tol v)))
			    ) map n)]
	       [for-each (op2-trf (Lam (f v)
				    (do ([i 0 (+1+ i)])
					((>= i (_len v)) #f)
					(f (_ref v i))
					)) for-each n)]
	       [tolist (op-trf _tol tolist n)]
	       [tovector (op-trf id tovector n)]
	       [tomatrix (op-trf id tomatrix n)] ;; TODO add rank
	       )
     (with-protocol #'n (:= copy clone length ..)
	  [([_] n)
	   ([_ copy] (copy n))
	   ([_ clone] (clone n (length n)))
	   ([_ clone s] (clone n s))
	   ([_ length] (length n))
	   ([_ (idx)] (ref n idx))
	   ([_ (idx .. . end)] (copy n idx . end))
	   ([_ (idx):= val] (set! n idx val))
	   ] . rs)))
 ))

(extend-ty-sugar-vector :f64vector
   f64vector-length
   f64vector-set!
   f64vector-ref
   f64vector->list
   list->f64vector)

(extend-ty-sugar-vector :bytevector
   bytevector-length
   bytevector-u8-set!
   bytevector-u8-ref
   bytevector->u8-list
   u8-list->bytevector)

(define-syntax-rule [TYPES k]
 (k :unknown
    :list :vector :string
    :fix :flo
    :char :int
    :f64vector
    :bytevector))

(define-syntax member?? (syntax-rules ()
      ([_ id () kt kf] kf)
      ([_ (x . y) z kt kf] kf)
      ([_ id (x . r) kt kf]
       (let-syntax ([test (syntax-rules (id)
			     ([_ id t f] t)
			     ([_ xx t f] f))])
	  (test x kt (member?? id r kt kf))))))
(define-syntax memb?? (syntax-rules ()
      ([_ id () kt kf] kf)
      ([_ (x . y) z kt kf] kf)
      ([_ id (x . r) kt kf]
       (let-syntax ([test (syntax-rules ()
			     ([_ id t f] t)
			     ([_ xx t f] f))])
	  (test x kt (memb?? id r kt kf))))))
(define-syntax-rule [nth db . spec]
  (letrec-syntax ([rec (syntax-rules .. ()
			  ([_ (y .. x)] x)
			  ([_ (y .. x) 1 . r] (rec (y ..) . r))
			  )])
     (db (rec [<undefined>] . spec))
     ))

(define-syntax-rule [_' x] x)

;(let-syntax ([let_ let]
;	     [letrec_ letrec])
(define-anaphora (type syntax  + - * /
		  = < > <= >=
		  neg min max
		  zero? even? odd? positive? negative?
		  and lsh not or rsh xor
		  copy clone length set! ref
		  map for-each
		  fix flo
		  ;elong llong bignum
		  char wchar int
		  list vector string
		  ;struct ucs2string utf8string
		  ;matrix array
		  _ _')
		  ;and lsh not or rsh xor
		  ;ord char wchar
		  ;copy clone length set! ref
		  ;map for-each
		  ;tolist tovector tostring _)
   (>-> rec0 (syntax-rules ()
		([_ 1 _1 _2 _3 fa] fa)
		([_ 1 (x ... thy thy') slfs ct fa ta . fb]
		 (let-syntax-rule ([K . types] 
		   (let-syntax-rule ([thy' (k db . as)]
				   (thy' (k (fa . db) . as)))
		      (let-syntax ([thy fa])
		      (memb?? ta types
			(rec3 (x ... thy thy') slfs (thy ta)
			 (redefine-thyself* (x ... thy thy') [] slfs
			    (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			    (rec0 1 (x ... thy thy') slfs ta . fb)
			    ))
			(rec3 (x ... thy thy') slfs (thy ct)
			 (redefine-thyself* (x ... thy thy') [] slfs
			    (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			    (rec0 1 (x ... thy thy') slfs ct ta . fb)
			    ))
			))
		     ))
		   (TYPES K)
		   ))
		([_ o s . rest]
		 (rec0 1 o s :unknown . rest))
		))
   (>=> rec1 (syntax-rules ()
		([_ 1 _1 _2 _3 fa] fa)
		([_ 1 (x ... thy thy') slfs ct fa ta . fb]
		 (let-syntax-rule ([K . types] 
		   (let ([thy' thy]
		       [thy fa])
		     (memb?? ta types
			(rec3 (x ... thy thy) slfs (thy ta)
			 (redefine-thyself* (x ... thy thy') [] slfs
			    (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			    (rec1 1 (x ... thy thy') slfs ta . fb)
			    ))
			(rec3 (x ... thy thy') slfs (thy ct)
			 (redefine-thyself* (x ... thy thy') [] slfs
			    (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			    (rec1 1 (x ... thy thy') slfs ct ta . fb)
			    ))
			)
		     ))
		    (TYPES K)
		 ))
		([_ o s . rest]
		 (rec1 1 o s :unknown . rest))
		))
   (>~> rec2 (syntax-rules ()
		([_ 1 _1 _2 _3 fa] fa)
		([_ 1 (x ... thy thy') slfs ct fa ta . fb]
		 (let-syntax-rule ([K . types] 
		   (let ([thy' thy]
		       [thy fa])
		     (memb?? ta types
			(rec3 (x ... thy thy') slfs (thy ta)
			 (redefine-thyself* (x ... thy thy') [] slfs
			    (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			    (and thy (rec2 1 (x ... thy thy') slfs ta . fb))
			    ))
			(rec3 (x ... thy thy') slfs (thy ct)
			 (redefine-thyself* (x ... thy thy') [] slfs
			    (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9)
			    (and thy (rec2 1 (x ... thy thy') slfs ct ta . fb))
			    ))
		     )
		 ))
		    (TYPES K)
		 ))
		([_ o s . rest]
		 (rec2 1 o s :unknown . rest))
		))
   (as rec3 (syntax-rules ()
	       ;; end
	       ([_ 1 os slfs ct () . k] (begin . k))
	       ;; there is a binding
	       ([_ 1 os slfs ct (n m . rest) . ts]
		(let-syntax-rule ([K . types] 
	          (member?? n types
		    (rec3 1 os slfs n (m . rest) . ts)
	            (member?? m types
		     (rec3 1 os slfs ct rest
			(ty-sugar m n os 
			   (redefine-thyself* os [] slfs
			      (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9) . ts)))
		     (rec3 1 os slfs ct (m . rest)
			(ty-sugar ct n os 
			   (redefine-thyself* os [] slfs
			      (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9) . ts)))
		     )))
                   (TYPES K)
                   ))
	       ;; last binding
	       ([_ 1 os slfs ct (n . rest) . ts]
                (let-syntax-rule ([K . types]
	          (member?? n types
		    (rec3 1 os slfs n rest . ts)
	            (rec3 1 os slfs ct rest
			(ty-sugar ct n os 
			   (redefine-thyself* os [] slfs
			      (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9) . ts))
			)))
                    (TYPES K)
                  ))
	       ;; catch the error (will loop otherwise)
	       ([_ 1 _ . r]
		(syntax-error "as" . r))	       
	       ;; start
	       ([_ os slfs ns . body]
		(rec3 1 os slfs :unknown ns . body))
	       ))
   (Lambda rec4 (syntax-rules ()
	       ;; end
	       ([_ 1 os slfs ct () . k] k)
	       ;; there is a binding
	       ([_ 1 os slfs ct (n m . rest) lt (bs ...) . ts]
                (let-syntax-rule ([K . types]
	          (member?? n types
		    (rec4 1 os slfs n (m . rest) lt (bs ...) . ts)
	            (member?? m types
		     (rec4 1 os slfs ct rest
			lt (bs ... n)
			(ty-sugar m n os 
			   (redefine-thyself* os [] slfs
			      (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9) . ts)))
		     (rec4 1 os slfs ct (m . rest)
			lt (bs ... n)
			(ty-sugar ct n os 
			   (redefine-thyself* os [] slfs
			      (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9) . ts)))
		     )))
                   (TYPES K)
                   ))
	       ;; last binding
	       ([_ 1 os slfs ct (n . rest) lt (bs ...) . ts]
		(let-syntax-rule ([K . types]
	          (member?? n types
		    (rec4 1 os slfs n rest lt (bs ...) . ts)
	            (rec4 1 os slfs ct rest
			lt (bs ... n)
			(ty-sugar ct n os 
			   (redefine-thyself* os [] slfs
			      (rec0 rec1 rec2 rec3 rec4 rec5 rec6 rec7 rec8 rec9) . ts))
			)))
                    (TYPES K)
                    ))
	       ;; catch the error (will loop otherwise)
	       ([_ 1 _ . r]
		(syntax-error "Lambda" . r))	       
	       ;; start
	       ([_ os slfs nvs . body]
		(rec4 1 os slfs :unknown nvs lambda () . body))
	       ))
   (Let rec5 (syntax-rules ()
	       ;; finish
               ([_ 1 o s ["loop" name . ns] vs () . body]
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
		(rec5 1 o s ["loop" name] [] (nvs ...) . body))
	       ))
   (Let* rec6 (syntax-rules ()
	       ;; finish
	       ([_ 1 o s ct () . body]
		(let () . body))
	       ;; engine
	       ([_ 1 o s ct ([n ... v] t . rest) . body]
		(let-syntax-rule ([K . types]
	          (member?? t types	
		     ((rec4 o s (ct n ... t)
			  (rec6 1 o s ct rest . body))
		      v)
		     ((rec4 o s (ct n ...)
			  (rec6 1 o s ct (t . rest) . body))
		      v)
		     ))
                   (TYPES K)
		   ))
	       ([_ 1 o s ct ([n ... v] . rest) . body]
		((rec4 o s (ct n ...)
		    (rec6 1 o s ct rest . body))
		 v))
	       ([_ 1 o s ct (nv . rest) . body]
		(rec6 1 o s nv rest . body))
	       ;; start
	       ([_ o s nvs . body]
		(rec6 1 o s :unknown nvs . body))
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
		   (ns ... n) (vs ... v) (<undefined> . ds)
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
		   (ns ... n) (vs ... v) (<undefined> . ds)
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
   );)

;; redefine a few derived forms to use new LAMBDA
(define-syntax Define (syntax-rules ()
      ((_ (var . args) . body) (define var (Lambda args . body)))
      ((_ var expr) (define var expr))
      ((_ var) (define var))
      ))
(define-syntax Def (syntax-rules ()
      ((_ (var . args) . body) (begin
	  (define var (Lambda args . body))
	  (define-syntax var var)
	  ))
      ((_ var expr) (begin
	  (define var expr)
	  (define-syntax var var)
	  ))
      ((_ var) (begin
	  (define var)
	  (define-syntax var var)
	  ))
      ))

(define-syntax Defn (syntax-rules ()
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
)