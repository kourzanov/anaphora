;#lang racket
#!r6rs
;#lang r6rs

;(module test scheme/base
; (require (for-syntax scheme/base))

;(define [it] <undefined>);(set! it it))
(define it #f)

(display [>>-
  (+ 123 234)
  (begin (display 'HERE) (* it 345))
  456
  (- it (>>- 6 (- it 1)))
  (cons pit it)
])
(newline)

(display [>>=
  (+ 123 234)
  (begin (display 'HERE) (* it 345))
  456
  (- it (>>= 6 (- it 1)))
  (cons pit it)
])
(newline)
;)

(Define [test s :string]
   (display (type s quote))(newline)
   (display #'(s length))(newline)
   (ref s 2)
   ;(test s)
   )

(display (test "0abcd")) (newline)

(display (Let ([li :list '#(1 2 3)]
	       [st :string "abcde"])
  (Let ([li :vector li]
  	[i :int 123]
	[x :fix 1]
	[y :flo 2.]
	[z 3])
   (display (type li quote))
     (newline)
     ;(set! li 1 20)
     (display (ref li 1))
     (newline)
     #'(li[1]:= 20)
     #'(li[1])
     (display (type st quote))
     (newline)
     (display #'(st[3]))
     (newline)
     #'(st[3]:= #\D)
     (display st)
     (newline)
     (display (type i quote))
     (display (char i))
     (newline)
     (display (+ x 2)) (newline)
     (display (+ y 1.)) (newline)
     (+ z .1)
     )))

(newline)

(display (Let (:fix [z 300] [y 200] [x 100])
(Do (:fix (i 0 (+ i 1))
          (x x (rsh x 1)))
    ((<= x 0) #f)
    (display (+ i 1))
    (display " ")
    (display (lsh x 1))
    (newline))
(+ y x)
))
(newline)

(display (>-> (+ 1 2 3) :fix
   (* it 2) 
   (+ it it) ;:flo
   (* 2 it)))
(newline)
(display (>=> (+ 1 2 3) :fix
   (* it 2) 
   (+ it it) ;:flo
   (* 2 it)))
(newline)

(Let ([v :bytevector '#vu8(1 2 3 4 5 6 7 8)])
   (display (length v))
   (newline)
   (display v)
   (newline)
   #'(v[1]:= 20)
   (display #'(v[1]))
   (newline)
   (display #'(v[0]:flo))
   (newline)
   #'(v[0]:= 3.1415926 :flo)
   (display v)
   (newline)
   (display #'(v[0]:flo))
   (newline)
   )

#;(Let ([v :f64vector '#vu8(10 20 30 40 50 60 70 80)])
   (display #'(v[0]))
   (newline)
)

(display (>-> 012 ;:fix
     123 
     234 ;:flo
     (+ it;[nth _']
	;[nth pit 1]
	[nth pit 1 1] ;_
	[nth pit 1 1 1]
	;[nth _' 1 1 1 1]
	)
     ))
(newline)

;)
