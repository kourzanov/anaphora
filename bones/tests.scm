#!bones-autocompile
(program;;bones
   (include "base.scm")
   (include "supp.scm")
   (include "fastmath.scm")
   (include "anaphoric.scm")
   (include "threading.scm")
   (include "basictype.scm")
(code
(print "Hello Bones!")
(print [>>-
  (+ 123 234)
  (begin (pp 'HERE) (* _ 345))
  456
  (- _ 5)
  (cons _' _)
])
(print [>>=
  (+ 123 234)
  (begin (write 'HERE) (* _ 345))
  456
  (- _ 5)
  (cons _' _)
])

(print (Let ([li :vector '#(1 2 3)])
  ;(as (li :list)
     (print (type li quote))
     (print (ref li 1))
     (set! li 1 20)
     (print #'(li[1]))
     (print #'(li[1]:= 30))
     ));)

(Define [test s :string]
   (print (length s) (type s quote)  #'(s length))
   (ref s 2)
   )

(print (test "abc"))

(print (Let ([li :list '#(1 2 3)]
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
     (display i)
     (display (type i quote))
     (newline)
     (display (char i))
     (newline)
     (print (+ x 2))
     (print (+ y 1.))
     (+ z .1)
     )))

;(Do ((i :fix 0 (+ i 1)))
;    ((>= i 10) #f)
;    (display i)
;    (newline))

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

(print (>=> (+ 1 2 3) :fix
   (* _ 2) 
   (+ _ _) ;flo
   (* 2 _)))

(print (>-> (+ 1 2 3) :fix
   (* _ 2) 
   (+ _ _) ;flo
   (max _ 25)
   (* 2 _)
   (flo _) :flo
   (+ _ .1)))

#u8(1 2 3 4)
(Let ([v :bytevector (bytevector 1 2 3)])
   (display (length v))
   (newline)
   (display v)
   (newline)
   #'(v[1]:= 20)
   (display #'(v[1]))
   (newline)
   )

(print (>-> 012 :fix
     123 
     234 ;:flo
     (+ _;[nth _']
	;[nth _' 1]
	[nth _' 1 1] ;_
	;[nth _' 1 1 1]
	;[nth _' 1 1 1 1]
	)
     ))

))
