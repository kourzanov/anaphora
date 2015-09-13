#! /usr/bin/env bgl
; begin
(cond-expand (bigloo-eval (module simplex-bigloo
   (library srfi1 slib);for debug
   (import (synrules "synrules.sch")
      helpers))
)(else (module simplex-bigloo
   (library srfi1 slib);for debug
   )
(load "synrules.sch")
(load "forall.scm")
(load "dodger.sch")
(load "cases.scm")
(load "cond-expand.sch")
(load "helpers.scm")
(load "obj-syntax.sch")
(load "debug.scm")
))

(def (fuck-up . args) (error "This shouldn't happen" 'error args))

(Defn (simplex a :matrix m1 m2 m3)
   (defn *epsilon* 1e-6)
   (if (not (and (>= m1 0)
		 (>= m2 0)
		 (>= m3 0)
		 (= {a .rows} (+2+ m1 m2 m3))))
       (fuck-up 'one))
   (Let* ((m12 (+1+ m1 m2))
	  (m (-2+ {a .rows}))
	  (n (-1+ {a .cols}))
	  (l1 :vector (make-vector n))
	  (l2 :vector (make-vector m))
	  (l3 :vector (make-vector m2))
	  (nl1 n)
	  (iposv :vector (make-vector m))
	  (izrov :vector (make-vector n))
	  (ip 0)
	  (kp 0)
	  (bmax 0.0)
	  (one? #f)
	  (pass2? #t))
      (defn (simp1 mm abs?)
	 (set! kp {l1[0]})
	 (set! bmax {a[mm kp]})
	 (do ((k 1 (+1+ k))) ((>= k nl1))
	     (if (positive?
		    (if abs?
			(- (abs {a[mm {l1[k]}]}) (abs bmax))
			(- {a[mm {l1[k]}]} bmax)))
		 (begin (set! kp {l1[k]})
			(set! bmax {a[mm {l1[k]}]})))))
      (defn (simp2)
	 (set! ip 0)
	 (let ((q1 0.0)
	       (flag? #f))
	    (do ((i 0 (+1+ i))) ((= i m))
		(if flag?
		    (if (< {a[{l2[i]} kp]} (- *epsilon*))
			(let ((q (/ (- {a[{l2[i]} 0]})
				    {a[{l2[i]} kp]})))
			   (cond
			      ((< q q1) (set! ip {l2[i]}) (set! q1 q))
			      ((= q q1)
			       (let ((qp 0.0)
				     (q0 0.0))
				  (let loop ((k 1))
				     (if (<= k n)
					 (begin
					    (set! qp
					       (/ (- {a[ip k]}) {a[ip kp]}))
					    (set! q0 (/ (- {a[{l2[i]} k]})
							{a[{l2[i]} kp]}))
					    (if (= q0 qp) (loop (+1+ k))))))
				  (if (< q0 qp) (set! ip {l2[i]})))))))
		    (if (< {a[{l2[i]} kp]} (- *epsilon*))
			(begin (set! q1 (/ (- {a[{l2[i]} 0]})
					   {a[{l2[i]} kp]}))
			       (set! ip {l2[i]})
			       (set! flag? #t)))))))
      (defn (simp3 one?)
	 (let ((piv (/ {a[ip kp]})))
	    (do ((ii 0 (+1+ ii))) ((= ii (+ m (if one? 2 1))))
		(if (not (= ii ip))
		    (begin {a[ii kp]:=(* piv {a[ii kp]})}
			   (do ((kk 0 (+1+ kk))) ((= kk (+1+ n)))
			       (if (not (= kk kp))
				   {a[ii kk]:=(- {a[ii kk]}
						 (* {a[ip kk]}
						    {a[ii kp]}))})))))
	    (do ((kk 0 (+1+ kk))) ((= kk (+1+ n)))
		(if (not  (= kk kp))
		    {a[ip kk]:=(* (- piv) {a[ip kk]})}))
	    {a[ip kp]:= piv}))
      (do ((k 0 (+1+ k))) ((= k n))
	  {l1[k]:=(+1+ k)}
	  {izrov[k]:= k})
      (do ((i 0 (+1+ i))) ((= i m))
	  (if (negative? {a[(+1+ i) 0]}) (fuck-up 'two))
	  {l2[i]:=(+1+ i)}
	  {iposv[i]:=(+ n i)})
      (do ((i 0 (+1+ i))) ((= i m2)) {l3[i]:=#t})
      (if (positive? (+ m2 m3))
	  (begin
	     (do ((k 0 (+1+ k))) ((= k (+1+ n)))
		 (do ((i (+1+ m1) (+1+ i)) (sum 0.0 (+ sum {a[i k]})))
		     ((> i m) {a[(+1+ m) k]:=(- sum)})))
	     (let loop ()
		(simp1 (+1+ m) #f)
		(cond
		   ((<= bmax *epsilon*)
		    (cond
		       ((< {a[(+1+ m) 0]} (- *epsilon*)) (set! pass2? #f))
		       ((<= {a[(+1+ m) 0]} *epsilon*)
			(let loop ((ip1 m12))
			   (if (<= ip1 m)
			       (cond ((= {iposv[(-1+ ip1)]} (-1+ ip n))
				      (simp1 ip1 #t)
				      (cond ((positive? bmax) (set! ip ip1) (set! one? #t))
					    (else (loop (+1+ ip1)))))
				     (else (loop (+1+ ip1))))
			       (do ((i (+1+ m1) (+1+ i))) ((>= i m12))
				   (if {l3[(- i m1 1)]}
				       (do ((k 0 (+1+ k))) ((= k (+1+ n)))
					   {a[i k]:=(- {a[i k]})}))))))
		       (else (simp2) (if (zero? ip) (set! pass2? #f) (set! one? #t)))))
		   (else (simp2) (if (zero? ip) (set! pass2? #f) (set! one? #t))))
		(if one?
		    (begin
		       (set! one? #f)
		       (simp3 #t)
		       (cond
			  ((>= {iposv[(-1+ ip)]} (-1+ n m12))
			   (let loop ((k 0))
			      (cond
				 ((and (< k nl1) (not (= kp {l1[k]})))
				  (loop (+1+ k)))
				 (else
				  (set! nl1 (-1+ nl1))
				  (do ((is k (+1+ is))) ((>= is nl1))
				      {l1[is]:={l1[(+1+ is)]}})
				  {a[(+1+ m) kp]:=(+1+ {a[(+1+ m) kp]})}
				  (do ((i 0 (+1+ i))) ((= i (+2+ m)))
				      {a[i kp]:=(- {a[i kp]})})))))
			  ((and (>= {iposv[(-1+ ip)]} (+ n m1))
				{l3[(- {iposv[(-1+ ip)]} m1 n)]})
			   {l3[(- {iposv[(-1+ ip)]} m1 n)]:=#f}
			   {a[(+1+ m) kp]:=(+1+ {a[(+1+ m) kp]})}
			   (do ((i 0 (+1+ i))) ((= i (+2+ m)))
			       {a[i kp]:=(- {a[i kp]})})))
		       (let ((t {izrov[(-1+ kp)]}))
			  {izrov[(-1+ kp)]:={iposv[(-1+ ip)]}}
			  {iposv[(-1+ ip)]:= t})
		       (loop))))))
      (and pass2?
	   (let loop ()
	      (simp1 0 #f)
	      (cond
		 ((positive? bmax)
		  (simp2)
		  (cond ((zero? ip) #t)
			(else (simp3 #f)
			      (let ((t {izrov[(-1+ kp)]}))
				 {izrov[(-1+ kp)]:={iposv[(-1+ ip)]}}
				 {iposv[(-1+ ip)]:= t})
			      (loop))))
		 (else `(,iposv ,izrov)))))))


(Defn (test1)
 (Let* ([d :matrix
	    '#(#(0.0 1.0 1.0 3.0 -0.5)
	       #(740.0 -1.0 0.0 -2.0 0.0)
	       #(0.0 0.0 -2.0 0.0 7.0)
	       #(0.5 0.0 -1.0 1.0 -2.0)
	       #(9.0 -1.0 -1.0 -1.0 -1.0)
	       #(0.0 0.0 0.0 0.0 0.0))]
	[r (simplex '#(#(0.0 1.0 1.0 3.0 -0.5)
	       #(740.0 -1.0 0.0 -2.0 0.0)
	       #(0.0 0.0 -2.0 0.0 7.0)
	       #(0.5 0.0 -1.0 1.0 -2.0)
	       #(9.0 -1.0 -1.0 -1.0 -1.0)
	       #(0.0 0.0 0.0 0.0 0.0)) 2 1 1)]
	[v1 :vector (car r)]
	[v2 :vector (cadr r)]
	[t :vector (make-vector 5)])
    (pp (do ([i 0 (+1+ i)])
	((= i 5) t)
	{t[i]:= 0}
	(do ([j 0 (+1+ j)])
	    ((= j {v2 .length}) '#?)
	    (debug i j {v2[j]} {d[i j]})
	    {t[i]:=(+ {t[i]} (* {v2[j]} {d[i (+1+ j)]}))}
	    ;(newline)
	    )))
    r
    ))

;(pp (test))
;(do ((i 0 (+ i 1))) ((= i 100000)) (test))

(Defn (test)
 (simplex (vector (vector 0.0 1.0 1.0 3.0 -0.5)
		  (vector 740.0 -1.0 0.0 -2.0 0.0)
		  (vector 0.0 0.0 -2.0 0.0 7.0)
		  (vector 0.5 0.0 -1.0 1.0 -2.0)
		  (vector 9.0 -1.0 -1.0 -1.0 -1.0)
		  (vector 0.0 0.0 0.0 0.0 0.0))
	  2 1 1)
)

(pp (test))

(let ([p '#(
	    #(1 1 1 1 0)
	    #(0 8 -16 0 0)
	    #(0 0 16 -12 0)
	    )])
   (begin
      (pp (simplex p 0 1 0 ))
      (pp p)))

(time (do ((i 0 (+ i 1))) ((= i 1000000)) (test)))

; the end