(code;;bones
(define-anaphora (_ _')
   (>>- rec1 (syntax-rules ()
		([_ _ x fa] fa)
		([_ (thy thy') slfs fa . fb]
		 (let-syntax ([thy' thy]
			      [thy fa])
		    (redefine-thyself* (thy thy') [] slfs (rec1 rec2 rec3)
		       (rec1 (thy thy') slfs . fb)
		       )
		    ))
		))
   (>>= rec2 (syntax-rules ()
		([_ _ x fa] fa)
		([_ (thy thy') slfs fa . fb]
		 (let ([thy' thy]
		       [thy fa])
		    (redefine-thyself* (thy thy') [] slfs (rec1 rec2 rec3)
		       (rec2 (thy thy') slfs . fb)
		       )
		    ))
		))
   (>>~ rec3 (syntax-rules ()
		([_ _ x fa] fa)
		([_ (thy thy') slfs fa . fb]
		 (let ([thy' thy]
		       [thy fa])
		    (redefine-thyself* (thy thy') [] slfs (rec1 rec2 rec3)
		       (and thy (rec3 (thy thy') slfs . fb))
		       )
		    ))
		))
   )
)