# anaphora
define-anaphora macro for threading and overloading in Scheme.


Implementation is provided for 2 systems based on the ALEXPANDER (Bigloo and Bones)
and for systems implementing R6RS (using syntax-rules expander implementing required
extensions). 3 R6RS systems were tested: Vicare, Racket and Larceny (although only 
Vicare seems to work well).

Both threading and overloading is implemented.

Some minor differences in the standard library support for bytevectors in Bones
and R6RS imply a slightly different interface. Minor point, can be corrected.

No attempt to provide define-reader-ctor was made for other systems than Bigloo.
With Bigloo, one can use {form} instead of #'form (see the simplex.scm and tfft.scm).
