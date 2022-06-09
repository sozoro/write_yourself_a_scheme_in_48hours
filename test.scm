(load "stdlib.scm")

(write "hello world!")

(define (counter inc) (lambda (x) (set! inc (+ inc x)) inc))
(define my-counter (counter 5))
(write (my-counter 3))
(write (my-counter 6))
(write (if (eqv? (my-counter 0) 14)
           "counter test: OK"
           "counter test: Failed"))

(define one-ten '(1 2 3 4 5 6 7 8 9 10))
(write (apply sum one-ten))
(write (length one-ten))
(write (map (lambda (x) (+ x 1)) one-ten))
(write (filter (lambda (x) (not (eqv? x 5))) one-ten))

(define test-var 2)
(define (loop func) (eval func) (loop func))
(loop '(write (eval (read))))
; This REPL is broken ↓
;   (define test-var 1)
;   1
;   test-var
;   1
;   (define test-var2 2)
;   2
;   test-var2
;   Getting an unbound variable: test-var2
;
; maybe, we should use nested environment
