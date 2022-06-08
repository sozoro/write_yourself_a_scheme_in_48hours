(define (not x)            (if x #f #t))
(define (null? obj)        (eqv? obj '()))

(define (list . objs)      objs)
(define (id obj)           obj)
(define (flip func)        (lambda (arg1 arg2) (func arg2 arg1)))
(define (curry func arg1)  (lambda (arg) (apply func (cons arg1 (list arg)))))
(define (compose f g)      (lambda (arg) (f (apply g arg))))

(define (foldr func end lst)
  (if (null? lst)
      end
      (func (car lst) (foldr func end (cdr lst)))))

(define (sum . lst)         (foldr + 0 lst))
(define (length lst)        (foldr (lambda (x y) (+ y 1)) 0 lst))
; (define (length lst)        (fold (lambda (x y) (+ x 1)) 0 lst))
(define (map func lst)      (foldr (lambda (x y) (cons (func x) y)) '() lst))
(define (filter pred lst)   (foldr (lambda (x y) (if (pred x) (cons x y) y)) '() lst))
