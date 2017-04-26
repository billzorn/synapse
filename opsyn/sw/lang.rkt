#lang s-exp rosette

(require "../engine/util.rkt" rosette/lib/reflect/match racket/serialize)

(provide (all-defined-out))

(struct operation () #:transparent)
(struct branch operation (op1 cases) #:transparent)
(struct arith operation (op1 op2) #:transparent)
(struct reference operation (x) #:transparent)

(define-syntax (define-operation stx)
  (syntax-case stx ()
    [(_ [id kind])
     (with-syntax ([deserialize-id (datum->syntax #'id
                                                  (string->symbol
                                                   (format "deserialize-info:~a" (syntax-e #'id)))
                                                  #'id)])
       #'(begin
           (define deserialize-id
             (make-deserialize-info
              (lambda e (apply id e))
              (const #f)))
           (struct id kind () #:transparent
             #:property prop:serializable
             (make-serialize-info
              (lambda (s)
                (match s
                  [(branch op1 cases) (vector op1 cases)]
                  [(arith op1 op2) (vector op1 op2)]
                  [(reference x) (vector x)]))
              #'deserialize-id
              #f
              (or (current-load-relative-directory) (current-directory))))))]
    [(_ [id kind] more ...)
     #'(begin
         (define-operation [id kind])
         (define-operation more ...))]))

(define-operation
  [switch branch]
  [swadd arith]
  [swmul arith]
  [swarg reference]
  [swconst reference])

(define (swinterp op inputs)
  (match op
    [(switch op1 (cons (cons branches op2) tail))
     (if (set-member? branches (swinterp op1 inputs))
         (swinterp op2 inputs)
         (swinterp (switch op1 tail) inputs))]
    [(swadd op1 op2) (finitize (+ (swinterp op1 inputs)
                                  (swinterp op2 inputs)))]
    [(swmul op1 op2) (finitize (* (swinterp op1 inputs)
                                  (swinterp op2 inputs)))]
    [(swarg x) (finitize (vector-ref inputs x))]
    [(swconst x) (finitize x)]))
