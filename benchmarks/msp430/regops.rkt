#lang s-exp rosette

(require (for-syntax racket/syntax))

(require "../../opsyn/bv/lang.rkt"  
         "../../opsyn/metasketches/superoptimization.rkt"  
         "../../opsyn/metasketches/cost.rkt")

(require "../../../SAT/msp430/process-measurements.rkt"
         "../../../SAT/data/iotabs.rkt")

(provide (all-defined-out))

; requires bitwidth > 4
(define (valid-inputs-nt inputs)
  (assert (and (= (first inputs) (bitwise-and (first inputs) #x1))
               (= (second inputs) (bitwise-and (second inputs) #xf))
               (= (third inputs) (bitwise-and (third inputs) #xf)))))

; requires bitwidth == 8
(define (valid-inputs-b8 inputs)
  (assert (and (= (first inputs) (bitwise-and (first inputs) #x1)))))

; requires bitwidth > 8
(define (valid-inputs-b16 inputs)
  (assert (and (= (first inputs) (bitwise-and (first inputs) #x1))
               (= (second inputs) (bitwise-and (second inputs) #xff))
               (= (third inputs) (bitwise-and (third inputs) #xff)))))
  
(define (msp-general post arity
               #:finite? [finite? #f]
               #:maxlength [maxlength 8]
               #:cost-model [cost-model constant-cost-model]
               #:pre (pre void))
  (printf "msp-general invoking superopt ~a ~a\n" post arity)
  (superopt∑ #:instructions bvops-dadd-nt
             #:maxlength (if finite? maxlength +inf.0)
             #:arity arity
             #:pre   pre
             #:post  post
             #:cost-model cost-model))

(define bvops8-cmp
  (list (bv 0) (bv 1) (bv 7) (bv 8) (bv #x80) (bv #x100)
        bvadd bvsub bvand bvor bvnot bvshl bvashr bvlshr 
        bvneg bvredor bvxor bvsle bvslt bveq bvule bvult))

(define bvops8
  (list (bv 0) (bv 1) (bv 7) (bv 8) (bv #b80) (bv #x100)
        bvadd bvsub bvand bvor bvnot bvshl bvashr bvlshr 
        bvneg bvredor bvxor bveq))

(define bvops16
  (list (bv 0) (bv 1) (bv 15) (bv 16) (bv #x8000) (bv #x10000)
        bvadd bvsub bvand bvor bvnot bvshl bvashr bvlshr 
        bvneg bvredor bvxor bveq))

(define bvops-addc
  (list (bv 15) bvadd bvand))

(define bvops-dadd-nt
  (list (bv 1) (bv #xf)
        bvand bvadd bvor shr4 msp_dcarry))

(define bvops-dadd-nt-nocarry
  (list (bv 1) (bv 6) (bv 10) (bv 15)
        bvadd bvand bvor bvule bvmul shr4))

(define (iotab-n4->post iotab)
  (define (post P inputs)
    (for* ([c (in-range 2)]
           [a (in-range 16)]
           [b (in-range 16)])
      (let* ([inputs (list c a b)]
             [x (iotab-lookup-n4 iotab inputs)]
             [assertion (= (interpret P inputs) x)])
        (assert assertion))))
  post)

(define-values (dadd.b-n4c dadd.b-n4v)
  (iotab-split (iotab-fmt1->n4 dadd.b) 2))
(define dadd.b-n4c/post (iotab-n4->post dadd.b-n4c))
(define dadd.b-n4v/post (iotab-n4->post dadd.b-n4v))

(define-values (addc.b-n4c addc.b-n4v)
  (iotab-split (iotab-fmt1->n4 addc.b) 2))
(define addc.b-n4c/post (iotab-n4->post addc.b-n4c))
(define addc.b-n4v/post (iotab-n4->post addc.b-n4v))


(define addc-prog
  (program 3
           (list
            (bvadd 0 1)
            (bvadd 2 3)
            (bv 15)
            (bvand 4 5))))

(define (test-addc)
  (for* ([c (in-range 2)]
         [a (in-range 16)]
         [b (in-range 16)])
    (let* ([inputs (list c a b)]
           [ref (iotab-lookup-n4 addc.b-n4v inputs)]
           [v (interpret addc-prog inputs)])
      (unless (= ref v)
        (printf "c:~a a:~a b:~a, ref:~a got:~a~n"
                c a b ref v)))))
                   




;; test - (a & 1) ^ (b & 1)
(define spec1-data
  (vector 0 1 1 0))
(define (spec1-idx a b)
  (bitwise-ior (arithmetic-shift (bitwise-and a 1) 1)
               (bitwise-and b 1)))
(define (spec1 inputs)
  (vector-ref spec1-data (apply spec1-idx inputs)))
(define (spec1-alt inputs)
  (vector-ref spec1-data
              (bitwise-ior (arithmetic-shift (bitwise-and (first inputs) 1) 1)
                           (bitwise-and (second inputs) 1))))
(define (spec1-alt2 inputs)
  (let ([idx (apply spec1-idx inputs)])
    (cond
      [(= idx 0) 0]
      [(= idx 1) 1]
      [(= idx 2) 1]
      [(= idx 3) 0])))
(define (spec1-post P inputs)
  (printf "going to make assertions\n")
  (for* ([a (in-range 2)]
         [b (in-range 2)])
    (printf "  for: ~a ~a~n" a b)
    (let* ([x (vector-ref spec1-data (spec1-idx a b))]
           [_ (printf "  x: ~a~n" x)]
           [assertion (= (interpret P (list a b)) x)])
      (printf "asserting: ~a~n" assertion)
      (assert assertion))))
(define (spec1-post-manual P inputs)
  (assert (= (interpret P (list 0 0)) 0))
  (assert (= (interpret P (list 0 1)) 1))
  (assert (= (interpret P (list 1 0)) 1))
  (assert (= (interpret P (list 1 1)) 0)))

(define (spec1-pre inputs)
  (assert (and (= (first inputs) (bitwise-and (first inputs) 1))
               (= (second inputs) (bitwise-and (second inputs) 1)))))

(define (spec1-simple inputs)
  (bitwise-xor (bitwise-and (first inputs) 1) (bitwise-and (second inputs) 1)))

(define (spec2 inputs)
  (first inputs))

(define dcarry-prog
  (program 1 (list (msp_dcarry 0))))
(define (dcarry-post P inputs)
  (let ([assertion (= (interpret P inputs) (interpret dcarry-prog inputs))])
    (printf "asserting: ~a~n" assertion)
    (assert assertion)))

(define ule
  (program 2 (list (bvule 0 1))))
(define ult
  (program 2 (list (bvult 0 1))))





(define (iter-4n/cv n compute/c compute/v)
  (define (op sr a b)
    (let ([carry-in (bitwise-and sr 1)])
      (for/fold ([c carry-in]
                 [v 0])
                ([offset (in-range 0 (* n 4) 4)])
        (let*
         ([a_n (bitwise-and (>> a offset) #xf)]
          [b_n (bitwise-and (>> b offset) #xf)]
          [c_n (compute/c c a_n b_n)]
          [v_n (compute/v c a_n b_n)])
          (values
           c_n
           (bitwise-ior v (<< v_n offset)))))))
    op)

(define (dadd/v c a b)
  (interpret (program
              3
              (list
               (bv 15)
               (bvadd 0 1)
               (bvadd 2 4)
               (msp_dcarry 5)
               (bvand 3 6)))
             (list c a b)))

(define (bcd-carry x)
  (if (or (> x 9) (< x 0)) (+ x 6) x))

(define (dadd-compute/v c a b)
  (bitwise-and (bcd-carry (+ c a b)) 15))
(define (dadd-compute/c c a b)
  (bitwise-and (>> (bitwise-ior (+ c a b) (bcd-carry (+ c a b))) 4) 1))

(define (dadd/c c a b)
  (interpret (program 3 (list (bv 1) (bvadd 0 1) (bvadd 2 4) (msp_dcarry 5) (bvor 5 6) (shr4 7) (bvand 3 8)))
             (list c a b)))

(define dadd.b-bv (iter-4n/cv 2 dadd/c dadd/v))
(define dadd.b-compute (iter-4n/cv 2 dadd-compute/c dadd-compute/v))

(define (dadd.b-bv-test)
  (parameterize ([current-bitwidth 20])
    (for* ([c (in-range 2)]
           [a (in-range 256)]
           [b (in-range 256)])
      (let*-values ([(observed) (iotab-lookup-fmt1 dadd.b (list c a b))]
                    [(observed-c) (bitwise-and (first observed) 1)]
                    [(observed-v) (second observed)]
                    [(bv-c bv-v) (dadd.b-compute c a b)])
        (unless (and (= observed-c bv-c) (= observed-v bv-v))
          (printf "~a ~a ~a - obs: ~a ~a, bv: ~a ~a~n" c a b observed-c observed-v bv-c bv-v))))))



; simple ops (likely defined by 1-3 instruction bv programs)

; sample some number of values from the data table and hope that the resulting assertions
; are sufficient to more or less uniquely define the operation

(define (iotab-sample->post samples arity result-ind)
  (define (post P inputs)
    (for* ([sample (in-vector samples)])
      (let* ([inputs (take sample arity)]
             [x (list-ref sample result-ind)]
             [assertion (= (bitwise-and (interpret P inputs) #xff) x)])
        (assert assertion))))
  post)

(define-syntax (define-sample-post stx)
  (syntax-case stx ()
    [(_ iotab type value)
     (with-syntax ([name (format-id #'iotab #:source #'iotab "~a-sample-~a/post" (syntax-e #'iotab) (syntax-e #'type))])
       #'(define name value))]))

; defines the following values (given e.g. an iotab called add.b):
;  - add.b-sample-val/post
;  - add.b-sample-c/post
;  - add.b-sample-z/post
;  - add.b-sample-v/post
;  - add.b-sample-f/post
(define-syntax-rule (define-iotab-post/sample iotab)
  (begin (define samples (iotab-fmt1-sample iotab 512))
    (define-sample-post iotab val (iotab-sample->post samples 3 3))
    (define-sample-post iotab c (iotab-sample->post samples 4 4))
    (define-sample-post iotab z (iotab-sample->post samples 4 5))
    (define-sample-post iotab n (iotab-sample->post samples 4 6))
    (define-sample-post iotab v (iotab-sample->post samples 4 7))))

; Note: the postconditions for the flags have an arity of 4, because they can
; also use the result of the computation as part of the computation of the flag
; value.

; These should find a valid result in (less than) 4 instructions for most values
; and flags. Notable exceptions: overflow flag for add.b
  
(define-iotab-post/sample xor.b)
(define-iotab-post/sample add.b)
(define-iotab-post/sample sub.b)
(define-iotab-post/sample and.b)
(define-iotab-post/sample cmp.b)
(define-iotab-post/sample addc.b)
(define-iotab-post/sample subc.b)
(define-iotab-post/sample bic.b)
(define-iotab-post/sample bis.b)
(define-iotab-post/sample bit.b)

; These should probably _not_ find a valid result in 4 instructions

(define-iotab-post/sample dadd.b)


(define (msp-simpleop post arity
               #:finite? [finite? #t]
               #:maxlength [maxlength 4]
               #:cost-model [cost-model constant-cost-model]
               #:pre (pre void))
  (superopt∑ #:instructions bvops-nocmp
             #:maxlength (if finite? maxlength +inf.0)
             #:arity arity
             #:pre   pre
             #:post  post
             #:cost-model cost-model))

; Notes:
; - there are two things which determine the parameters of a synthesis search:
;    1. The assertions used (n4 carry-left, n4 carry-right, n8/16 sample)
;    2. The parameters passed to superopt (maxlength [?], timeout, pre/post
;    conditions (see above)

