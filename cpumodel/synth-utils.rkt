#lang s-exp rosette ; Requires a Racket 6.2 / Rosette 1.0 environment

(require (for-syntax racket/syntax))

(require "../opsyn/bv/lang.rkt"  
         "../opsyn/metasketches/superoptimization.rkt"  
         "../opsyn/metasketches/cost.rkt"
         "iotab.rkt")

(provide (all-defined-out))

(define (bvop.b-simple post arity
               #:finite? [finite? #t]
               #:maxlength [maxlength 4]
               #:cost-model [cost-model constant-cost-model]
               #:pre (pre void))
  (superopt∑ #:instructions bvops.b
             #:maxlength (if finite? maxlength +inf.0)
             #:arity arity
             #:pre   pre
             #:post  post
             #:cost-model cost-model))

(define (bvop.w-simple post arity
               #:finite? [finite? #t]
               #:maxlength [maxlength 4]
               #:cost-model [cost-model constant-cost-model]
               #:pre (pre void))
  (superopt∑ #:instructions bvops.w
             #:maxlength (if finite? maxlength +inf.0)
             #:arity arity
             #:pre   pre
             #:post  post
             #:cost-model cost-model))

(define bvops.b
  (list (bv 0) (bv 1) (bv #xf) bit8 bit9
        bvadd bvsub bvand bvor bvnot bvneg bvxor bveq
        pass eq0 samesign8 diffsign8 shr4 msp_dcarry))

(define bvops.w
  (list (bv 0) (bv 1) bit16 bit17
        bvadd bvsub bvand bvor bvnot bvneg bvxor bveq
        pass eq0 samesign16 diffsign16))

(define (valid-inputs.b inputs)
  (assert (and (= (first inputs) (bitwise-and (first inputs) #x1))
               (= (second inputs) (bitwise-and (second inputs) #xff))
               (= (third inputs) (bitwise-and (third inputs) #xff)))))
               ;(= (fourth inputs) (bitwise-and (fourth inputs) #xff)))))

(define (valid-inputs.w inputs)
  (assert (and (= (first inputs) (bitwise-and (first inputs) #x1))
               (= (second inputs) (bitwise-and (second inputs) #xffff))
               (= (third inputs) (bitwise-and (third inputs) #xffff)))))

; Utilities for passing samples between the harness and synapse worker processes

; Generate a temporary file for the samples based on the name of the iotab
; they're being sampled from
(define (iotab-samples.rkt iotab-file)
  (string-append 
    "/tmp/" 
    (string-replace 
      (last (string-split iotab-file "/")) 
      ".rkt" 
      "-samples.rkt.tmp")))

; NOTE: only runs on the parent, so we can reference iotab directly
(define (iotab-generate-samples iotab-file iotab #:nsamples (nsamples 64))
    (with-output-to-file #:exists 'replace
      (iotab-samples.rkt iotab-file)
      (thunk (write (iotab-fmt1-sample iotab nsamples)))))

(define (iotab-add-sample iotab-file sample)
  (let ([samples (with-input-from-file (iotab-samples.rkt iotab-file) read)])
    (with-output-to-file #:exists 'replace
      (iotab-samples.rkt iotab-file) 
      (thunk (write (vector-append samples (vector sample)))))))


(define (eq-under-width width a b)
  (define mask (- (arithmetic-shift 1 width) 1))
  (= (bitwise-and a mask) (bitwise-and b mask)))

; Turn an iotab sample into a postcondition function
; NOTE: runs under all workers! Anything passed to this function needs to be
; invariant after program startup!
(define (iotab-sample->post sample-file #:arity (arity 3) #:index (result-ind 0) #:width (width 8))
  (λ (P inputs)
    (let ([samples (with-input-from-file sample-file read)])
      (for* ([sample (in-vector samples )])
        (let* ([inputs (take sample arity)]
               [x (list-ref sample result-ind)]
               [assertion (eq-under-width width (interpret P inputs) x)])
          (assert assertion))))))

