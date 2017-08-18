#lang s-exp rosette ; Requires a Racket 6.2 / Rosette 1.0 environment

(require racket/cmdline
         racket/format
         "../opsyn/engine/search.rkt"
         "../opsyn/bv/lang.rkt"
         "synth-utils.rkt"
         "iotab.rkt")

; Command line parameters

(define timeout (make-parameter 1800))
(define threads (make-parameter 2))
(define bitwidth (make-parameter 8))
(define arity (make-parameter 3))
(define index (make-parameter 0))
(define maxlength (make-parameter 4))
(define nsamples (make-parameter 64))

(define iotab-file (make-parameter ""))
(define iotab (make-parameter (void)))

(define result (make-parameter #f))

; Utility functions
(define (load-iotab file)
  (with-input-from-file file (λ () 
    (let ([tab (make-hash)] [pair (read)])
      (for ([i (in-naturals)] #:break (eof-object? pair))
        (hash-set! tab (first pair) (rest pair))
        (set! pair (read)))
      tab))))

; Command line parsing
(command-line 
  #:once-each
  [("-w" "--width") w ("Bitwidth to use for synthesis."
                       "In order to correctly handle overflow, operations will actually"
                       "be performed at bitwidth one greater than that provided here.")
                    (bitwidth (string->number w))]
  [("-a" "--arity") a ("The number of inputs to the operation (default 4)."
                       "This will determine how many values from the io table entry are"
                       "available to synthesized operations.")
                    (arity (string->number a))]
  [("-i" "--index") i ("Which item in the io table entry to synthesize the computation of,"
                       "starting after <arity> inputs. For example, an io table entry "
                       "might look like:"
                       "  (carry-in op1 op2 result carry zero neg overflow)"
                       "If arity is 3, and index is 0, then 'result' will be the value"
                       "calculated.")
                    (index (string->number i))]
  [("-m" "--maxlength") m ("Maximum number of instructions for a synthesized calculation."
                           "If no acceptable programs are found with fewer than <maxlength>"
                           "operations, then #f is returned.")
                        (maxlength (string->number m))]
  [("-n" "--nsamples") n ("Initial number of samples from the io tables to use in synthesis."
                          "More samples will take longer to evaluate, but will have a better"
                          "chance of capturing the complete behavior of the operation.")
                       (nsamples (string->number n))]
  [("-j" "--jobs" "--threads") j ("Number of jobs to use for synthesis.")
                               (threads (string->number j))]
  [("-t" "--timeout") t ("Timeout for synthesis.")
                      (timeout t)]
  #:ps ""
  #:args (iotab-file-name)

  ; Positional argument handling
  (if (file-exists? iotab-file-name) 
    (begin (iotab-file iotab-file-name)
           (iotab (load-iotab iotab-file-name)) 
           (iotab-generate-samples (iotab-file) (iotab) #:nsamples (nsamples)))
    (begin (printf "No such file: ~a\n" iotab-file-name) (exit))))

; Utilities for synthesis

; Macro that calls synapse search directly
(define-syntax-rule (synthesize-op precond postcond)
  (let ([sketch (case (bitwidth)
                  [(8) `bvop.b-simple]
                  [(16) `bvop.w-simple])])
    (search #:metasketch `(,sketch ,postcond ,(arity) #:pre ,precond #:maxlength ,(maxlength))
            #:threads (threads)
            #:timeout (timeout)
            #:bitwidth (+ (bitwidth) 1)
            #:exchange-samples #t
            #:exchange-costs #t
            #:use-structure #t
            #:incremental #t
            #:widening #f
            #:synthesizer 'kodkod-incremental%
            #:verifier 'kodkod%
            #:verbose #f)))

; Function that turns a synapse bv program into a string
(define (program->string p)
  (if (false? p) 
    "#f"
    (let* ([args '("carry-in" "op1" "op2" "dst")]
           [arity (program-inputs p)]
           [statements (make-vector (+ arity (length (program-instructions p))))])
      (for ([i (in-range (vector-length statements))])
        (if (< i arity)
          (vector-set! statements i (list-ref args i))
          (let* ([instr (list-ref (program-instructions p) (- i arity))]
                 [s (if (bv? instr) (format "(bv #x~a)" (~r (unary-r1 instr))) (format "~v" instr))])
            (for ([j (in-range i)])
              (set! s (string-replace s (format " ~a" j) (string-append " " (vector-ref statements j)))))
            (vector-set! statements i s))))
      (vector-ref statements (- (vector-length statements) 1)))))

; Perform the actual synthesis (and iterative check)
(let* ([pre (case (bitwidth)
                [(8) `valid-inputs.b]
                [(16) `valid-inputs.w])]
       [post `(iotab-sample->post ,(iotab-samples.rkt (iotab-file)) 
                                  #:arity ,(arity)
                                  #:index ,(+ (arity) (index)) 
                                  #:width ,(bitwidth))]
       [tab (iotab)]
       [sat #t])
(define (check)
  (set! sat #t)
  (let ([p (synthesize-op pre post)])
    (if (equal? p #f) #f
      (for ([kv (in-list (hash->list tab))])
        #:break (not sat)
        (define-values (key value) (values (first kv) (list-tail kv 1)))
        (define-values (c a b) (values (sr-carry (first key)) (second key) (third key)))
        (define sample (append (cons (sr-carry (first key)) (rest key)) (iotab-entry-separate value)))
        (define result (list-ref sample 3))
        (define inputs (list c a b result))
        (define val (list-ref sample (+ (arity) (index))))
        (set! sat (eq-under-width (bitwidth) (interpret p (take inputs (arity))) val))
        (unless sat (begin ;(printf "Program ~v doesn't satisfy iotab for ~a, ~a (was ~a, should be ~a), adding ~a to sample set\n" p a b (interpret p (take inputs arity)) val inputs)
                           (iotab-add-sample (iotab-file) sample)))))
    (if sat (result p) (check))))
(parameterize ([current-bitwidth (+ (bitwidth) 1)])
  (check)))

(printf "~a" (program->string (result)))

; Notes:
; - there are two things which determine the parameters of a synthesis search:
;    1. The assertions used (n4 carry-left, n4 carry-right, n8/16 sample)
;    2. The parameters passed to superopt (maxlength, timeout, pre/post
;    conditions (see above)

