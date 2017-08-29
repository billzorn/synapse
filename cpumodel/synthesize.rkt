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
(define strategy (make-parameter 'full))

(define iotab-file (make-parameter ""))
(define iotab (make-parameter (void)))

(define result (make-parameter #f))

(define (lookup-strat s)
  (case s
    [("n4-up") 'n4-up]
    [("full") 'full]
    [else (error "invalid strategy specified")]))

(define (iotab-generate-samples iotab-file iotab)
  (let ([sample
          (case (strategy)
            [(full) (iotab-fmt1-sample (bitwidth) (nsamples))]
            [(n4-up) iotab-n4-sample])])
    (with-output-to-file #:exists 'replace
      (iotab-samples.rkt iotab-file)
      (thunk (write (sample iotab))))))

(define (sread s)
  (define i (open-input-string s))
  (read i))

; Command line parsing
(command-line 
  #:once-each
  [("-w" "--width") w ("Bitwidth to use for synthesis."
                       "In order to correctly handle overflow, operations will actually"
                       "be performed at bitwidth one greater than that provided here.")
                    (bitwidth (string->number w))]
  [("-a" "--arity") a ("The number of inputs to the operation (default 3 -- input SR, op1 and op2)."
                       "This will determine how many values from the io table entry are"
                       "available to synthesized operations. Index may be a list of numbers "
                       "   (e.g. '(1, 2, 3))"
                       "in which case multiple syntheses will be run.")
                    (arity (sread a))]
  [("-i" "--index") i ("Which item in the io table entry to synthesize the computation of,"
                       "starting after <arity> inputs. For example, an io table entry "
                       "might look like:"
                       "  (carry-in op1 op2 result carry zero neg overflow)"
                       "If arity is 3, and index is 0, then 'result' will be the value"
                       "calculated. Index may be a list of numbers (e.g. '(1, 2, 3), in "
                       "which case multiple syntheses will be run. If both arity and index"
                       "are lists, they must have the same length.")
                    (index (sread i))]
  [("-m" "--maxlength") m ("Maximum number of instructions for a synthesized calculation."
                           "If no acceptable programs are found with fewer than <maxlength>"
                           "operations, then #f is returned.")
                        (maxlength (sread m))]
  [("-n" "--nsamples") n ("Initial number of samples from the io tables to use in synthesis."
                          "More samples will take longer to evaluate, but will have a better"
                          "chance of capturing the complete behavior of the operation.")
                       (nsamples (string->number n))]
  [("-s" "--strategy") s ("Strategy to use for synthesis. Available values:"
                          "  full, n4-up")
                       (strategy (lookup-strat s))]
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
           (iotab-generate-samples (iotab-file) (iotab)))
    (error "No such file: ~a\n" iotab-file-name)))

; Utilities for synthesis

; Macro that calls synapse search directly
(define-syntax-rule (synthesize-op ops precond postcond)
  (search #:metasketch `(bvop-simple ,ops ,postcond ,(arity) #:pre ,precond #:maxlength ,(maxlength))
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
          #:verbose #f))

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
(define (synthesize-and-check)
  (let ([pre (case (bitwidth)
               [(8) `valid-inputs.b]
               [(16) `valid-inputs.w])]
        [ops (case (bitwidth)
               [(8) `bvops.b]
               [(16) `bvops.w])]
        [post `(iotab-sample->post ,(iotab-samples.rkt (iotab-file)) 
                                   #:arity ,(arity)
                                   #:index ,(+ (arity) (index)) 
                                   #:width ,(bitwidth))]
        [tab (iotab)]
        [sat #t])
  (define (check)
    (set! sat #t)
    (let ([p (synthesize-op ops pre post)])
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
    (check))))

; Perform the actual synthesis, piecewise starting from LSB+3:LSB
(define (synthesize-n4-up)
  (let* ([post 
           (if (number? (index))
             `(iotab-sample->post ,(iotab-samples.rkt (iotab-file)) 
                                   #:arity ,(arity)
                                   #:index ,(+ (arity) (index))
                                   #:width ,(bitwidth))
             `(iotab-sample->post/n4-up-carry ,(iotab-samples.rkt (iotab-file)) 
                                              #:arity ,(arity)))]
         [tab (iotab)]
         [p (synthesize-op `bvops-nt `valid-inputs-n4 post)])
    (result p)))

(define (pad-list l n)
  (if (= n 0) null
    (if (null? (cdr l))
      (cons (car l) (pad-list l (- n 1)))
      (cons (car l) (pad-list (cdr l) (- n 1))))))

(unless (list? (arity)) (arity (list (arity))))
(unless (list? (index)) (index (list (index))))
(unless (list? (maxlength)) (maxlength (list (maxlength))))
(define num-syntheses (max (length (arity)) (length (index)) (length (maxlength))))

(arity (pad-list (arity) num-syntheses))
(index (pad-list (index) num-syntheses))
(maxlength (pad-list (maxlength) num-syntheses))

(printf "(")
(for ([i (in-range num-syntheses)])
  (parameterize ([arity (list-ref (arity) i)] 
                 [index (list-ref (index) i)] 
                 [maxlength (list-ref (maxlength) i)])
    (case (strategy)
      [(full)
       (synthesize-and-check)
       (printf "\"~a\" " (program->string (result)))
       (flush-output)]
      [(n4-up) 
       (synthesize-n4-up)
       (printf "\"(~a (lambda () ~a))\" " (if (= (arity) 3) "n4-up" "n4-up/c") (program->string (result)))
       (flush-output)])))
(printf ")")
(flush-output)
