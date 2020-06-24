#lang racket #| CSC324 Summer 2020 Assignment 1 |# 
#|
Module: rake_errors
Description: Assignment 1: The Rake Interpreter

   ___             _               \\
  | _ \   __ _    | |__    ___      \\
  |   /  / _` |   | / /   / -_)      \\
  |_|_\  \__,_|   |_\_\   \___|       \\
_|"""""|_|"""""|_|"""""|_|"""""|    ///\\\
"`-0-0-'"`-0-0-'"`-0-0-'"`-0-0-'   ///  \\\

This code is provided solely for the personal and private use of students
taking the CSC324 course at the University of Toronto. Copying for purposes
other than this use is expressly prohibited. All forms of distribution of
this code, including but not limited to public repositories on GitHub,
GitLab, Bitbucket, or any other online platform, whether as given or with
any changes, are expressly prohibited.

Copyright: (c) University of Toronto
               CSC324 Principles of Programming Languages, Summer 2020

|#
(provide run-interpreter)

(require racket/hash)  ; You may use the functions imported from this module.
(require "rake_errors.rkt")


;-----------------------------------------------------------------------------------------
; Main functions (skeleton provided in starter code)
;-----------------------------------------------------------------------------------------
#|
(run-interpreter prog) -> any
  prog: datum?
    A syntactically-valid Rake program.

  Evaluates the Rake program and returns its value, or raises an error if the program is
  not semantically valid.
|#
(define (run-interpreter prog)
  (let ([env (make-hash '())]
        [contract-env (make-hash '())])
    (foldl(lambda (code _) (match code
                             [(list 'def id expr) (reg-binding contract-env env id expr)] ; function definition
                             [(list 'def-contract id expr) (contract-binding contract-env env id expr)] ; contract definition
                             [_ (interpret contract-env env code)] ; evaluate expression
                             ))
          '()
          prog))) 


(define (reg-binding contract-env env id expr)
  (if (hash-has-key? env id) (report-error 'duplicate-name id) (begin
                                                                 (hash-set! env id (closure empty empty empty))    ;; empty closure as default value for recursive call check
                                                                 (hash-set! env id (interpret contract-env env expr))))
  )


(define (contract-binding contract-env env id expr)
  (cond
    [(not (hash-has-key? env id)) (report-error 'unbound-name id)] ; throw error if function has not been defined
    [(hash-has-key? contract-env id) (report-error 'duplicate-name id)] ; throw error if contract definition has already been defined
    [else (hash-set! contract-env id expr)]
    ))


#| Check each argument against contract PRE-condition from left to right
Returns false if any of the checks fail, otherwise return true
|#
(define (valid-precondition? contract-env env id args)

  (if (hash-has-key? contract-env id)
      (match (hash-ref contract-env id)
        [(list preconds ... '-> postcond ...)
         (foldl (lambda (precond arg result)
                  (if (not result) #f ; return false if one of the previous precondtions failed
                      ; check if current argument matches corresponding precondition
                      (check-condition contract-env env precond arg)))
                #t
                preconds
                args )]
        [_ #f])
      #t ; return true if no contract is defined
      ))


#| Check return value against contract POST-condition
if check fails return false, otherwise return true
|#
(define (valid-postcondition? contract-env env id return-val)
  (if (hash-has-key? contract-env id)
      (match (hash-ref contract-env id)
        [(list preconds ... '-> postcond)
         ; check if return value matches postcondition
         (check-condition contract-env env postcond return-val)]
        [_ #f])
      #t ; return true if no contract is defined
      ))


(define (check-condition contract-env env condition value)
  ; check if value matches condition
  (match condition
    ; type check
    ['boolean? (boolean? value)]
    ['integer? (integer? value)]
    ['procedure? (is-procedure value)]
    ; predicate check, evaluate predicate on same environment
    [(list 'fun args fbody) (interpret contract-env env (list condition value))]
    ; no constraint
    ['any #t]
    ))
  

#|
(interpret env expr) -> any
  env: hash?
    The environment with which to evaluate the expression.
  expr: datum?
    A syntactically-valid Rake expression.

  Returns the value of the Rake expression under the given environment.
|#
(define (interpret contract-env env expr)
  (match expr
    [(list 'fun args fbody) (if (validate-closure-env env args fbody) (closure args (hash-copy env) fbody) (void))]
    [(list 'when cond-expr then-expr else-expr) (if (interpret contract-env env cond-expr) (interpret contract-env env then-expr) (interpret contract-env env else-expr))]
    [(list-rest f-raw args-raw)  (let ([func (interpret contract-env env f-raw)])
                                   (if (is-procedure func)    ;; 1 check if is function
                                       (let ([args (map (lambda (arg) (interpret contract-env env arg)) args-raw)])    ;; 2 eager eval args
                                         (cond [(and (not (hash-has-key? env f-raw)) (builtin? f-raw)) (apply func args)]    ;; 3 built-ins get evalueated without error checking. Shadowing allowed
                                               [(not (equal? (length (closure-args func)) (length args))) (report-error 'arity-mismatch (length args) (length (closure-args func)))]    ;; 3 arity mismatch
                                               [(not (valid-precondition? contract-env env f-raw args)) (report-error 'contract-violation)]   ;; 4 check contract pre-conditions before function application
                                               [else (let ([return-val (interpret-func contract-env env func args)]) ;; 5 func application
                                                       (if (not (valid-postcondition? contract-env env f-raw return-val))   ;; 6 check post-condition on return value
                                                           (report-error 'contract-violation)
                                                           return-val   ;; 7 produce return value
                                                           ))]    
                                               ))
                                       (report-error 'not-a-function func)))]
    [_ (cond
         [(or (number? expr) (boolean? expr)) expr]
         [(hash-has-key? env expr) (hash-ref env expr)]
         [(builtin? expr) (hash-ref builtins expr)]
         [else (report-error 'unbound-name expr)]
         )]))


(define (interpret-func contract-env env func args)
  (let ([comp-env (make-hash '())])
    (begin
      (for ([(k v) (closure-env func)])
        (hash-set! comp-env k v))    ;; add compile-time statically evaluated identifiers in closure to composite env
      (for ([i (in-naturals 0)] [key (closure-args func)])
        (hash-set! comp-env key (list-ref args i)))    ;; add passed-in arguments to composite env
      (interpret contract-env comp-env (closure-body func))
      )
    )
  )


(define (validate-closure-env env args expr)
  (if (list? expr)
      (foldl (lambda (elem _) (cond
                                [(list? elem) (validate-closure-env env args elem)]    ;; recursive env
                                [else         (validate-closure-element env args elem)]))                    
             #t expr)
      (validate-closure-element env args expr))
  )

(define (validate-closure-element env args elem)
  (cond
    [(or (number? elem) (boolean? elem)) #t]
    [(member? elem args) #t]
    [(not (hash-has-key? env elem)) #t]    ;; identifier validity checked at runtime
    [else (let ([val (hash-ref env elem)])    ;; if elem is an empty closure, which is used to represent an on-going function definition, report unbound-name error
            (if (and (closure? val) (empty? (closure-args val)) (empty? (closure-env val)) (empty? (closure-body val)))
                (report-error 'unbound-name elem)
                #t))]
    )
  )


(define (member? elem lst)
  (match (member elem lst)
    [(list-rest _ _) #t]
    [_ #f]
    )
  )

(define (is-procedure x)
  (or (closure? x) (member? x (hash-values builtins))))

;-----------------------------------------------------------------------------------------
; Helpers: Builtins and closures
;-----------------------------------------------------------------------------------------
; A hash mapping symbols for Rake builtin functions to their corresponding Racket value.
(define builtins
  (hash
   '+ +
   'equal? equal?
   '< <
   'integer? integer?
   'boolean? boolean?
   ; Note: You'll almost certainly need to replace procedure? here to properly return #t
   ; when given your closure data structure at the end of Task 1!
   'procedure? is-procedure
   ))

; Returns whether a given symbol refers to a builtin Rake function.
(define (builtin? identifier) (hash-has-key? builtins identifier))

#|
Starter definition for a closure "struct". Racket structs behave similarly to
C structs (contain fields but no methods or encapsulation).
Read more at https://docs.racket-lang.org/guide/define-struct.html.

You can and should modify this as necessary. If you're having trouble working with
Racket structs, feel free to switch this implementation to use a list/hash instead.
|#
(struct closure (args env body))
