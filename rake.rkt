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
  (let ([env (make-hash '())]) (foldl (lambda (code _) (match code
                                                         [(list 'def id expr) (reg-binding env id expr)]
                                                         [_ (interpret env code)])) '() prog)))

(define (reg-binding env id expr)
  (if (hash-has-key? env id) (report-error 'duplicate-name id) (begin
                                                                 (hash-set! env id (closure empty empty empty))    ;; empty closure as default value for recursive call check
                                                                 (hash-set! env id (interpret env expr))))
  )

#|
(interpret env expr) -> any
  env: hash?
    The environment with which to evaluate the expression.
  expr: datum?
    A syntactically-valid Rake expression.

  Returns the value of the Rake expression under the given environment.
|#
(define (interpret env expr)
  (match expr
    [(list 'fun args fbody) (closure args (make-closure-env env (make-hash '()) args fbody) fbody)]
    [(list 'when cond-expr then-expr else-expr) (print "NOT YET")]
    [(list-rest f-raw args-raw)  (let ([func (interpret env f-raw)])
                                   (if (is-procedure func)    ;; 1 check if is function
                                       (let ([args (map (lambda (arg) (interpret env arg)) args-raw)])    ;; 2 eager eval args
                                         (begin
                                           (cond [(builtin? f-raw) (apply func args)]    ;; built-ins get evalueated directly without error checking args
                                                 [(not (equal? (length (closure-args func)) (length args))) (report-error 'arity-mismatch (length args) (length (closure-args func)))]    ;; 3 arity mismatch
                                                 [else (interpret-func env func args)])    ;; 4 func application
                                           )
                                         )
                                       (report-error 'not-a-function func)))]
    [_ (cond
         [(or (number? expr) (boolean? expr)) expr]
         [(hash-has-key? env expr) (hash-ref env expr)]
         [(builtin? expr) (hash-ref builtins expr)]
         [else (report-error 'unbound-name expr)]
         )]))


(define (interpret-func env func args)
  (let ([comp-env (hash-copy env)])
    (begin
      (for ([(k v) (closure-closure-env func)]) (hash-set! comp-env k v))    ;; add compile-time statically evaluated identifiers in closure to composite env
      (for ([i (in-naturals 0)] [key (closure-args func)]) (hash-set! comp-env key (list-ref args i)))    ;; add passed-in arguments to composite env
      (interpret comp-env (closure-body func))
      )
    )
  )

(define (make-closure-env env closure-env args expr)
  (foldl (lambda (elem closure-env) (cond
                                      [(list? elem) (make-closure-env env closure-env args elem)]    ;; recursive env
                                      [(or (number? elem) (boolean? elem)) closure-env]
                                      [(member? elem args) closure-env]
                                      [(not (hash-has-key? env elem)) closure-env]    ;; identifier validity checked at runtime
                                      [else (let ([val (hash-ref env elem)])    ;; if elem is an empty closure, which is used to represent an on-going function definition, report unbound-name error
                                              (if (and (closure? val) (empty? (closure-args val)) (empty? (closure-closure-env val)) (empty? (closure-body val)))
                                                  (report-error 'unbound-name elem)
                                                  (begin (hash-set! closure-env elem val)    ;; otherwise set closure-env and return it
                                                         closure-env)))]))                    
         closure-env expr)
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
(struct closure (args closure-env body))
