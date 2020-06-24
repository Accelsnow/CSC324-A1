#lang racket #| â ̃... CSC324 Fall 2019: Assignment 1 Sample Tests â ̃... |#
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

Warning: as usual, these sample tests are very incomplete, and are meant to
give you a sense of the test structure we'll use, but NOT to verify the
complete correctness of your work on this assignment! Please add your own
tests here.  I recommend writing tests as you develop your interpreter's
functionality.
|#

(require rackunit)
(require "rake.rkt")
(require "rake_errors.rkt")


(module+ test
  (test-equal? "Numeric literal"
               (run-interpreter '(30))
               30)

  (test-equal? "Multiple independent defines"
               (run-interpreter '((def a 1)
                                  (def b #t)
                                  (def c #f)
                                  b))
               #t)

  (test-exn "Identifier with unused define (unbound-name error)"
            (regexp (format (hash-ref error-strings 'unbound-name) 'b))
            (thunk (run-interpreter '((def a 10)
                                      b))))

  (test-equal? "Simple +"
               (run-interpreter '((+ 30 40)))
               70)
  
  (test-equal? "Nullary function call"
               (run-interpreter '((def x 1)
                                  (def f (fun () (+ x 1)))
                                  (f)))
               2) ;; Ryland added test

  (test-equal? "Unary function call"
               (run-interpreter '(((fun (x) (+ x 1)) 1)))
               2)

  (test-equal? "Function returns argument itself"
               (run-interpreter '(
                                  (def f (fun (x) x))
                                  (f 10)))
               10) ;; Ryland added test
  
  (test-equal? "Multivariate function call"
               (run-interpreter '(
                                  (def f (fun (x y z) (+ z (+ x y))))
                                  (f 1 2 -3)
                                  ))
               0) ;; Ryland added test

  
  (test-equal? "Multivariate function call with unused arguments"
               (run-interpreter '(((fun (x y) (< 3 10)) 1 -10)))
               #t) ;; Ryland added


  (test-equal? "lexical scoping"
               (run-interpreter '((def y 4)
                                  ((fun (x) (+ x y)) 1)))
               5) ;; Ryland added test


  (test-equal? "lexical scoping 2 - runtime binding"
               (run-interpreter '((def f (fun (x) (+ x y))) ; y is bound at run time
                                  (def y 4)
                                  (f 1)))
               5) ;; Ryland added test
  
  (test-equal? "make-adder (like lecture)"
               (run-interpreter '((def make-adder
                                    (fun (n)
                                         (fun (m)
                                              (+ n m))))
                                  (def add-one (make-adder 1))
                                  (def add-two (make-adder 2))
                                  (+ (add-one 5) (add-two 10))))
               ; We write out explicitly the computation produced using
               ; correct substitution.
               (+ (+ 1 5) (+ 2 10)))
  
  (test-exn "Unbound identifier in function (fn called)"
            (regexp (format (hash-ref error-strings 'unbound-name) 'y))
            (thunk (run-interpreter '((def f (fun (x) (+ x y)))
                                      (f 1)))))
  
  (test-equal? "Unbound identifier in function (fn not called)"
               (run-interpreter '((def f (fun (x) (+ x y)))
                                  42))
               42)


  (test-equal? "if else simple"
               (run-interpreter '((when (< 1 2) 1 2)))
               1)    ;; adrian added test
  
  (test-equal? "if else with HOF then case"
               (run-interpreter '((def a (fun (condf thenf elsef v) (when (condf v) thenf elsef)))
                                  (def f1 (fun (v) (equal? v 0)))
                                  (def f2 (fun (v) (+ v 22)))
                                  (def f3 (fun (v) (integer? v)))
                                  ((a f1 f2 f3 0) 1)))
               23)    ;; adrian added test

  (test-equal? "if else with HOF else case and procedure?"
               (run-interpreter '((def a (fun (condf thenf elsef v) (when (condf v) thenf elsef)))
                                  (def f1 (fun (v) (equal? v 0)))
                                  (def f2 (fun (v) (+ v 22)))
                                  (def f3 (fun (v) (procedure? v)))
                                  ((a f1 f2 f3 1) #t)))
               #f)    ;; adrian added test
  
  (test-exn "duplicate identifier"
            (regexp (format (hash-ref error-strings 'duplicate-name) 'f))
            (thunk (run-interpreter '((def f (fun (x) (+ x 1)))
                                      (def f 2))))) ;; Ryland added test

  (test-exn "Invalid recursive call"
            (regexp (format (hash-ref error-strings 'unbound-name) 'f))
            (thunk (run-interpreter '((def f (fun (x) (f x)))
                                      10)))) ;; Ryland added test

  
  (test-equal? "HOF"
               (run-interpreter '((def a (fun (f1) (fun (k) (+ (f1 k) k))))
                                  ((a (fun (i) (+ i -10))) 5)))
               0)    ;; adrian added test
  
  (test-equal? "HOF with lambda"
               (run-interpreter '((def f (fun (x f1) (f1 x)))
                                  (f 1 (lambda (x) (< x 2)))))
               #t)    ;; Ryland added test
  

  (test-equal? "HOF with closures, ie returns another function"
               (run-interpreter '((def f (fun (x) (fun (k) (+ x k))))
                                  ((f 1) 5)))
               6)    ;; Ryland added test
  
  (test-equal? "shaowding & HOF"
               (run-interpreter '((def a
                                    (fun (f1 f2 k)
                                         (fun (f1 k)
                                              (fun (k) (f1 (f2 k) k)))))
                                  (def f1 (fun (a b) (+ a b)))
                                  (def f2 (fun (a) (+ a 3)))
                                  (def f3 (fun (a b) (+ a 22 b)))
                                  (((a f1 f2 10) f3 5) 1)))
               27)    ;; f1 is shadowed in function call. k = 1. adrian added test

  
  (test-exn "Unbound name: Contract defined before function"
            (regexp (format (hash-ref error-strings 'unbound-name) 'f))
            (thunk (run-interpreter '((def-contract f (any -> any)) ; contract defined before identifier f is bound
                                      (def f (fun (x) (+ x 1))))))) ;; Ryland added test

  (test-exn "Duplicate contract"
            (regexp (format (hash-ref error-strings 'duplicate-name) 'f))
            (thunk (run-interpreter '((def f (fun (x) (+ x 1)))
                                      (def-contract f (any -> any)) 
                                      (def-contract f (integer? any -> boolean?)) ; duplicate contract defintion
                                      )))) ;; Ryland added test


  (test-equal? "valid contract. no duplicate error thrown"
               (run-interpreter '((def f (fun (x) (+ x 0)))
                                  (def g f)
                                  (def-contract f (any -> any))
                                  (def-contract g (any -> any))
                                  (f 1000)
                                  ) )
               1000) ;; Ryland added test
  
  (test-equal? "Contract: g defined after f but before f's contract"
               (run-interpreter '((def f (fun (x) (+ x 1)))
                                  (def g (fun (x) (f x))) ; the env for g does not know about the contract!
                                  (def small 10)
                                  (def-contract f ((fun (x) (< x small)) -> integer?)) 
                                  (g 999)))
               1000)
  
  (test-exn "Contract: g defined after f and after f's contract"
            (regexp (hash-ref error-strings 'contract-violation))
            (thunk (run-interpreter '((def f (fun (x) (+ x 1)))
                                      (def small 10)
                                      (def-contract f ((fun (x) (< x small)) -> integer?))
                                      (def g (fun (x) (f x))) ; the env for g knows about the contract!
                                      (g 999)))))
  
  (test-equal? "Contract: (integer? -> boolean?), valid call"
               (run-interpreter '((def f (fun (x) (< x 3)))
                                  (def-contract f (integer? -> boolean?))
                                  (f 1)))
               #t))

(test-equal? "Contract with multiple precondtiions, valid call"
             (run-interpreter '((def low 100)
                                (def my-add (fun (x y) (+ x y)))
                                (def f (fun (a b f2) (f2 (+ a b) 2)))
                                (def-contract f (any (fun (x) (< x low)) procedure? -> integer?)) ;; contract predicate evaluted on same environment, ie lexical scoping applies
                                (f -900 99 my-add)))
             -799) ;; Ryland added test

(test-exn "Contract violation: precondition fails"
          (regexp (hash-ref error-strings 'contract-violation))
          (thunk  (run-interpreter '((def f (fun (x) (< x 3)))
                                     (def-contract f ((fun (x) (< x 0)) -> boolean?))
                                     (f 1))))) ;; Ryland added test


(test-exn "Contract violation: postcondition fails"
          (regexp (hash-ref error-strings 'contract-violation))
          (thunk  (run-interpreter '((def f (fun (x) (< x 3)))
                                     (def-contract f (any -> integer?))
                                     (f 1))))) ;; Ryland added test