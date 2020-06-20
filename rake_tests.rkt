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

  (test-equal? "Unary function call"
               (run-interpreter '(((fun (x) (+ x 1)) 1)))
               2)

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
  
  (test-equal? "HOF"
               (run-interpreter '((def a (fun (f1) (fun (k) (+ (f1 k) k))))
                                  ((a (fun (i) (+ i -10))) 5)))
               0)    ;; adrian added test
  
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

  #;(test-equal? "Contract: g defined after f but before f's contract"
               (run-interpreter '((def f (fun (x) (+ x 1)))
                                  (def g (fun (x) (f x))) ; the env for g does not know about the contract!
                                  (def small 10)
                                  (def-contract f ((fun (x) (< x small)) -> integer?)) 
                                  (g 999)))
               1000)
  
  #;(test-exn "Contract: g defined after f and after f's contract"
            (regexp (hash-ref error-strings 'contract-violation))
            (thunk (run-interpreter '((def f (fun (x) (+ x 1)))
                                      (def small 10)
                                      (def-contract f ((fun (x) (< x small)) -> integer?))
                                      (def g (fun (x) (f x))) ; the env for g knows about the contract!
                                      (g 999)))))
  
  #;(test-equal? "Contract: (integer? -> boolean?), valid call"
                 (run-interpreter '((def f (fun (x) (< x 3)))
                                    (def-contract f (integer? -> boolean?))
                                    (f 1)))
                 #t))
