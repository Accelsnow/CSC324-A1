#lang racket #| CSC324 Summer 2020: Assignment 1 Error Handling |#
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

Support module for reporting semantic errors in Rake programs.
You should read through this file to make sure you know how to call
`report-error` appropriately, but may not make any changes to this
file. (You aren't submitting it; we're providing our own version for testing.)
|#
(provide report-error error-strings)

;-------------------------------------------------------------------------------
; â ̃... Error reporting (don't change this) â ̃...
;-------------------------------------------------------------------------------
(define error-strings
  #hash(
        ; Requires the identifier (a symbol).
        (duplicate-name . "Error: identifier ~a was used twice in a definition.")

        ; Requires the identifier (a symbol).
        (unbound-name . "Error: identifier ~a could not be found.")

        ; Requires the value being called (by process of elimination, an integer or boolean).
        (not-a-function . "Error: trying to call ~a, but it is not a function.")

        ; Requires the number of arguments the function was called with, and the number of arguments it was expecting.
        (arity-mismatch . "ERROR: function called with an incorrect number of arguments. Given: ~a, Expected: ~a")

        ; Requires the name passed to the define-contract (i.e., the ID in the grammar rule).
        (invalid-contract . "ERROR: invalid contract for ~a.")

        ; Note that this does *not* require the function name.
        (contract-violation . "ERROR: contract violation occurred.")))


#|
(report-error error-type . args)
  error-type: symbol?
    A symbol corresponding to one of the semantic errors your interpreter should handle.
    See the assignment handout or the `error-strings` hash table for the valid keys.
  args: any?
    Additional arguments passed into the format string for the error. These are documented
    individually for each error type; see the error-strings hash table for details.

  Raises an error with a message generated from `error-strings`.
  Pay attention to the required `args` for each error string!

  For example, reporting a 'duplicate-name error requires passing in the name that's
  been duplicated, as a symbol: (report-error 'duplicate-name 'x)
|#
(define (report-error error-type . args)
  (error (apply format (cons (hash-ref error-strings error-type) args))))