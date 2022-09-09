;;; for-helper.el --- Helper -*- lexical-binding: t; -*-

;; Copyright (C) 2022 Wing Hei Chan

;; Author: Wing Hei Chan <whmunkchan@outlook.com>
;; URL: https://github.com/usaoc/elisp-for
;; Keywords: extensions

;; This file is not part of GNU Emacs.

;; This program is free software: you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation, either version 3 of the
;; License, or (at your option) any later version.

;; This program is distributed in the hope that it will be useful, but
;; WITHOUT ANY WARRANTY; without even the implied warranty of
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE. See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program. If not, see
;; <https://www.gnu.org/licenses/>.

;;; Commentary:
;; This file provides internal helpers.

;;; Code:
;;;; Require
(eval-when-compile
  (require 'cl-lib)
  (require 'subr-x))

;;;; Interface
(defmacro for--defspecial (name arglist docstring &rest cases-or-body)
  "Define the special clause operator NAME.

ARGLIST, DOCSTRING, and CASES-OR-BODY are as in
`define-for-special-clause' forms.

\(fn NAME ARGLIST DOCSTRING [CASES-OR-BODY...])"
  (declare (debug define-for-special-clause)
           (doc-string 3) (indent 2))
  `(define-for-special-clause ,name ,arglist
     ,(concat docstring "\n\n"
              "See Info node `(for)Special-Clause Operators'.")
     . ,cases-or-body))

(defmacro for--defmacro (name arglist docstring decl &rest body)
  "Define the iteration macro NAME with the starred version.

ARGLIST, DOCSTRING, DECL, and BODY are as in normal `defmacro'
forms.

\(fn NAME ARGLIST DOCSTRING DECL BODY...)"
  (declare (debug defmacro) (doc-string 3) (indent 2))
  (let ((docstring
         (let ((extra "BODY = [[BODY-FORM...] MULTIPLE-VALUE-FORM]

BODY-FORM = SPECIAL-CLAUSE | EXPRESSION

FOR-CLAUSES = ([[FOR-CLAUSE...] MULTIPLE-VALUE-FORM])

FOR-CLAUSE = SPECIAL-CLAUSE | ITERATION-CLAUSE

SPECIAL-CLAUSE = (KEYWORD [SUBFORM...])

ITERATION-CLAUSE = ([IDENTIFIER] SEQUENCE-FORM)

See Info node `(for)Iteration Macros'."))
           (save-match-data
             (if (string-match (rx bol "..." eol) docstring)
                 (replace-match extra 'fixedcase 'literal docstring)
               (string-join
                (list docstring extra
                      (concat "(fn "
                              (mapconcat
                               (lambda (symbol)
                                 (upcase (symbol-name symbol)))
                               (remq '&rest arglist)
                               " ")
                              ")"))
                "\n\n"))))))
    `(prog1 (defmacro ,name ,arglist ,docstring ,decl . ,body)
       (defmacro ,(intern (concat (symbol-name name) "*")) ,arglist
         ,docstring ,decl
         (cl-flet ((for--parse-body (for-clauses body)
                     (pcase-let ((`(,for-clauses . ,value-form)
                                  (for--parse-body for-clauses body)))
                       `(,(for--nest-for-clauses for-clauses)
                         . ,value-form))))
           . ,body)))))

(defmacro for--defseq (name arglist docstring &rest subforms)
  "Define a sequence constructor NAME with ARGLIST and DOCSTRING.

A SUBFORM in SUBFORMS can be either a `:type', `:expander', or
`:expander-case' form as in `define-for-sequence' forms.

\(fn NAME ARGLIST DOCSTRING [DECLARATION] [SUBFORM...] [BODY...])"
  (declare (debug define-for-sequence) (doc-string 3) (indent 2))
  (let ((extra "See Info node `(for)Sequence Constructors'."))
    (cl-flet* ((make-arg (arg) (upcase (symbol-name arg)))
               (make-rest (arg) (concat "[" (make-arg arg) "...]"))
               (make-docstring (args)
                 (string-join (list docstring extra
                                    (concat "(fn "
                                            (string-join args " ")
                                            ")"))
                              "\n\n")))
      `(define-for-sequence ,name ,arglist
         ,(save-match-data
            (cond ((string-match (rx bol "..." eol) docstring)
                   (replace-match extra
                                  'fixedcase 'literal docstring))
                  ((memq '&optional arglist)
                   (make-docstring
                    (named-let parse ((arglist arglist))
                      (pcase-exhaustive arglist
                        ('() '())
                        (`(&optional . ,arglist)
                         (named-let parse ((arglist arglist))
                           (pcase-exhaustive arglist
                             ('() '())
                             (`(&rest ,arg) `(,(make-rest arg)))
                             (`(,arg . ,arglist)
                              `(,(concat "[" (string-join
                                              `(,(make-arg arg)
                                                . ,(parse arglist))
                                              " ")
                                         "]"))))))
                        (`(,arg . ,arglist)
                         `(,(make-arg arg) . ,(parse arglist)))))))
                  ((memq '&rest arglist)
                   (make-docstring
                    (named-let parse ((arglist arglist))
                      (pcase-exhaustive arglist
                        ('() '())
                        (`(&rest ,arg) `(,(make-rest arg)))
                        (`(,arg . ,arglist)
                         `(,(make-arg arg) . ,(parse arglist)))))))
                  (t (concat docstring "\n\n" extra))))
         . ,(pcase-let
                (((or `(,(and `(declare . ,_) declaration)
                        . ,subforms)
                      (and subforms
                           (let declaration
                             '(declare (side-effect-free t)))))
                  subforms))
              `(,declaration
                (:alias ,(intern (string-remove-prefix
                                  "for-" (symbol-name name))))
                . ,subforms))))))

(defmacro for--with-gensyms (names &rest body)
  "Bind NAMEs in NAMES to generated identifiers and evaluate BODY.

\(fn (NAME...) BODY...)"
  (declare (debug ((&rest symbolp) body)) (indent 1))
  (pcase-exhaustive names
    ((and `(,_ . ,_) (let `(,_ . ,_) body)
          (app (mapcar (lambda (name)
                         `(,name (gensym ,(symbol-name name)))))
               bindings))
     `(let ,bindings . ,body))))

;;;; Provide
(provide 'for-helper)
;;; for-helper.el ends here
