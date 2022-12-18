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
(require 'cl-lib)
(eval-when-compile
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

(defmacro for--defspecial-let (name head docstring)
  "Define the special clause operator NAME.

HEAD is a `let'-like macro.  DOCSTRING is the documentation string."
  (declare (debug (&define [&name keywordp] symbolp))
           (doc-string 3) (indent 2))
  (cl-flet ((make-def (name head)
              `(for--defspecial ,name (#1=#:body)
                 ,(format docstring head)
                 (`(,_ . ,#2=#:bindings)
                  ,(let ((body `((,head . ,'(,#2# . ,#1#)))))
                     (list '\` body)))))
            (make-star (name)
              (intern (concat (symbol-name name) "*"))))
    `(prog1 ,(make-def name head)
       ,(make-def (make-star name) (make-star head)))))

(defmacro for--defmacro (name arglist docstring decl &rest body)
  "Define the iteration macro NAME with the starred version.

ARGLIST, DOCSTRING, DECL, and BODY are as in normal `defmacro'
forms.

\(fn NAME ARGLIST DOCSTRING DECL BODY...)"
  (declare (debug defmacro) (doc-string 3) (indent 2))
  (let ((docstring
         (let ((extra (concat (pcase name
                                ('for-do "BODY = [BODY-FORM...]

BODY-FORM = SPECIAL-CLAUSE | EXPRESSION

FOR-CLAUSES = ([FOR-CLAUSE...])")
                                (_ "\
BODY = [[BODY-FORM...] MULTIPLE-VALUE-FORM]

BODY-FORM = SPECIAL-CLAUSE | EXPRESSION

FOR-CLAUSES = ([[FOR-CLAUSE...] MULTIPLE-VALUE-FORM])"))
                              "\n\n" "\
FOR-CLAUSE = SPECIAL-CLAUSE | ITERATION-CLAUSE

SPECIAL-CLAUSE = (KEYWORD [SUBFORM...])

ITERATION-CLAUSE = ([IDENTIFIER] SEQUENCE-FORM)

See Info node `(for)Iteration Macros'.")))
           (save-match-data
             (if (string-match (rx bol "..." eol) docstring)
                 (replace-match extra 'fixedcase 'literal docstring)
               (let ((arglist (mapconcat
                               (lambda (symbol)
                                 (upcase (symbol-name symbol)))
                               (remq '&rest arglist)
                               " ")))
                 (concat docstring "\n\n" extra "\n\n"
                         "(fn " arglist ")")))))))
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
                 (concat docstring "\n\n" extra "\n\n"
                         "(fn " (string-join args " ") ")")))
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
                         `(,(named-let parse ((arglist arglist))
                              (pcase-exhaustive arglist
                                (`(,arg)
                                 (concat "[" (make-arg arg) "]"))
                                (`(&rest ,arg) (make-rest arg))
                                (`(,arg . ,arglist)
                                 (concat "[" (make-arg arg) " "
                                         (parse arglist) "]"))))))
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

(defmacro for--in-list (id form)
  "Return an iteration clause suitable for (ID (in-list FORM))."
  (cl-flet ((\, (form) (list '\, form)))
    (cl-flet ((make-id (form)
                (pcase form
                  ((or `(,id ,_) id) (make-symbol (symbol-name id)))))
              (make-binding (id form)
                (pcase form ((or `(,form ,_) form) `(,,id ,,form))))
              (make-default (id form)
                (pcase form
                  (`(,_ ,default) `((,,id (or ,,id ,default))))
                  (_ '()))))
      (pcase form
        ((or (and `(,head . ,(and (app (mapcar #'make-id) ids)
                                  (app (cl-mapcar #'make-binding ids)
                                       bindings)
                                  (app (cl-mapcan #'make-default ids)
                                       defaults)))
                  (let tail-form `(,head . ,(mapcar #'\, ids))))
             (and (let list '#:list)
                  (let ids `(,list))
                  (let bindings `((,,list ,,form)))
                  (let defaults '())
                  (let tail-form ,list)))
         (let ((tail '#:tail))
           `(for--with-gensyms (,@ids ,tail)
              ,(list '\` `(,,id (:do-in ,bindings ,defaults
                                        ((,,tail ,tail-form)) (,,tail)
                                        ((,,id (car ,,tail)))
                                        ((cdr ,,tail))))))))))))

(defmacro for--with-gensyms (names &rest body)
  "Bind NAMEs in NAMES to generated identifiers and evaluate BODY.

\(fn (NAME...) BODY...)"
  (declare (debug ((&rest symbolp) body)) (indent 1))
  `(let ,(mapcar (lambda (name) `(,name (gensym ,(symbol-name name))))
                 names)
     . ,body))

(pcase-defmacro for--funcall (&rest args)
  "Matches EXPVAL as an arglist according to ARGS."
  (named-let parse ((mand-args '()) (args args))
    (pcase args
      (`(&optional . ,opt-args)
       (cl-flet
           ((\, (form) (list '\, form))
            (args-pat (args) (list '\` (cons (list '\, '_) args))))
         (let ((args (mapcar #'\, (nreverse mand-args))))
           (named-let build
               ((args args) (opt-args opt-args) (pat (args-pat args)))
             (pcase opt-args
               ('() pat)
               (`(,arg . ,opt-args)
                (let ((args `(,@args ,,arg)))
                  (build args opt-args
                         `(or (and ,pat (let ,arg nil))
                              ,(args-pat args))))))))))
      (`(,arg . ,args) (parse `(,arg . ,mand-args) args)))))

;;;; Provide
(provide 'for-helper)
;;; for-helper.el ends here
