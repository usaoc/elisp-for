;;; for-iteration.el --- Iteration -*- lexical-binding: t; -*-

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
;; MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU
;; General Public License for more details.

;; You should have received a copy of the GNU General Public License
;; along with this program.  If not, see
;; <https://www.gnu.org/licenses/>.

;;; Commentary:
;; This file provides iteration forms.

;;; Code:
;;;; Require
(require 'cl-lib)

;;;; Internal
(defvar for--datum-dispatch-alist '()
  "Alist of type specifiers vs generators.")

(defun for--datum-to-iterator (datum)
  "Dispatch on DATUM and return an iterator.

Find the generator in `for--datum-dispatch-alist' and apply it to
DATUM."
  (pcase (alist-get datum for--datum-dispatch-alist
                    nil nil (lambda (type datum)
                              (cl-typep datum type)))
    ('nil (signal 'for-unhandled-type (list datum)))
    (generator (funcall generator datum))))

(defun for--datum-to-sequence (datum)
  "Transform DATUM to a sequence form.

Currently, literal lists, arrays, and integers are transformed to
`for-in-list', `for-in-array', and `for-in-range' sequences."
  (declare (side-effect-free t))
  (pcase datum
    ((or '() `',(cl-type list)) `(for-in-list ,datum))
    ((or (cl-type array) `',(cl-type array)) `(for-in-array ,datum))
    ((or (cl-type integer) `',(cl-type integer))
     `(for-in-range ,datum))
    (_ nil)))

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

(defun for--iterator-for-clause (iteration-clause)
  "Transform ITERATION-CLAUSE to iterate over an iterator.

ITERATION-CLAUSE is (FORM ITERATOR) where FORM is an arbitrary
form and ITERATOR is an expression that produces an iterator."
  (declare (side-effect-free t))
  (pcase-exhaustive iteration-clause
    (`(,id ,form)
     (for--with-gensyms (iterator next)
       (let* ((returned '#:returned)
              (next* `(condition-case nil (iter-next ,iterator)
                        (iter-end-of-sequence ',returned))))
         `(,id (:do-in ((,iterator ,form)) () ((,next ,next*))
                       ((not (eq ,next ',returned))) ((,id ,next))
                       (,next*))))))))

(defun for--expand-iteration-clause (clause)
  "Expand the iteration clause CLAUSE as much as possible.

CLAUSE as (FORM SEQUENCE-FORM) is expanded when SEQUENCE-FORM is
a recognized literal object, is an alias, has an associated
expander, or is treated as a function form.  The expansion stops
when SEQUENCE-FORM is a `:do-in' form."
  (named-let expand
      ((clause (pcase-exhaustive clause
                 (`(,sequence) `(,(make-symbol "_id") ,sequence))
                 (`(,_ ,_) clause))))
    (pcase-exhaustive clause
      ((and `(,_ (:do-in ,(cl-type list) ,(cl-type list)
                         ,(and (cl-type list) loop-bindings)
                         ,(cl-type list) ,(cl-type list)
                         ,(and (cl-type list) loop-forms)))
            (guard (= (length loop-bindings) (length loop-forms))))
       clause)
      (`(,id ,(app for--datum-to-sequence
                   (and (pred identity) sequence)))
       (expand `(,id ,sequence)))
      (`(,id (,(and (cl-type symbol)
                    (app (lambda (head) (get head 'for--alias))
                         (and (pred identity) base)))
              . ,subforms))
       (expand `(,id (,base . ,subforms))))
      (`(,_ (,(and (cl-type symbol)
                   (app (lambda (head)
                          (get head 'for--sequence-expander))
                        (and (pred identity) expander)))
             . ,_))
       (expand (funcall expander clause)))
      (`(,id ,datum)
       (expand (for--iterator-for-clause
                `(,id (for--datum-to-iterator ,datum))))))))

(defun for--nest-for-clauses (for-clauses)
  "Transform FOR-CLAUSES to implicitly nesting clauses.

A vacuous special clause is inserted between each pair of
adjacent iteration clauses."
  (declare (side-effect-free t))
  (named-let parse ((nested '()) (iteration nil)
                    (clauses (reverse for-clauses)))
    (pcase-exhaustive clauses
      ('() nested)
      (`(,clause . ,clauses)
       (pcase-exhaustive clause
         (`(,(cl-type keyword) . ,_)
          (parse `(,clause . ,nested) nil clauses))
         ((or `(,_) `(,_ ,_))
          (parse (if iteration `(,clause (:do) . ,nested)
                   `(,clause . ,nested))
                 t clauses)))))))

(defun for--parse-value-form (form number make-value)
  "Parse FORM as a multiple-value form.

A tail form of FORM is (`values' [VALUE...]) with as many VALUEs
as NUMBER.  An expression EXPR as a tail form is normalized
to (`:values' EXPR), then the tail form FORM is replaced
by (`funcall' MAKE-VALUE FORM)."
  (cl-flet ((parse-body (body)
              (pcase-let
                  ((`(,tail-form . ,(app nreverse forms))
                    (reverse body)))
                `(,@forms ,(for--parse-value-form
                            tail-form number make-value)))))
    (pcase-exhaustive
        (pcase form
          ((cl-type symbol) form)
          (_ (macroexpand form macroexpand-all-environment)))
      (`(cond . ,(and `(,_ . ,_)
                      (pred (cl-every (lambda (form)
                                        (pcase-exhaustive form
                                          (`(,_) nil)
                                          (`(,_ ,_ . ,_) t)))))
                      clauses))
       `(cond . ,(mapcar (pcase-lambda (`(,guard . ,body))
                           `(,guard . ,(parse-body body)))
                         clauses)))
      (`(if ,guard ,then . ,(and `(,_ . ,_) else))
       `(if ,guard ,(for--parse-value-form then number make-value)
          . ,(parse-body else)))
      (`(,(and (or 'let 'let*) head) ,bindings
         . ,(and `(,_ . ,_) body))
       `(,head ,bindings . ,(parse-body body)))
      (`(,(and (or 'progn 'save-current-buffer 'save-excursion
                   'save-restriction)
               head)
         . ,(and `(,_ . ,_) body))
       `(,head . ,(parse-body body)))
      ((or (and `(:values . ,(app length (pred (= number))))
                tail-form)
           (and (guard (= number 1))
                (app (lambda (form) `(:values ,form)) tail-form)))
       (funcall make-value tail-form)))))

(defun for--parse-bindings (bindings)
  "Parse BINDINGS as the subform of `for-fold'.

The result forms are extracted from BINDINGS or else the default
result forms are used.  Return a `cons' of BINDINGS without the
result forms and the result forms."
  (declare (side-effect-free t))
  (pcase-exhaustive bindings
    ((or (and '() bindings (let result-forms '(nil)))
         (and `((:result . ,(and `(,_ . ,_) result-forms)))
              (let bindings '()))
         (and `(,_ . ,_)
              (or (app reverse
                       `((:result . ,(and `(,_ . ,_) result-forms))
                         . ,(app nreverse bindings)))
                  (and bindings
                       (app (mapcar (lambda (binding)
                                      (pcase-exhaustive binding
                                        ((or `(,id ,_) id) id))))
                            (or (and `(,_) result-forms)
                                (and `(,_ ,_) (app (lambda (ids)
                                                     `((cons . ,ids)))
                                                   result-forms))
                                (app (lambda (ids) `((list . ,ids)))
                                     result-forms)))))))
     `(,(mapcar (lambda (binding)
                  (pcase-exhaustive binding
                    ((or (and `(,_ ,_) binding)
                         (app (lambda (id) `(,id nil)) binding))
                     binding)))
                bindings)
       . ,result-forms))))

(defun for--parse-body (for-clauses body)
  "Parse FOR-CLAUSES and BODY as the subforms of `for-fold'.

Each form in BODY is transformed to a `:do' special clause unless
the form is already a special clause.  The forms are then
appended to FOR-CLAUSES.  Finally, the multiple-value form of the
parsed for clauses is extracted, and a `cons' of the remaining
for clauses and the multiple-value form is returned."
  (declare (side-effect-free t))
  (cl-flet ((transform (form)
              (pcase form
                (`(,(cl-type keyword) . ,_) form) (_ `(:do ,form)))))
    (pcase-exhaustive body
      ((or (and '() (let (or (and `(,value-form) (let clauses '()))
                             (and `(,_ . ,_)
                                  (app reverse
                                       `(,value-form
                                         . ,(app nreverse clauses)))))
                      for-clauses))
           (and (let (cl-type list) for-clauses)
                (or (and `(,value-form) (let clauses for-clauses))
                    (and `(,_ . ,_)
                         (app reverse
                              `(,value-form
                                . ,(app nreverse
                                        (app (mapcar #'transform)
                                             (app (lambda (clauses)
                                                    `(,@for-clauses
                                                      ,@clauses))
                                                  clauses)))))))))
       `(,clauses . ,value-form)))))

(defun for--parse-for-clauses (for-clauses)
  "Parse FOR-CLAUSES.

Split FOR-CLAUSES into ([GROUP...]) where GROUP is (HEAD
[MEMOIZED-BINDINGS OUTER-BINDINGS LOOP-BINDINGS LOOP-GUARDS
INNER-BINDINGS LOOP-FORMS]) and HEAD is either (`:break'
[GUARD...]), (`:final' [GUARD...]), or (EXPANDER [SUBFORM...])."
  (named-let parse
      ((memoize-bindings '()) (outer-bindings '()) (loop-bindings '())
       (loop-guards '()) (inner-bindings '()) (loop-forms '())
       (iteration nil) (groups '()) (clauses (reverse for-clauses)))
    (cl-symbol-macrolet
        ((group (if (not iteration) '()
                  `(,memoize-bindings
                    ,outer-bindings ,loop-bindings ,loop-guards
                    ,inner-bindings ,loop-forms))))
      (pcase-exhaustive clauses
        ('() `(((,(lambda (_special-clause body) body)) . ,group)
               . ,groups))
        (`(,(or (and (or `(:break . ,_) `(:final . ,_)) head)
                (and `(,(and (cl-type keyword)
                             (app
                              (lambda (keyword)
                                (get keyword
                                     'for--special-clause-expander))
                              (and (pred identity) expander)))
                       . ,_)
                     (app (lambda (special-clause)
                            `(,expander . ,special-clause))
                          head)))
           . ,clauses)
         (parse '() '() '() '() '() '() nil
                `((,head . ,group) . ,groups) clauses))
        (`(,(app for--expand-iteration-clause clause) . ,clauses)
         (pcase-let
             ((`(,_ (:do-in
                     ,more-memoize-bindings ,more-outer-bindings
                     ,more-loop-bindings ,more-loop-guards
                     ,more-inner-bindings ,more-loop-forms))
               clause))
           (parse `(,@more-memoize-bindings . ,memoize-bindings)
                  `(,@more-outer-bindings . ,outer-bindings)
                  `(,@more-loop-bindings . ,loop-bindings)
                  `(,@more-loop-guards . ,loop-guards)
                  `(,@more-inner-bindings . ,inner-bindings)
                  `(,@more-loop-forms . ,loop-forms)
                  t groups clauses)))))))

(defmacro for--setq (&rest pairs)
  "Expand to a form equivalent to (`cl-psetq' [ID VALUE]...).

For a pair of ID and VALUE in PAIRS, when VALUE or the
first-order symbol macro of VALUE is `eq' to ID, eliminate them
from the expanded form.

\(fn (ID VALUE)...)"
  (declare (debug (&rest (symbolp form))))
  (cl-reduce (lambda (pair form)
               (cl-flet
                   ((identifier= (id-a id-b)
                      (or (eq id-a id-b)
                          (pcase macroexpand-all-environment
                            ((app (alist-get :cl-symbol-macros)
                                  (and (pred identity)
                                       (app (assq id-b) `(,_ ,id-b))))
                             (eq id-a id-b))
                            (_ nil)))))
                 (pcase-exhaustive pair
                   (`(,id ,value)
                    (if (identifier= id value) form
                      `(setq ,id (prog1 ,value ,form)))))))
             pairs :from-end t :initial-value nil))

(eval-when-compile
  (defmacro for--defspecial
      (name arglist docstring &rest cases-or-body)
    "Define the special clause operator NAME.

ARGLIST, DOCSTRING, and CASES-OR-BODY are as in
`define-for-special-clause' forms.

\(fn NAME ARGLIST DOCSTRING [CASES-OR-BODY...])"
    (declare (debug (&define [&name keywordp]
                             [&or [(arg arg) lambda-doc def-body]
                                  [(arg) lambda-doc
                                   &rest [pcase-PAT body]]]))
             (doc-string 3) (indent 2))
    `(define-for-special-clause ,name ,arglist
       ,(concat docstring "\n\n"
                "See Info node `(for)Special-Clause Operators'.")
       . ,cases-or-body))
  (defmacro for--defmacro (name arglist &rest body)
    "Define the iteration macro NAME with the star version.

ARGLIST, DOCSTRING, DECL, and BODY are as in normal `defmacro'
forms.

\(fn NAME ARGLIST [DOCSTRING] [DECL] BODY...)"
    (declare (debug (&define name lambda-list lambda-doc
                             [&optional ("declare" def-declarations)]
                             def-body))
             (doc-string 3) (indent 2))
    (pcase-let* (((or `(,(and (cl-type string)
                              (app (lambda (docstring)
                                     `(,(replace-regexp-in-string
                                         (rx bol "..." eol) "\
BODY = [[BODY-FORM...] MULTIPLE-VALUE-FORM]

BODY-FORM = SPECIAL-CLAUSE | EXPRESSION

FOR-CLAUSES = ([[FOR-CLAUSE...] MULTIPLE-VALUE-FORM])

FOR-CLAUSE = SPECIAL-CLAUSE | ITERATION-CLAUSE

SPECIAL-CLAUSE = (KEYWORD [SUBFORM...])

ITERATION-CLAUSE = ([IDENTIFIER] SEQUENCE-FORM)

See Info node `(for)Iteration Macros'." docstring)))
                                   docstring))
                        . ,body)
                      (and body (let docstring '())))
                  body)
                 ((or `(,(and `(declare . ,_)
                              (app (lambda (form) `(,form))
                                   declaration))
                        . ,body)
                      (and body (let declaration '())))
                  body))
      `(prog1 (defmacro ,name ,arglist
                ,@docstring ,@declaration . ,body)
         (defmacro ,(intern (concat (symbol-name name) "*")) ,arglist
           ,@docstring ,@declaration
           (cl-flet
               ((for--parse-body (for-clauses body)
                  (pcase-let ((`(,for-clauses . ,value-form)
                               (for--parse-body for-clauses body)))
                    `(,(for--nest-for-clauses for-clauses)
                      . ,value-form))))
             . ,body))))))

(def-edebug-spec for--result-clause-spec (":result" body))

(def-edebug-spec for--bindings-spec
  ([&rest [&or symbolp (symbolp form)]] for--result-clause-spec))

(def-edebug-spec for--iteration-clauses-spec (sexp form))

(def-edebug-spec for--special-clauses-spec
  [&or ([&or ":break" ":final" ":if" ":if-not" ":do"] &rest form)
       ([&or ":let" ":if-let"] &rest (sexp form))
       ([&or ":pcase" ":pcase-not"] &rest pcase-PAT) (keywordp sexp)])

(def-edebug-spec for--value-clause-spec
  [&or (":values" &rest form) sexp])

(def-edebug-spec for--for-clauses-spec
  ([&rest [&or for--special-clauses-spec for--iteration-clauses-spec]]
   for--value-clause-spec))

(def-edebug-spec for--body-spec
  [[&rest [&or for--special-clauses-spec form]]
   for--value-clause-spec])

(def-edebug-spec for--fold-spec
  (for--fold-bindings-spec for--for-clauses-spec for--body-spec))

(def-edebug-spec for--do-for-clauses-spec
  (&rest [&or for--special-clauses-spec for--iteration-clauses-spec]))

(def-edebug-spec for--do-body-spec
  [&rest [&or for--special-clauses-spec form]])

(def-edebug-spec for--do-spec
  (for--do-for-clauses-spec for--do-body-spec))

(def-edebug-spec for--accumulator-spec
  (for--for-clauses-spec for--body-spec))

(def-edebug-spec for--vector-body-spec
  [[&optional ":length" form [&optional ":init" form]]
   for--body-spec])

(def-edebug-spec for--vector-spec
  (for--for-clauses-spec for--vector-body-spec))

(def-edebug-spec for--string-body-spec
  [[&optional ":length" form
              [&optional ":init" form
                         [&optional ":multibyte" form]]]
   for--body-spec])

(def-edebug-spec for--string-spec
  (for--for-clauses-spec for--string-body-spec))

(def-edebug-spec for--lists-bindings-spec
  ([&rest symbolp] for--result-clause-spec))

(def-edebug-spec for--lists-spec
  (for--lists-bindings-spec for--for-clauses-spec for--body-spec))

;;;; Interface
(define-error 'for-unhandled-type "Unhandled type")

;;;###autoload(define-symbol-prop 'for-binder 'safe-local-variable #'symbolp)
(defvar-local for-binder 'pcase-let
  "The head of certain `let'-like forms in iteration forms.

See Info node `(for)Buffer-Local Variables'.")

(defmacro define-for-special-clause (name arglist &rest cases-or-body)
  "Define the special clause operator NAME.

NAME is a keyword.  ARGLIST is the argument list which has either
one or two identifiers.  Correspondingly, CASES-OR-BODY are
either the cases of `pcase-exhaustive' or the body.  See Info
node `(for)Definers'.

\(fn NAME ARGLIST [DOCSTRING] [CASES-OR-BODY...])"
  (declare (debug (&define [&name keywordp]
                           [&or [(arg arg) lambda-doc def-body]
                                [(arg) lambda-doc
                                 &rest [pcase-PAT body]]]))
           (doc-string 3) (indent 2))
  (pcase-let (((or `(,(and (cl-type string)
                           (app (lambda (form) `(,form)) docstring))
                     . ,cases-or-body)
                   (and cases-or-body (let docstring '())))
               cases-or-body))
    (pcase-exhaustive cases-or-body
      ((or (and (let `(,body-form) arglist)
                (let arglist `(special-clause ,body-form))
                (app (lambda (cases)
                       `((pcase-exhaustive special-clause . ,cases)))
                     body))
           (and (let `(,_ ,_) arglist) body))
       (let ((id (intern (concat (symbol-name (cl-the keyword name))
                                 "--for-special-clause-expander"))))
         `(prog1 (eval-and-compile
                   (defun ,id ,arglist ,@docstring . ,body))
            (define-symbol-prop
             ',name 'for--special-clause-expander ',id)))))))

(for--defspecial :if (body)
  "Evaluate BODY when all subforms are non-nil."
  (`(,_ . ,guards) `((when (and . ,guards) . ,body))) )

(for--defspecial :if-not (body)
  "Evaluate BODY unless all subforms are non-nil."
  (`(,_ . ,guards) `((unless (and . ,guards) . ,body))) )

(for--defspecial :let (body)
  "Evaluate BODY with subforms bound by `for-binder'."
  (`(,_ . ,bindings) `((,for-binder ,bindings . ,body))))

(for--defspecial :if-let (body)
  "Evaluate BODY with subforms bound by `when-let*'."
  (`(,_ . ,bindings) `((when-let* ,bindings . ,body))))

(for--defspecial :pcase (body)
  "Evaluate BODY when the first subform is matched.

The remaining subforms are the patterns as in `pcase'.  When an
optional sequence [`:exhaustive'] is present in the remaining
subforms, match exhaustively, that is, use `pcase-exhaustive'."
  ((or (and `(,_ ,expr :exhaustive . ,pats)
            (let head 'pcase-exhaustive))
       (and `(,_ ,expr . ,pats) (let head 'pcase)))
   `((,head ,expr ((and . ,pats) . ,body)))))

(for--defspecial :pcase-not (body)
  "Evaluate BODY when the first subform is not matched.

The remaining subforms are the patterns as in `pcase'.  When an
optional sequence [`:as' AS] is present in the remaining
subforms, the value of the first subform is bound to AS, and the
subforms after the sequence are the patterns."
  ((or `(,_ ,expr :as ,(and (cl-type symbol) as) . ,pats)
       (and `(,_ ,expr . ,pats) (let as '_)))
   `((pcase ,expr ((and . ,pats) nil) (,as . ,body)))))

(for--defspecial :do (body)
  "Evaluate the subforms before evaluating BODY."
  (`(,_ . ,forms) `(,@forms . ,body)))

(for--defmacro for-fold (bindings for-clauses &rest body)
  "The fundamental folding iteration macro.

BINDINGS = ([BINDING...] [(:result [EXPRESSION...])])

BINDING = IDENTIFIER | (IDENTIFIER EXPRESSION)

...

\(fn BINDINGS FOR-CLAUSES BODY)"
  (declare (debug for--fold-spec) (indent 2))
  (pcase-let
      ((binder for-binder)
       (`(,(and bindings
                (app (mapcar (pcase-lambda (`(,id ,_))
                               (make-symbol (symbol-name id))))
                     renamed-ids)
                (app length length-bindings))
          . ,result-forms)
        (for--parse-bindings bindings))
       (`(,(app (lambda (clauses)
                  (named-let parse
                      ((final-ids '()) (body '()) (parsed '())
                       (clauses (reverse clauses)))
                    (pcase-exhaustive clauses
                      ('() `(,final-ids ,body ,parsed))
                      (`(,clause . ,clauses)
                       (pcase clause
                         (`(:final . ,guards)
                          (for--with-gensyms (final final-guard)
                            (parse `(,final . ,final-ids)
                                   `((when ,final-guard
                                       (setq ,final nil))
                                     . ,body)
                                   `((:final ,final-guard . ,guards)
                                     . ,parsed)
                                   clauses)))
                         (_ (parse final-ids body
                                   `(,clause . ,parsed) clauses)))))))
                `(,final-ids
                  ,body
                  ,(app for--parse-for-clauses for-clauses)))
          . ,value-form)
        (for--parse-body for-clauses body)))
    (named-let expand
        ((break-ids '())
         (body `(,(for--parse-value-form
                   value-form length-bindings
                   (if (zerop length-bindings) (lambda (_form) nil)
                     (pcase-lambda (`(:values . ,forms))
                       `(for--setq
                         . ,(cl-mapcar (lambda (id form) `(,id ,form))
                                       renamed-ids forms)))))
                 . ,body))
         (clauses (reverse for-clauses)))
      (cl-flet
          ((make-iteration (body memoize-bindings outer-bindings
                                 loop-bindings loop-guards
                                 inner-bindings loop-forms)
             (let* ((body (if (null loop-forms) body
                            `(,@body
                              (when (and ,@break-ids ,@final-ids)
                                (for--setq
                                 . ,(cl-mapcar
                                     (lambda (binding form)
                                       (pcase-exhaustive binding
                                         (`(,id ,_) `(,id ,form))))
                                     loop-bindings loop-forms))))))
                    (body (if (null inner-bindings) body
                            `((,binder ,inner-bindings . ,body))))
                    (body `((while (and ,@break-ids
                                        ,@final-ids . ,loop-guards)
                              . ,body)))
                    (body (if (null loop-bindings) body
                            `((let ,loop-bindings . ,body))))
                    (body (if (null outer-bindings) body
                            `((let ,outer-bindings . ,body))))
                    (body (if (null memoize-bindings) body
                            `((let ,memoize-bindings . ,body)))))
               body)))
        (if (null clauses)
            (let* ((body (pcase (nconc break-ids final-ids)
                           ('() body)
                           (ids `((let ,(mapcar (lambda (id) `(,id t))
                                                ids)
                                    . ,body)))))
                   (body (if (null result-forms) body
                           `(,@body . ,result-forms)))
                   (body (if (null bindings) body
                           `((let ,(cl-mapcar
                                    (pcase-lambda (id `(,_ ,value))
                                      `(,id ,value))
                                    renamed-ids bindings)
                               (cl-symbol-macrolet
                                   ,(cl-mapcar
                                     (pcase-lambda (`(,id ,_) value)
                                       `(,id ,value))
                                     bindings renamed-ids)
                                 . ,body))))))
              (macroexp-progn body))
          (pcase-let ((`((,head . ,iteration-forms) . ,clauses)
                       clauses))
            (cl-symbol-macrolet
                ((expanded (if (null iteration-forms) body
                             (apply #'make-iteration
                                    body iteration-forms))))
              (pcase-exhaustive head
                (`(:break . ,guards)
                 (for--with-gensyms (break)
                   (expand `(,break . ,break-ids)
                           `((if (and . ,guards) (setq ,break nil)
                               . ,expanded))
                           clauses)))
                (`(:final . ,guards)
                 (pcase-let ((`(,final-guard . ,guards) guards))
                   (expand break-ids
                           `((let ((,final-guard (and . ,guards)))
                               . ,expanded))
                           clauses)))
                (`(,expander . ,special-clause)
                 (expand break-ids
                         (funcall expander special-clause expanded)
                         clauses))))))))))

(for--defmacro for-do (for-clauses &rest body)
  "The side-effecting iteration macro.

...

\(fn FOR-CLAUSES BODY)"
  (declare (debug for--do-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses `(,@body (:values)))))
    `(for-fold () (,@for-clauses ,value-form))))

(for--defmacro for-list (for-clauses &rest body)
  "The list-building iteration macro.

...

\(fn FOR-CLAUSES BODY)"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (list)
      `(for-fold ((,list '()) (:result (nreverse ,list)))
           (,@for-clauses ,(for--parse-value-form
                            value-form 1
                            (pcase-lambda (`(:values ,form))
                              `(cons ,form ,list))))))))

(for--defmacro for-lists (bindings for-clauses &rest body)
  "The multiple-list-building iteration macro.

BINDINGS = ([IDENTIFIER...] [(:result [EXPRESSION...])])

...

\(fn BINDINGS FOR-CLAUSES BODY)"
  (declare (debug for--lists-spec) (indent 2))
  (pcase-let
      ((`(,(and bindings
                (app (mapcar (pcase-lambda (`(,id ,_)) id)) ids)
                (app length length-bindings))
          . ,result-forms)
        (for--parse-bindings
         (mapcar (lambda (form)
                   (pcase-exhaustive form
                     ((cl-type symbol) `(,form '()))
                     (`(:result . ,_) form)))
                 bindings)))
       (`(,for-clauses . ,value-form)
        (for--parse-body for-clauses body)))
    `(for-fold
         (,@bindings
          (:result . ,(if (null ids) result-forms
                        `((let ,(mapcar (lambda (id)
                                          `(,id (nreverse ,id)))
                                        ids)
                            . ,result-forms)))))
         (,@for-clauses
          ,(for--parse-value-form
            value-form length-bindings
            (if (zerop length-bindings) #'identity
              (pcase-lambda (`(:values . ,forms))
                `(:values . ,(cl-mapcar (lambda (form id)
                                          `(cons ,form ,id))
                                        forms ids)))))))))

(for--defmacro for-vector (for-clauses &rest body)
  "The vector-building iteration macro.

...

\(fn FOR-CLAUSES [:length LENGTH [:init INIT]] BODY)"
  (declare (debug for--vector-spec) (indent 1))
  (pcase body
    ((or `(:length ,length-form :init ,init-form . ,body)
         (and `(:length ,length-form . ,body) (let init-form nil)))
     (pcase-let ((`(,for-clauses . ,value-form)
                  (for--parse-body for-clauses body)))
       (for--with-gensyms (length init index vector)
         `(let ((,length ,length-form) (,init ,init-form))
            (let ((,vector (make-vector ,length ,init)))
              (let ((,index 0))
                (for-do (,@for-clauses
                         (:do ,(for--parse-value-form
                                value-form 1
                                (pcase-lambda (`(:values ,form))
                                  `(setf (aref ,vector ,index)
                                         ,form)))
                              (cl-incf ,index))
                         (:break (= ,index ,length)))))
              ,vector)))))
    (_ (pcase-let ((`(,for-clauses . ,value-form)
                    (for--parse-body for-clauses body)))
         `(apply #'vector (for-list (,@for-clauses ,value-form)))))))

(for--defmacro for-string (for-clauses &rest body)
  "The string-building iteration macro.

...

\(fn FOR-CLAUSES [:length LENGTH [:init INIT [:multibyte MULTIBYTE]]] BODY)"
  (declare (debug for--string-spec) (indent 1))
  (pcase body
    ((or `(:length ,length-form :init ,init-form
                   :multibyte ,multibyte-form . ,body)
         (and (or `(:length ,length-form :init ,init-form . ,body)
                  (and `(:length ,length-form . ,body)
                       (let init-form nil)))
              (let multibyte-form nil)))
     (pcase-let ((`(,for-clauses . ,value-form)
                  (for--parse-body for-clauses body)))
       (for--with-gensyms (length init multibyte index string)
         `(let ((,length ,length-form)
                (,init (or ,init-form ?\0))
                (,multibyte ,multibyte-form))
            (let ((,string (make-string ,length ,init ,multibyte)))
              (let ((,index 0))
                (for-do (,@for-clauses
                         (:do ,(for--parse-value-form
                                value-form 1
                                (pcase-lambda (`(:values ,form))
                                  `(setf (aref ,string ,index)
                                         ,form)))
                              (cl-incf ,index))
                         (:break (= ,index ,length)))))
              ,string)))))
    (_ (pcase-let ((`(,for-clauses . ,value-form)
                    (for--parse-body for-clauses body)))
         `(apply #'string (for-list (,@for-clauses ,value-form)))))))

(for--defmacro for-and (for-clauses &rest body)
  "The `and'-folding iteration macro.

...

\(fn FOR-CLAUSES BODY)"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (value)
      `(let ((,value t))
         (for-do (,@for-clauses
                  (:do ,(for--parse-value-form
                         value-form 1
                         (pcase-lambda (`(:values ,form))
                           `(setq ,value ,form))))
                  (:break (not ,value))))
         ,value))))

(for--defmacro for-or (for-clauses &rest body)
  "The `or'-folding iteration macro.

...

\(fn FOR-CLAUSES BODY)"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (value)
      `(let ((,value nil))
         (for-do (,@for-clauses
                  (:do ,(for--parse-value-form
                         value-form 1
                         (pcase-lambda (`(:values ,form))
                           `(setq ,value ,form))))
                  (:break ,value)))
         ,value))))

(for--defmacro for-sum (for-clauses &rest body)
  "The sum-accumulating iteration macro.

...

\(fn FOR-CLAUSES BODY)"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (sum)
      `(for-fold ((,sum 0))
           (,@for-clauses ,(for--parse-value-form
                            value-form 1
                            (pcase-lambda (`(:values ,form))
                              `(+ ,form ,sum))))))))

(for--defmacro for-product (for-clauses &rest body)
  "The product-accumulating iteration macro.

...

\(fn FOR-CLAUSES BODY)"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (product)
      `(for-fold ((,product 1))
           (,@for-clauses ,(for--parse-value-form
                            value-form 1
                            (pcase-lambda (`(:values ,form))
                              `(* ,form ,product))))))))

(for--defmacro for-first (for-clauses &rest body)
  "The first-value-returning iteration macro.

...

\(fn FOR-CLAUSES BODY)"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (value)
      `(for-fold ((,value nil))
           (,@for-clauses (:final) ,value-form)))))

(for--defmacro for-last (for-clauses &rest body)
  "The last-value-returning iteration macro.

...

\(fn FOR-CLAUSES BODY)"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (value)
      `(for-fold ((,value nil)) (,@for-clauses ,value-form)))))

(for--defmacro for-max (for-clauses &rest body)
  "The `max'-folding iteration macro.

...

\(fn FOR-CLAUSES BODY)"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (max)
      `(for-fold ((,max -1.0e+INF))
           (,@for-clauses ,(for--parse-value-form
                            value-form 1
                            (pcase-lambda (`(:values ,form))
                              `(max ,form ,max))))))))

(for--defmacro for-min (for-clauses &rest body)
  "The `min'-folding iteration macro.

...

\(fn FOR-CLAUSES BODY)"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (min)
      `(for-fold ((,min 1.0e+INF))
           (,@for-clauses ,(for--parse-value-form
                            value-form 1
                            (pcase-lambda (`(:values ,form))
                              `(min ,form ,min))))))))

;;;; Provide
(provide 'for-iteration)
;;; for-iteration.el ends here
