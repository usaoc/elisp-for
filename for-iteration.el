;;; for-iteration.el --- Iteration -*- lexical-binding: t; -*-

;; Copyright (C) 2022 Wing Hei Chan

;; Author: Wing Hei Chan <whmunkchan@outlook.com>
;; URL: https://github.com/usaoc/elisp-for
;; Keywords: extensions
;; Package-Requires: ((emacs "28.1"))

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
(defun for--macroexpand (form)
  "Expand FORM as much as possible.

Repeatedly call `macroexpand' and `cl-compiler-macroexpand' on
FORM until FORM cannot be further expanded.
`macroexpand-all-environment' is taken into account.  Vacuous
quotes are removed."
  (pcase (named-let expand ((form form))
           (pcase (cl-compiler-macroexpand
                   (macroexpand form macroexpand-all-environment))
             ((pred (eq form)) form) (expanded (expand expanded))))
    (`(,(or 'quote 'function)
       ,(and (cl-type atom) (pred macroexp-const-p) quoted))
     quoted)
    (form form)))

(pcase-defmacro for--lit (&rest pats)
  "Pcase pattern that matches expanded object.

Apply `for--macroexpand' to EXPVAL and matches the result against
PATS."
  `(app for--macroexpand
        ,(pcase pats ('() '_) (`(,pat) pat) (_ `(and . ,pats)))))

(pcase-defmacro for--type (type &rest pats)
  "Pcase pattern that matches the type of expanded object.

Apply `for--macroexpand' to EXPVAL and matches the result against
TYPE and PATS.  TYPE is transformed to a suitable pattern that
matches the type of EXPVAL literally.  See Info node `(cl)Type
Predicates'."
  `(for--lit ,(pcase type
                ('list '(or '() `',(cl-type list)))
                ('symbol '`',(cl-type symbol)) (_ `(cl-type ,type)))
             . ,pats))

(defvar for--datum-dispatch-alist '()
  "Alist of type specifiers vs generators.")

(define-error 'for-unhandled-type "Unhandled type")

(defun for--datum-to-iterator (datum)
  "Dispatch on DATUM and return an iterator.

Find the generator in `for--datum-dispatch-alist' and apply it to
DATUM."
  (let ((missing '#:missing))
    (pcase (alist-get datum for--datum-dispatch-alist
                      missing nil (lambda (type datum)
                                    (cl-typep datum type)))
      ((pred (eq missing)) (signal 'for-unhandled-type (list datum)))
      (generator (funcall generator datum)))))

(defun for--datum-to-sequence (datum)
  "Transform DATUM to a sequence form.

Currently, literal lists, arrays, and integers after
macro-expansion are transformed to `for-in-list', `for-in-array',
and `for-in-range' sequences."
  (declare (side-effect-free t))
  (pcase datum
    ((for--type list) `(for-in-list ,datum))
    ((for--type array) `(for-in-array ,datum))
    ((for--type integer) `(for-in-range ,datum)) (_ nil)))

(defun for--iterator-for-clause (iteration-clause)
  "Transform ITERATION-CLAUSE to iterate over an iterator.

ITERATION-CLAUSE is (FORM ITERATOR) where FORM is an arbitrary
form and ITERATOR is an expression that produces an iterator."
  (declare (side-effect-free t))
  (pcase-exhaustive iteration-clause
    (`(,id ,form)
     (cl-with-gensyms (iterator next)
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
      (`(,_ (:do-in ,_ ,_ ,_ ,_ ,_ ,_)) clause)
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
      ((and `(,clause . ,clauses)
            (or (and (let `(,(cl-type keyword) . ,_) clause)
                     (let infix '()) (let iteration nil))
                (and (let `(,_ ,_) clause)
                     (let infix (if iteration '((:do)) '()))
                     (let iteration t))))
       (parse `(,clause ,@infix . ,nested) iteration clauses)))))

(defun for--parse-value-form (form number make-value)
  "Parse FORM as a multiple-value form after macro-expansion.

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
    (pcase-exhaustive (for--macroexpand form)
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
  (pcase-exhaustive body
    ((or (and '() (let (and `(,_ . ,_)
                            (app reverse
                                 `(,value-form
                                   . ,(app nreverse clauses))))
                    for-clauses))
         (and `(,_ . ,_) (let (or '() `(,_ . ,_)) for-clauses)
              (app reverse
                   (app (mapcar
                         (pcase-lambda
                           ((or (and `(,(cl-type keyword) . ,_)
                                     clause)
                                (app (lambda (form) `(:do ,form))
                                     clause)))
                           clause))
                        `(,(or `(:do ,value-form) value-form)
                          . ,(app nreverse
                                  (app (lambda (clauses)
                                         `(,@for-clauses ,@clauses))
                                       clauses)))))))
     `(,clauses . ,value-form))))

(defun for--parse-for-clauses (for-clauses)
  "Parse FOR-CLAUSES.

Split FOR-CLAUSES into ([GROUP...]) where GROUP is (HEAD
[MEMOIZED-BINDINGS OUTER-BINDINGS LOOP-BINDINGS LOOP-GUARDS
INNER-BINDINGS LOOP-FORMS]) and HEAD is either (`:break'
[GUARD...]) or (EXPANDER [SUBFORM...])."
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
        (`(,(or (and `(:break . ,_) head)
                (and `(,(and (cl-type keyword)
                             (app (lambda (keyword)
                                    (get keyword
                                         'for--special-clause-expander
                                         ))
                                  (and (pred identity) expander)))
                       . ,_)
                     (app (lambda (special-clause)
                            `(,expander . ,special-clause))
                          head)))
           . ,clauses)
         (parse '() '() '() '() '() '() nil
                `((,head . ,group) . ,groups) clauses))
        (`(,(app for--expand-iteration-clause
                 (and `(,_ (:do-in ,more-memoize-bindings
                                   ,more-outer-bindings
                                   ,more-loop-bindings
                                   ,more-loop-guards
                                   ,more-inner-bindings
                                   ,more-loop-forms))
                      (guard (= (length more-loop-bindings)
                                (length more-loop-forms)))))
           . ,clauses)
         (parse (append more-memoize-bindings memoize-bindings)
                (append more-outer-bindings outer-bindings)
                (append more-loop-bindings loop-bindings)
                (append more-loop-guards loop-guards)
                (append more-inner-bindings inner-bindings)
                (append more-loop-forms loop-forms)
                t groups clauses))))))

(defmacro for--setq (&rest pairs)
  "Expand to a form equivalent to (`cl-psetq' [ID VALUE]...).

When a pair of ID and VALUE in PAIRS is `eq' after
macro-expansion, eliminate them from the expanded form.

\(fn (ID VALUE)...)"
  (declare (debug (&rest (symbolp form))))
  (cl-reduce (lambda (pair form)
               (pcase-exhaustive pair
                 (`(,(for--lit id) ,(for--lit id)) form)
                 (`(,(for--lit id) ,(for--lit value))
                  `(setq ,id (prog1 ,value ,form)))))
             pairs :from-end t :initial-value nil))

(eval-when-compile
  (defmacro for--defmacro (name arglist &rest body)
    "Define the iteration macro NAME with the star version.

ARGLIST, DOCSTRING, DECL, and BODY are as in normal `defmacro'
forms.

\(fn NAME ARGLIST [DOCSTRING] [DECL] BODY...)"
    (declare (debug (&define name lambda-list lambda-doc
                             [&optional ("declare" def-declarations)]
                             def-body))
             (doc-string 3) (indent 2))
    (pcase-exhaustive (reverse arglist)
      (`(,body-form &rest ,for-clause-form
                    . ,(app (mapcar (lambda (form) (list '\, form)))
                            (app nreverse forms)))
       (pcase-let*
           (((or `(,(and (cl-type string)
                         (app (lambda (docstring)
                                `(,(replace-regexp-in-string
                                    (rx bol "..." eol) "\
BODY = SPECIAL-CLAUSE | EXPRESSION

FOR-CLAUSE = SPECIAL-CLAUSE | ITERATION-CLAUSE

SPECIAL-CLAUSE = (KEYWORD [SUBFORM...])

ITERATION-CLAUSE = ([IDENTIFIER] SEQUENCE-FORM)

See Info node `(for)Iteration Macros'." docstring)))
                              docstring))
                   . ,body)
                 (and body (let docstring '())))
             body)
            ((or `(,(and `(declare . ,_)
                         (app (lambda (form) `(,form)) declaration))
                   . ,body)
                 (and body (let declaration '())))
             body))
         `(prog1 (defmacro ,name ,arglist
                   ,@docstring ,@declaration . ,body)
            (defmacro ,(intern (concat (symbol-name name) "*"))
                ,arglist ,@docstring ,@declaration
                (pcase-let
                    ((`(,(app for--nest-for-clauses for-clauses)
                        . ,value-form)
                      (for--parse-body ,for-clause-form ,body-form)))
                  ,(list '\` `(,name ,@forms ,'(,@for-clauses
                                                ,value-form)))))))))))

(def-edebug-spec for--result-clauses-spec (":result" body))

(def-edebug-spec for--bindings-spec
  (&rest [&or for--result-clauses-spec (symbolp form)]))

(def-edebug-spec for--iteration-clauses-spec (sexp form))

(def-edebug-spec for--special-clauses-spec
  [&or ([&or ":break" ":final" ":if" ":if-not" ":do"] &rest form)
       ([&or ":let" ":if-let"] &rest (sexp form))
       ([&or ":pcase" ":pcase-not"] &rest pcase-PAT) (keywordp sexp)])

(def-edebug-spec for--value-clauses-spec (":values" &rest form))

(def-edebug-spec for--for-clauses-spec
  (&rest [&or for--value-clauses-spec for--special-clauses-spec
              for--iteration-clauses-spec]))

(def-edebug-spec for--body-spec
  (&rest [&or for--value-clauses-spec for--special-clauses-spec
              form]))

(def-edebug-spec for--fold-spec
  (for--fold-bindings-spec for--for-clauses-spec for--body-spec))

(def-edebug-spec for--do-for-clauses-spec
  (&rest [&or for--special-clauses-spec for--iteration-clauses-spec]))

(def-edebug-spec for--do-body-spec
  (&rest [&or for--special-clauses-spec form]))

(def-edebug-spec for--do-spec
  (for--do-for-clauses-spec for--do-body-spec))

(def-edebug-spec for--accumulator-spec
  (for--for-clauses-spec for--body-spec))

(def-edebug-spec for--lists-bindings-spec
  (&rest [&or symbolp for--result-clauses-spec]))

(def-edebug-spec for--lists-spec
  (for--lists-bindings-spec for--for-clauses-spec for--body-spec))

;;;; Interface
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

;;;###autoload(define-symbol-prop 'for-binder 'safe-local-variable #'symbolp)
(defvar-local for-binder 'pcase-let
  "The head of certain `let'-like forms in iteration forms.

See Info node `(for)Buffer-Local Variables'.")

(define-for-special-clause :if (body)
  "Evaluate BODY when all subforms are non-nil.

See Info node `(for)Special-Clause Operators'"
  (`(,_ . ,guards) `((when (and . ,guards) . ,body))) )

(define-for-special-clause :if-not (body)
  "Evaluate BODY unless all subforms are non-nil.

See Info node `(for)Special-Clause Operators'"
  (`(,_ . ,guards) `((unless (and . ,guards) . ,body))) )

(define-for-special-clause :let (body)
  "Evaluate BODY with subforms bound by `for-binder'.

See Info node `(for)Special-Clause Operators'"
  (`(,_ . ,bindings) `((,for-binder ,bindings . ,body))))

(define-for-special-clause :if-let (body)
  "Evaluate BODY with subforms bound by `when-let*'.

See Info node `(for)Special-Clause Operators'"
  (`(,_ . ,bindings) `((when-let* ,bindings . ,body))))

(define-for-special-clause :pcase (body)
  "Evaluate BODY when the first subform is matched.

The remaining subforms are the patterns as in `pcase'.  When an
optional sequence [`:exhaustive'] is present in the remaining
subforms, match exhaustively, that is, use `pcase-exhaustive'.

See Info node `(for)Special-Clause Operators'"
  ((or (and `(,_ ,expr :exhaustive . ,pats)
            (let head 'pcase-exhaustive))
       (and `(,_ ,expr . ,pats) (let head 'pcase)))
   `((,head ,expr ((and . ,pats) . ,body)))))

(define-for-special-clause :pcase-not (body)
  "Evaluate BODY when the first subform is not matched.

The remaining subforms are the patterns as in `pcase'.  When an
optional sequence [`:as' AS] is present in the remaining
subforms, the value of the first subform is bound to AS, and the
subforms after the sequence are the patterns.

See Info node `(for)Special-Clause Operators'"
  ((or `(,_ ,expr :as ,(and (cl-type symbol) as) . ,pats)
       (and `(,_ ,expr . ,pats) (let as '_)))
   `((pcase ,expr ((and . ,pats) nil) (,as . ,body)))))

(define-for-special-clause :do (body)
  "Evaluate the subforms before evaluating BODY.

See Info node `(for)Special-Clause Operators'"
  (`(,_ . ,forms) `(,@forms . ,body)))

(for--defmacro for-fold (bindings for-clauses &rest body)
  "The fundamental folding iteration macro.

...

\(fn ([(IDENTIFIER INITIAL-VALUE)] [(:result EXPRESSION...)]) (FOR-CLAUSE... [MULTIPLE-VALUE-FORM]) [BODY... MULTIPLE-VALUE-FORM])"
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
                  (named-let loop
                      ((final-ids '()) (body '()) (parsed '())
                       (clauses (reverse clauses)))
                    (pcase-exhaustive clauses
                      ('() `(,final-ids ,body ,parsed))
                      (`(,clause . ,clauses)
                       (pcase clause
                         (`(:final . ,guards)
                          (cl-with-gensyms (final)
                            (let ((once '#:once))
                              (loop `(,final . ,final-ids)
                                    `((when (eq ,final ',once)
                                        (setq ,final nil))
                                      . ,body)
                                    `((:do (when (and . ,guards)
                                             (setq ,final ',once)))
                                      . ,parsed)
                                    clauses))))
                         (_ (loop final-ids body
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
                   (if (zerop length-bindings)
                       (pcase-lambda (`(:values)) nil)
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
                 (cl-with-gensyms (break)
                   (expand `(,break . ,break-ids)
                           `((if (and . ,guards) (setq ,break nil)
                               . ,expanded))
                           clauses)))
                (`(,expander . ,special-clause)
                 (expand break-ids
                         (funcall expander special-clause expanded)
                         clauses))))))))))

(for--defmacro for-do (for-clauses &rest body)
  "The side-effecting iteration macro.

...

\(fn (FOR-CLAUSE...) [BODY...])"
  (declare (debug for--do-spec) (indent 1))
  `(for-fold () ,for-clauses ,@body (:values)))

(for--defmacro for-list (for-clauses &rest body)
  "The list-building iteration macro.

...

\(fn (FOR-CLAUSE... [MULTIPLE-VALUE-FORM]) [BODY... MULTIPLE-VALUE-FORM])"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (cl-with-gensyms (list)
      `(for-fold ((,list '()) (:result (nreverse ,list)))
           (,@for-clauses ,(for--parse-value-form
                            value-form 1
                            (pcase-lambda (`(:values ,form))
                              `(cons ,form ,list))))))))

(for--defmacro for-lists (bindings for-clauses &rest body)
  "The multiple-list-building iteration macro.

...

\(fn ([IDENTIFIER...] [(:result EXPRESSION...)]) (FOR-CLAUSE... [MULTIPLE-VALUE-FORM]) [BODY... MULTIPLE-VALUE-FORM])"
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
            (pcase-lambda (`(:values . ,forms))
              `(:values . ,(cl-mapcar (lambda (form id)
                                        `(cons ,form ,id))
                                      forms ids))))))))

(for--defmacro for-vector (for-clauses &rest body)
  "The vector-building iteration macro.

...

\(fn (FOR-CLAUSE... [MULTIPLE-VALUE-FORM]) [:length LENGTH [:init INIT]] [BODY... MULTIPLE-VALUE-FORM])"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase body
    ((or (and `(:length ,length-form :init ,init-form . ,body))
         (and `(:length ,length-form . ,body) (let init-form nil)))
     (pcase-let ((`(,for-clauses . ,value-form)
                  (for--parse-body for-clauses body)))
       (cl-with-gensyms (length init index vector)
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
    (_ `(vconcat (for-list ,for-clauses . ,body)))))

(for--defmacro for-and (for-clauses &rest body)
  "The `and'-folding iteration macro.

...

\(fn (FOR-CLAUSE... [MULTIPLE-VALUE-FORM]) [BODY... MULTIPLE-VALUE-FORM])"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (cl-with-gensyms (value)
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

\(fn (FOR-CLAUSE... [MULTIPLE-VALUE-FORM]) [BODY... MULTIPLE-VALUE-FORM])"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (cl-with-gensyms (value)
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

\(fn (FOR-CLAUSE... [MULTIPLE-VALUE-FORM]) [BODY... MULTIPLE-VALUE-FORM])"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (cl-with-gensyms (sum)
      `(for-fold ((,sum 0))
           (,@for-clauses ,(for--parse-value-form
                            value-form 1
                            (pcase-lambda (`(:values ,form))
                              `(+ ,form ,sum))))))))

(for--defmacro for-product (for-clauses &rest body)
  "The product-accumulating iteration macro.

...

\(fn (FOR-CLAUSE... [MULTIPLE-VALUE-FORM]) [BODY... MULTIPLE-VALUE-FORM])"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (cl-with-gensyms (product)
      `(for-fold ((,product 1))
           (,@for-clauses ,(for--parse-value-form
                            value-form 1
                            (pcase-lambda (`(:values ,form))
                              `(* ,form ,product))))))))

(for--defmacro for-first (for-clauses &rest body)
  "The first-value-returning iteration macro.

...

\(fn (FOR-CLAUSE... [MULTIPLE-VALUE-FORM]) [BODY... MULTIPLE-VALUE-FORM])"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (cl-with-gensyms (value)
      `(for-fold ((,value nil))
           (,@for-clauses (:final) ,value-form)))))

(for--defmacro for-last (for-clauses &rest body)
  "The last-value-returning iteration macro.

...

\(fn (FOR-CLAUSE... [MULTIPLE-VALUE-FORM]) [BODY... MULTIPLE-VALUE-FORM])"
  (declare (debug for--accumulator-spec) (indent 1))
  (cl-with-gensyms (value)
    `(for-fold ((,value nil)) ,for-clauses . ,body)))

(for--defmacro for-max (for-clauses &rest body)
  "The `max'-folding iteration macro.

...

\(fn (FOR-CLAUSE... [MULTIPLE-VALUE-FORM]) [BODY... MULTIPLE-VALUE-FORM])"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (cl-with-gensyms (max)
      `(for-fold ((,max -1.0e+INF))
           (,@for-clauses ,(for--parse-value-form
                            value-form 1
                            (pcase-lambda (`(:values ,form))
                              `(max ,form ,max))))))))

(for--defmacro for-min (for-clauses &rest body)
  "The `min'-folding iteration macro.

...

\(fn (FOR-CLAUSE... [MULTIPLE-VALUE-FORM]) [BODY... MULTIPLE-VALUE-FORM])"
  (declare (debug for--accumulator-spec) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (cl-with-gensyms (min)
      `(for-fold ((,min 1.0e+INF))
           (,@for-clauses ,(for--parse-value-form
                            value-form 1
                            (pcase-lambda (`(:values ,form))
                              `(min ,form ,min))))))))

;;;; Provide
(provide 'for-iteration)
;;; for-iteration.el ends here
