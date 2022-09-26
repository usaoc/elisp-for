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
(eval-when-compile
  (require 'for-helper)
  (require 'subr-x))
(require 'cl-lib)
(require 'generator)

;;;; Internal
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

(defun for--expand-iteration-clause (clause)
  "Expand the iteration clause CLAUSE as much as possible.

CLAUSE as (FORM SEQUENCE-FORM) is expanded when SEQUENCE-FORM is
a recognized literal object, is an alias, has an associated
expander, or is treated as a function form.  The expansion stops
when SEQUENCE-FORM is a `:do-in' form."
  (named-let expand
      ((clause (pcase-exhaustive clause
                 (`(,sequence) `(,(gensym "_id") ,sequence))
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
       (expand `(,id (for-in-iterator (for-generator ,datum))))))))

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

A tail form of FORM is (`:values' [VALUE...]) with as many VALUEs
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

(defun for--parse-single-value (value-form)
  "Parse VALUE-FORM as a single-value multiple-value form."
  (declare (side-effect-free t))
  (for--parse-value-form
   value-form 1 (pcase-lambda (`(:values ,form)) form)))

(defun for--parse-bindings (bindings make-binding)
  "Parse BINDINGS as the subform of `for-fold'.

The result forms are extracted from BINDINGS or else the default
result forms are used.  Each BINDING in BINDINGS is replaced
by (`funcall' MAKE-BINDING BINDING).  Return a `cons' of the
transformed BINDINGs and the result forms."
  (declare (side-effect-free t))
  (pcase-exhaustive bindings
    ((or (and '() bindings (let result-forms '(nil)))
         (and `((:result . ,(and `(,_ . ,_) result-forms)))
              (let bindings '()))
         (and `(,_ . ,_)
              (or (app reverse
                       `((:result . ,(and `(,_ . ,_) result-forms))
                         . ,(app nreverse (app (mapcar make-binding)
                                               bindings))))
                  (app (mapcar make-binding)
                       (and bindings
                            (app (mapcar (pcase-lambda (`(,id ,_))
                                           id))
                                 (or (and `(,_) result-forms)
                                     (and `(,_ ,_)
                                          (app (lambda (ids)
                                                 `((cons . ,ids)))
                                               result-forms))
                                     (app (lambda (ids)
                                            `((list . ,ids)))
                                          result-forms))))))))
     `(,bindings . ,result-forms))))

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

(defun for--normalize-binding (binding)
  "Normalize each BINDING to be (ID VALUE)."
  (declare (side-effect-free t))
  (pcase-exhaustive binding
    ((or (and `(,_ ,_) binding)
         (and `(,id) (let binding `(,id nil)))
         (and (cl-type symbol)
              (app (lambda (id) `(,id nil)) binding)))
     binding)))

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

(defmacro for--named-let (name bindings &rest body)
  "Named `let'-ish construct.

NAME is bound to a local macro that updates BINDINGS in BODY.

\(fn NAME (BINDING...) BODY...)"
  (declare (debug (symbolp
                   (&rest &or (symbolp &optional form) symbolp)
                   body))
           (indent 2))
  (pcase-let
      (((and (app (mapcar (pcase-lambda (`(,id ,_)) id))
                  (and ids (app (mapcar (lambda (id)
                                          (gensym (symbol-name id))))
                                renamed-ids)))
             (app (mapcar (pcase-lambda (`(,_ ,value)) value))
                  values))
        bindings))
    (cl-flet ((make-binding (id value) `(,id ,value)))
      `(let ,(cl-mapcar #'make-binding renamed-ids values)
         (cl-symbol-macrolet
             ,(cl-mapcar #'make-binding ids renamed-ids)
           (cl-macrolet
               ((,name (&rest values)
                  `(for--setq . ,(cl-mapcar (lambda (id value)
                                              `(,id ,value))
                                            ',renamed-ids values))))
             . ,body))))))

;;;; Interface
(def-edebug-elem-spec 'for-result-clause '((":result" body)))

(def-edebug-elem-spec 'for-sequence-form
  '(&or (":do-in"
         (&rest &or (symbolp &optional form) symbolp)
         (&rest &or (symbolp &optional form) symbolp)
         (&rest &or (symbolp &optional form) symbolp)
         (&rest form)
         (&rest (pcase-PAT &optional form))
         (&rest form))
        (symbolp &rest sexp)
        form))

(def-edebug-elem-spec 'for-iteration-clause
  '(([&optional pcase-PAT] for-sequence-form)))

(def-edebug-elem-spec 'for-special-clause
  '(&or ([&or ":break" ":final" ":if" ":if-not" ":do"] &rest form)
        ([&or ":let" ":let*"] &rest (pcase-PAT &optional form))
        (":if-let" &or
         [symbolp form]
         [&rest &or symbolp ([&optional symbolp] form)])
        (":if-let*" &rest &or symbolp ([&optional symbolp] form))
        (":pcase" form [&optional ":exhaustive"] &rest pcase-PAT)
        (":pcase-not" form [&optional ":as" symbolp] &rest pcase-PAT)
        (keywordp &rest sexp)))

(def-edebug-elem-spec 'for-multiple-value-form
  '(&or (":values" &rest form) sexp))

(def-edebug-elem-spec 'for-for-clause
  '(&or for-iteration-clause for-special-clause))

(def-edebug-elem-spec 'for-body-form '(&or for-special-clause form))

(def-edebug-elem-spec 'for-fold-bindings
  '(([&rest &or (symbolp &optional form) symbolp]
     [&optional for-result-clause])))

(def-edebug-elem-spec 'for-vector-keywords
  '(&optional [":length" form &optional [":init" form]]))

(def-edebug-elem-spec 'for-string-keywords
  '(&optional [":length" form
               &optional [":init" form
                          &optional [":multibyte" form]]]))

(def-edebug-elem-spec 'for-lists-bindings
  '(([&rest symbolp] [&optional for-result-clause])))

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
                                 &rest (pcase-PAT body)]]))
           (doc-string 3) (indent 2))
  (pcase-let (((or `(,(and (cl-type string)
                           (app (lambda (form) `(,form)) docstring))
                     . ,cases-or-body)
                   (and cases-or-body (let docstring '())))
               cases-or-body))
    (pcase-exhaustive cases-or-body
      ((or (and (let `(,body-arg) arglist)
                (let `(,arglist . ,body)
                  (for--with-gensyms (special-clause)
                    `((,special-clause ,body-arg)
                      (pcase-exhaustive ,special-clause
                        . ,cases-or-body)))))
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

(for--defspecial-let :let pcase-let
  "Evaluate BODY with subforms bound by `%S'.")

(for--defspecial-let :if-let when-let
  "Evaluate BODY with subforms bound by `%S'.")

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

BINDINGS = ([BINDING...] [(:result EXPRESSION...)])

BINDING = IDENTIFIER | (IDENTIFIER [EXPRESSION])"
  (declare (debug (&or [for-fold-bindings
                        ([&rest for-for-clause]
                         for-multiple-value-form)]
                       [for-fold-bindings
                        (&rest for-for-clause)
                        [&rest for-body-form]
                        for-multiple-value-form]))
           (indent 2))
  (pcase-let
      ((`(,bindings . ,result-forms)
        (for--parse-bindings bindings #'for--normalize-binding))
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
                                   `((:let (,final-guard
                                            (and . ,guards)))
                                     . ,parsed)
                                   clauses)))
                         (_ (parse final-ids body
                                   `(,clause . ,parsed) clauses)))))))
                `(,final-ids
                  ,body
                  ,(app for--parse-for-clauses for-clauses)))
          . ,value-form)
        (for--parse-body for-clauses body)))
    (cl-flet
        ((make-body (update)
           (named-let expand
               ((break-ids '()) (body `(,update . ,body))
                (clauses (reverse for-clauses)))
             (cl-flet
                 ((make-iteration (body
                                   memoize-bindings outer-bindings
                                   loop-bindings loop-guards
                                   inner-bindings loop-forms)
                    (cl-flet ((make-body (body)
                                `((while (and ,@break-ids
                                              ,@final-ids
                                              . ,loop-guards)
                                    . ,(if (null inner-bindings) body
                                         `((pcase-let ,inner-bindings
                                             . ,body)))))))
                      (let* ((body
                              (pcase-exhaustive loop-bindings
                                ('() (make-body body))
                                (`(,_ . ,_)
                                 (for--with-gensyms (update)
                                   `((for--named-let ,update
                                         ,(mapcar
                                           #'for--normalize-binding
                                           loop-bindings)
                                       . ,(make-body
                                           `(,@body
                                             (when (and ,@break-ids
                                                        ,@final-ids)
                                               (,update
                                                ,@loop-forms))))))))))
                             (body
                              (if (null outer-bindings) body
                                `((let ,outer-bindings . ,body))))
                             (body
                              (if (null memoize-bindings) body
                                `((let ,memoize-bindings . ,body)))))
                        body))))
               (if (null clauses)
                   (let* ((body (pcase (nconc break-ids final-ids)
                                  ('() body)
                                  (ids `((let ,(mapcar (lambda (id)
                                                         `(,id t))
                                                       ids)
                                           . ,body)))))
                          (body (if (null result-forms) body
                                  `(,@body . ,result-forms))))
                     body)
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
                                  `((if (and . ,guards)
                                        (setq ,break nil)
                                      . ,expanded))
                                  clauses)))
                       (`(,expander . ,special-clause)
                        (expand break-ids
                                (funcall expander
                                         special-clause expanded)
                                clauses))))))))))
      (macroexp-progn
       (if (null bindings)
           (make-body (for--parse-value-form
                       value-form 0 (lambda (_form) nil)))
         (for--with-gensyms (update)
           `((for--named-let ,update ,bindings
               . ,(make-body (for--parse-value-form
                              value-form (length bindings)
                              (pcase-lambda (`(:values . ,forms))
                                `(,update . ,forms))))))))))))

(for--defmacro for-foldr (bindings for-clauses &rest body)
  "The reverse-folding iteration macro.

BINDINGS = ([BINDING...] [(:result EXPRESSION...)])

BINDING = IDENTIFIER | (IDENTIFIER [EXPRESSION])"
  (declare (debug for-fold) (indent 2))
  (cl-assert lexical-binding)
  (pcase-let
      ((`(,bindings . ,result-forms)
        (for--parse-bindings bindings #'for--normalize-binding))
       (`(,for-clauses . ,value-form)
        (for--parse-body for-clauses body)))
    (for--with-gensyms (update next)
      `(for--named-let ,update ,bindings
         (funcall (for-fold ((,next (lambda () nil)))
                      (,@for-clauses
                       (:let (,next ,next))
                       (lambda ()
                         ,(for--parse-value-form
                           value-form (length bindings)
                           (pcase-lambda (`(:values . ,forms))
                             `(,update . ,forms)))
                         (funcall ,next)))))
         . ,result-forms))))

(for--defmacro for-do (for-clauses &rest body)
  "The side-effecting iteration macro."
  (declare (debug ((&rest for-for-clause) &rest for-body-form))
           (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses `(,@body (:values)))))
    `(for-fold () (,@for-clauses ,value-form))))

(for--defmacro for-list (for-clauses &rest body)
  "The list-building iteration macro."
  (declare (debug (&or ([&rest for-for-clause]
                        for-multiple-value-form)
                       [(&rest for-for-clause)
                        [&rest for-body-form]
                        for-multiple-value-form]))
           (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (list)
      `(for-fold ((,list '()) (:result (nreverse ,list)))
           (,@for-clauses
            (cons ,(for--parse-single-value value-form) ,list))))))

(for--defmacro for-iter (for-clauses &rest body)
  "The iterator-returning macro."
  (declare (debug for-list) (indent 1))
  (cl-assert lexical-binding)
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    `(iter-make
      (for-do (,@for-clauses
               (:do (iter-yield
                     ,(for--parse-single-value value-form))))))))

(for--defmacro for-lists (bindings for-clauses &rest body)
  "The multiple-list-building iteration macro.

BINDINGS = ([IDENTIFIER...] [(:result EXPRESSION...)])"
  (declare (debug (&or [for-lists-bindings
                        ([&rest for-for-clause]
                         for-multiple-value-form)]
                       [for-lists-bindings
                        (&rest for-for-clause)
                        [&rest for-body-form]
                        for-multiple-value-form]))
           (indent 2))
  (pcase-let ((`(,bindings . ,result-forms)
               (for--parse-bindings
                bindings (lambda (id) `(,(cl-the symbol id) '()))))
              (`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (cl-flet ((make-fold (bindings value-form)
                `(for-fold ,bindings (,@for-clauses ,value-form))))
      (if (null bindings)
          (make-fold `((:result . ,result-forms)) value-form)
        (let ((ids (mapcar (pcase-lambda (`(,id ,_)) id) bindings)))
          (make-fold `(,@bindings
                       (:result (let ,(mapcar (lambda (id)
                                                `(,id (nreverse ,id)))
                                              ids)
                                  . ,result-forms)))
                     (for--parse-value-form
                      value-form (length bindings)
                      (pcase-lambda (`(:values . ,forms))
                        `(:values . ,(cl-mapcar (lambda (form id)
                                                  `(cons ,form ,id))
                                                forms ids))))))))))

(for--defmacro for-vector (for-clauses &rest body)
  "The vector-building iteration macro.

...

\(fn FOR-CLAUSES [:length LENGTH [:init INIT]] BODY)"
  (declare (debug (&or [([&rest for-for-clause]
                         for-multiple-value-form)
                        for-vector-keywords]
                       [(&rest for-for-clause)
                        for-vector-keywords [&rest for-body-form]
                        for-multiple-value-form]))
           (indent 1))
  (pcase body
    ((or `(:length ,length-form :init ,init-form . ,body)
         (and `(:length ,length-form . ,body) (let init-form 0)))
     (pcase-let ((`(,for-clauses . ,value-form)
                  (for--parse-body for-clauses body)))
       (for--with-gensyms (length init index vector)
         `(let ((,length ,length-form) (,init ,init-form))
            (if (zerop ,length) []
              (let ((,vector (make-vector ,length ,init)))
                (for-fold ((,index 0))
                    (,@for-clauses
                     (:do (setf (aref ,vector ,index)
                                ,(for--parse-single-value
                                  value-form)))
                     (:let (,index (1+ ,index)))
                     (:break (= ,index ,length))
                     ,index))
                ,vector))))))
    (_ (pcase-let ((`(,for-clauses . ,value-form)
                    (for--parse-body for-clauses body)))
         `(vconcat (for-list (,@for-clauses ,value-form)))))))

(for--defmacro for-string (for-clauses &rest body)
  "The string-building iteration macro.

...

\(fn FOR-CLAUSES [:length LENGTH [:init INIT [:multibyte MULTIBYTE]]] BODY)"
  (declare (debug (&or [([&rest for-for-clause]
                         for-multiple-value-form)
                        for-string-keywords]
                       [(&rest for-for-clause)
                        for-string-keywords [&rest for-body-form]
                        for-multiple-value-form]))
           (indent 1))
  (pcase body
    ((or `(:length ,length-form :init ,init-form
                   :multibyte ,multibyte-form . ,body)
         (and (or `(:length ,length-form :init ,init-form . ,body)
                  (and `(:length ,length-form . ,body)
                       (let init-form ?\0)))
              (let multibyte-form nil)))
     (pcase-let ((`(,for-clauses . ,value-form)
                  (for--parse-body for-clauses body)))
       (for--with-gensyms (length init multibyte index string)
         `(let ((,length ,length-form) (,init ,init-form)
                (,multibyte ,multibyte-form))
            (if (zerop ,length)
                (if ,multibyte (make-string 0 ?\0 'multibyte) "")
              (let ((,string (make-string ,length ,init ,multibyte)))
                (for-fold ((,index 0))
                    (,@for-clauses
                     (:do (setf (aref ,string ,index)
                                ,(for--parse-single-value
                                  value-form)))
                     (:let (,index (1+ ,index)))
                     (:break (= ,index ,length))
                     ,index))
                ,string))))))
    (_ (pcase-let ((`(,for-clauses . ,value-form)
                    (for--parse-body for-clauses body)))
         `(concat (for-list (,@for-clauses ,value-form)))))))

(for--defmacro for-and (for-clauses &rest body)
  "The `and'-folding iteration macro."
  (declare (debug for-list) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (value)
      `(for-fold ((,value t))
           (,@for-clauses
            (:let (,value ,(for--parse-single-value value-form)))
            (:final (not ,value))
            ,value)))))

(for--defmacro for-or (for-clauses &rest body)
  "The `or'-folding iteration macro."
  (declare (debug for-list) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (value)
      `(for-fold ((,value nil))
           (,@for-clauses
            (:let (,value ,(for--parse-single-value value-form)))
            (:final ,value)
            ,value)))))

(for--defmacro for-sum (for-clauses &rest body)
  "The sum-accumulating iteration macro."
  (declare (debug for-list) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (sum)
      `(for-fold ((,sum 0))
           (,@for-clauses
            (+ ,(for--parse-single-value value-form) ,sum))))))

(for--defmacro for-product (for-clauses &rest body)
  "The product-accumulating iteration macro."
  (declare (debug for-list) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (product)
      `(for-fold ((,product 1))
           (,@for-clauses
            (* ,(for--parse-single-value value-form) ,product))))))

(for--defmacro for-first (for-clauses &rest body)
  "The first-value-returning iteration macro."
  (declare (debug for-list) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (value)
      `(for-fold ((,value nil))
           ((:final) ,@for-clauses ,value-form)))))

(for--defmacro for-last (for-clauses &rest body)
  "The last-value-returning iteration macro."
  (declare (debug for-list) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (value)
      `(for-fold ((,value nil)) (,@for-clauses ,value-form)))))

(for--defmacro for-max (for-clauses &rest body)
  "The `max'-folding iteration macro."
  (declare (debug for-list) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (max)
      `(for-fold ((,max -1.0e+INF))
           (,@for-clauses
            (max ,(for--parse-single-value value-form) ,max))))))

(for--defmacro for-min (for-clauses &rest body)
  "The `min'-folding iteration macro."
  (declare (debug for-list) (indent 1))
  (pcase-let ((`(,for-clauses . ,value-form)
               (for--parse-body for-clauses body)))
    (for--with-gensyms (min)
      `(for-fold ((,min 1.0e+INF))
           (,@for-clauses
            (min ,(for--parse-single-value value-form) ,min))))))

;;;; Provide
(provide 'for-iteration)
;;; for-iteration.el ends here
