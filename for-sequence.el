;;; for-sequence.el --- Sequence -*- lexical-binding: t; -*-

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
;; This file provides sequence constructors.

;;; Code:
;;;; Require
(require 'cl-lib)
(require 'generator)
(eval-when-compile
  (require 'for-helper)
  (require 'for-iteration)
  (require 'subr-x))

;;;; Internal
(defsubst for--make-circular (&rest values)
  "Make a circular list of VALUES."
  (declare (pure t) (side-effect-free error-free))
  (let (last)
    (let ((tail values))
      (while tail (cl-shiftf last tail (cdr tail))))
    (setf (cdr last) values)))

(defsubst for--overlay-list (buffer)
  "Return (`overlays-in' (`point-min') (`point-max')).

BUFFER is used as the current buffer."
  (declare (side-effect-free t))
  (if (not buffer) (overlays-in (point-min) (point-max))
    (with-current-buffer buffer
      (overlays-in (point-min) (point-max)))))

;;;; Interface
(defmacro define-for-sequence (name arglist &rest subforms)
  "Define a sequence constructor NAME with ARGLIST and DOCSTRING.

A SUBFORM in SUBFORMS is one of the following types:

- (`declare' [DECLARATION...]), which is a `declare' form;

- (`:alias' [ALIAS...]) where ALIAS is a identifier as an aliases
  of NAME;

- (`:type' [TYPE...]) where TYPE is a type specifier;

- (`:expander' (ARG) BODY...) where (`lambda' (ARG) BODY...) is
  the definition of the expander or (`:expander-case' [CASE...])
  equivalent to (`:expander' (ARG) (`pcase-exhaustive' ARG
  [CASE...])).

BODY are the body of generator.  See Info node `(for)Definers'.

\(fn NAME ARGLIST [DOCSTRING] [SUBFORM...] [BODY...])"
  (declare (debug (&define name lambda-list lambda-doc
                           [&optional
                            [&or ("declare" def-declarations)
                                 (":alias" &rest symbolp)
                                 (":type" &rest cl-type-spec)
                                 (&define ":expander" (arg) def-body)
                                 (&define ":expander-case"
                                          &rest (pcase-PAT body))]]
                           def-body))
           (doc-string 3) (indent 2))
  (pcase-let
      ((name-string (symbol-name name))
       ((or `(,(and (cl-type string)
                    (app (lambda (form) `(,form)) docstring))
              . ,subforms)
            (let docstring '()))
        subforms))
    (named-let parse ((declaration '()) (aliases '())
                      (types '()) (expander '()) (subforms subforms))
      (pcase subforms
        (`(,(and (let '() declaration) `(declare . ,_)
                 (app (lambda (form) `(,form)) more))
           . ,subforms)
         (parse more aliases types expander subforms))
        (`(,(and (let '() aliases) `(:alias . ,more)) . ,subforms)
         (parse declaration more types expander subforms))
        (`(,(and (let '() types) `(:type . ,more)) . ,subforms)
         (parse declaration aliases more expander subforms))
        (`(,(and (let '() expander)
                 (or `(:expander . ,(and `((,_) ,_ . ,_) body))
                     `(:expander-case
                       . ,(app (lambda (cases)
                                 `((#1=#:for-clause)
                                   (pcase-exhaustive #1# . ,cases)))
                               body))))
           . ,subforms)
         (let ((id (intern (concat name-string
                                   "--for-sequence-expander"))))
           (parse declaration aliases types
                  `((eval-and-compile (defun ,id . ,body))
                    (define-symbol-prop
                     ',name 'for--sequence-expander ',id))
                  subforms)))
        (_ (let ((body
                  (pcase-exhaustive subforms
                    ((and '() (let (and (pred (not (memq '&rest)))
                                        (app (remq '&optional) args))
                                arglist))
                     (for--with-gensyms (value)
                       `((for-iter ((,value (,name . ,args))
                                    ,value)))))
                    (`(,_ . ,_) subforms))))
             `(progn
                ,@expander
                ,@(mapcar (lambda (alias)
                            `(define-symbol-prop
                              ',alias 'for--alias ',name))
                          aliases)
                ,@(mapcar (lambda (type)
                            `(cl-defmethod for-generator
                               ((#1=#:datum ,type))
                               ,(concat "Call `" name-string
                                        "' with DATUM.")
                               (,name #1#)))
                          types)
                (defun ,name ,arglist
                  ,@docstring ,@declaration . ,body))))))))

(define-error 'for-unhandled-type "Unhandled type")

(cl-defgeneric for-generator (datum)
  "Return an iterator of DATUM.

As a special case, return DATUM as is when it is a function.  See
Info node `(for)Sequence Constructors'.")

(cl-defmethod for-generator :around (datum)
  "Return DATUM as is when it is a function.

Otherwise, invoke `cl-call-next-method'."
  (pcase datum
    ((cl-type function) datum) (_ (cl-call-next-method))))

(cl-defmethod for-generator (datum)
  "Signal `for-unhandled-type' with DATUM."
  (signal 'for-unhandled-type (list datum)))

(for--defseq for-in-array (array &optional start end step)
  "Return an iterator that returns each item in ARRAY.

Indexes are iterated as in (`for-in-range' START END STEP),
except that END defaults to (`length' ARRAY) when it is nil or
omitted."
  (:type array)
  (:expander-case
   (`(,id ,(for--funcall array-form
                         &optional start-form end-form step-form))
    (for--with-gensyms (array start end step continuep index)
      `(,id (:do-in ((,array ,array-form)
                     (,start ,start-form)
                     (,end ,end-form)
                     (,step ,step-form))
                    ((,start (or ,start 0))
                     (,end (or ,end (length ,array)))
                     (,step (or ,step 1))
                     (,continuep (if (< ,step 0) #'> #'<)))
                    ((,index ,start))
                    ((funcall ,continuep ,index ,end))
                    ((,id (aref ,array ,index)))
                    ((+ ,index ,step))))))))

(for--defseq for-in-inclusive-range (start end &optional step)
  "Return an iterator that returns each number in inclusive range.

START is the start of range, and END is the end of range.  STEP
defaults to 1 when it is nil or omitted.  Unlike `for-in-range',
the range is closed."
  (:expander-case
   (`(,id ,(for--funcall start-form end-form &optional step-form))
    (for--with-gensyms (start end step continuep number)
      `(,id (:do-in ((,start ,start-form)
                     (,end ,end-form)
                     (,step ,step-form))
                    ((,step (or ,step 1))
                     (,continuep (if (< ,step 0) #'>= #'<=)))
                    ((,number ,start))
                    ((funcall ,continuep ,number ,end))
                    ((,id ,number)) ((+ ,number ,step))))))))

(for--defseq for-in-infinite-range (start &optional step)
  "Return an iterator that returns each number in infinite range.

START is the start of range.  STEP defaults to 1 when it is nil
or omitted."
  (:expander-case
   (`(,id ,(for--funcall start-form &optional step-form))
    (for--with-gensyms (start step number)
      `(,id (:do-in ((,start ,start-form)
                     (,step ,step-form))
                    ((,step (or ,step 1)))
                    ((,number ,start)) () ((,id ,number))
                    ((+ ,number ,step))))))))

(for--defseq for-in-list (list)
  "Return an iterator that returns each element in LIST."
  (:type list)
  (:expander-case (`(,id (,_ ,list)) (for--in-list id list))))

(for--defseq for-in-producer (producer &rest args)
  "Return an iterator that returns each call to PRODUCER.

When CONTINUEP is omitted, the iterator is infinite.  Otherwise,
CONTINUEP is a unary predicate.  PRODUCER is applied to ARGS in
each iteration, and the produced value is tested by CONTINUEP.
When CONTINUEP returns nil, the iterator stops.

...

\(fn PRODUCER [CONTINUEP [ARG...]])"
  (:expander-case
   (`(,id (,_ ,producer-form))
    (for--with-gensyms (producer value)
      (let ((value-form `(funcall ,producer)))
        `(,id (:do-in ((,producer ,producer-form)) ()
                      ((,value ,value-form)) () ((,id ,value))
                      (,value-form))))))
   (`(,id (,_ ,producer-form ,continuep-form
              . ,(or (and '() arg-ids arg-bindings)
                     (and `(,_ . ,_)
                          (app (mapcar (lambda (_form)
                                         (gensym "arg")))
                               arg-ids)
                          (app (cl-mapcar (lambda (arg-id arg-form)
                                            `(,arg-id ,arg-form))
                                          arg-ids)
                               arg-bindings)))))
    (for--with-gensyms (producer continuep value)
      (let ((value-form `(funcall ,producer . ,arg-ids)))
        `(,id (:do-in ((,producer ,producer-form)
                       (,continuep ,continuep-form) . ,arg-bindings)
                      () ((,value ,value-form))
                      ((funcall ,continuep ,value))
                      ((,id ,value)) (,value-form)))))))
  (if (null args)
      (iter-make (cl-loop (iter-yield (funcall producer))))
    (pcase-let ((`(,continuep . ,args) args))
      (if (null args)
          (iter-make (let ((value (funcall producer)))
                       (while (funcall continuep value)
                         (iter-yield value)
                         (setq value (funcall producer)))))
        (iter-make (let ((value (apply producer args)))
                     (while (funcall continuep value)
                       (iter-yield value)
                       (setq value (apply producer args)))))))))

(for--defseq for-in-range (start-or-end &optional end step)
  "Return an iterator that returns each number in range.

When both END and STEP is nil, START-OR-END is the end of range,
and the start of range is 0.  Otherwise, START-OR-END is the
start of range, and END is the end of range.  STEP defaults to 1
when it is nil or omitted.  Unlike `for-in-inclusive-range', the
range is right half-open when STEP is non-negative, or left
half-open when STEP is negative."
  (:type integer)
  (:expander-case
   (`(,id ,(for--funcall start-or-end-form
                         &optional end-form step-form))
    (for--with-gensyms (start-or-end end step start continuep number)
      `(,id (:do-in ((,start-or-end ,start-or-end-form)
                     (,end ,end-form)
                     (,step ,step-form))
                    ((,start (if ,end ,start-or-end 0))
                     (,end (if ,end ,end ,start-or-end))
                     (,step (or ,step 1))
                     (,continuep (if (< ,step 0) #'> #'<)))
                    ((,number ,start))
                    ((funcall ,continuep ,number ,end))
                    ((,id ,number)) ((+ ,number ,step))))))))

(for--defseq for-in-iterator (iterator)
  "Return the function ITERATOR as is."
  (declare (pure t) (side-effect-free t))
  (:expander-case
   (`(,id (,_ ,iterator-form))
    (for--with-gensyms (returned iterator value)
      (let* ((returned `',returned)
             (next `(condition-case nil (iter-next ,iterator)
                      (iter-end-of-sequence ,returned))))
        `(,id (:do-in ((,iterator ,iterator-form)) () ((,value ,next))
                      ((not (eq ,value ,returned))) ((,id ,value))
                      (,next)))))))
  (cl-the function iterator))

(for--defseq for-in-repeat (value &rest values)
  "Return an iterator that repeatedly returns each VALUE.

...

\(fn VALUE...)"
  (:expander-case
   (`(,id (,_ ,value-form))
    (for--with-gensyms (value)
      `(,id (:do-in ((,value ,value-form)) () () () ((,id ,value))
                    ()))))
   (`(,id (,_ . ,(and `(,_ . ,_)
                      (app (mapcar (lambda (_form) (gensym "value")))
                           value-ids)
                      (app (cl-mapcar (lambda (value-id value-form)
                                        `(,value-id ,value-form))
                                      value-ids)
                           value-bindings))))
    (for--with-gensyms (values tail)
      `(,id (:do-in ,value-bindings
                    ((,values (for--make-circular . ,value-ids)))
                    ((,tail ,values)) () ((,id (car ,tail)))
                    ((cdr ,tail)))))))
  (if (null values) (iter-make (cl-loop (iter-yield value)))
    (iter-make (iter-yield value)
               (let (last)
                 (let ((tail values))
                   (while tail
                     (iter-yield (car tail))
                     (cl-shiftf last tail (cdr tail))))
                 (setf (cdr last) (push value values)))
               (cl-loop (iter-yield (car values))
                        (cl-callf cdr values)))))

(for--defseq for-in-value (value)
  "Return an iterator that returns VALUE once."
  (:expander-case
   (`(,id (,_ ,value-form))
    (for--with-gensyms (value continue)
      `(,id (:do-in ((,value ,value-form)) () ((,continue t))
                    (,continue) ((,id ,value)) (nil))))))
  (iter-make (iter-yield value)))

(for--defseq for-on-list (list)
  "Return an iterator that returns each cons on LIST."
  (:expander-case
   (`(,id (,_ ,list-form))
    (for--with-gensyms (list tail)
      `(,id (:do-in ((,list ,list-form)) () ((,tail ,list))
                    (,tail) ((,id ,tail)) ((cdr ,tail))))))))

(for--defseq for-in-directory
    (directory &optional full match nosort count)
  "Return an iterator that returns each file in DIRECTORY.

Equivalent to (`for-in-list' (`directory-files' DIRECTORY FULL
MATCH NOSORT COUNT)), where FULL, NOSORT, and COUNT defaults to
nil when omitted, and MATCH defaults to
`directory-files-no-dot-files-regexp' when it is nil or omitted."
  (:expander-case
   (`(,id ,(for--funcall directory &optional full match nosort count))
    (for--in-list id
                  (directory-files
                   directory full
                   (match directory-files-no-dot-files-regexp)
                   nosort count)))))

(for--defseq for-in-directory-recursively
    (dir regexp
         &optional include-directories predicate follow-symlinks)
  "Return an iterator that returns each file under DIRECTORY.

Equivalent to (`for-in-list' (`directory-files-recursively' DIR
REGEXP INCLUDE-DIRECTORIES PREDICATE FOLLOW-SYMLINKS)) where
INCLUDE-DIRECTORIES, PREDICATE, and FOLLOW-SYMLINKS defaults to
nil when omitted."
  (:expander-case
   (`(,id ,(for--funcall
            dir regexp
            &optional include-directories predicate follow-symlinks))
    (for--in-list id
                  (directory-files-recursively
                   dir regexp
                   include-directories predicate follow-symlinks)))))

(for--defseq for-the-buffers (&optional frame)
  "Return an iterator that returns each buffer in FRAME.

Equivalent to (`for-in-list' (`buffer-list' FRAME)) where FRAME
defaults to nil when omitted."
  (:expander-case
   (`(,id ,(or (and `(,_) (let frame nil)) `(,_ ,frame)))
    (for--in-list id (buffer-list frame)))))

(for--defseq for-the-frames ()
  "Return an iterator that returns each frame.

Not equivalent to (`for-in-list' (`frame-list')), since the
frames are visited from the selected frame in `next-frame'
order.

See Info node `(for)Sequence Constructors'."
  (:expander-case
   (`(,id (,_))
    (for--with-gensyms (current original visited)
      `(,id (:do-in () ((,original (selected-frame)) (,visited nil))
                    ((,current ,original))
                    ((or (not (eq ,current ,original))
                         (and (not ,visited) (setq ,visited t))))
                    ((,id ,current)) ((next-frame ,current)))))))
  (iter-make (let ((original (selected-frame)))
               (iter-yield original)
               (let ((current (next-frame original)))
                 (while (not (eq current original))
                   (iter-yield current)
                   (cl-callf next-frame current))))))

(for--defseq for-the-overlays (&optional buffer)
  "Return an iterator that returns each overlay in BUFFER.

Equivalent
to (`for-in-list' (`overlays-in' (`point-min') (`point-max')))
with BUFFER as the current buffer.  BUFFER defaults to the
current buffer when it is nil or omitted."
  (:expander-case
   (`(,id ,(or (and `(,_) (let buffer nil)) `(,_ ,buffer)))
    (for--in-list id (for--overlay-list buffer)))))

(for--defseq for-the-windows (&optional frame minibuf)
  "Return an iterator that returns each window in FRAME.

Not equivalent to (`for-in-list' (`window-list')), since the
frames are visited from the selected window of FRAME in
`next-window' order.  FRAME defaults to the selected frame when
it is not a frame or omitted.  MINIBUF and FRAME are passed to
`next-window' as the MINIBUF and ALL-FRAMES arguments where
MINIBUF defaults to nil when it is omitted."
  (:expander-case
   (`(,id ,(for--funcall &optional frame-form minibuf-form))
    (for--with-gensyms (frame minibuf current original visited)
      `(,id (:do-in ((,frame ,frame-form) (,minibuf ,minibuf-form))
                    ((,original (frame-selected-window
                                 (and (framep ,frame) ,frame)))
                     (,visited nil))
                    ((,current ,original))
                    ((or (not (eq ,current ,original))
                         (and (not ,visited) (setq ,visited t))))
                    ((,id ,current))
                    ((next-window ,current ,minibuf ,frame)))))))
  (iter-make (let ((original (frame-selected-window
                              (and (framep frame) frame))))
               (iter-yield original)
               (let ((current (next-window original minibuf frame)))
                 (while (not (eq current original))
                   (iter-yield current)
                   (cl-callf next-window current minibuf frame))))))

;;;; Provide
(provide 'for-sequence)
;;; for-sequence.el ends here
