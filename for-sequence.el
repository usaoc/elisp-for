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
(require 'for-iteration)
(require 'generator)

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
      (((or `(,(and (cl-type string)
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
                                 `((for-clause)
                                   (pcase-exhaustive for-clause
                                     . ,cases)))
                               body))))
           . ,subforms)
         (let ((id (intern (concat (symbol-name name)
                                   "--for-sequence-expander"))))
           (parse declaration aliases types
                  `((eval-and-compile (defun ,id . ,body))
                    (define-symbol-prop
                     ',name 'for--sequence-expander ',id))
                  subforms)))
        (_ `(progn
              ,@expander
              ,@(mapcar (lambda (alias)
                          `(define-symbol-prop
                            ',alias 'for--alias ',name))
                        aliases)
              ,@(mapcar (lambda (type)
                          `(setf (alist-get
                                  ',type for--datum-dispatch-alist
                                  nil nil #'equal)
                                 #',name))
                        types)
              (defun ,name ,arglist
                ,@docstring ,@declaration
                . ,(pcase-exhaustive subforms
                     ((and '() (let (and (pred (not (memq '&rest)))
                                         (app (remq '&optional) args))
                                 arglist))
                      `((iter-make
                         (for-do ((value (,name . ,args))
                                  (:do (iter-yield value)))))))
                     (`(,_ . ,_) subforms)))))))))

(define-for-sequence for-in-array (array)
  "Return an iterator that returns each item in ARRAY.

See Info node `(for)Sequence Constructors'."
  (:alias in-array) (:type array)
  (:expander-case
   (`(,id (,_ ,array-form))
    (for--with-gensyms (array length index)
      `(,id (:do-in ((,array ,array-form)) ((,length (length ,array)))
                    ((,index 0)) ((< ,index ,length))
                    ((,id (aref ,array ,index))) ((1+ ,index)))))))
  (declare (side-effect-free t)))

(define-for-sequence for-in-inclusive-range (start end &optional step)
  "Return an iterator that returns each number in inclusive range.

START is the start of range, and END is the end of range.  STEP
defaults to 1 when it is nil or omitted.  Unlike `for-in-range',
the range is closed.

See Info node `(for)Sequence Constructors'.

\(fn START END [STEP])"
  (:alias in-inclusive-range)
  (:expander-case
   (`(,id ,(or (and `(,_ ,start-form ,end-form)
                    (let step-form nil))
               `(,_ ,start-form ,end-form ,step-form)))
    (for--with-gensyms (start end step continuep number)
      `(,id (:do-in ((,start ,start-form) (,end ,end-form)
                     (,step (or ,step-form 1)))
                    ((,continuep (if (< ,step 0) #'>= #'<=)))
                    ((,number ,start))
                    ((funcall ,continuep ,number ,end))
                    ((,id ,number)) ((+ ,number ,step)))))))
  (declare (side-effect-free t)))

(define-for-sequence for-in-list (list)
  "Return an iterator that returns each element in LIST.

See Info node `(for)Sequence Constructors'."
  (:alias in-list) (:type list)
  (:expander-case
   (`(,id (,_ ,list-form))
    (for--with-gensyms (list tail)
      `(,id (:do-in ((,list ,list-form)) () ((,tail ,list))
                    (,tail) ((,id (car ,tail))) ((cdr ,tail)))))))
  (declare (side-effect-free t)))

(define-for-sequence for-in-naturals (&optional start)
  "Return an iterator that returns each natural number from START.

START defaults to 0 when it is nil or omitted.

See Info node `(for)Sequence Constructors'.

\(fn [START])"
  (:alias in-naturals)
  (:expander-case
   (`(,id ,(or (and `(,_) (let start-form 0))
               `(,_ ,start-form)))
    (for--with-gensyms (start number)
      `(,id (:do-in ((,start ,start-form)) ()
                    ((,number (cl-the (integer 0) ,start))) ()
                    ((,id ,number)) ((1+ ,number)))))))
  (declare (side-effect-free t)))

(define-for-sequence for-in-producer (producer &rest args)
  "Return an iterator that returns each call to PRODUCER.

When CONTINUEP is omitted, the iterator is infinite.  Otherwise,
CONTINUEP is a unary predicate.  PRODUCER is applied to ARGS in
each iteration, and the produced value is tested by CONTINUEP.
When CONTINUEP returns nil, the iterator stops.

See Info node `(for)Sequence Constructors'.

\(fn PRODUCER [CONTINUEP [ARG...]])"
  (:alias in-producer)
  (:expander-case
   (`(,id (,_ ,producer-form))
    (for--with-gensyms (producer value)
      (let ((value-form `(funcall ,producer)))
        `(,id (:do-in ((,producer ,producer-form)) ()
                      ((,value ,value-form)) () ((,id ,value))
                      (,value-form))))))
   (`(,id (,_ ,producer-form ,continuep-form . ,arg-forms))
    (pcase-let
        ((`(,arg-ids . ,arg-bindings)
          (for-lists (ids bindings)
              ((arg-form (in-list arg-forms))
               (for--with-gensyms (arg)
                 (:values arg `(,arg ,arg-form)))))))
      (for--with-gensyms (producer continuep value)
        (let ((value-form `(funcall ,producer . ,arg-ids)))
          `(,id (:do-in ((,producer ,producer-form)
                         (,continuep ,continuep-form) . ,arg-bindings)
                        () ((,value ,value-form))
                        ((funcall ,continuep ,value))
                        ((,id ,value)) (,value-form))))))))
  (declare (side-effect-free t))
  (if (null args)
      (iter-make (let ((value (funcall producer)))
                   (cl-loop (iter-yield value)
                            (setq value (funcall producer)))))
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

(define-for-sequence for-in-range (start-or-end &optional end step)
  "Return an iterator that returns each number in range.

When both END and STEP is nil, START-OR-END is the end of range,
and the start of range is 0.  Otherwise, START-OR-END is the
start of range, and END is the end of range.  STEP defaults to 1
when it is nil or omitted.  Unlike `for-in-inclusive-range', the
range is right half-open when STEP is non-negative, or left
half-open when STEP is negative.

See Info node `(for)Sequence Constructors'.

\(fn START-OR-END [END [STEP]])"
  (:alias in-range) (:type integer)
  (:expander-case
   (`(,id ,(or (and (or (and `(,_ ,start-or-end-form)
                             (let end-form nil))
                        `(,_ ,start-or-end-form ,end-form))
                    (let step-form nil))
               `(,_ ,start-or-end-form ,end-form ,step-form)))
    (for--with-gensyms (start-or-end end step start continuep number)
      `(,id (:do-in ((,start-or-end ,start-or-end-form)
                     (,end ,end-form)
                     (,step (or ,step-form 1)))
                    ((,start (if ,end ,start-or-end 0))
                     (,end (if ,end ,end ,start-or-end))
                     (,continuep (if (< ,step 0) #'> #'<)))
                    ((,number ,start))
                    ((funcall ,continuep ,number ,end))
                    ((,id ,number)) ((+ ,number ,step)))))))
  (declare (side-effect-free t)))

(define-for-sequence for-in-iterator (iterator)
  "Return the function ITERATOR as is.

See Info node `(for)Sequence Constructors'."
  (:alias in-iterator) (:type function)
  (:expander-case
   (`(,id (,_ ,iterator-form))
    (for--iterator-for-clause `(,id ,iterator-form))))
  (declare (pure t) (side-effect-free t))
  (cl-the function iterator))

(defsubst for--make-circular (&rest values)
  "Make a circular list of VALUES."
  (declare (pure t) (side-effect-free error-free))
  (let ((last nil))
    (let ((tail values))
      (while tail (cl-shiftf last tail (cdr tail))))
    (setf (cdr last) values)))

(define-for-sequence for-in-repeat (value &rest values)
  "Return an iterator that repeatedly returns each VALUE.

See Info node `(for)Sequence Constructors'.

\(fn VALUE...)"
  (:alias in-repeat)
  (:expander-case
   (`(,id (,_ . ,(and `(,_ . ,_) value-forms)))
    (for--with-gensyms (values tail)
      `(,id (:do-in ((,values (for--make-circular . ,value-forms))) ()
                    ((,tail ,values)) () ((,id (car ,tail)))
                    ((cdr ,tail)))))))
  (declare (side-effect-free t))
  (iter-make (iter-yield value)
             (let ((last nil))
               (let ((values values))
                 (while values
                   (iter-yield (car values))
                   (cl-shiftf last values (cdr values))))
               (setf (cdr last) (push value values)))
             (cl-loop (iter-yield (pop values)))))

(define-for-sequence for-in-value (value)
  "Return an iterator that returns VALUE once.

See Info node `(for)Sequence Constructors'."
  (:alias in-value)
  (:expander-case
   (`(,id (,_ ,value-form))
    (for--with-gensyms (value)
      (let ((returned '#:returned))
        `(,id (:do-in ((,value ,value-form)) () ((,value ,value))
                      ((not (eq ,value ',returned)))
                      ((,id ,value)) (',returned)))))))
  (declare (side-effect-free t))
  (iter-make (iter-yield value)))

(define-for-sequence for-on-array (array)
  "Return an iterator that returns each index on ARRAY.

See Info node `(for)Sequence Constructors'."
  (:alias on-array)
  (:expander-case
   (`(,id (,_ ,array-form))
    (for--with-gensyms (array length index)
      `(,id (:do-in ((,array ,array-form)) ((,length (length ,array)))
                    ((,index 0)) ((< ,index ,length))
                    ((,id ,index)) ((1+ ,index)))))))
  (declare (side-effect-free t)))

(define-for-sequence for-on-list (list)
  "Return an iterator that returns each cons on LIST.

See Info node `(for)Sequence Constructors'."
  (:alias on-list)
  (:expander-case
   (`(,id (,_ ,list-form))
    (for--with-gensyms (list tail)
      `(,id (:do-in ((,list ,list-form)) () ((,tail ,list))
                    (,tail) ((,id ,tail)) ((cdr ,tail)))))))
  (declare (side-effect-free t)))

(define-for-sequence for-in-directory
    (directory &optional full match nosort count)
  "Return an iterator that returns each file in DIRECTORY.

Equivalent to (`for-in-list' (`directory-files' DIRECTORY FULL
MATCH NOSORT COUNT)), where FULL, NOSORT, and COUNT defaults to
nil when omitted, and MATCH defaults to
`directory-files-no-dot-files-regexp' when it is nil or omitted.

See Info node `(for)Sequence Constructors'.

\(fn DIRECTORY [FULL [MATCH [NOSORT [COUNT]]]])"
  (:alias in-directory)
  (:expander-case
   (`(,id ,(or (and (or (and (or (and (or (and `(,_ ,directory)
                                               (let full nil))
                                          `(,_ ,directory ,full))
                                      (let match nil))
                                 `(,_ ,directory ,full ,match))
                             (let nosort nil))
                        `(,_ ,directory ,full ,match ,nosort))
                    (let count nil))
               `(,_ ,directory ,full ,match ,nosort ,count)))
    `(,id (for-in-list
           (directory-files
            ,directory ,full
            (or ,match directory-files-no-dot-files-regexp)
            ,nosort ,count)))))
  (declare (side-effect-free t)))

(define-for-sequence for-in-directory-recursively
    (dir regexp
         &optional include-directories predicate follow-symlinks)
  "Return an iterator that returns each file under DIRECTORY.

Equivalent to (`for-in-list' (`directory-files-recursively' DIR
REGEXP INCLUDE-DIRECTORIES PREDICATE FOLLOW-SYMLINKS)) where
INCLUDE-DIRECTORIES, PREDICATE, and FOLLOW-SYMLINKS defaults to
nil when omitted.

See Info node `(for)Sequence Constructors'.

\(fn DIR REGEXP [INCLUDE-DIRECTORIES [PREDICATE [FOLLOW-SYMLINKS]]])"
  (:alias in-directory-recursively)
  (:expander-case
   (`(,id ,(or (and (or (and (or (and `(,_ ,dir ,regexp)
                                      (let include-directories nil))
                                 `(,_ ,dir ,regexp
                                      ,include-directories))
                             (let predicate nil))
                        `(,_ ,dir ,regexp
                             ,include-directories ,predicate))
                    (let follow-symlinks nil))
               `(,_ ,dir ,regexp
                    ,include-directories ,predicate
                    ,follow-symlinks)))
    `(,id (for-in-list
           (directory-files-recursively
            ,dir ,regexp
            ,include-directories ,predicate ,follow-symlinks)))))
  (declare (side-effect-free t)))

(define-for-sequence for-the-buffers (&optional frame)
  "Return an iterator that returns each buffer in FRAME.

Equivalent to (`for-in-list' (`buffer-list' FRAME)) where FRAME
defaults to nil when omitted.

See Info node `(for)Sequence Constructors'.

\(fn [FRAME])"
  (:alias the-buffers)
  (:expander-case
   (`(,id ,(or (and `(,_) (let frame nil)) `(,_ ,frame)))
    `(,id (for-in-list (buffer-list ,frame)))))
  (declare (side-effect-free t)))

(define-for-sequence for-the-frames ()
  "Return an iterator that returns each frame.

Not equivalent to (`for-in-list' (`frame-list')), since the
frames are visited from the selected frame in `next-frame'
order.

See Info node `(for)Sequence Constructors'."
  (:alias the-frames)
  (:expander-case
   (`(,id (,_))
    (for--with-gensyms (current original visited)
      `(,id (:do-in () ((,original (selected-frame)) (,visited nil))
                    ((,current ,original))
                    ((eq ,current ,original)
                     (if ,visited nil (setq ,visited t)))
                    ((,id ,current)) ((next-frame ,current)))))))
  (declare (side-effect-free t))
  (iter-make (let ((original (selected-frame)))
               (iter-yield original)
               (let ((current (next-frame original)))
                 (while (not (eq current original))
                   (iter-yield current)
                   (cl-callf next-frame current))))))

(define-for-sequence for-the-overlays (&optional buffer)
  "Return an iterator that returns each overlay in BUFFER.

Equivalent
to (`for-in-list' (`overlays-in' (`point-min') (`point-max')))
with BUFFER as the current buffer.  BUFFER defaults to the
current buffer when it is nil or omitted.

See Info node `(for)Sequence Constructors'.

\(fn [BUFFER])"
  (:alias the-overlays)
  (:expander-case
   (`(,id ,(or (and `(,_) (let buffer-form nil)) `(,_ ,buffer-form)))
    `(,id (for-in-list (if-let ((buffer ,buffer-form))
                           (with-current-buffer buffer
                             (overlays-in (point-min) (point-max)))
                         (overlays-in (point-min) (point-max)))))))
  (declare (side-effect-free t)))

(define-for-sequence for-the-windows (&optional frame minibuf)
  "Return an iterator that returns each window in FRAME.

Not equivalent to (`for-in-list' (`window-list')), since the
frames are visited from the selected window of FRAME in
`next-window' order.  FRAME defaults to the selected frame when
it is not a frame or omitted.  MINIBUF and FRAME are passed to
`next-window' as the MINIBUF and ALL-FRAMES arguments where
MINIBUF defaults to nil when it is omitted.

See Info node `(for)Sequence Constructors'.

\(fn [FRAME [MINIBUF]])"
  (:alias the-windows)
  (:expander-case
   (`(,id ,(or (and (or (and `(,_) (let frame-form nil))
                        `(,_ ,frame-form))
                    (let minibuf-form nil))
               `(,_ ,frame-form ,minibuf-form)))
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
  (declare (side-effect-free t))
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
