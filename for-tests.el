;;; for-tests.el --- Tests -*- lexical-binding: t; -*-

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
;; This file provides test suites.

;;; Code:
;;;; Require
(eval-when-compile
  (require 'for-helper)
  (require 'subr-x))
(require 'cl-lib)
(require 'ert)
(require 'for)
(require 'generator)

;;;; Internal
(eval-when-compile
  (defmacro for--make-test-list (&optional length item)
    "Make a list of LENGTH and ITEM suitable for test."
    (declare (debug (&optional form form)))
    `(cl-loop repeat (or ,length (+ 5 (random 5)))
              collect (or ,item (random 10))))
  (defmacro for--eval (form &optional dynamic)
    "Evaluate implicitly quasiquoted FORM under DYNAMIC binding."
    (declare (debug (backquote-form &optional form)))
    (if (macroexp-compiling-p)
        `(funcall (byte-compile
                   (eval (backquote #'(lambda () ,form))
                         (or ,dynamic 'lexical))))
      `(eval (backquote ,form) (or ,dynamic 'lexical))))
  (defmacro for--deftest-dyn (&rest body)
    "Define test for dynamic dispatch."
    (declare (debug (def-body)) (indent 0))
    `(progn
       (ert-deftest for-dynamic-dispatch ()
         "Dynamic dispatch."
         (cl-macrolet ((seq (seq value) `(for-list (,seq ,value))))
           . ,body))
       (ert-deftest for-generic-function ()
         "Generic function."
         (cl-macrolet
             ((seq (seq value)
                (pcase-let ((`(,id ,form) seq))
                  `(cl-loop for ,id iter-by (for-generator ,form)
                            collect ,value))))
           . ,body))))
  (defmacro for--deftest-seq (&rest body)
    "Define test for sequence constructor."
    (declare (debug (def-body)) (indent 0))
    (for--with-gensyms (with)
      `(cl-macrolet
           ((,with (expander &rest body)
              `(cl-macrolet
                   ((seq (&rest subforms)
                      (funcall ,expander subforms))
                    (seq* (&rest subforms)
                      (let ((form (funcall ,expander subforms)))
                        `(for--eval ,form))))
                 . ,body)))
         (ert-deftest for-sequence-expanders ()
           "Sequence expanders."
           (,with (lambda (subforms) `(for-list ,subforms)) . ,body))
         (ert-deftest for-sequence-generators ()
           "Sequence generators."
           (,with (lambda (subforms)
                    (cl-flet
                        ((make-clause (head seq)
                           (pcase-let*
                               (((or `(,id ,seq)
                                     (and `(,seq) (let id nil)))
                                 seq)
                                (`(,(app symbol-name
                                         (app (concat "for-")
                                              (app intern cons)))
                                   . ,forms)
                                 seq))
                             `(,head ,id iter-by (,cons . ,forms)))))
                      (pcase-let
                          ((`(,seq . ,(app reverse
                                           `(,value . ,(app nreverse
                                                            seqs))))
                            subforms))
                        `(cl-loop ,@(make-clause 'for seq)
                                  ,@(mapcan (lambda (seq)
                                              (make-clause 'and seq))
                                            seqs)
                                  collect ,value))))
                  . ,body))))))

;;;; Iteration
(ert-deftest for-plain-iteration-macros ()
  "Plain iteration macros."
  (let* ((list (for--make-test-list)) (result (mapcar #'1+ list)))
    (let ((init (random 10)))
      (should (equal (for-fold ((value init))
                         ((i (in-list list)) (cons (1+ i) value)))
                     (cl-reduce (lambda (car cdr) (cons cdr car))
                                result :initial-value init))))
    (should (string= (with-output-to-string
                       (for-do ((i (in-list list))
                                (:do (prin1 (1+ i))))))
                     (with-output-to-string (mapc #'prin1 result))))
    (should (equal (for-list ((i (in-list list)) (1+ i))) result))
    (should (equal (for-lists (list1 list2)
                       ((i (in-list list)) (:values (1+ i) (1- i))))
                   (cons result (mapcar #'1- list))))
    (let* ((tail-length (+ 5 (random 5)))
           (length (+ (length list) tail-length)))
      (let ((init-default 0) (init-test (random 10)))
        (should (equal (for-vector ((i (in-list list)) (1+ i)))
                       (vconcat result)))
        (should (equal (for-vector ((i (in-list list)) (1+ i))
                         :length length)
                       (vconcat result
                                (make-vector tail-length
                                             init-default))))
        (should (equal (for-vector ((i (in-list list)) (1+ i))
                         :length length :init init-test)
                       (vconcat result
                                (make-vector tail-length
                                             init-test))))
        (should (cl-every (lambda (vector) (eq vector []))
                          (list (for-vector ((i (in-list list)) i)
                                  :length 0)
                                (for-vector ((i (in-list list)) i)
                                  :length 0 :init init-test)))))
      (let ((init-default ?\0) (init-test (random 10)))
        (let ((string (for-string ((i (in-list list)) (1+ i)))))
          (should (string= string (concat result)))
          (should-not (multibyte-string-p string)))
        (let ((string (for-string ((i (in-list list)) (1+ i))
                        :length length)))
          (should (string= string
                           (concat result
                                   (make-string tail-length
                                                init-default))))
          (should-not (multibyte-string-p string)))
        (let ((string* (concat result
                               (make-string tail-length init-test))))
          (let ((string (for-string ((i (in-list list)) (1+ i))
                          :length length :init init-test)))
            (should (string= string string*))
            (should-not (multibyte-string-p string)))
          (let ((string (for-string ((i (in-list list)) (1+ i))
                          :length length :init init-test
                          :multibyte t)))
            (should (string= string string*))
            (should (multibyte-string-p string))))
        (should (cl-every (lambda (string) (eq string ""))
                          (list (for-string ((i (in-list list)) i)
                                  :length 0)
                                (for-string ((i (in-list list)) i)
                                  :length 0 :init init-test))))
        (should (eq (for-string ((i (in-list list)) i)
                      :length 0 :init init-test :multibyte t)
                    (make-string 0 ?\0 'multibyte)))))
    (should (eq (for-and ((i (in-list list)) (< i 5)))
                (cl-every (lambda (i) (< i 5)) list)))
    (should (eq (for-or ((i (in-list list)) (< i 5)))
                (cl-some (lambda (i) (< i 5)) list)))
    (should (eql (for-sum ((i (in-list list)) (1+ i)))
                 (cl-reduce #'+ result :initial-value (+))))
    (should (eql (for-product ((i (in-list list)) (1+ i)))
                 (cl-reduce #'* result :initial-value (*))))
    (should (eql (for-first ((i (in-list list)) (1+ i)))
                 (pcase-let ((`(,i . ,_) result)) i)))
    (should (eql (for-last ((i (in-list list)) (1+ i)))
                 (pcase-let ((`(,i) (last result))) i)))
    (should (eql (for-max ((i (in-list list)) (1+ i)))
                 (cl-reduce #'max result :initial-value -1.0e+INF)))
    (should (eql (for-min ((i (in-list list)) (1+ i)))
                 (cl-reduce #'min result :initial-value 1.0e+INF)))))

(ert-deftest for-implicitly-nesting-iteration-macros ()
  "Implicitly nesting iteration macros."
  (let* ((list1 (for--make-test-list)) (list2 (for--make-test-list))
         (zipped-list (mapcan (lambda (i)
                                (mapcar (lambda (j) `(,i . ,j))
                                        list2))
                              list1))
         (result (mapcar (pcase-lambda (`(,i . ,j)) (+ i j))
                         zipped-list)))
    (let ((init (random 10)))
      (should (eql (for-fold* ((value init))
                       (((in-list list1)) ((in-list list2))
                        (1+ value)))
                   (cl-reduce #'+ (mapcar (lambda (_) 1) zipped-list)
                              :initial-value init))))
    (should (string= (with-output-to-string
                       (for-do* ((i (in-list list1))
                                 (j (in-list list2))
                                 (:do (prin1 i) (terpri) (prin1 j)))))
                     (with-output-to-string
                       (mapc (pcase-lambda (`(,i . ,j))
                               (prin1 i) (terpri) (prin1 j))
                             zipped-list))))
    (should (equal (for-list* ((i (in-list list1)) (j (in-list list2))
                               (+ i j)))
                   result))
    (should (equal (for-lists* (list3 list4)
                       ((i (in-list list1)) (j (in-list list2))
                        (:values (+ i j) (- i j))))
                   (cons result
                         (mapcar (pcase-lambda (`(,i . ,j)) (- i j))
                                 zipped-list))))
    (let* ((tail-length (+ 5 (random 5)))
           (length (+ (* (length list1) (length list2)) tail-length)))
      (let ((init-default 0) (init-test (random 10)))
        (should (equal (for-vector* ((i (in-list list1))
                                     (j (in-list list2))
                                     (+ i j)))
                       (vconcat result)))
        (should (equal (for-vector* ((i (in-list list1))
                                     (j (in-list list2))
                                     (+ i j))
                         :length length)
                       (vconcat result
                                (make-vector tail-length
                                             init-default))))
        (should (equal (for-vector* ((i (in-list list1))
                                     (j (in-list list2))
                                     (+ i j))
                         :length length :init init-test)
                       (vconcat result
                                (make-vector tail-length
                                             init-test)))))
      (let ((init-default ?\0) (init-test (random 10)))
        (let ((string (for-string* ((i (in-list list1))
                                    (j (in-list list2))
                                    (+ i j)))))
          (should (string= string (concat result)))
          (should-not (multibyte-string-p string)))
        (let ((string (for-string* ((i (in-list list1))
                                    (j (in-list list2))
                                    (+ i j))
                        :length length)))
          (should (string= string
                           (concat result
                                   (make-string tail-length
                                                init-default))))
          (should-not (multibyte-string-p string)))
        (let ((string* (concat result
                               (make-string tail-length init-test))))
          (let ((string (for-string* ((i (in-list list1))
                                      (j (in-list list2))
                                      (+ i j))
                          :length length :init init-test)))
            (should (string= string string*))
            (should-not (multibyte-string-p string)))
          (let ((string (for-string* ((i (in-list list1))
                                      (j (in-list list2))
                                      (+ i j))
                          :length length :init init-test
                          :multibyte t)))
            (should (string= string string*))
            (should (multibyte-string-p string))))))
    (should (eq (for-and* ((i (in-list list1)) (j (in-list list2))
                           (< (+ i j) 10)))
                (cl-every (pcase-lambda (`(,i . ,j)) (< (+ i j) 10))
                          zipped-list)))
    (should (eq (for-or* ((i (in-list list1)) (j (in-list list2))
                          (< (+ i j) 10)))
                (cl-some (pcase-lambda (`(,i . ,j)) (< (+ i j) 10))
                         zipped-list)))
    (should (eql (for-sum* ((i (in-list list1))
                            (j (in-list list2))
                            (+ i j)))
                 (cl-reduce #'+ result :initial-value (+))))
    (should (eql (for-product* ((i (in-list list1))
                                (j (in-list list2))
                                (+ i j)))
                 (cl-reduce #'* result :initial-value (*))))
    (let ((n (+ 2 (random 2))))
      (should (equal (for-first* ((i (in-naturals n))
                                  (j (in-value i))
                                  (k (in-value j))
                                  (list i j k)))
                     (list n n n)))
      (should (equal (for-last* ((i (in-range n))
                                 (j (in-list list1))
                                 (k (in-list list2))
                                 (list i j k)))
                     (pcase-let ((`(,j) (last list1))
                                 (`(,k) (last list2)))
                       (list (1- n) j k)))))
    (should (eql (for-max* ((i (in-list list1)) (j (in-list list2))
                            (+ i j)))
                 (cl-reduce #'max result :initial-value -1.0e+INF)))
    (should (eql (for-min* ((i (in-list list1)) (j (in-list list2))
                            (+ i j)))
                 (cl-reduce #'min result :initial-value 1.0e+INF)))))

(ert-deftest for-multiple-value-forms ()
  "Multiple-value forms."
  (let ((list (for--make-test-list)))
    (let ((init1 (append)) (init2 (+)) (init3 (*)))
      (should (equal (for-fold ((value1 init1)
                                (value2 init2)
                                (value3 init3))
                         ((i (in-list list))
                          (cond ((cl-oddp i)
                                 (let ((i i))
                                   (progn
                                     nil
                                     (save-current-buffer
                                       nil
                                       (:values (cons i value1)
                                                (+ i value2)
                                                (* i value3))))))
                                ((cl-evenp i)
                                 (let* ((i i))
                                   (save-excursion
                                     nil
                                     (save-restriction
                                       nil
                                       (:values (cons i value1)
                                                (+ i value2)
                                                (* i value3))))))
                                (t (if i (:values i i i)
                                     (:values init1 init2 init3))))))
                     (list (cl-reduce (lambda (cdr car)
                                        (cons car cdr))
                                      list :initial-value init1)
                           (cl-reduce #'+ list
                                      :initial-value init2)
                           (cl-reduce #'* list
                                      :initial-value init3)))))
    (should (eql (for-fold ((value nil))
                     ((i (in-list list))
                      (if (cl-oddp i) (1+ i) (:values i))))
                 (pcase-let ((`(,i) (last list)))
                   (if (cl-oddp i) (1+ i) i))))
    (should-error (for-fold ((value1 nil) (value2 nil) (value3 nil))
                      ((i (in-list list))
                       (pcase (1+ i)
                         ((and (cl-type integer) j)
                          (:values i j (1- i)))
                         (_ (:values nil nil))))))))

(ert-deftest for-named-let-semantics ()
  "Named `let' semantics."
  (let ((list (for--make-test-list)))
    (let ((item (random 10)))
      (should (equal (for-list
                         ((i (in-list list))
                          (progn (ignore i) (let ((i item)) i))))
                     (mapcar (lambda (_) item) list)))
      (should (eql (for-fold ((value nil))
                       (((in-list list))
                        (let ((value item)) value)))
                   item)))
    (should (equal (for-fold ((value1 nil) (value2 nil) (value3 nil))
                       ((i (in-list list)) (:values i value1 value2)))
                   (pcase-let ((`(,value1 ,value2 ,value3)
                                (reverse list)))
                     (list value1 value2 value3))))))

(ert-deftest for-result-clauses ()
  "Result clauses."
  (let ((list (for--make-test-list)))
    (let ((init (+)))
      (should (eql (for-fold ((value init) (:result (1- value)))
                       ((i (in-list list)) (+ i value)))
                   (1- (cl-reduce #'+ list :initial-value init)))))
    (should (equal (for-lists
                       (list1 list2 (:result (nconc list1 list2)))
                       ((i (in-list list)) (:values (1- i) (1+ i))))
                   (nconc (mapcar #'1- list) (mapcar #'1+ list))))
    (should (string= (with-output-to-string
                       (for-lists (list1
                                   list2
                                   (:result (prin1 list1) (terpri)
                                            (prin1 list2)))
                           ((i (in-list list))
                            (:values (1- i) (1+ i)))))
                     (with-output-to-string
                       (prin1 (mapcar #'1- list)) (terpri)
                       (prin1 (mapcar #'1+ list)))))))

(ert-deftest for-special-clauses ()
  "Special clauses."
  (let ((list (for--make-test-list nil (- (random 10) 5))))
    (should (equal (for-list ((i (in-list list))
                              (:if (cl-evenp i))
                              (:if-not (cl-plusp i))
                              (1+ i)))
                   (thread-last list
                                (cl-remove-if-not #'cl-evenp)
                                (cl-remove-if #'cl-plusp)
                                (mapcar #'1+))))
    (let ((list (mapcar (lambda (i) `(,(1- i) . ,(1+ i))) list)))
      (should (equal (for-list
                         ((i (in-list list))
                          (:let (`(,j . ,k) i))
                          (:if-let (l (and (cl-evenp j) (1+ j))))
                          (list j k l)))
                     (thread-last
                       list
                       (mapcar (pcase-lambda (`(,j . ,k))
                                 (and-let* (((cl-evenp j)) (l (1+ j))
                                            ((list j k l))))))
                       (delq nil)))))
    (let ((list (apply #'for--make-circular list))
          (length (- (length list) (+ 2 (random 2)))))
      (should (string= (with-output-to-string
                         (for-do ((i (in-list list)) (j (in-naturals))
                                  (:break (= j length))
                                  (:do (prin1 i) (terpri)))))
                       (with-output-to-string
                         (cl-loop for i in list repeat length
                                  do (prin1 i) (terpri))))))
    (should (equal (for-last (((and `(,_ . ,rest) i) (on-list list))
                              (:final (null rest)) i))
                   (last list))))
  (let ((tree '((1) ((a)) "b")))
    (should (equal (for-list
                       ((i (in-list tree))
                        (:pcase i (or `(,(cl-type integer))
                                      (cl-type string)))
                        i))
                   (thread-last
                     tree
                     (mapcar (lambda (i)
                               (pcase i
                                 ((or `(,(cl-type integer))
                                      (cl-type string))
                                  i)
                                 (_ nil))))
                     (delq nil))))
    (should (equal (for-list ((i (in-list tree))
                              (:pcase-not i :as j `(,_)) j))
                   (thread-last
                     tree
                     (mapcar (lambda (i) (pcase i (`(,_) nil) (j j))))
                     (delq nil))))
    (should-error (for-do ((i (in-list tree))
                           (:pcase i :exhaustive `(,_)))))))

;;;; Sequence
(for--deftest-dyn
  (let* ((list (for--make-test-list))
         (result (mapcar #'1+ list)))
    (should (equal (seq (i list) (1+ i)) result))
    (should (equal (seq (i (iter-make (let ((tail list))
                                        (while tail
                                          (iter-yield (pop tail))))))
                        (1+ i))
                   result))
    (should (equal (seq (i (apply #'vector list)) (1+ i)) result))
    (should (equal (seq (i (apply #'string list)) (1+ i)) result)))
  (let ((end (+ 5 (random 5))))
    (should (equal (seq (i end) (1+ i)) (number-sequence 1 end))))
  (should-error (seq (i (record '#:some-type)) i)
                :type 'for-unhandled-type))

(ert-deftest for-literal-sequences ()
  "Literal sequences."
  (let ((list (for--make-test-list)))
    (let ((result (mapcar #'1+ list)))
      (should (equal (for--eval (for-list ((i ',list) (1+ i))))
                     result))
      (should (equal (for--eval (for-list ((i [,@list]) (1+ i))))
                     result)))
    (pcase-let ((`(,end . ,_) list))
      (should (eql (for--eval (for-sum ((i ,end) (1+ i))))
                   (cl-loop for i below end sum (1+ i)))))))

(for--deftest-seq
  (let ((list (for--make-test-list)))
    (let ((result (mapcar #'1+ list)))
      (should (equal (seq (i (in-array (vconcat list))) (1+ i))
                     result))
      (should (equal (seq (i (in-array (concat list))) (1+ i))
                     result))
      (should (equal (seq (i (in-list list)) (1+ i)) result)))
    (should (equal (seq (i (on-list list)) i)
                   (cl-maplist #'identity list)))
    (let ((length (length list)))
      (should (equal (seq (i (on-array (vconcat list))) i)
                     (cl-loop for i below length collect i)))
      (should (equal (seq (i (on-array (concat list))) i)
                     (cl-loop for i below length collect i))))
    (let ((int (random 10)))
      (should (equal (seq (i (in-naturals int)) ((in-range 10))
                          (1+ i))
                     (cl-loop for i from int repeat 10
                              collect (1+ i))))
      (should-error (seq (i (in-naturals (float int))) i)
                    :type 'wrong-type-argument))
    (pcase-let*
        ((`(,(and (app (+ 5 (random 5)) end) start) . ,_) list)
         (step (+ (/ (random 15) 10.0) 0.5)) (step* (- step)))
      (should (equal (seq (i (in-inclusive-range start end))
                          (1+ i))
                     (cl-loop for i from start to end
                              collect (1+ i))))
      (should (equal (seq (i (in-inclusive-range end start step*))
                          (1+ i))
                     (cl-loop for i from end downto start by step
                              collect (1+ i))))
      (should (equal (seq (i (in-range end)) (1+ i))
                     (cl-loop for i below end collect (1+ i))))
      (should (equal (seq (i (in-range start end)) (1+ i))
                     (cl-loop for i from start below end
                              collect (1+ i))))
      (should (equal (seq (i (in-range end start step*)) (1+ i))
                     (cl-loop for i from end above start by step
                              collect (1+ i)))))
    (let ((length (+ 10 (random 5))))
      (should (equal (seq* (i (in-repeat . ,list))
                           ((in-range ,length))
                           i)
                     (cl-flet ((cdr* (xs)
                                 (pcase (cdr xs) ('() list) (xs xs))))
                       (cl-loop for i in list by #'cdr*
                                repeat length collect i))))
      (pcase-let ((`(,value . ,_) list))
        (should (equal (seq (i (in-repeat value)) ((in-range length))
                            i)
                       (make-list length value)))))
    (let ((value (random 10)))
      (should (equal (seq (i (in-value value)) (j (in-list list))
                          (cons i j))
                     (cl-loop for i in (list value) for j in list
                              collect (cons i j))))))
  (let ((dir "."))
    (let ((regexp directory-files-no-dot-files-regexp))
      (should (equal (seq (i (in-directory dir)) i)
                     (directory-files dir nil regexp)))
      (should (equal (seq (i (in-directory dir 'full)) i)
                     (directory-files dir 'full regexp))))
    (let ((regexp (rx ".el" eos)))
      (should (equal (seq (i (in-directory dir 'full regexp)) i)
                     (directory-files dir 'full regexp)))
      (should (equal (seq (i (in-directory dir 'full regexp 'nosort))
                          i)
                     (directory-files dir 'full regexp 'nosort)))
      (let ((count (random 5)))
        (should (equal (seq (i (in-directory
                                dir 'full regexp 'nosort count))
                            i)
                       (directory-files
                        dir 'full regexp 'nosort count))))))
  (let ((dir ".") (regexp (rx bos (not "."))))
    (should (equal (seq (i (in-directory-recursively dir regexp)) i)
                   (directory-files-recursively dir regexp)))
    (should (equal (seq (i (in-directory-recursively
                            dir regexp 'include-directories))
                        i)
                   (directory-files-recursively
                    dir regexp 'include-directories)))
    (should (equal (seq (i (in-directory-recursively
                            dir regexp 'include-directories t))
                        i)
                   (directory-files-recursively
                    dir regexp 'include-directories t)))
    (should (equal (seq (i (in-directory-recursively
                            dir regexp
                            'include-directories t 'follow-symlinks))
                        i)
                   (directory-files-recursively
                    dir regexp
                    'include-directories t 'follow-symlinks))))
  (cl-symbol-macrolet
      ((producer (let ((n 0))
                   (lambda (&optional m)
                     (and (< n 10) (+ (cl-incf n) (or m 0)))))))
    (should (equal (seq (i (in-producer producer)) ((in-range 10))
                        (1+ i))
                   (cl-loop with producer = producer repeat 10
                            collect (1+ (funcall producer)))))
    (should (equal (seq (i (in-producer producer #'identity)) (1+ i))
                   (cl-loop with producer = producer
                            for i = (funcall producer)
                            if i collect (1+ i) into list
                            else return list)))
    (should (equal (seq (i (in-producer producer #'identity 5))
                        (1+ i))
                   (cl-loop with producer = producer
                            for i = (funcall producer 5)
                            if i collect (1+ i) into list
                            else return list))))
  (cl-symbol-macrolet
      ((iter (iter-make (dotimes (n 10) (iter-yield n)))))
    (should (equal (seq (i (in-iterator iter)) (1+ i))
                   (cl-loop for i iter-by iter collect (1+ i)))))
  (should-error (seq (i (in-iterator '#:not-a-function)) i)
                :type '(void-function wrong-type-argument))
  (should (equal (seq (i (the-buffers)) i) (buffer-list)))
  (should (null (cl-nset-difference (seq (i (the-frames)) i)
                                    (frame-list))))
  (should (null (cl-nset-difference (seq (i (the-windows)) i)
                                    (window-list))))
  (let ((frame (selected-frame)))
    (should (equal (seq (i (the-buffers frame)) i)
                   (buffer-list frame)))
    (should (null (cl-nset-difference (seq (i (the-windows frame)) i)
                                      (window-list frame))))
    (should (null (cl-nset-difference (seq (i (the-windows frame t))
                                           i)
                                      (window-list frame t)))))
  (should (equal (seq (i (the-overlays)) i)
                 (overlays-in (point-min) (point-max))))
  (let ((buffer (current-buffer)))
    (should (equal (seq (i (the-overlays buffer)) i)
                   (with-current-buffer buffer
                     (overlays-in (point-min) (point-max)))))))
;;; for-tests.el ends here
