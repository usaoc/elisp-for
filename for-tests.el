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
(eval-when-compile (require 'subr-x))
(require 'ert)
(require 'for)

;;;; Internal
(defun for--make-test-list ()
  "Make a list suitable for test."
  (declare (side-effect-free error-free))
  (cl-loop repeat (+ 5 (random 5)) collect (random 10)))

(eval-when-compile
  (defmacro for--eval (form &optional dynamic)
    "Evaluate implicitly quasiquoted FORM under DYNAMIC binding."
    (declare (debug (backquote-form)))
    (if (macroexp-compiling-p)
        `(funcall (byte-compile
                   (eval ,(macroexpand (list '\` `#'(lambda () ,form))
                                       macroexpand-all-environment)
                         (or ,dynamic 'lexical))))
      `(eval ,(macroexpand (list '\` form)
                           macroexpand-all-environment)
             (or ,dynamic 'lexical))))
  (defmacro for--deftest-seq (&rest body)
    "Define test for sequence constructor."
    (declare (debug body) (indent 0))
    `(cl-macrolet
         ((seq* (&rest subforms)
            `(for--eval ,(macroexpand `(seq . ,subforms)
                                      macroexpand-all-environment))))
       (ert-deftest for-sequence-expanders ()
         "Sequence expanders."
         (cl-macrolet ((seq (&rest subforms) `(for-list ,subforms)))
           . ,body))
       (ert-deftest for-sequence-generators ()
         "Sequence generators."
         (cl-macrolet
             ((seq (&rest subforms)
                (pcase-let ((`(,value . ,(app nreverse seqs))
                             (reverse subforms)))
                  `(cl-loop
                    ,@(mapcan
                       (lambda (seq)
                         (pcase-let*
                             (((or `(,id ,seq)
                                   (and `(,seq) (let id nil)))
                               seq)
                              (`(,(app symbol-name
                                       (app (concat "for-")
                                            (app intern head)))
                                 . ,subforms)
                               seq))
                           `(for ,id iter-by (,head . ,subforms))))
                       seqs)
                    collect ,value))))
           . ,body)))))

;;;; Iteration
(ert-deftest for-iteration-macros ()
  "Iteration macros."
  (let* ((list (for--make-test-list))
         (list-length (length list)))
    (let ((init (random 10)))
      (should (eql (for-fold ((value init))
                       ((i (in-list list)) (+ value i)))
                   (cl-reduce #'+ list :initial-value init))))
    (should (equal (for-list ((i (in-list list)) (1+ i)))
                   (mapcar #'1+ list)))
    (let* ((tail-length (+ 5 (random 5)))
           (length (+ list-length tail-length)))
      (let ((init-default nil) (init-test (random 10)))
        (should (equal (for-vector ((i (in-list list)) (1+ i)))
                       (cl-map 'vector #'1+ list)))
        (should (equal (for-vector ((i (in-list list)) (1+ i))
                         :length length)
                       (vconcat
                        (cl-map 'vector #'1+ list)
                        (make-vector tail-length init-default))))
        (should (equal (for-vector ((i (in-list list)) (1+ i))
                         :length length :init init-test)
                       (vconcat
                        (cl-map 'vector #'1+ list)
                        (make-vector tail-length init-test)))))
      (let ((init-default ?\0) (init-test (random 10)))
        (should (string= (for-string ((i (in-list list)) (1+ i)))
                         (cl-map 'string #'1+ list)))
        (should (string= (for-string ((i (in-list list)) (1+ i))
                           :length length)
                         (concat
                          (cl-map 'string #'1+ list)
                          (make-string tail-length init-default))))
        (let ((string (for-string ((i (in-list list)) (1+ i))
                        :length length :init init-test)))
          (should (string= string
                           (concat
                            (cl-map 'string #'1+ list)
                            (make-string tail-length init-test))))
          (should-not (multibyte-string-p string)))
        (should (multibyte-string-p
                 (for-string ((i (in-list list)) (1+ i))
                   :length length :init init-test
                   :multibyte t)))))
    (should (eq (for-and ((i (in-list list)) (< i 5)))
                (cl-every (lambda (i) (< i 5)) list)))
    (should (eq (for-or ((i (in-list list)) (< i 5)))
                (cl-some (lambda (i) (< i 5)) list)))
    (should (eql (for-sum ((i (in-list list)) (1+ i)))
                 (cl-reduce (lambda (sum i) (+ (1+ i) sum))
                            list :initial-value (+))))
    (should (eql (for-product ((i (in-list list)) (1+ i)))
                 (cl-reduce (lambda (product i) (* (1+ i) product))
                            list :initial-value (*))))
    (should (eql (for-first ((i (in-list list)) (1+ i)))
                 (1+ (cl-first list))))
    (should (eql (for-last ((i (in-list list)) (1+ i)))
                 (1+ (cl-first (last list)))))
    (should (eql (for-max ((i (in-list list)) (1+ i)))
                 (cl-reduce (lambda (max i) (max (1+ i) max))
                            list :initial-value -1.0e+INF)))
    (should (eql (for-min ((i (in-list list)) (1+ i)))
                 (cl-reduce (lambda (min i) (min (1+ i) min))
                            list :initial-value 1.0e+INF)))))

(ert-deftest for-multiple-values ()
  "Multiple-value forms."
  (let ((list (for--make-test-list)))
    (should (string= (with-output-to-string
                       (for-do ((i (in-list list)) (:do (prin1 i)))))
                     (with-output-to-string (mapc #'prin1 list))))
    (let ((init1 (append)) (init2 (+)) (init3 (*)))
      (should (equal (for-lists (list1 list2)
                         ((i (in-list list)) (:values (1+ i) (1- i))))
                     (cons (mapcar #'1+ list) (mapcar #'1- list))))
      (should (equal (for-fold ((value1 init1)
                                (value2 init2)
                                (value3 init3))
                         ((i (in-list list))
                          (:values (cons i value1)
                                   (+ i value2)
                                   (* i value3))))
                     (list (cl-reduce (lambda (cdr car)
                                        (cons car cdr))
                                      list :initial-value init1)
                           (cl-reduce #'+ list
                                      :initial-value init2)
                           (cl-reduce #'* list
                                      :initial-value init3)))))
    (should-error (for-fold ((value1 nil) (value2 nil) (value3 nil))
                      ((i (in-list list))
                       (pcase (1+ i)
                         ((and (cl-type integer) j)
                          (save-excursion (:values i j (1- i))))
                         (_ (:values nil nil))))))))

(ert-deftest for-named-let-semantics ()
  "Named `let' semantics."
  (let ((list (for--make-test-list)))
    (let ((item (random 10)) (length (length list)))
      (should (equal (for-list
                         ((i list)
                          (progn (ignore i) (let ((i item)) i))))
                     (cl-loop repeat length collect item))))
    (should (equal (for-fold ((value1 nil) (value2 nil) (value3 nil))
                       ((i list) (:values i value1 value2)))
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
                   (nconc (mapcar #'1- list) (mapcar #'1+ list))))))

(ert-deftest for-special-clauses ()
  "Special clauses."
  (let ((list (for--make-test-list)))
    (should (equal (for-list ((i (in-list list))
                              (:if (< i 2)) (:if-not (> i 8)) (1+ i)))
                   (thread-last
                     list
                     (cl-remove-if-not (lambda (i) (< i 2)))
                     (cl-remove-if (lambda (i) (> i 8)))
                     (mapcar #'1+))))
    (let ((list (mapcar (lambda (i) `(,(1- i) . ,(1+ i))) list)))
      (should (equal (for-list
                         ((i (in-list list))
                          (:let (`(,j . ,k) i))
                          (:if-let (l (and (> j 2) (1+ j))))
                          (list j k l)))
                     (thread-last
                       list
                       (mapcar (pcase-lambda (`(,j . ,k))
                                 (and-let* ((l (and (> j 2) (1+ j)))
                                            ((list j k l))))))
                       (delq nil)))))
    (let ((list (apply #'for--make-circular list)))
      (should (string= (with-output-to-string
                         (for-do ((i (in-list list)) (j (in-naturals))
                                  (:break (not (< j 5)))
                                  (:do (prin1 i) (terpri)))))
                       (with-output-to-string
                         (cl-loop for i in list repeat 5
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

(ert-deftest for-nesting-sequences ()
  "Nesting sequences."
  (let* ((start (random 5)) (end (+ start 5 (random 5))))
    (let ((tail-length (+ 5 (random 5))) (init (random 5)))
      (should (equal (for-vector* ((i (in-inclusive-range start end))
                                   (j (in-inclusive-range start i))
                                   (+ i j))
                       :length (let ((end (1+ (- end start))))
                                 (+ (/ (* end (1+ end)) 2)
                                    tail-length))
                       :init init)
                     (vconcat
                      (cl-loop for i from start to end
                               vconcat (cl-loop for j from start to i
                                                collect (+ i j)))
                      (make-vector tail-length init)))))
    (should (eql (for-sum ((i (in-inclusive-range start end))
                           (:if-not (< i 5))
                           (j (in-inclusive-range start i))
                           (+ i j)))
                 (cl-loop for i from start to end if (not (< i 5))
                          sum (cl-loop for j from start to i
                                       sum (+ i j)))))))

(ert-deftest for-buffer-local-variables ()
  "Buffer-local variables."
  (let ((for-binder 'cl-symbol-macrolet)
        (list (for--make-test-list)) (item (random 10)))
    (should (cl-every (lambda (i) (eql i item))
                      (for--eval (let ((list (list . ,list)))
                                   (for-do ((i (in-list list))
                                            (:do (setf i ,item))))
                                   list))))
    (should (cl-every (lambda (i) (eql i item))
                      (for--eval (let ((vector (vector . ,list)))
                                   (for-do ((i (in-array vector))
                                            (:do (setf i ,item))))
                                   vector))))))

;;;; Sequence
(ert-deftest for-dynamic-dispatch ()
  "Dynamic dispatch."
  (let* ((list (for--make-test-list))
         (result (mapcar #'1+ list)))
    (should (equal (for-list ((i list) (1+ i))) result))
    (should (equal (for-list
                       ((i (let ((tail list))
                             (iter-make (while tail
                                          (iter-yield (pop tail))))))
                        (1+ i)))
                   result))
    (let ((vector (vconcat list)))
      (should (equal (for-list ((i vector) (1+ i))) result)))
    (let ((string (concat list)))
      (should (equal (for-list ((i string) (1+ i))) result))))
  (let ((end (+ 5 (random 5))))
    (should (equal (for-list ((i end) (1+ i)))
                   (cl-loop for i below end collect (1+ i)))))
  (let ((some-object (make-record 'some-type 0 nil)))
    (should-error (for-list ((item some-object) item))
                  :type 'for-unhandled-type)))

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
    (should (equal (seq* (i (in-repeat . ,list)) ((in-range 10)) i)
                   (cl-loop for i in (apply #'for--make-circular list)
                            repeat 10 collect i)))
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
