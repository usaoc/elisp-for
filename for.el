;;; for.el --- Iteration and sequence -*- lexical-binding: t; -*-

;; Copyright (C) 2022 Wing Hei Chan

;; Author: Wing Hei Chan <whmunkchan@outlook.com>
;; URL: https://github.com/usaoc/elisp-for
;; Keywords: extensions
;; Package-Requires: ((emacs "28.1"))
;; Version: 0.2

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
;; This package provides iteration and sequence forms inspired by
;; Racket.  Two major facilities are provided:

;; 1. Generic iteration forms equivalent to `named-let' forms;

;; 2. Generic sequence constructors that are both expanders and
;; generators.

;;; Code:
;;;; Require
(require 'for-iteration)
(require 'for-sequence)

;;;; Provide
(provide 'for)
;;; for.el ends here
