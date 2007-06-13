;;; creol-mode.el -- Emacs mode for the programming language Creol

;; Copyright (C) 2007 Marcel Kyas <kyas@ifi.uio.no>

;; This program is free software; you can redistribute it and/or
;; modify it under the terms of the GNU General Public License as
;; published by the Free Software Foundation; either version 2 of
;; the License, or (at your option) any later version.

;; This program is distributed in the hope that it will be
;; useful, but WITHOUT ANY WARRANTY; without even the implied
;; warranty of MERCHANTABILITY or FITNESS FOR A PARTICULAR
;; PURPOSE.  See the GNU General Public License for more details.

;; You should have received a copy of the GNU General Public
;; License along with this program; if not, write to the Free
;; Software Foundation, Inc., 59 Temple Place, Suite 330, Boston,
;; MA 02111-1307 USA

(eval-when-compile
  (require 'regexp-opt))

(require 'custom)

(defgroup creol-mode nil
  "Support for the Creol language."
  :group 'languages)

(defcustom creol-command
  "creolc.opt"
  "Command used to invoke Creol."
  :type '(string)
  :group 'creol-mode)

(defvar creol-mode-hook nil)

;; Font-lock for Creol.
;;
(defconst creol-keywords
  (eval-when-compile
    (regexp-opt
     '("assert" "await" "begin" "by" "case" "class" "contracts"
       "ctor" "datatype" "do" "else" "end" "ensures" "exception"
       "exists" "extern" "forall" "for" "fun" "if" "implements"
       "inherits" "interface" "inv" "in" "new" "not" "of" "op"
       "out" "skip" "some" "then" "to" "try" "var" "when" "while"
       "with") 'words))
  "List of creol keywords.")

(defconst creol-constants
  (eval-when-compile
    (regexp-opt
     '("true" "false" "null" "nil" "caller" "this" "history")
     'words))
  "List of creol special words")

(defconst creol-builtins
  (eval-when-compile
    (regexp-opt
     '("fst" "snd" "head" "tail")
     'words))
  "List of creol builtin functions")

(defvar creol-font-lock-keywords
    (list
     (cons "\\(//.*\\)\n" 'font-lock-comment-face)
     (cons creol-keywords 'font-lock-keyword-face)
     (cons creol-constants 'font-lock-constant-face)
     (cons creol-builtins 'font-lock-builtin-face)
     (list "op \\(\\sw+\\)" 1 'font-lock-function-name-face)
     (list "\\(\\sw+\\)[[:space:]]*(" 1 'font-lock-function-name-face)
     (cons "\\(\\b[[:lower:]][[:alnum:]]*\\)" 'font-lock-variable-name-face)
     (cons "\\(\\b[[:upper:]][[:alpha:]]*\\)" 'font-lock-type-face)
     (list "\\<\\(# \w+\\)\\>" 1 'font-lock-warning-face t))
    "Creol keywords")

;; Compiling the current buffer.
;;
(require 'compile)

;; Put the regular expression for finding error messages here.
;;
(defconst creol-error-regexp
  "^[^\0-@]+ \"\\(^\"\n]+\\)\", [^\0-@]+ \\([0-9]+\\)[-,:]"
  "Regular expression matching the error messages produced by creolc.")

(if (boundp 'compilation-error-regexp-alist)
    (or (assoc creol-error-regexp compilation-error-regexp-alist)
        (setq compilation-error-regexp-alist
              (cons (list creol-error-regexp 1 2)
		    compilation-error-regexp-alist))))

;; Creol mode keymap.
;;
(defvar creol-mode-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-c\C-c" 'compile)
    map)
  "Keymap for Creol major mode")

;; Putting it all together.
;;
(define-derived-mode creol-mode fundamental-mode "Creol"
  "Major mode for editing Creol files"
  ;; :syntax-table creol-mode-syntax-table
  (set (make-local-variable 'comment-start) "/*")
  (set (make-local-variable 'comment-start-skip) "//+\\s-*")
  (set (make-local-variable 'comment-end) "*/")
  (use-local-map creol-mode-map)
  (set (make-local-variable 'font-lock-defaults) '(creol-font-lock-keywords))
  ;; (set (make-local-variable 'indent-line-function) 'creol-indent-line)
)

(add-to-list 'auto-mode-alist '("\\.creol\\'" . creol-mode))

(provide 'creol-mode)
