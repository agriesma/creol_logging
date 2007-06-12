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

(defvar creol-mode-map
  (let ((map (make-sparse-keymap)))
    nil
    map)
  "Keymap for Creol major mode")

(defvar creol-mode-hook nil)

(defconst creol-keywords
  (eval-when-compile
    (regexp-opt
     '("assert" "await" "begin" "by" "case" "class" "contracts"
       "ctor" "datatype" "do" "else" "end" "ensures" "exception"
       "exists" "extern" "forall" "for" "fun" "if" "implements"
       "inherits" "interface" "inv" "in" "new" "not" "of" "op"
       "out" "skip" "some" "then" "to" "try" "var" "when"
       "with") 'words))
  "List of creol keywords.")

(defconst creol-constants
  (eval-when-compile
    (regexp-opt
     '("true" "false" "null" "nil" "caller" "this" "history")
     'words))
  "List of creol special words")

(defvar creol-font-lock-keywords
    '(("\\(//.*\\)\n" . font-lock-comment-face)
      (list creol-keywords 0 font-lock-keyword-face)
      (list creol-constants 0 font-lock-constant-face)
      ("\\<\\(fst\\|scd\\|head\\|tail\\|length\\)\\>" . font-lock-builtin-face)
      ("op \\(\\sw+\\)" (1 font-lock-function-name-face))
      ("\\.\\(\\sw+\\)" (1 font-lock-function-name-face))
      ("\\(\\b[[:lower:]][[:alnum:]]*\\)" . font-lock-variable-name-face)
      ("\\(\\b[[:upper:]][[:alpha:]]*\\)" . font-lock-type-face)
      ("\\<\\(# \w+\\)\\>" 1 font-lock-warning-face t))
    "Creol keywords")

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
