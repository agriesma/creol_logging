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


(defvar creol-mode-map
  (let ((map (make-sparse-keymap)))
    nil
    map)
  "Keymap for Creol major mode")

(defvar creol-mode-hook nil)

(defvar creol-font-lock-keywords
  '(("\\(//\\[^\n\\]*\\)\n" . font-lock-comment-face)
    ("\\<\\(and\\|begin\\|class\\|contracts\\|new\\|else\\|end\\|fi\\|if\\|implements\\|inherits\\|interface\\|in\\|not\\|op\\|or\\|out\\|skip\\|then\\|var\\|wait\\|with\\)\\>" . font-lock-keyword-face)
    ("\\<\\(true\\|false\\|null\\|nil\\)\\>" . font-lock-constant-face)
    ("\\<\\(fst\\|scd\\|head\\|tail\\|length\\)\\>" . font-lock-builtin-face)
    ("op \\(\\sw+\\)" (1 font-lock-function-name-face))
    ("\\.\\(\\sw+\\)" (1 font-lock-function-name-face))
    ("\\(\\b[[:lower:]][[:alnum:]]+\\)" . font-lock-variable-name-face)
    ("\\(\\b[[:upper:]][[:alnum:]]+\\)" . font-lock-type-face)
    ("\\<\\(# \w+\\)\\>" 1 font-lock-warning-face t)
    )
  "Creol keywords")

(define-derived-mode creol-mode fundamental-mode "Creol"
  "Major mode for editing Creol files"
  :syntax-table creol-mode-syntax-table
  (set (make-local-variable 'comment-start) "//")
  (set (make-local-variable 'comment-start-skip) "//+\\s-*")
  (use-local-map creol-mode-map)
  (set (make-local-variable 'font-lock-defaults) '(creol-font-lock-keywords))
  ;; (set (make-local-variable 'indent-line-function) 'creol-indent-line)
)

(add-to-list 'auto-mode-alist '("\\.creol\\'" . creol-mode))

(provide 'creol-mode)
