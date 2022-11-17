;;; package --- Summary

;;; Commentary:

;; Derived from typos.el and others.

;;; Code:

;; define several class of keywords

(defvar ola-keywords '("func"
                       "main"
                       "match"
                       "local"
                       "var"
                       "let"
                       "type"
                       "role"
                       "session"
                       "protocol"
                       "when"
                       "if"
                       "else"
                       "call"
                       "rec"
                       "end"
                       "struct"
                       "union"
                       "tuple"))

(defvar ola-types '("Int" "Bool" "String" "Char" "Unit" "FILE" "PROC" "Role"))

(defvar ola-operators '("?" "!" "+" "|" "&" "."))

(defvar ola-symbols   '(":" "->" "==>" "="
                        "[" "]"
                        "<" ">"
                        "{" "}"
                        "(" ")"))

(defvar ola-functions '("and" "not" "or"
                        "lt" "lte" "eq" "gt" "gte"
                        "add" "sub" "mul" "div"
                        "size" "strCons" "slice"
                        "ord" "chr" "string" "toString"
                        "the"
                        "print"
                        "set" "get" "mut"
                        ))

(defvar ola-constants '("true" "false" "unit"))


(defvar ola-font-lock-defaults
  `((
    ( ,(regexp-opt ola-keywords  'words) . font-lock-keyword-face)
    ( ,(regexp-opt ola-types     'words) . font-lock-type-face)
    ( ,(regexp-opt ola-operators 'words) . font-lock-builtin-face)
    ( ,(regexp-opt ola-symbols   'words) . font-lock-builtin-face)
    ( ,(regexp-opt ola-functions 'words) . font-lock-function-name-face)
    ( ,(regexp-opt ola-constants 'words) . font-lock-constant-face)
)))

;;; Clear memory
(setq ola-keywords  nil
      ola-types     nil
      ola-operators nil
      ola-symbols   nil
      ola-functions nil
      ola-constants nil
      )

;; syntax table
(defvar ola-syntax-table nil "Syntax table for `ola-mode'.")
(setq ola-syntax-table
  (let ((synTable (make-syntax-table)))

  (modify-syntax-entry ?\( "()" synTable)
  (modify-syntax-entry ?\) ")(" synTable)
  (modify-syntax-entry ?\[ "(]" synTable)
  (modify-syntax-entry ?\] ")[" synTable)

    ;; comments
  (modify-syntax-entry ?\-  ". 123" synTable)
  (modify-syntax-entry ?\n  ">"    synTable)

  (modify-syntax-entry ?\{  "(} 1nb" synTable)
  (modify-syntax-entry ?\}  "){ 4nb" synTable)

  (mapc (lambda (x)
            (modify-syntax-entry x "." synTable))
          ;; Some of these are actually OK by default.
            "?=:")

  ;; Whitespace is whitespace
  (modify-syntax-entry ?\  " " synTable)
  (modify-syntax-entry ?\t " " synTable)

  ;; ;; Strings
  (modify-syntax-entry ?\" "\"" synTable)
  (modify-syntax-entry ?\\ "/"  synTable)

  synTable))

(defvar ola-mode-hook nil "Hook for ola-mode.")

;; define the mode
(define-derived-mode ola-mode fundamental-mode
  "Ola mode"

  ;; handling comments
  :syntax-table ola-syntax-table

  ;; syntax highlighting
  (make-local-variable 'ola-font-lock-defaults)
  (make-local-variable 'comment-start)
  (make-local-variable 'comment-end)
  (make-local-variable 'comment-start-skip)
  (make-local-variable 'comment-end-skip)
  (make-local-variable 'comment-column)
  (make-local-variable 'comment-padding)
  (make-local-variable 'comment-multi-line)
  ;;(make-local-variable 'comment-indent-function)

  (setq font-lock-defaults ola-font-lock-defaults
        comment-start           "-- "
        comment-end             ""
        comment-start-skip      "[-{]-[ \t]*"
        comment-end-skip        "[ \t]*\\(-}\\|\\s>\\)"
        comment-column          60
        comment-padding         0
        comment-multi-line      nil
        ;;comment-indent-function 'java-comment-indent
        ;;indent-tabs-mode        t
        )
  (run-hooks 'ola-mode-hook)
)

;; Customisation options

(defgroup ola nil
  "A language."
  :group 'languages)

;;(defcustom ola-command "ola"
;;  "The path to the Ola command to run."
;;  :type 'string
;;  :group 'ola)

(defcustom ola-options nil
  "Command line options to pass to ola."
  :type 'string
  :group 'ola)

(provide 'ola)
;;; ola.el ends here
