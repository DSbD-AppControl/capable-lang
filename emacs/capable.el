;;; package --- Summary

;;; Commentary:

;; Derived from typos.el and others.

;;; Code:

;; define several class of keywords

(defvar capable-keywords '("func"
                       "main"
                       "match"
                       "catch"
                       "local"
                       "var"
                       "let"
                       "type"
                       "loop"
                       "role"
                       "session"
                       "protocol"
                       "when"
                       "run" "with" "as" "recv" "send"
                       "if"
                       "else"
                       "call"
                       "rec"
                       "end"
                       "struct"
                       "union"
                       "tuple"))

(defvar capable-types '("Int" "Bool" "String" "Char" "Unit" "FILE" "PROC" "Role"))

(defvar capable-operators '("?" "!" "+" "|" "&" "."))

(defvar capable-symbols   '(":" "->" "==>" "="
                        "[" "]"
                        "<" ">"
                        "{" "}"
                        "(" ")"))

(defvar capable-functions '("and" "not" "or"
                        "lt" "lte" "eq" "gt" "gte"
                        "add" "sub" "mul" "div"
                        "size" "strCons" "slice"
                        "ord" "chr" "string" "toString"
                        "the"
                        "print"
                        "set" "get" "mut" "project" "replace"
                        ))

(defvar capable-constants '("true" "false" "unit"))


(defvar capable-font-lock-defaults
  `((
    ( ,(regexp-opt capable-keywords  'words) . font-lock-keyword-face)
    ( ,(regexp-opt capable-types     'words) . font-lock-type-face)
    ( ,(regexp-opt capable-operators 'words) . font-lock-builtin-face)
    ( ,(regexp-opt capable-symbols   'words) . font-lock-builtin-face)
    ( ,(regexp-opt capable-functions 'words) . font-lock-function-name-face)
    ( ,(regexp-opt capable-constants 'words) . font-lock-constant-face)
)))

;;; Clear memory
(setq capable-keywords  nil
      capable-types     nil
      capable-operators nil
      capable-symbols   nil
      capable-functions nil
      capable-constants nil
      )

;; syntax table
(defvar capable-syntax-table nil "Syntax table for `capable-mode'.")
(setq capable-syntax-table
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

(defvar capable-mode-hook nil "Hook for capable-mode.")

;; define the mode
(define-derived-mode capable-mode fundamental-mode
  "Capable mode"

  ;; handling comments
  :syntax-table capable-syntax-table

  ;; syntax highlighting
  (make-local-variable 'capable-font-lock-defaults)
  (make-local-variable 'comment-start)
  (make-local-variable 'comment-end)
  (make-local-variable 'comment-start-skip)
  (make-local-variable 'comment-end-skip)
  (make-local-variable 'comment-column)
  (make-local-variable 'comment-padding)
  (make-local-variable 'comment-multi-line)
  ;;(make-local-variable 'comment-indent-function)

  (setq font-lock-defaults capable-font-lock-defaults
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
  (run-hooks 'capable-mode-hook)
)

;; Customisation options

(defgroup capable nil
  "A language."
  :group 'languages)

;;(defcustom capable-command "capable"
;;  "The path to the Capable command to run."
;;  :type 'string
;;  :group 'capable)

(defcustom capable-options nil
  "Command line options to pass to capable."
  :type 'string
  :group 'capable)

(provide 'capable)
;;; capable.el ends here
