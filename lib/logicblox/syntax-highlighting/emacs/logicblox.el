;; logicblox.el --- LogicBlox major mode
;;
;; Copyright (C) 2011
;;   LogicBlox
;;
;; Authors: Martin Bravenboer <martin.bravenboer@logicblox.com>
;;          Todd J. Green <todd.green@logicblox.com>

(require 'comint)

(autoload 'comint-mode "comint")

(defgroup logicblox nil
  "LogicBlox major mode."
  :group 'languages
  :version "22.1"
)

(defcustom bloxbatch-command "bloxbatch"
  "*The bloxbatch utility."
  :type 'file
  :group 'logicblox)

(defcustom bloxbatch-command-args '("-interactive")
  "*List of string arguments to be used when starting a bloxbatch
shell."
  :type '(repeat-string)
  :group 'logicblox)

;; Allow the user to run their own code when the mode is run
(defvar logicblox-mode-hook nil)

(setq bloxbatch-commands
  `(
	"abort"
	"addBlock"
	"agg"
	"alias"
	"buildProject"
	"checkFact"
	"close"
	"commit"
	"comparePredicates"
	"connect"
	"connectBlox"
	"create"
	"createMeasures"
	"datalogProfiling"
	"disconnect"
	"echo"
	"elapsedTime"
	"exec"
	"execRetry"
	"executeServerCommand"
	"exit"
	"export"
   "exportXML"
	"extractProject"
	"generateImportExportLogic"
	"generateMigrationScript"
	"help"
	"import"
   "xmlAddSpec"
   "xmlImport"
	"importDelimited"
	"installProject"
   "list"
	"listArrays"
	"listen"
	"loadLibrary"
	"logLevel"
	"logWriter"
	"migrateData"
	"open"
	"option"
	"pager"
	"predInfo"
	"prepareForCopy"
	"print"
	"printArray"
	"printDatalogProfile"
	"printExecutionGraph"
	"printLocks"
	"printLog"
	"protoAddSpec"
	"protoExport"
	"protoImport"
	"provenance"
	"query"
	"recomputeIDB"
	"releaseLocks"
	"removeBlock"
	"replaceBlock"
	"resetDatalogProfile"
	"rm"
   "seq"
	"set"
	"sleep"
	"source"
	"startTimer"
	"statistics"
	"status"
	"timestamp"
	"trace"
	"transaction"
	"transactionInfo"
	"transactionLog"
	"watch"
))

(setq bloxbatch-commands-regexp
  (regexp-opt bloxbatch-commands `words))

;; Regular expressions for syntax highlighting, based on VisualBlox
;; IDE conventions (see file mode-datalog_highlight_rules.js).  The
;; rules for comments and strings are handled elsewhere via the syntax
;; table.  Order in the list below matters, with earlier coloring
;; rules applied to a given line before later rules.
(setq logicblox-font-lock-keywords
      `(
        ;; constants
        ("#[0-9A-Z: -\\+/]+#" . font-lock-constant-face)
        ("`[a-zA-Z_][a-zA-Z0-9_:@]*" . font-lock-constant-face)
        ("-?[0-9]+\\.[0-9]+[eE][-+]?[0-9]+[df]?" . font-lock-constant-face)
        ("-?[0-9]+[eE][-+]?[0-9]+[df]?" . font-lock-constant-face)
        ("-?[0-9]+\\.[0-9]+[df]?" . font-lock-constant-face)
        ("\\<true\\>" . font-lock-constant-face)
        ("\\<false\\>" . font-lock-constant-face)

        ;; predicates
        ("\\([a-zA-Z_][a-zA-Z0-9_:@]*\\)\\((\\|\\[\\)"
         (1 font-lock-function-name-face) )
        ("[a-zA-Z_][a-zA-Z0-9_:@]*@[a-zA-Z]*"
        . font-lock-function-name-face)
        ("@[a-zA-Z]+" . font-lock-function-name-face)
        
        ;; bloxbatch commands
        (,bloxbatch-commands-regexp . font-lock-keyword-face)

        ;; level-1 variables
        ("\\?[a-zA-Z_][a-zA-Z0-9_]*" . font-lock-preprocessor-face)

        ;; level-0 variables
        ("[a-zA-Z_][a-zA-Z0-9_]*" . font-lock-variable-name-face)        

        ;; constants
        ("-?[0-9]+[df]?" . font-lock-preprocessor-face)
))

;; the command to comment/uncomment text
(defun logicblox-comment-dwim (arg)
  "Comment or uncomment current line or region in a smart way.
For details, see `comment-dwim'."
   (interactive "*P")
   (require 'newcomment)
   (let ((deactivate-mark nil) (comment-start "//") (comment-end ""))
     (comment-dwim arg)))

(defvar bloxbatch-bufname "bloxbatch")

(defvar comint-prompt-regexp)
(setq comint-prompt-regexp "^<blox>: ")

(add-to-list 'comint-dynamic-complete-functions
             'bloxbatch-complete-command)

(defvar bloxbatch-buffer nil
  "*The current bloxbatch process buffer.

Commands that send text from source buffers to bloxbatch processes
have to choose a process to send to.  This is determined by
buffer-local value of `bloxbatch-buffer'.  If its value in the current
buffer, i.e., both any local value and the default one, is nil,
`run-bloxbatch' and commands that send to the bloxbatch process will
start a new process.

Whenever \\[run-bloxbatch] starts a new proccess, it resets the
default value of `bloxbatch-buffer' to be the new process's buffer and
sets the buffer-local value similarly if the current buffer is in
LogicBlox mode, so that source buffer stays associated with a specific
sub-process.

Use \\[logicblox-set-proc] to set the default value from a buffer with
a local value.")
(make-variable-buffer-local 'bloxbatch-buffer)

(defun bloxbatch-mode-hook ()
  (define-key comint-mode-map "\t" 'comint-dynamic-complete))

(add-hook 'comint-mode-hook 'bloxbatch-mode-hook)

;;;###autoload
(defun run-bloxbatch (&optional argprompt)
  "Run an inferior bloxbatch process, input and output via buffer
*bloxbatch*.  A new process is started if one isn't running attached
to `bloxbatch-buffer'.  Otherwise, if a process is already running in
`bloxbatch-buffer', switch to that buffer.

This is like Shell mode, except that bloxbatch is running in the
buffer instead of a shell.  See the `Interactive Shell' and
`Shell Mode' sections of the Emacs manual for details, especially
for the key bindings active in the `*bloxbatch*' buffer.

With optional \\[universal-argument], the user is prompted for
the flags to pass to bloxbatch.  This has no effect when this
command is used to switch to an existing process, only when a new
process is started.  If you use this, you will probably want to
ensure that the current arguments are retained (they will be
included in the prompt).  This argument is ignored when this
function is called programmatically."
  (interactive "P")
  (when (not (comint-check-proc bloxbatch-buffer))
    (with-current-buffer
      (let ((args bloxbatch-command-args))
        (when (and argprompt
                   (called-interactively-p 'interactive)
                   (fboundp 'split-string))
          ;; TBD: Perhaps force "-interactive" in the final list?
          (setq args (split-string
                      (read-string (concat bloxbatch-bufname
                                           " arguments: ")
                                   (concat
                                    (mapconcat 'identity
                                   bloxbatch-command-args " ") " ")
                                   ))))
        (apply 'make-comint bloxbatch-bufname bloxbatch-command
                nil args))
        (setq-default bloxbatch-buffer (current-buffer))
        (setq bloxbatch-buffer (current-buffer))))
  (if (derived-mode-p 'logicblox)
      (setq bloxbatch-buffer (default-value 'bloxbatch-buffer)))
  (pop-to-buffer bloxbatch-buffer t))

;; Keymap and syntax
(defvar logicblox-map
  (let ((map (make-sparse-keymap)))
    (define-key map "\C-c\C-s" 'bloxbatch-send-string)
    (define-key map [remap comment-dwim] 'logicblox-comment-dwim)
    (define-key map "\C-c\C-o" 'bloxbatch-open-workspace)
    (define-key map "\C-c\C-l" 'bloxbatch-close-workspace)
    (define-key map "\C-c\C-s" 'bloxbatch-transaction)
    (define-key map "\C-c\C-p" 'bloxbatch-print-predicate-at-point)
    (define-key map "\C-c\C-t" 'bloxbatch-commit)
    (define-key map "\C-c\C-c" 'bloxbatch-send-buffer)
    (define-key map "\C-c\C-r" 'bloxbatch-send-region)
    (define-key map "\C-c\M-r" 'bloxbatch-send-region-and-go)
    (define-key map "\C-c\C-z" 'logicblox-switch-to-bloxbatch)
    (easy-menu-define logicblox-menu map "LogicBlox Mode menu"
      `("LogicBlox"
        :help "LogicBlox-specific Features"
        ["Run bloxbatch" run-bloxbatch
         :help "Invoke the bloxbatch shell"]))
    map))

(defun bloxbatch-complete-command ()
  "Dynamically complete the bloxbatch command at point.

Returns t if successful."
  (interactive)
  
  (let ((command (comint-word comint-file-name-chars)))
        (and command (comint-dynamic-simple-complete command
        bloxbatch-commands))))

(defun bloxbatch-send-buffer ()
  "Send the current buffer to the inferior bloxbatch process."
  (interactive)
  (bloxbatch-send-region (point-min) (point-max)))

(defun bloxbatch-open-workspace (string)
  "Open workspace STRING in inferior bloxbatch process."
  (interactive "Dworkspace: ")
  (comint-send-string (bloxbatch-proc) (concat "open " string "\n")))

(defun bloxbatch-close-workspace ()
  "Close workspace in inferior bloxbatch process."
  (interactive)
  (comint-send-string (bloxbatch-proc) "close\n"))

(defun bloxbatch-transaction ()
  "Begin transaction in inferior bloxbatch process."
  (interactive)
  (comint-send-string (bloxbatch-proc) "transaction\n"))

(defun bloxbatch-commit ()
  "Commit current transaction in inferior bloxbatch process."
  (interactive)
  (comint-send-string (bloxbatch-proc) "commit\n"))

(defun bloxbatch-print-predicate-at-point ()
  "Print the contents of the predicate at point in inferior bloxbatch
process."
  (interactive)
  (comint-send-string (bloxbatch-proc) 
                      (concat "print " 
                               (thing-at-point 'word)
                               "\n")))

(defun bloxbatch-send-string (string)
  "Evaluate STRING in inferior bloxbatch process."
  (interactive "sbloxbatch command: ")
  (comint-send-string (bloxbatch-proc) string)
  (unless (string-match "\n\\'" string)
    ;; Make sure the text is properly LF-terminated.
    (comint-send-string (bloxbatch-proc) "\n"))
  (when (string-match "\n[ \t].*\n?\\'" string)
    ;; If the string contains a final indented line, add a second
    ;; newline so as to make sure we terminate the multiline
    ;; instruction.
    (comint-send-string (bloxbatch-proc) "\n")))

(defun bloxbatch-send-region (start end)
  "Send the region to the inferior bloxbatch process."
  (interactive "r")
  (comint-send-string (bloxbatch-proc) (buffer-substring start end))
)

(defun bloxbatch-proc ()
  "Return the current bloxbatch process.  See variable
  `logicblox-buffer'.  Starts a new process if necessary."
  (unless (comint-check-proc bloxbatch-buffer)
    (run-bloxbatch))
  (get-buffer-process bloxbatch-buffer))    

(defun logicblox-switch-to-bloxbatch (eob-p)
  "Switch to the bloxbatch process buffer, maybe starting new
  process.  With prefix arg, position cursor at end of buffer."
  (interactive "P")
  (pop-to-buffer (process-buffer (bloxbatch-proc)) t)
  (when eob-p
    (push-mark)
    (goto-char (point-max))))

(defun bloxbatch-send-region-and-go (start end)
  "Send the region to the inferior bloxbatch process.  Then switch to
  the process buffer."
  (interactive "r")
  (bloxbatch-send-region start end)
  (logicblox-switch-to-bloxbatch t))

;; define the mode
(define-derived-mode logicblox fundamental-mode
  "LogicBlox"
  "Major mode for editing LogicBlox Datalog source files and
interacting with the bloxbatch utility.
\\<logicblox-map>
\\{logicblox-map}"
  :group 'logicblox

  ;; code for syntax highlighting
  (setq font-lock-defaults '((logicblox-font-lock-keywords)))

  ;; Commenting
  (setq comment-start "//")

  ;; Support line-style "// ..." and block-style "/* ... */" comments
  (modify-syntax-entry ?/  ". 124b" logicblox-syntax-table)
  (modify-syntax-entry ?*  ". 23"   logicblox-syntax-table)
  (modify-syntax-entry ?\n "> b"  logicblox-syntax-table)
  (modify-syntax-entry ?\^m "> b" logicblox-syntax-table)

  ;; Allow the underscore character to be a valid part of a word;
  ;; colons, dollar signs, and question marks too.
  (modify-syntax-entry ?_ "w" logicblox-syntax-table)
  (modify-syntax-entry ?: "w" logicblox-syntax-table)
  (modify-syntax-entry ?$ "w" logicblox-syntax-table)
  (modify-syntax-entry ?? "w" logicblox-syntax-table)
)

(provide 'logicblox)

(setq auto-mode-alist (cons '("\\.testsuite\\'" . logicblox)
                            auto-mode-alist))
(setq auto-mode-alist (cons '("\\.logic$" . logicblox)
                            auto-mode-alist)) 
(setq auto-mode-alist (cons '("\\.lb$" . logicblox) auto-mode-alist)) 
(setq auto-mode-alist (cons '("\\.schema$" . logicblox) auto-mode-alist)) 
