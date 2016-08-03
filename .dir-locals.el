;; Specify coq-load path relative to project root
(coq-mode (eval (cl-flet
					((pre (s) (concat (locate-dominating-file buffer-file-name ".dir-locals.el") s)))
				  (setq coq-load-path
						`((rec ,(pre "coq") "LLVMBerry")
						  (rec ,(pre "lib/sflib") "sflib")
						  (rec ,(pre "lib/paco/src") "Paco")
						  (rec ,(pre "lib/vellvm/src") "Vellvm")
						  (rec ,(pre "lib/vellvm/lib/metalib") "metalib")
						  (rec ,(pre "lib/vellvm/lib/cpdtlib") "Cpdt")
						  (rec ,(pre "lib/vellvm/lib/compcert-2.4") "compcert")
						  ))))
		  (coq-prog-args "-emacs-U"))
