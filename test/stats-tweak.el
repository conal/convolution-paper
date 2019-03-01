(defun stats-tweak ()
  "Tweak running times for the non-terminating examples"
  (interactive)
  (beginning-of-buffer)
  (forward-sexp 3)
  (kill-sexp 2)
  (insert "{\\hang}{\\hang}")
  )
