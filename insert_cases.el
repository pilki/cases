(defun insert-case ()
 "Insert the proper Case tactic at cursor position."
 (interactive)
 (let (names tmpname spoint cont)
  (setq names '("S11Case" "S10Case" "S9Case" "S8Case" 
                "S7Case" "SSSSSSSCase" 
                "S6Case" "SSSSSSCase"
                "S5Case" "SSSSSCase"
                "S4Case" "SSSSCase"
                "S3Case" "SSSCase" "SSCase"
                "SCase" "Case"))
  (setq cont nil)
  (with-current-buffer "*goals*"
    (goto-char (point-min))
    (while names
      (setq tmpname (pop names))
      (if (search-forward (concat " " tmpname) nil t)
          (progn
            (search-forward "\"")
            (setq spoint (1- (point)))
            (search-forward "\"")
            (setq cont
                  (concat tmpname " "
                    (buffer-substring-no-properties spoint (point)) "."))
            (setq names nil)
            )
        )
      )
    )
  (if cont (insert cont)))
)

(global-set-key (kbd "C-c C-a C-z") 'insert-case)


(defun insert-all-cases ()
 "Insert all the proper Case tactics at cursor position."
 (interactive)
 (let (names tmpname spoint cont)
  (setq names '("Case" "SCase"
                "SSCase" "S3Case" "SSSCase" "S4Case" "SSSSCase"
                "S5Case" "SSSSSCase" "S6Case" "SSSSSSCase"
                "S7Case" "SSSSSSSCase"
                "S8Case" "S9Case" "S10Case" "S11Case" ))
  (setq cont nil)
  (with-current-buffer "*goals*"
    (while names
      (goto-char (point-min))
      (setq tmpname (pop names))
      (if (search-forward (concat " " tmpname) nil t)
          (progn
            (search-forward "\"")
            (setq spoint (1- (point)))
            (search-forward "\"")
            (setq cont
                (if cont
                  (concat cont "; " tmpname " "
                    (buffer-substring-no-properties spoint (point)))
                  (concat tmpname " "
                    (buffer-substring-no-properties spoint (point)))
                  )
             )
            )
        )
      )
    )
  (if cont (insert (concat cont ". "))))
)

(global-set-key (kbd "C-c C-a C-q") 'insert-all-cases)
