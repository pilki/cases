(defun insert-case ()
 "Insert the proper Case tactic at cursor position."
 (interactive)
 (let (names tmpname spoint cont)
  (setq names '("SSSSSSCase" "SSSSSCase"
                "SSSSCase" "SSSCase" "SSCase"
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
                "SSCase" "SSSCase" "SSSSCase"
                "SSSSSCase" "SSSSSSCase"))
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
  (if cont (insert (concat cont "."))))
)

(global-set-key (kbd "C-c C-a C-q") 'insert-all-cases)
