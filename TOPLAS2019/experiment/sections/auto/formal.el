(TeX-add-style-hook
 "formal"
 (lambda ()
   (LaTeX-add-environments
    '("ottaltgrammar" LaTeX-env-args ["argument"] 0)
    '("rulesection" LaTeX-env-args ["argument"] 2)
    '("drulepar" LaTeX-env-args ["argument"] 2)))
 :plain-tex)

