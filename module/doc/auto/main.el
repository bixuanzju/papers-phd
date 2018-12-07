(TeX-add-style-hook
 "main"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("babel" "british") ("threeparttable" "para" "online" "flushleft")))
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "sections/test"
    "article"
    "art10"
    "amsmath"
    "amssymb"
    "amsthm"
    "mathtools"
    "xspace"
    "comment"
    "csquotes"
    "babel"
    "hyperref"
    "paralist"
    "graphicx"
    "float"
    "listings"
    "xcolor"
    "styles/mathpartir"
    "booktabs"
    "tabularx"
    "threeparttable")
   (TeX-add-symbols
    '("hlmath" ["argument"] 1)
    '("hl" ["argument"] 1)
    '("kw" 1)
    '("labeledjudge" 1)
    '("huang" 1)
    '("jeremy" 1)
    '("bruno" 1)
    '("authornote" 3))
   (LaTeX-add-bibliographies)
   (LaTeX-add-amsthm-newtheorems
    "thm"
    "lem"
    "dfn")
   (LaTeX-add-xcolor-definecolors
    "#2"))
 :latex)

