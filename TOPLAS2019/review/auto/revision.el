(TeX-add-style-hook
 "revision"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("article" "dvipsnames")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("natbib" "round") ("hyperref" "colorlinks=true" "urlcolor=blue" "citecolor=blue")))
   (add-to-list 'LaTeX-verbatim-environments-local "lstlisting")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "lstinline")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "lstinline")
   (TeX-run-style-hooks
    "latex2e"
    "../doc/paper_utility"
    "article"
    "art10"
    "parskip"
    "pdfpages"
    "listings"
    "amsmath"
    "amssymb"
    "natbib"
    "hyperref"
    "longtable")
   (TeX-add-symbols
    '("reply" 1)
    '("jeremy" 1)
    '("ningning" 1)
    '("tom" 1)
    '("bruno" 1)
    '("mynote" 3)))
 :latex)

