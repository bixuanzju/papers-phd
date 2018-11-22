(TeX-add-style-hook
 "paper"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-class-options
                     '(("llncs" "oribibl" "dvipsnames")))
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("cleveref" "capitalise") ("ifsym" "misc")))
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (TeX-run-style-hooks
    "latex2e"
    "paper_utility"
    "sections/formal"
    "sections/typesystem"
    "llncs"
    "llncs10"
    "llncsdoc"
    "booktabs"
    "subcaption"
    "amsmath"
    "amssymb"
    "mathtools"
    "mdwlist"
    "pifont"
    "paralist"
    "graphicx"
    "epstopdf"
    "float"
    "longtable"
    "multirow"
    "xspace"
    "comment"
    "tikz"
    "url"
    ""
    "nameref"
    "hyperref"
    "cleveref"
    "thmtools"
    "thm-restate"
    "ifsym"
    "rotating"
    "supertabular"
    "ottalt")
   (TeX-add-symbols
    '("hlmath" ["argument"] 1)
    '("hl" ["argument"] 1)
    '("jeremy" 1)
    '("ningning" 1)
    '("bruno" 1)
    '("mynote" 3)))
 :latex)

