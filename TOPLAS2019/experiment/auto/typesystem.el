(TeX-add-style-hook
 "typesystem"
 (lambda ()
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "path")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "url")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "nolinkurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperbaseurl")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperimage")
   (add-to-list 'LaTeX-verbatim-macros-with-braces-local "hyperref")
   (add-to-list 'LaTeX-verbatim-macros-with-delims-local "path")
   (LaTeX-add-labels
    "lemma:size_e"
    "lemma:decrease_stop"
    "lemma:type_decrease"
    "lemma:subst_dec_measure"
    "lemma:repr"
    "def:contamination"
    "thm:inst_soundness"
    "thm:sub_soundness"
    "thm:type_sound"
    "thm:inst_complete"
    "thm:sub_completeness"
    "thm:match_complete"))
 :latex)

