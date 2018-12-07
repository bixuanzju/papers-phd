(TeX-add-style-hook
 "sigplanconf"
 (lambda ()
   (TeX-add-to-alist 'LaTeX-provided-package-options
                     '(("mathtime" "mtbold" "noTS1") ("natbib" "authoryear" "square" "numbers" "sort&compress")))
   (TeX-run-style-hooks
    "article"
    "art10"
    "mathtime"
    "natbib")
   (TeX-add-symbols
    '("centeroncapheight" 1)
    '("titlenote" 1)
    '("titlebanner" 1)
    '("authorinfo" 3)
    '("subtitle" 1)
    '("preprintfooter" 1)
    '("mono" 1)
    '("proceedings" 1)
    '("doi" 1)
    '("copyrightdata" 1)
    '("copyrightyear" 1)
    '("conferenceinfo" 2)
    '("authorversion" 4)
    '("permission" 1)
    '("reprintprice" 1)
    '("category" 3)
    '("setvspace" 2)
    "exclusivelicense"
    "permissiontopublish"
    "ACMCanadapermission"
    "ACMUSpermission"
    "USpublicpermission"
    "nocaptionrule"
    "acks"
    "keywords"
    "terms"
    "balancecolumns"
    "nut"
    "softraggedright"
    "euro")
   (LaTeX-add-labels
    "sigplanconf@finalpage"
    "@addauthors")
   (LaTeX-add-pagestyles
    "plain"
    "empty"
    "headings"
    "myheadings"))
 :latex)

