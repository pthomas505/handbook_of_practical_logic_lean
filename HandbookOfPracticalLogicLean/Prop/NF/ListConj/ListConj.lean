import HandbookOfPracticalLogicLean.Prop.Formula


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


open Formula_


/--
  `list_conj FS` := If the list of formulas `FS` is empty then `true_`. If `FS` is not empty then the iterated conjunction of the formulas in `FS`.
-/
@[nolint defsWithUnderscore]
def list_conj :
  List Formula_ → Formula_
  | [] => true_
  | [P] => P
  | hd :: tl => and_ hd (list_conj tl)


#lint
