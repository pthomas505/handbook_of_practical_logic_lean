import HandbookOfPracticalLogicLean.Prop.Formula


set_option autoImplicit false


open Formula_


/--
  `list_conj FS` := If the list of formulas `FS` is empty then `true_`. If `FS` is not empty then the iterated conjunction of the formulas in `FS`.
-/
def list_conj :
  List Formula_ → Formula_
  | [] => true_
  | [P] => P
  | hd :: tl => and_ hd (list_conj tl)


#lint
