import HandbookOfPracticalLogicLean.Chapter2.Formula


set_option autoImplicit false


open Formula_


/--
  `list_disj FS` := If the list of formulas `FS` is empty then `false_`. If `FS` is not empty then the iterated disjunction of the formulas in `FS`.
-/
def list_disj :
  List Formula_ → Formula_
  | [] => false_
  | [P] => P
  | hd :: tl => or_ hd (list_disj tl)


#lint
