import HandbookOfPracticalLogicLean.Chapter2.Formula


set_option autoImplicit false


open Formula_


/--
  `list_disj l` := If the list of formulas `l` is empty then `false_`. If `l` is not empty then the iterated disjunction of the formulas in `l`.
-/
def list_disj :
  List Formula_ → Formula_
  | [] => false_
  | [P] => P
  | hd :: tl => or_ hd (list_disj tl)


#lint
