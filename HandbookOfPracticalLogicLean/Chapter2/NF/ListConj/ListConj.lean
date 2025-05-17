import HandbookOfPracticalLogicLean.Chapter2.Semantics


set_option autoImplicit false


open Formula_


/--
  `list_conj l` := If the list of formulas `l` is empty then `true_`. If `l` is not empty then the iterated conjunction of the formulas in `l`.
-/
def list_conj :
  List Formula_ → Formula_
  | [] => true_
  | [P] => P
  | hd :: tl => and_ hd (list_conj tl)


#lint
