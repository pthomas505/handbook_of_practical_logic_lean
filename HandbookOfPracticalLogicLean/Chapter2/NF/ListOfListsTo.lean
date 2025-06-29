import HandbookOfPracticalLogicLean.Chapter2.NF.ListConj.ListConj
import HandbookOfPracticalLogicLean.Chapter2.NF.ListDisj.ListDisj


set_option autoImplicit false


open Formula_


/--
  `list_of_lists_to_disjunction_of_conjunctions FSS` := Translates the list of lists of formulas `FSS` to a disjunction of conjunctions.
-/
def list_of_lists_to_disjunction_of_conjunctions
  (FSS : List (List Formula_)) :
  Formula_ :=
  list_disj (List.map list_conj FSS)


/--
  `list_of_lists_to_conjunction_of_disjunctions FSS` := Translates the list of lists of formulas `FSS` to a conjunction of disjunctions.
-/
def list_of_lists_to_conjunction_of_disjunctions
  (FSS : List (List Formula_)) :
  Formula_ :=
  list_conj (List.map list_disj FSS)


#lint
