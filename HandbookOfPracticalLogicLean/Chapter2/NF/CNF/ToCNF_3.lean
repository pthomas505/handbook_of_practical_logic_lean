import HandbookOfPracticalLogicLean.Chapter2.NF.DeMorgan
import HandbookOfPracticalLogicLean.Chapter2.NF.NF
import HandbookOfPracticalLogicLean.Chapter2.NF.NNF.NNF_1
import HandbookOfPracticalLogicLean.Chapter2.NF.DNF.ToDNF_3


set_option autoImplicit false


open Formula_


/--
  Helper function for `to_cnf_v3`.
-/
def to_cnf_v3_aux
  (F : Formula_) :
  List (List Formula_) :=
  map_map_not (to_dnf_v3_aux (to_nnf_v1 (not_ F)))

#eval (to_cnf_v3_aux (Formula_| ((p \/ (q /\ r)) /\ (~ p \/ ~ r)))).toString


/--
  `to_cnf_v3 F` := Translates the formula `F` to a logically equivalent formula. If `F` is in negation normal form then `to_cnf_v3 F` is in conjunctive normal form.
-/
def to_cnf_v3
  (F : Formula_) :
  Formula_ :=
  list_of_lists_to_conjunction_of_disjunctions (to_cnf_v3_aux F)


#eval (list_of_lists_to_conjunction_of_disjunctions [[atom_ "P", atom_ "Q"], [not_ (atom_ "P"), atom_ "R"]]).toString


lemma eval_eq_eval_to_cnf_v3
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = true ↔ eval V (to_cnf_v3 F) = true :=
  by
  unfold to_cnf_v3
  unfold to_cnf_v3_aux
  rewrite [← de_morgan_list_of_lists_1]
  simp only [eval]
  simp only [bool_iff_prop_not]
  rewrite [← eval_eq_eval_to_dnf_v3_aux]
  simp only [← eval_eq_eval_to_nnf_v1]
  simp only [eval]
  simp only [bool_iff_prop_not]
  simp only [Bool.not_eq_true, Bool.not_eq_false]


-------------------------------------------------------------------------------


lemma list_of_lists_to_conjunction_of_disjunctions_singleton
  (F : Formula_) :
  list_of_lists_to_conjunction_of_disjunctions [[F]] = F :=
  by
  unfold list_of_lists_to_conjunction_of_disjunctions
  simp only [List.map_cons, List.map_nil]
  unfold list_disj
  unfold list_conj
  rfl


#lint
