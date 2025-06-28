import MathlibExtraLean.AllPairs

import HandbookOfPracticalLogicLean.Chapter2.NF.NF
import HandbookOfPracticalLogicLean.Chapter2.NF.Negate
import HandbookOfPracticalLogicLean.Chapter2.NF.NNF.NNF_1
import HandbookOfPracticalLogicLean.Chapter2.NF.DNF.ToDNF_3

import HandbookOfPracticalLogicLean.Chapter2.NF.ListConj.Semantics
import HandbookOfPracticalLogicLean.Chapter2.NF.ListDisj.Semantics


set_option autoImplicit false


open Formula_


/--
  Helper function for `to_cnf_v3`.
-/
def to_cnf_v3_aux
  (F : Formula_) :
  List (List Formula_) :=
  List.map (fun (FS : List Formula_) => List.map negate_literal FS) (to_dnf_v3_aux (to_nnf_v1 (not_ F)))

#eval (to_cnf_v3_aux (Formula_| ((p \/ (q /\ r)) /\ (~ p \/ ~ r)))).toString


/--
  Helper function for `to_cnf_v3`.
-/
def to_cnf_v3_aux_alt :
  Formula_ → List (List Formula_)
  | and_ p q => (to_cnf_v3_aux_alt p) ∪ (to_cnf_v3_aux_alt q)
  | or_ p q => all_pairs_v4 List.union (to_cnf_v3_aux_alt p) (to_cnf_v3_aux_alt q)
  | F => [[F]]

#eval (to_cnf_v3_aux_alt (Formula_| ((p \/ (q /\ r)) /\ (~ p \/ ~ r)))).toString


/--
  `list_of_lists_to_conjunction_of_disjunctions FSS` := Translates the list of lists of formulas `FSS` to a conjunction of disjunctions.
-/
def list_of_lists_to_conjunction_of_disjunctions
  (FSS : List (List Formula_)) :
  Formula_ :=
  list_conj (List.map list_disj FSS)


/--
  `to_cnf_v3 F` := Translates the formula `F` to a logically equivalent formula. If `F` is in negation normal form then `to_cnf_v3 F` is in conjunctive normal form.
-/
def to_cnf_v3
  (F : Formula_) :
  Formula_ :=
  list_of_lists_to_conjunction_of_disjunctions (to_cnf_v3_aux F)


#eval (list_of_lists_to_conjunction_of_disjunctions [[atom_ "P", atom_ "Q"], [not_ (atom_ "P"), atom_ "R"]]).toString


lemma de_morgan_1
  (V : ValuationAsTotalFunction)
  (P Q : Formula_) :
  eval V (not_ (and_ P Q)) = true ↔
    eval V (or_ (not_ P) (not_ Q)) = true :=
  by
  simp only [eval]
  simp only [bool_iff_prop_or]
  simp only [bool_iff_prop_not]
  simp only [bool_iff_prop_and]
  constructor
  · intro a1
    by_cases c1 : eval V P = true
    case pos =>
      right
      intro contra
      apply a1
      exact ⟨c1, contra⟩
    case neg =>
      left
      exact c1
  · intro a1
    intro contra
    obtain ⟨contra_left, contra_right⟩ := contra
    cases a1
    case inl a1 =>
      apply a1
      exact contra_left
    case inr a1 =>
      apply a1
      exact contra_right


lemma de_morgan_2
  (V : ValuationAsTotalFunction)
  (P Q : Formula_) :
  eval V (not_ (or_ P Q)) = true ↔
    eval V (and_ (not_ P) (not_ Q)) = true :=
  by
  simp only [eval]
  simp only [bool_iff_prop_and]
  simp only [bool_iff_prop_not]
  simp only [bool_iff_prop_or]
  constructor
  · intro a1
    constructor
    · intro contra
      apply a1
      left
      exact contra
    · intro contra
      apply a1
      right
      exact contra
  · intro a1 contra
    obtain ⟨a1_left, a1_right⟩ := a1
    cases contra
    case inl contra =>
      apply a1_left
      exact contra
    case inr contra =>
      apply a1_right
      exact contra


lemma de_morgan_list_1
  (V : ValuationAsTotalFunction)
  (FS : List Formula_) :
  eval V (not_ (list_conj FS)) = true ↔
    eval V (list_disj (List.map not_ FS)) = true :=
  by
  induction FS
  case nil =>
    simp only [List.map_nil]
    simp only [list_conj]
    simp only [list_disj]
    simp only [eval]
    simp only [b_not]
  case cons hd tl ih =>
    cases tl
    case nil =>
      simp only [List.map_cons, List.map_nil]
      unfold list_conj
      unfold list_disj
      rfl
    case cons tl_hd tl_tl =>
      simp only [List.map_cons] at ih

      simp only [List.map_cons]
      unfold list_conj
      unfold list_disj
      simp only [de_morgan_1]
      unfold eval
      simp only [bool_iff_prop_or]
      rewrite [ih]
      rfl


lemma de_morgan_list_2
  (V : ValuationAsTotalFunction)
  (FS : List Formula_) :
  eval V (not_ (list_disj FS)) = true ↔
    eval V (list_conj (List.map not_ FS)) = true :=
  by
  induction FS
  case nil =>
    simp only [List.map_nil]
    simp only [list_disj]
    simp only [list_conj]
    simp only [eval]
    simp only [b_not]
  case cons hd tl ih =>
    cases tl
    case nil =>
      simp only [List.map_cons, List.map_nil]
      unfold list_disj
      unfold list_conj
      rfl
    case cons tl_hd tl_tl =>
      simp only [List.map_cons] at ih

      simp only [List.map_cons]
      unfold list_disj
      unfold list_conj
      simp only [de_morgan_2]
      unfold eval
      simp only [bool_iff_prop_and]
      rewrite [ih]
      rfl


lemma eval_eq_eval_to_cnf_v3
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = true ↔ eval V (to_cnf_v3 F) = true :=
  by
  sorry


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
