import MathlibExtraLean.AllPairs

import HandbookOfPracticalLogicLean.Chapter2.NF.NF
import HandbookOfPracticalLogicLean.Chapter2.NF.DNF.ToDNF_1
import HandbookOfPracticalLogicLean.Chapter2.NF.ListConj.Semantics
import HandbookOfPracticalLogicLean.Chapter2.NF.ListDisj.Semantics


set_option autoImplicit false


open Formula_


/--
  Helper function for `to_cnf`.
-/
def to_cnf_aux :
  Formula_ → List (List Formula_)
  | and_ p q => (to_cnf_aux p) ∪ (to_cnf_aux q)
  | or_ p q => all_pairs_v4 List.union (to_cnf_aux p) (to_cnf_aux q)
  | F => [[F]]

#eval (to_cnf_aux (Formula_| ((p \/ (q /\ r)) /\ (~ p \/ ~ r)))).toString


/--
  `list_of_lists_to_conjunction_of_disjunctions FSS` := Translates the list of lists of formulas `FSS` to a conjunction of disjunctions.
-/
def list_of_lists_to_conjunction_of_disjunctions
  (FSS : List (List Formula_)) :
  Formula_ :=
  list_conj (List.map list_disj FSS)


/--
  `to_cnf F` := Translates the formula `F` to a logically equivalent formula. If `F` is in negation normal form then `to_cnf F` is in conjunctive normal form.
-/
def to_cnf
  (F : Formula_) :
  Formula_ :=
  list_of_lists_to_conjunction_of_disjunctions (to_cnf_aux F)


#eval (list_of_lists_to_conjunction_of_disjunctions [[atom_ "P", atom_ "Q"], [not_ (atom_ "P"), atom_ "R"]]).toString


lemma eval_eq_eval_to_cnf
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = true ↔ eval V (to_cnf F) = true :=
  by
  unfold to_cnf
  induction F
  case and_ phi psi phi_ih psi_ih =>
    unfold list_of_lists_to_conjunction_of_disjunctions at phi_ih

    unfold list_of_lists_to_conjunction_of_disjunctions at psi_ih

    unfold to_cnf_aux
    unfold list_of_lists_to_conjunction_of_disjunctions
    simp only [eval]
    simp only [bool_iff_prop_and]
    rewrite [phi_ih]
    rewrite [psi_ih]
    simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true]
    simp only [List.mem_map, List.mem_union_iff]
    constructor
    · intro a1
      obtain ⟨a1_left, a1_right⟩ := a1
      intro F a2
      obtain ⟨FS, a2_left, a2_right⟩ := a2
      cases a2_left
      case inl a2_left =>
        apply a1_left
        apply Exists.intro FS
        exact ⟨a2_left, a2_right⟩
      case inr a2_left =>
        apply a1_right
        apply Exists.intro FS
        exact ⟨a2_left, a2_right⟩
    · intro a1
      constructor
      · intro F a2
        obtain ⟨FS, a2_left, a2_right⟩ := a2
        apply a1
        apply Exists.intro FS
        constructor
        · left
          exact a2_left
        · exact a2_right
      · intro F a2
        obtain ⟨FS, a2_left, a2_right⟩ := a2
        apply a1
        apply Exists.intro FS
        constructor
        · right
          exact a2_left
        · exact a2_right
  case or_ phi psi phi_ih psi_ih =>
    unfold list_of_lists_to_conjunction_of_disjunctions at phi_ih

    unfold list_of_lists_to_conjunction_of_disjunctions at psi_ih

    unfold to_cnf_aux
    unfold list_of_lists_to_conjunction_of_disjunctions
    simp only [eval]
    simp only [bool_iff_prop_or]
    rewrite [phi_ih]
    rewrite [psi_ih]
    simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true]
    simp only [List.mem_map]
    simp only [mem_all_pairs_v4_union_iff_eq_union]
    constructor
    · intro a1 F a2
      obtain ⟨FS, ⟨PS, QS, ⟨PS_mem, QS_mem, a2_left⟩⟩, a2_right⟩ := a2
      rewrite [← a2_right]
      rewrite [← a2_left]
      simp only [eval_list_disj_union]
      cases a1
      case inl a1 =>
        left
        apply a1
        apply Exists.intro PS
        constructor
        · exact PS_mem
        · rfl
      case inr a1 =>
        right
        apply a1
        apply Exists.intro QS
        constructor
        · exact QS_mem
        · rfl
    · intro a1
      simp? at a1
      simp?
      clear phi_ih
      clear psi_ih
      simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
      sorry
  all_goals
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
