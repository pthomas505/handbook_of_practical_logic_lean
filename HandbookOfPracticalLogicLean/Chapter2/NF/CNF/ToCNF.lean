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
  List.map (fun (l : List Formula_) => List.map negate_literal l) (to_dnf_v3_aux (to_nnf_v1 (not_ F)))

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


lemma eval_eq_eval_to_cnf_v3
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = true ↔ eval V (to_cnf_v3 F) = true :=
  by
  unfold to_cnf_v3
  induction F
  case and_ phi psi phi_ih psi_ih =>
    unfold list_of_lists_to_conjunction_of_disjunctions at phi_ih

    unfold list_of_lists_to_conjunction_of_disjunctions at psi_ih

    unfold to_cnf_v3_aux
    unfold list_of_lists_to_conjunction_of_disjunctions
    simp only [eval]
    simp only [bool_iff_prop_and]
    rewrite [phi_ih]
    rewrite [psi_ih]
    simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true]
    simp only [List.mem_map]
    constructor
    · intro a1 F a2
      obtain ⟨a1_left, a1_right⟩ := a1

      obtain ⟨FS, ⟨PS, a2_left_left, a2_left_right⟩, a2_right⟩ := a2
      simp only [to_nnf_v1] at a2_left_left
      simp only [to_nnf_neg_v1] at a2_left_left
      unfold to_dnf_v3_aux at a2_left_left
      simp only [List.mem_union_iff] at a2_left_left

      cases a2_left_left
      case inl a2_left_left =>
        apply a1_left
        apply Exists.intro FS
        constructor
        · unfold to_cnf_v3_aux
          simp only [List.mem_map]
          unfold to_nnf_v1
          apply Exists.intro PS
          exact ⟨a2_left_left, a2_left_right⟩
        · exact a2_right
      case inr a2_left_left =>
        apply a1_right
        apply Exists.intro FS
        constructor
        · unfold to_cnf_v3_aux
          simp only [List.mem_map]
          unfold to_nnf_v1
          apply Exists.intro PS
          exact ⟨a2_left_left, a2_left_right⟩
        · exact a2_right
    · intro a1
      constructor
      · intro F a2
        obtain ⟨FS, a2_left, a2_right⟩ := a2
        unfold to_cnf_v3_aux at a2_left
        simp only [List.mem_map] at a2_left
        obtain ⟨PS, a2_left_left, a2_left_right⟩ := a2_left
        unfold to_nnf_v1 at a2_left_left

        apply a1
        apply Exists.intro FS
        constructor
        · unfold to_nnf_v1
          unfold to_nnf_neg_v1
          unfold to_dnf_v3_aux
          simp only [List.mem_union_iff]
          apply Exists.intro PS
          constructor
          · left
            exact a2_left_left
          · exact a2_left_right
        · exact a2_right
      · intro F a2
        obtain ⟨FS, a2_left, a2_right⟩ := a2
        unfold to_cnf_v3_aux at a2_left
        simp only [List.mem_map] at a2_left
        obtain ⟨PS, a2_left_left, a2_left_right⟩ := a2_left
        unfold to_nnf_v1 at a2_left_left

        apply a1
        apply Exists.intro FS
        constructor
        · unfold to_nnf_v1
          unfold to_nnf_neg_v1
          unfold to_dnf_v3_aux
          simp only [List.mem_union_iff]
          apply Exists.intro PS
          constructor
          · right
            exact a2_left_left
          · exact a2_left_right
        · exact a2_right
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
