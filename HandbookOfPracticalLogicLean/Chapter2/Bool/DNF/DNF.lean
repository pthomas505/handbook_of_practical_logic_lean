import MathlibExtraLean.FunctionUpdateFromListOfPairsITE

import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.IsDNF
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.ListConj
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.MkLits
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.ListDisj
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.GenAllValuations
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.ToDNF
import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.AllPairs

import Mathlib.Tactic


set_option autoImplicit false


namespace Bool_


open Formula_




-------------------------------------------------------------------------------




-------------------------------------------------------------------------------




-------------------------------------------------------------------------------




-------------------------------------------------------------------------------




-------------------------------------------------------------------------------




-------------------------------------------------------------------------------






def pure_dnf :
  Formula_ → List (List Formula_)
  | and_ p q => all_pairs_alt_alt List.union (pure_dnf p) (pure_dnf q)
  | or_ p q => (pure_dnf p) ∪ (pure_dnf q)
  | F => [[F]]

#eval (pure_dnf (Formula_| ((p \/ (q /\ r)) /\ (~p \/ ~ r)))).toString


def dnf_list_of_list_to_formula
  (l : List (List Formula_)) :
  Formula_ :=
  list_disj (List.map list_conj l)


#eval (dnf_list_of_list_to_formula [[atom_ "P", atom_ "Q"], [not_ (atom_ "P"), atom_ "R"]]).toString


example
  {α β : Type}
  [DecidableEq α]
  [DecidableEq β]
  (f : α → β)
  (l1 l2 : List α)
  (h1 : Function.Injective f) :
  List.map f (l1 ∪ l2) = (List.map f l1) ∪ (List.map f l2) :=
  by
  induction l1
  case nil =>
    simp only [List.map_nil]
    simp only [List.nil_union]
  case cons hd tl ih =>
    simp only [List.cons_union, List.map_cons]
    rewrite [← ih]
    unfold List.insert

    have s1 : List.elem (f hd) (List.map f (tl ∪ l2)) = true ↔ List.elem hd (tl ∪ l2) = true :=
    by
      simp only [List.elem_eq_mem, decide_eq_true_eq]
      apply List.mem_map_of_injective
      exact h1

    simp only [s1]
    split_ifs
    case pos c1 =>
      rfl
    case neg c1 =>
      simp only [List.map_cons]


lemma mem_all_pairs_alt_alt_imp_eq_union
  {α : Type}
  [DecidableEq α]
  (l1 l2 : List (List α))
  (l : List α)
  (h1 : l ∈ all_pairs_alt_alt List.union l1 l2) :
  ∃ (xs : List α) (ys : List α), xs ∈ l1 ∧ ys ∈ l2 ∧ xs ∪ ys = l :=
  by
  induction l1
  case nil =>
    unfold all_pairs_alt_alt at h1
    simp only [List.not_mem_nil] at h1
  case cons hd tl ih =>
    unfold all_pairs_alt_alt at h1
    simp only [List.mem_append, List.mem_map] at h1
    cases h1
    case inl h1 =>
      obtain ⟨a, h1⟩ := h1
      apply Exists.intro hd
      apply Exists.intro a
      constructor
      · simp only [List.mem_cons]
        left
        exact trivial
      · exact h1
    case inr h1 =>
      specialize ih h1
      obtain ⟨xs, ys, ih_left, ih_right⟩ := ih
      apply Exists.intro xs
      apply Exists.intro ys
      constructor
      · simp only [List.mem_cons]
        right
        exact ih_left
      · exact ih_right


lemma eq_union_imp_mem_all_pairs_alt_alt
  {α : Type}
  [DecidableEq α]
  (l1 l2 : List (List α))
  (l : List α)
  (h1 : ∃ (xs : List α) (ys : List α), xs ∈ l1 ∧ ys ∈ l2 ∧ xs ∪ ys = l) :
  l ∈ all_pairs_alt_alt List.union l1 l2 :=
  by
  obtain ⟨xs, ys, xs_mem, ys_mem, eq⟩ := h1
  induction l1
  case nil =>
    simp only [List.not_mem_nil] at xs_mem
  case cons l1_hd l1_tl l1_ih =>
    simp only [List.mem_cons] at xs_mem

    unfold all_pairs_alt_alt
    simp only [List.mem_append, List.mem_map]
    cases xs_mem
    case inl xs_mem =>
      left
      apply Exists.intro ys
      constructor
      · exact ys_mem
      · rewrite [← xs_mem]
        exact eq
    case inr xs_mem =>
      right
      apply l1_ih
      exact xs_mem


lemma mem_all_pairs_alt_alt_iff_eq_union
  {α : Type}
  [DecidableEq α]
  (l1 l2 : List (List α))
  (l : List α) :
  l ∈ all_pairs_alt_alt List.union l1 l2 ↔
    ∃ (xs : List α) (ys : List α), xs ∈ l1 ∧ ys ∈ l2 ∧ xs ∪ ys = l :=
  by
  constructor
  · apply mem_all_pairs_alt_alt_imp_eq_union
  · apply eq_union_imp_mem_all_pairs_alt_alt


lemma aux_5
  (F : Formula_)
  (l : List Formula_)
  (P : Formula_)
  (h1 : is_nnf F)
  (h2 : l ∈ pure_dnf F)
  (h3 : P ∈ l) :
  is_constant_ind P ∨ is_literal_ind P :=
  by
  induction F generalizing l
  case false_ =>
    unfold pure_dnf at h2
    simp only [List.mem_singleton] at h2
    rewrite [h2] at h3

    simp only [List.mem_singleton] at h3
    rewrite [h3]

    left
    apply is_constant_ind.rule_1
  case true_ =>
    unfold pure_dnf at h2
    simp only [List.mem_singleton] at h2
    rewrite [h2] at h3

    simp only [List.mem_singleton] at h3
    rewrite [h3]

    left
    apply is_constant_ind.rule_2
  case atom_ X =>
    unfold pure_dnf at h2
    simp only [List.mem_singleton] at h2
    rewrite [h2] at h3

    simp only [List.mem_singleton] at h3
    rewrite [h3]

    right
    apply is_literal_ind.rule_1
  case not_ phi ih =>
    unfold pure_dnf at h2
    simp only [List.mem_singleton] at h2
    rewrite [h2] at h3

    simp only [List.mem_singleton] at h3
    rewrite [h3]

    cases phi
    case atom_ X =>
      right
      apply is_literal_ind.rule_2
    all_goals
      unfold is_nnf at h1
      contradiction
  case and_ phi psi phi_ih psi_ih =>
    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold pure_dnf at h2

    obtain s1 := mem_all_pairs_alt_alt_imp_eq_union (pure_dnf phi) (pure_dnf psi) l h2
    obtain ⟨xs, ys, xs_mem, ys_mem, eq⟩ := s1
    rewrite [← eq] at h3

    simp only [List.mem_union_iff] at h3
    cases h3
    case inl h3 =>
      apply phi_ih xs
      · exact h1_left
      · exact xs_mem
      · exact h3
    case inr h3 =>
      apply psi_ih ys
      · exact h1_right
      · exact ys_mem
      · exact h3
  case or_ phi psi phi_ih psi_ih =>
    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold pure_dnf at h2
    simp only [List.mem_union_iff] at h2

    cases h2
    case inl h2 =>
      apply phi_ih l
      · exact h1_left
      · exact h2
      · exact h3
    case inr h2 =>
      apply psi_ih l
      · exact h1_right
      · exact h2
      · exact h3
  all_goals
    unfold is_nnf at h1
    contradiction


example
  (F : Formula_)
  (h1 : is_nnf F) :
  is_dnf_ind (dnf_list_of_list_to_formula (pure_dnf F)) :=
  by
  cases F
  case false_ =>
    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    simp only [List.map_cons, List.map_nil]
    unfold list_conj
    unfold list_disj
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_3
    apply is_constant_ind.rule_1
  case true_ =>
    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    simp only [List.map_cons, List.map_nil]
    unfold list_conj
    unfold list_disj
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_3
    apply is_constant_ind.rule_2
  case atom_ X =>
    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    simp only [List.map_cons, List.map_nil]
    unfold list_conj
    unfold list_disj
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_4
    apply is_literal_ind.rule_1
  case not_ phi =>
    cases phi
    case atom_ X =>
      unfold pure_dnf
      unfold dnf_list_of_list_to_formula
      simp only [List.map_cons, List.map_nil]
      unfold list_conj
      unfold list_disj
      apply is_dnf_ind.rule_2
      apply is_conj_ind.rule_4
      apply is_literal_ind.rule_2
    all_goals
      unfold is_nnf at h1
      contradiction
  case and_ phi psi =>
    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    apply list_disj_of_is_conj_ind_is_dnf_ind
    intro F a1
    simp only [List.mem_map] at a1
    obtain ⟨l, a1_left, a1_right⟩ := a1
    rewrite [← a1_right]
    apply list_conj_of_is_constant_ind_or_is_literal_ind_is_conj_ind
    intro P a2

    obtain s1 := mem_all_pairs_alt_alt_imp_eq_union (pure_dnf phi) (pure_dnf psi) l a1_left
    obtain ⟨xs, ys, xs_mem, ys_mem, eq⟩ := s1
    rewrite [← eq] at a2
    simp only [List.mem_union_iff] at a2

    cases a2
    case inl a2 =>
      apply aux_5 phi xs
      · exact h1_left
      · exact xs_mem
      · exact a2
    case inr a2 =>
      apply aux_5 psi ys
      · exact h1_right
      · exact ys_mem
      · exact a2
  case or_ phi psi =>
    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    apply list_disj_of_is_conj_ind_is_dnf_ind
    intro F a1
    simp only [List.mem_map, List.mem_union_iff] at a1
    obtain ⟨l, a1_left, a1_right⟩ := a1
    rewrite [← a1_right]
    apply list_conj_of_is_constant_ind_or_is_literal_ind_is_conj_ind
    intro P a2

    cases a1_left
    case inl a1_left =>
      apply aux_5 phi l
      · exact h1_left
      · exact a1_left
      · exact a2
    case inr a1_left =>
      apply aux_5 psi l
      · exact h1_right
      · exact a1_left
      · exact a2
  all_goals
    unfold is_nnf at h1
    contradiction


example
  (V : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : is_nnf F) :
  eval V (dnf_list_of_list_to_formula (pure_dnf F)) = true ↔ eval V F = true :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    simp only [List.map_cons, List.map_nil]
    unfold list_conj
    unfold list_disj
    rfl
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      unfold pure_dnf
      unfold dnf_list_of_list_to_formula
      simp only [List.map_cons, List.map_nil]
      unfold list_conj
      unfold list_disj
      rfl
    all_goals
      unfold is_nnf at h1
      contradiction
  case and_ phi psi phi_ih psi_ih =>
    unfold dnf_list_of_list_to_formula at phi_ih
    unfold dnf_list_of_list_to_formula at psi_ih

    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    specialize phi_ih h1_left
    specialize psi_ih h1_right

    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    simp only [eval]
    simp only [bool_iff_prop_and]
    rewrite [← phi_ih]
    rewrite [← psi_ih]
    simp only [← eval_exists_eq_true_iff_eval_list_disj_eq_true]
    simp only [List.mem_map]
    simp only [mem_all_pairs_alt_alt_iff_eq_union]
    constructor
    · intro a1
      obtain ⟨F, ⟨P, ⟨xs, ys, ⟨xs_mem, ys_mem, eq⟩⟩, a1_left⟩, a1_right⟩ := a1
      rewrite [← a1_left] at a1_right
      rewrite [← eq] at a1_right
      simp only [eval_list_conj_union] at a1_right
      obtain ⟨a1_right_left, a1_right_right⟩ := a1_right
      constructor
      · apply Exists.intro (list_conj xs)
        constructor
        · apply Exists.intro xs
          exact ⟨xs_mem, rfl⟩
        · exact a1_right_left
      · apply Exists.intro (list_conj ys)
        constructor
        · apply Exists.intro ys
          exact ⟨ys_mem, rfl⟩
        · exact a1_right_right
    · intro a1
      obtain ⟨⟨P, ⟨xs, xs_mem, a1_left_left⟩, a1_left_right⟩ , ⟨Q, ⟨ys, ys_mem, a1_right_left⟩, a1_right_right⟩ ⟩ := a1
      rewrite [← a1_left_left] at a1_left_right
      rewrite [← a1_right_left] at a1_right_right
      apply Exists.intro (list_conj (xs ∪ ys))
      constructor
      · apply Exists.intro (xs ∪ ys)
        constructor
        · apply Exists.intro xs
          apply Exists.intro ys
          exact ⟨xs_mem, ys_mem, rfl⟩
        · rfl
      · simp only [eval_list_conj_union]
        exact ⟨a1_left_right, a1_right_right⟩
  case or_ phi psi phi_ih psi_ih =>
    unfold dnf_list_of_list_to_formula at phi_ih
    unfold dnf_list_of_list_to_formula at psi_ih

    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    specialize phi_ih h1_left
    specialize psi_ih h1_right

    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    simp only [eval]
    simp only [bool_iff_prop_or]
    rewrite [← phi_ih]
    rewrite [← psi_ih]
    simp only [← eval_exists_eq_true_iff_eval_list_disj_eq_true]
    simp only [List.mem_map, List.mem_union_iff]
    constructor
    · intro a1
      obtain ⟨F, ⟨l, a1_left_left, a1_left_right⟩, a1_right⟩ := a1
      cases a1_left_left
      case inl a1_left_left =>
        left
        apply Exists.intro F
        constructor
        · apply Exists.intro l
          exact ⟨a1_left_left, a1_left_right⟩
        · exact a1_right
      case inr a1_left_left =>
        right
        apply Exists.intro F
        constructor
        · apply Exists.intro l
          exact ⟨a1_left_left, a1_left_right⟩
        · exact a1_right
    · intro a1
      cases a1
      case inl a1 =>
        obtain ⟨F, ⟨l, a1_left_left, a1_left_right⟩, a1_right⟩ := a1
        apply Exists.intro F
        constructor
        · apply Exists.intro l
          constructor
          · left
            exact a1_left_left
          · exact a1_left_right
        · exact a1_right
      case inr a1 =>
        obtain ⟨F, ⟨l, a1_left_left, a1_left_right⟩, a1_right⟩ := a1
        apply Exists.intro F
        constructor
        · apply Exists.intro l
          constructor
          · right
            exact a1_left_left
          · exact a1_left_right
        · exact a1_right
  all_goals
    unfold is_nnf at h1
    contradiction
