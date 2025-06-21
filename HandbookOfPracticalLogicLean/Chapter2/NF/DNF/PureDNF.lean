import MathlibExtraLean.AllPairs

import HandbookOfPracticalLogicLean.Chapter2.NF.NF
import HandbookOfPracticalLogicLean.Chapter2.NF.DNF.ToDNF
import HandbookOfPracticalLogicLean.Chapter2.NF.ListConj.Semantics
import HandbookOfPracticalLogicLean.Chapter2.NF.ListDisj.Semantics


set_option autoImplicit false


open Formula_


/--
  Helper function for `to_dnf_v3`.
-/
def to_dnf_v3_aux_1 :
  Formula_ → List (List Formula_)
  | and_ p q => all_pairs_v4 List.union (to_dnf_v3_aux_1 p) (to_dnf_v3_aux_1 q)
  | or_ p q => (to_dnf_v3_aux_1 p) ∪ (to_dnf_v3_aux_1 q)
  | F => [[F]]

#eval (to_dnf_v3_aux_1 (Formula_| ((p \/ (q /\ r)) /\ (~p \/ ~ r)))).toString


/--
  Helper function for `to_dnf_v3`.
-/
def to_dnf_v3_aux_2
  (FSS : List (List Formula_)) :
  Formula_ :=
  list_disj (List.map list_conj FSS)


/--
  `to_dnf_v3 F` := Translates the formula `F` to a logically equivalent formula. If `F` is in negation normal form then `to_dnf_v3 F` is in disjunctive normal form.
-/
def to_dnf_v3
  (F : Formula_) :
  Formula_ :=
  to_dnf_v3_aux_2 (to_dnf_v3_aux_1 F)


#eval (to_dnf_v3_aux_2 [[atom_ "P", atom_ "Q"], [not_ (atom_ "P"), atom_ "R"]]).toString


lemma eval_eq_eval_to_dnf_v3
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = true ↔ eval V (to_dnf_v3 F) = true :=
  by
  unfold to_dnf_v3
  induction F
  case and_ phi psi phi_ih psi_ih =>
    unfold to_dnf_v3_aux_2 at phi_ih

    unfold to_dnf_v3_aux_2 at psi_ih

    unfold to_dnf_v3_aux_1
    unfold to_dnf_v3_aux_2
    simp only [eval]
    simp only [bool_iff_prop_and]
    rewrite [phi_ih]
    rewrite [psi_ih]
    simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
    simp only [List.mem_map]
    simp only [mem_all_pairs_v4_union_iff_eq_union]
    constructor
    · intro a1
      obtain ⟨⟨P, ⟨l1, l1_mem, a1_left_left⟩, a1_left_right⟩ , ⟨Q, ⟨l2, l2_mem, a1_right_left⟩, a1_right_right⟩⟩ := a1
      rewrite [← a1_left_left] at a1_left_right
      rewrite [← a1_right_left] at a1_right_right
      apply Exists.intro (list_conj (l1 ∪ l2))
      constructor
      · apply Exists.intro (l1 ∪ l2)
        constructor
        · apply Exists.intro l1
          apply Exists.intro l2
          exact ⟨l1_mem, l2_mem, rfl⟩
        · rfl
      · simp only [eval_list_conj_union]
        exact ⟨a1_left_right, a1_right_right⟩
    · intro a1
      obtain ⟨F, ⟨P, ⟨l1, l2, ⟨l1_mem, l2_mem, eq⟩⟩, a1_left⟩, a1_right⟩ := a1
      rewrite [← a1_left] at a1_right
      rewrite [← eq] at a1_right
      simp only [eval_list_conj_union] at a1_right
      obtain ⟨a1_right_left, a1_right_right⟩ := a1_right
      constructor
      · apply Exists.intro (list_conj l1)
        constructor
        · apply Exists.intro l1
          exact ⟨l1_mem, rfl⟩
        · exact a1_right_left
      · apply Exists.intro (list_conj l2)
        constructor
        · apply Exists.intro l2
          exact ⟨l2_mem, rfl⟩
        · exact a1_right_right
  case or_ phi psi phi_ih psi_ih =>
    unfold to_dnf_v3_aux_2 at phi_ih

    unfold to_dnf_v3_aux_2 at psi_ih

    unfold to_dnf_v3_aux_1
    unfold to_dnf_v3_aux_2
    simp only [eval]
    simp only [bool_iff_prop_or]
    rewrite [phi_ih]
    rewrite [psi_ih]
    simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
    simp only [List.mem_map, List.mem_union_iff]
    constructor
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
  all_goals
    rfl


-------------------------------------------------------------------------------


lemma to_dnf_v3_aux_2_singleton
  (F : Formula_) :
  to_dnf_v3_aux_2 [[F]] = F :=
  by
  unfold to_dnf_v3_aux_2
  simp only [List.map_cons, List.map_nil]
  unfold list_conj
  unfold list_disj
  rfl


lemma mem_list_mem_to_dnf_v3_aux_1_of_nnf_rec_v1_imp_is_constant_or_literal
  (F : Formula_)
  (PS : List Formula_)
  (P : Formula_)
  (h1 : is_nnf_rec_v1 F)
  (h2 : PS ∈ to_dnf_v3_aux_1 F)
  (h3 : P ∈ PS) :
  is_constant_ind P ∨ is_literal_ind P :=
  by
  induction F generalizing PS
  case false_ =>
    unfold to_dnf_v3_aux_1 at h2
    simp only [List.mem_singleton] at h2
    rewrite [h2] at h3

    simp only [List.mem_singleton] at h3
    rewrite [h3]

    left
    apply is_constant_ind.rule_1
  case true_ =>
    unfold to_dnf_v3_aux_1 at h2
    simp only [List.mem_singleton] at h2
    rewrite [h2] at h3

    simp only [List.mem_singleton] at h3
    rewrite [h3]

    left
    apply is_constant_ind.rule_2
  case atom_ X =>
    unfold to_dnf_v3_aux_1 at h2
    simp only [List.mem_singleton] at h2
    rewrite [h2] at h3

    simp only [List.mem_singleton] at h3
    rewrite [h3]

    right
    apply is_literal_ind.rule_1
  case not_ phi ih =>
    unfold to_dnf_v3_aux_1 at h2
    simp only [List.mem_singleton] at h2
    rewrite [h2] at h3

    simp only [List.mem_singleton] at h3
    rewrite [h3]

    cases phi
    case atom_ X =>
      right
      apply is_literal_ind.rule_2
    all_goals
      unfold is_nnf_rec_v1 at h1
      contradiction
  case and_ phi psi phi_ih psi_ih =>
    unfold is_nnf_rec_v1 at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold to_dnf_v3_aux_1 at h2

    obtain s1 := mem_all_pairs_v4_union_imp_eq_union (to_dnf_v3_aux_1 phi) (to_dnf_v3_aux_1 psi) PS h2
    obtain ⟨PS_1, PS_2, PS_1_mem, PS_2_mem, eq⟩ := s1

    rewrite [← eq] at h3
    simp only [List.mem_union_iff] at h3

    cases h3
    case inl h3 =>
      apply phi_ih PS_1
      · exact h1_left
      · exact PS_1_mem
      · exact h3
    case inr h3 =>
      apply psi_ih PS_2
      · exact h1_right
      · exact PS_2_mem
      · exact h3
  case or_ phi psi phi_ih psi_ih =>
    unfold is_nnf_rec_v1 at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold to_dnf_v3_aux_1 at h2
    simp only [List.mem_union_iff] at h2

    cases h2
    case inl h2 =>
      apply phi_ih PS
      · exact h1_left
      · exact h2
      · exact h3
    case inr h2 =>
      apply psi_ih PS
      · exact h1_right
      · exact h2
      · exact h3
  all_goals
    unfold is_nnf_rec_v1 at h1
    contradiction


lemma is_nnf_rec_v1_imp_to_dnf_v3_is_dnf_ind_v1
  (F : Formula_)
  (h1 : is_nnf_rec_v1 F) :
  is_dnf_ind_v1 (to_dnf_v3 F) :=
  by
  cases F
  case false_ =>
    unfold to_dnf_v3
    unfold to_dnf_v3_aux_1
    simp only [to_dnf_v3_aux_2_singleton]
    apply is_dnf_ind_v1.rule_1
    apply is_conj_ind_v1.rule_1
    apply is_constant_ind.rule_1
  case true_ =>
    unfold to_dnf_v3
    unfold to_dnf_v3_aux_1
    simp only [to_dnf_v3_aux_2_singleton]
    apply is_dnf_ind_v1.rule_1
    apply is_conj_ind_v1.rule_1
    apply is_constant_ind.rule_2
  case atom_ X =>
    unfold to_dnf_v3
    unfold to_dnf_v3_aux_1
    simp only [to_dnf_v3_aux_2_singleton]
    apply is_dnf_ind_v1.rule_1
    apply is_conj_ind_v1.rule_2
    apply is_literal_ind.rule_1
  case not_ phi =>
    unfold to_dnf_v3
    unfold to_dnf_v3_aux_1
    simp only [to_dnf_v3_aux_2_singleton]
    cases phi
    case atom_ X =>
      apply is_dnf_ind_v1.rule_1
      apply is_conj_ind_v1.rule_2
      apply is_literal_ind.rule_2
    all_goals
      unfold is_nnf_rec_v1 at h1
      contradiction
  case and_ phi psi =>
    unfold is_nnf_rec_v1 at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    apply list_disj_of_is_conj_ind_v1_is_dnf_ind_v1
    intro F a1
    simp only [List.mem_map] at a1
    obtain ⟨l, a1_left, a1_right⟩ := a1
    rewrite [← a1_right]
    apply list_conj_of_list_of_is_constant_ind_or_is_literal_ind_is_conj_ind_v1
    intro P a2

    obtain s1 := mem_all_pairs_v4_union_imp_eq_union (to_dnf_v3_aux_1 phi) (to_dnf_v3_aux_1 psi) l a1_left
    obtain ⟨l1, l2, l1_mem, l2_mem, eq⟩ := s1
    rewrite [← eq] at a2
    simp only [List.mem_union_iff] at a2

    cases a2
    case inl a2 =>
      apply mem_list_mem_to_dnf_v3_aux_1_of_nnf_rec_v1_imp_is_constant_or_literal phi l1
      · exact h1_left
      · exact l1_mem
      · exact a2
    case inr a2 =>
      apply mem_list_mem_to_dnf_v3_aux_1_of_nnf_rec_v1_imp_is_constant_or_literal psi l2
      · exact h1_right
      · exact l2_mem
      · exact a2
  case or_ phi psi =>
    unfold is_nnf_rec_v1 at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold to_dnf_v3
    unfold to_dnf_v3_aux_1
    unfold to_dnf_v3_aux_2
    apply list_disj_of_is_conj_ind_v1_is_dnf_ind_v1
    intro F a1
    simp only [List.mem_map, List.mem_union_iff] at a1
    obtain ⟨l, a1_left, a1_right⟩ := a1
    rewrite [← a1_right]
    apply list_conj_of_list_of_is_constant_ind_or_is_literal_ind_is_conj_ind_v1
    intro P a2

    cases a1_left
    case inl a1_left =>
      apply mem_list_mem_to_dnf_v3_aux_1_of_nnf_rec_v1_imp_is_constant_or_literal phi l
      · exact h1_left
      · exact a1_left
      · exact a2
    case inr a1_left =>
      apply mem_list_mem_to_dnf_v3_aux_1_of_nnf_rec_v1_imp_is_constant_or_literal psi l
      · exact h1_right
      · exact a1_left
      · exact a2
  all_goals
    unfold is_nnf_rec_v1 at h1
    contradiction


#lint
