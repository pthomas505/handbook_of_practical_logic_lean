import MathlibExtraLean.AllPairs

import HandbookOfPracticalLogicLean.Chapter2.NF.NF
import HandbookOfPracticalLogicLean.Chapter2.NF.ListOfListsTo
import HandbookOfPracticalLogicLean.Chapter2.NF.DNF.ToDNF_1
import HandbookOfPracticalLogicLean.Chapter2.NF.ListConj.Semantics
import HandbookOfPracticalLogicLean.Chapter2.NF.ListDisj.Semantics


set_option autoImplicit false


open Formula_


/--
  Helper function for `to_dnf_v3`.
-/
def to_dnf_v3_aux :
  Formula_ → List (List Formula_)
  | and_ p q => all_pairs_v4 List.union (to_dnf_v3_aux p) (to_dnf_v3_aux q)
  | or_ p q => (to_dnf_v3_aux p) ∪ (to_dnf_v3_aux q)
  | F => [[F]]

#eval (to_dnf_v3_aux (Formula_| ((p \/ (q /\ r)) /\ (~ p \/ ~ r)))).toString


/--
  `to_dnf_v3 F` := Translates the formula `F` to a logically equivalent formula. If `F` is in negation normal form then `to_dnf_v3 F` is in disjunctive normal form.
-/
def to_dnf_v3
  (F : Formula_) :
  Formula_ :=
  list_of_lists_to_disjunction_of_conjunctions (to_dnf_v3_aux F)


#eval (list_of_lists_to_disjunction_of_conjunctions [[atom_ "P", atom_ "Q"], [not_ (atom_ "P"), atom_ "R"]]).toString


lemma eval_eq_eval_to_dnf_v3_aux
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = true ↔ eval V (list_of_lists_to_disjunction_of_conjunctions (to_dnf_v3_aux F)) = true :=
  by
  induction F
  case and_ phi psi phi_ih psi_ih =>
    unfold list_of_lists_to_disjunction_of_conjunctions at phi_ih

    unfold list_of_lists_to_disjunction_of_conjunctions at psi_ih

    unfold to_dnf_v3_aux
    unfold list_of_lists_to_disjunction_of_conjunctions
    simp only [eval]
    simp only [bool_iff_prop_and]
    rewrite [phi_ih]
    rewrite [psi_ih]
    simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
    simp only [List.mem_map]
    simp only [mem_all_pairs_v4_union_iff_eq_union]
    constructor
    · intro a1
      obtain ⟨⟨P, ⟨PS, PS_mem, a1_left_left⟩, a1_left_right⟩, ⟨Q, ⟨QS, QS_mem, a1_right_left⟩, a1_right_right⟩⟩ := a1
      rewrite [← a1_left_left] at a1_left_right
      rewrite [← a1_right_left] at a1_right_right
      apply Exists.intro (list_conj (PS ∪ QS))
      constructor
      · apply Exists.intro (PS ∪ QS)
        constructor
        · apply Exists.intro PS
          apply Exists.intro QS
          exact ⟨PS_mem, QS_mem, rfl⟩
        · rfl
      · simp only [eval_list_conj_union]
        exact ⟨a1_left_right, a1_right_right⟩
    · intro a1
      obtain ⟨F, ⟨FS, ⟨PS, QS, ⟨PS_mem, QS_mem, eq⟩⟩, a1_left⟩, a1_right⟩ := a1
      rewrite [← a1_left] at a1_right
      rewrite [← eq] at a1_right
      simp only [eval_list_conj_union] at a1_right
      obtain ⟨a1_right_left, a1_right_right⟩ := a1_right
      constructor
      · apply Exists.intro (list_conj PS)
        constructor
        · apply Exists.intro PS
          exact ⟨PS_mem, rfl⟩
        · exact a1_right_left
      · apply Exists.intro (list_conj QS)
        constructor
        · apply Exists.intro QS
          exact ⟨QS_mem, rfl⟩
        · exact a1_right_right
  case or_ phi psi phi_ih psi_ih =>
    unfold list_of_lists_to_disjunction_of_conjunctions at phi_ih

    unfold list_of_lists_to_disjunction_of_conjunctions at psi_ih

    unfold to_dnf_v3_aux
    unfold list_of_lists_to_disjunction_of_conjunctions
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
        obtain ⟨F, ⟨FS, a1_left_left, a1_left_right⟩, a1_right⟩ := a1
        apply Exists.intro F
        constructor
        · apply Exists.intro FS
          constructor
          · left
            exact a1_left_left
          · exact a1_left_right
        · exact a1_right
      case inr a1 =>
        obtain ⟨F, ⟨FS, a1_left_left, a1_left_right⟩, a1_right⟩ := a1
        apply Exists.intro F
        constructor
        · apply Exists.intro FS
          constructor
          · right
            exact a1_left_left
          · exact a1_left_right
        · exact a1_right
    · intro a1
      obtain ⟨F, ⟨FS, a1_left_left, a1_left_right⟩, a1_right⟩ := a1
      cases a1_left_left
      case inl a1_left_left =>
        left
        apply Exists.intro F
        constructor
        · apply Exists.intro FS
          exact ⟨a1_left_left, a1_left_right⟩
        · exact a1_right
      case inr a1_left_left =>
        right
        apply Exists.intro F
        constructor
        · apply Exists.intro FS
          exact ⟨a1_left_left, a1_left_right⟩
        · exact a1_right
  all_goals
    rfl


lemma eval_eq_eval_to_dnf_v3
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = true ↔ eval V (to_dnf_v3 F) = true :=
  by
  unfold to_dnf_v3
  apply eval_eq_eval_to_dnf_v3_aux


-------------------------------------------------------------------------------


lemma list_of_lists_to_disjunction_of_conjunctions_singleton
  (F : Formula_) :
  list_of_lists_to_disjunction_of_conjunctions [[F]] = F :=
  by
  unfold list_of_lists_to_disjunction_of_conjunctions
  simp only [List.map_cons, List.map_nil]
  unfold list_conj
  unfold list_disj
  rfl


lemma mem_list_mem_to_dnf_v3_aux_of_nnf_rec_v1_imp_is_constant_or_literal
  (F : Formula_)
  (FS : List Formula_)
  (F_mem : Formula_)
  (h1 : is_nnf_rec_v1 F)
  (h2 : FS ∈ to_dnf_v3_aux F)
  (h3 : F_mem ∈ FS) :
  is_constant_ind F_mem ∨ is_literal_ind F_mem :=
  by
  induction F generalizing FS
  case false_ =>
    unfold to_dnf_v3_aux at h2
    simp only [List.mem_singleton] at h2
    rewrite [h2] at h3

    simp only [List.mem_singleton] at h3
    rewrite [h3]

    left
    apply is_constant_ind.rule_1
  case true_ =>
    unfold to_dnf_v3_aux at h2
    simp only [List.mem_singleton] at h2
    rewrite [h2] at h3

    simp only [List.mem_singleton] at h3
    rewrite [h3]

    left
    apply is_constant_ind.rule_2
  case atom_ X =>
    unfold to_dnf_v3_aux at h2
    simp only [List.mem_singleton] at h2
    rewrite [h2] at h3

    simp only [List.mem_singleton] at h3
    rewrite [h3]

    right
    apply is_literal_ind.rule_1
  case not_ phi ih =>
    unfold to_dnf_v3_aux at h2
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

    unfold to_dnf_v3_aux at h2

    obtain s1 := mem_all_pairs_v4_union_imp_eq_union (to_dnf_v3_aux phi) (to_dnf_v3_aux psi) FS h2
    obtain ⟨PS, QS, PS_mem, QS_mem, eq⟩ := s1

    rewrite [← eq] at h3
    simp only [List.mem_union_iff] at h3

    cases h3
    case inl h3 =>
      apply phi_ih PS
      · exact h1_left
      · exact PS_mem
      · exact h3
    case inr h3 =>
      apply psi_ih QS
      · exact h1_right
      · exact QS_mem
      · exact h3
  case or_ phi psi phi_ih psi_ih =>
    unfold is_nnf_rec_v1 at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold to_dnf_v3_aux at h2
    simp only [List.mem_union_iff] at h2

    cases h2
    case inl h2 =>
      apply phi_ih FS
      · exact h1_left
      · exact h2
      · exact h3
    case inr h2 =>
      apply psi_ih FS
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
    unfold to_dnf_v3_aux
    simp only [list_of_lists_to_disjunction_of_conjunctions_singleton]
    apply is_dnf_ind_v1.rule_1
    apply is_conj_ind_v1.rule_1
    apply is_constant_ind.rule_1
  case true_ =>
    unfold to_dnf_v3
    unfold to_dnf_v3_aux
    simp only [list_of_lists_to_disjunction_of_conjunctions_singleton]
    apply is_dnf_ind_v1.rule_1
    apply is_conj_ind_v1.rule_1
    apply is_constant_ind.rule_2
  case atom_ X =>
    unfold to_dnf_v3
    unfold to_dnf_v3_aux
    simp only [list_of_lists_to_disjunction_of_conjunctions_singleton]
    apply is_dnf_ind_v1.rule_1
    apply is_conj_ind_v1.rule_2
    apply is_literal_ind.rule_1
  case not_ phi =>
    unfold to_dnf_v3
    unfold to_dnf_v3_aux
    simp only [list_of_lists_to_disjunction_of_conjunctions_singleton]
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
    obtain ⟨FS, a1_left, a1_right⟩ := a1
    rewrite [← a1_right]
    apply list_conj_of_list_of_is_constant_ind_or_is_literal_ind_is_conj_ind_v1
    intro P a2

    obtain s1 := mem_all_pairs_v4_union_imp_eq_union (to_dnf_v3_aux phi) (to_dnf_v3_aux psi) FS a1_left
    obtain ⟨PS, QS, PS_mem, QS_mem, eq⟩ := s1
    rewrite [← eq] at a2
    simp only [List.mem_union_iff] at a2

    cases a2
    case inl a2 =>
      apply mem_list_mem_to_dnf_v3_aux_of_nnf_rec_v1_imp_is_constant_or_literal phi PS
      · exact h1_left
      · exact PS_mem
      · exact a2
    case inr a2 =>
      apply mem_list_mem_to_dnf_v3_aux_of_nnf_rec_v1_imp_is_constant_or_literal psi QS
      · exact h1_right
      · exact QS_mem
      · exact a2
  case or_ phi psi =>
    unfold is_nnf_rec_v1 at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold to_dnf_v3
    unfold to_dnf_v3_aux
    unfold list_of_lists_to_disjunction_of_conjunctions
    apply list_disj_of_is_conj_ind_v1_is_dnf_ind_v1
    intro F a1
    simp only [List.mem_map, List.mem_union_iff] at a1
    obtain ⟨FS, a1_left, a1_right⟩ := a1
    rewrite [← a1_right]
    apply list_conj_of_list_of_is_constant_ind_or_is_literal_ind_is_conj_ind_v1
    intro P a2

    cases a1_left
    case inl a1_left =>
      apply mem_list_mem_to_dnf_v3_aux_of_nnf_rec_v1_imp_is_constant_or_literal phi FS
      · exact h1_left
      · exact a1_left
      · exact a2
    case inr a1_left =>
      apply mem_list_mem_to_dnf_v3_aux_of_nnf_rec_v1_imp_is_constant_or_literal psi FS
      · exact h1_right
      · exact a1_left
      · exact a2
  all_goals
    unfold is_nnf_rec_v1 at h1
    contradiction


#lint
