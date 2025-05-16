import HandbookOfPracticalLogicLean.Chapter2.NF
import HandbookOfPracticalLogicLean.Chapter2.Semantics


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


lemma list_disj_of_is_conj_ind_v1_is_dnf_ind_v1
  (l : List Formula_)
  (h1 : ∀ (F : Formula_), F ∈ l → is_conj_ind_v1 F) :
  is_dnf_ind_v1 (list_disj l) :=
  by
  induction l
  case nil =>
    unfold list_disj
    apply is_dnf_ind_v1.rule_1
    apply is_conj_ind_v1.rule_1
    exact is_constant_ind.rule_1
  case cons hd tl ih =>
    cases tl
    case nil =>
      unfold list_disj
      apply is_dnf_ind_v1.rule_1
      apply h1
      simp only [List.mem_singleton]
    case cons tl_hd tl_tl =>
      unfold list_disj
      apply is_dnf_ind_v1.rule_2
      · apply h1
        simp only [List.mem_cons]
        left
        exact trivial
      · apply ih
        intro F a1
        apply h1
        simp only [List.mem_cons]
        right
        simp only [List.mem_cons] at a1
        exact a1


example
  (F : Formula_)
  (l : List Formula_)
  (h1 : is_dnf_ind_v1 (list_disj l))
  (h2 : F ∈ l) :
  is_dnf_ind_v1 F :=
  by
  induction l
  case nil =>
    simp only [List.not_mem_nil] at h2
  case cons hd tl ih =>
    simp only [List.mem_cons] at h2

    cases tl
    case nil =>
      simp only [list_disj] at h1

      cases h2
      case inl h2 =>
        rewrite [h2]
        exact h1
      case inr h2 =>
        simp only [List.not_mem_nil] at h2
    case cons tl_hd tl_tl =>
      simp only [list_disj] at h1

      cases h1
      case rule_1 ih_1 =>
        contradiction
      case rule_2 ih_1 ih_2 =>
        cases h2
        case inl h2 =>
          rewrite [h2]
          apply is_dnf_ind_v1.rule_1
          exact ih_1
        case inr h2 =>
          apply ih
          · exact ih_2
          · exact h2


-------------------------------------------------------------------------------


lemma is_dnf_ind_v1_list_disj_cons_left
  (F : Formula_)
  (l : List Formula_)
  (h1 : is_dnf_ind_v1 (list_disj (F :: l))) :
  is_dnf_ind_v1 (list_disj l) :=
  by
  cases l
  case nil =>
    unfold list_disj
    apply is_dnf_ind_v1.rule_1
    apply is_conj_ind_v1.rule_1
    exact is_constant_ind.rule_1
  case cons hd tl =>
    unfold list_disj at h1

    cases h1
    case rule_1 ih_1 =>
      contradiction
    case rule_2 ih_1 ih_2 =>
      exact ih_2


lemma is_dnf_ind_v1_list_disj_cons_right
  (F : Formula_)
  (l : List Formula_)
  (h1 : is_conj_ind_v1 F)
  (h2 : is_dnf_ind_v1 (list_disj l)) :
  is_dnf_ind_v1 (list_disj (F :: l)) :=
  by
  cases l
  case nil =>
    unfold list_disj
    apply is_dnf_ind_v1.rule_1
    exact h1
  case cons hd tl =>
    unfold list_disj
    apply is_dnf_ind_v1.rule_2
    · exact h1
    · exact h2


lemma is_dnf_ind_v1_list_disj_filter
  (l : List Formula_)
  (pred : Formula_ → Bool)
  (h1 : is_dnf_ind_v1 (list_disj l)) :
  is_dnf_ind_v1 (list_disj (List.filter pred l)) :=
  by
  induction l
  case nil =>
    simp only [List.filter_nil]
    exact h1
  case cons hd tl ih =>
    simp only [List.filter_cons]
    split_ifs
    case pos c1 =>
      cases tl
      case nil =>
        simp only [List.filter_nil]
        exact h1
      case cons tl_hd tl_tl =>
        unfold list_disj at h1

        cases h1
        case rule_1 ih_1 =>
          contradiction
        case rule_2 ih_1 ih_2 =>
          apply is_dnf_ind_v1_list_disj_cons_right
          · exact ih_1
          · apply ih
            exact ih_2
    case neg c1 =>
      apply ih
      exact is_dnf_ind_v1_list_disj_cons_left hd tl h1


-------------------------------------------------------------------------------


lemma eval_list_disj_eq_true_imp_exists_eval_eq_true
  (V : ValuationAsTotalFunction)
  (l : List Formula_)
  (h1 : eval V (list_disj l) = true) :
  ∃ (F : Formula_), F ∈ l ∧ eval V F = true :=
  by
  induction l
  case nil =>
    unfold list_disj at h1
    unfold eval at h1

    contradiction
  case cons hd tl ih =>
    cases tl
    case nil =>
      unfold list_disj at h1

      apply Exists.intro hd
      simp only [List.mem_singleton]
      constructor
      · exact trivial
      · exact h1
    case cons tl_hd tl_tl =>
      unfold list_disj at h1
      unfold eval at h1
      simp only [bool_iff_prop_or] at h1

      cases h1
      case inl h1_left =>
        apply Exists.intro hd
        simp only [List.mem_cons]
        constructor
        · left
          exact trivial
        · exact h1_left
      case inr h1_right =>
        specialize ih h1_right
        obtain ⟨F, ⟨ih_left, ih_right⟩⟩ := ih
        simp only [List.mem_cons] at ih_left

        apply Exists.intro F
        simp only [List.mem_cons]
        constructor
        · right
          exact ih_left
        · exact ih_right


lemma exists_eval_eq_true_imp_eval_list_disj_eq_true
  (V : ValuationAsTotalFunction)
  (l : List Formula_)
  (h1 : ∃ (F : Formula_), F ∈ l ∧ eval V F = true) :
  eval V (list_disj l) = true :=
  by
  induction l
  case nil =>
    obtain ⟨F, ⟨h1_left, h1_right⟩⟩ := h1
    simp only [List.not_mem_nil] at h1_left
  case cons hd tl ih =>
    cases tl
    case nil =>
      obtain ⟨F, ⟨h1_left, h1_right⟩⟩ := h1
      simp only [List.mem_singleton] at h1_left

      unfold list_disj
      rewrite [← h1_left]
      exact h1_right
    case cons tl_hd tl_tl =>
      simp only [List.mem_cons] at h1
      obtain ⟨F, ⟨h1_left, h1_right⟩⟩ := h1

      unfold list_disj
      unfold eval
      simp only [bool_iff_prop_or]
      cases h1_left
      case inl h1_left_left =>
        rewrite [← h1_left_left]
        left
        exact h1_right
      case inr h1_left_right =>
        right
        apply ih
        apply Exists.intro F
        simp only [List.mem_cons]
        constructor
        · exact h1_left_right
        · exact h1_right


lemma eval_list_disj_eq_true_iff_exists_eval_eq_true
  (V : ValuationAsTotalFunction)
  (l : List Formula_) :
  eval V (list_disj l) = true ↔ (∃ (F : Formula_), F ∈ l ∧ eval V F = true) :=
  by
  constructor
  · apply eval_list_disj_eq_true_imp_exists_eval_eq_true
  · apply exists_eval_eq_true_imp_eval_list_disj_eq_true


#lint
