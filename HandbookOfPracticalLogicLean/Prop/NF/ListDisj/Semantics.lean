import HandbookOfPracticalLogicLean.Prop.Semantics

import HandbookOfPracticalLogicLean.Prop.NF.ListDisj.ListDisj


set_option autoImplicit false


open Formula_


lemma eval_list_disj_eq_true_imp_exists_eval_eq_true
  (V : ValuationAsTotalFunction)
  (FS : List Formula_)
  (h1 : eval V (list_disj FS) = true) :
  ∃ (F : Formula_), F ∈ FS ∧ eval V F = true :=
  by
  induction FS
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
      case inl h1 =>
        apply Exists.intro hd
        simp only [List.mem_cons]
        constructor
        · left
          exact trivial
        · exact h1
      case inr h1 =>
        specialize ih h1
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
  (FS : List Formula_)
  (h1 : ∃ (F : Formula_), F ∈ FS ∧ eval V F = true) :
  eval V (list_disj FS) = true :=
  by
  induction FS
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
      case inl h1_left =>
        rewrite [← h1_left]
        left
        exact h1_right
      case inr h1_left =>
        right
        apply ih
        apply Exists.intro F
        simp only [List.mem_cons]
        constructor
        · exact h1_left
        · exact h1_right


lemma eval_list_disj_eq_true_iff_exists_eval_eq_true
  (V : ValuationAsTotalFunction)
  (FS : List Formula_) :
  eval V (list_disj FS) = true ↔ (∃ (F : Formula_), F ∈ FS ∧ eval V F = true) :=
  by
  constructor
  · apply eval_list_disj_eq_true_imp_exists_eval_eq_true
  · apply exists_eval_eq_true_imp_eval_list_disj_eq_true


-------------------------------------------------------------------------------


lemma eval_list_disj_union
  (V : ValuationAsTotalFunction)
  (PS QS : List Formula_) :
  eval V (list_disj (PS ∪ QS)) = true ↔ (eval V (list_disj PS) = true ∨ eval V (list_disj QS) = true) :=
  by
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  simp only [List.mem_union_iff]
  constructor
  · intro a1
    obtain ⟨F, ⟨a1_left, a1_right⟩⟩ := a1

    cases a1_left
    case inl a1_left =>
      left
      apply Exists.intro F
      exact ⟨a1_left, a1_right⟩
    case inr a1_left =>
      right
      apply Exists.intro F
      exact ⟨a1_left, a1_right⟩
  · intro a1
    cases a1
    case inl a1 =>
      obtain ⟨F, ⟨a1_left, a1_right⟩⟩ := a1
      apply Exists.intro F
      constructor
      · left
        exact a1_left
      · exact a1_right
    case inr a1 =>
      obtain ⟨F, ⟨a1_left, a1_right⟩⟩ := a1
      apply Exists.intro F
      constructor
      · right
        exact a1_left
      · exact a1_right


lemma eval_list_disj_subset
  (V : ValuationAsTotalFunction)
  (PS QS : List Formula_)
  (h1 : PS ⊆ QS)
  (h2 : eval V (list_disj PS) = true) :
  eval V (list_disj QS) = true :=
  by
  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true] at h2
  obtain ⟨F, ⟨h2_left, h2_right⟩⟩ := h2

  simp only [eval_list_disj_eq_true_iff_exists_eval_eq_true]
  apply Exists.intro F
  constructor
  · exact h1 h2_left
  · exact h2_right


#lint
