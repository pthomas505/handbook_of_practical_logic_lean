import HandbookOfPracticalLogicLean.Prop.Semantics

import HandbookOfPracticalLogicLean.Prop.NF.ListConj.ListConj


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


open Formula_


theorem eval_list_conj_eq_true_imp_forall_eval_eq_true
  (σ : ValuationAsTotalFunction)
  (FS : List Formula_)
  (h1 : eval σ (list_conj FS) = true) :
  ∀ (F : Formula_), F ∈ FS → eval σ F = true :=
  by
  intro F a1
  induction FS
  case nil =>
    simp only [List.not_mem_nil] at a1
  case cons hd tl ih =>
    cases tl
    case nil =>
      unfold list_conj at h1

      simp only [List.mem_singleton] at a1
      rewrite [a1]
      exact h1
    case cons tl_hd tl_tl =>
      unfold list_conj at h1
      unfold eval at h1
      simp only [bool_iff_prop_and] at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      simp only [List.mem_cons] at a1
      cases a1
      case inl a1 =>
        rewrite [a1]
        exact h1_left
      case inr a1 =>
        apply ih
        · exact h1_right
        · simp only [List.mem_cons]
          exact a1


theorem forall_eval_eq_true_imp_eval_list_conj_eq_true
  (σ : ValuationAsTotalFunction)
  (FS : List Formula_)
  (h1 : ∀ (F : Formula_), F ∈ FS → eval σ F = true) :
  eval σ (list_conj FS) = true :=
  by
  induction FS
  case nil =>
    unfold list_conj
    unfold eval
    apply Eq.refl
  case cons hd tl ih =>
    cases tl
    case nil =>
      unfold list_conj
      apply h1
      simp only [List.mem_singleton]
    case cons tl_hd tl_tl =>
      unfold list_conj
      unfold eval
      simp only [bool_iff_prop_and]
      constructor
      · apply h1
        simp only [List.mem_cons]
        left
        exact True.intro
      · apply ih
        intro F a1
        apply h1
        simp only [List.mem_cons] at a1
        simp only [List.mem_cons]
        right
        exact a1


theorem eval_list_conj_eq_true_iff_forall_eval_eq_true
  (σ : ValuationAsTotalFunction)
  (FS : List Formula_) :
  eval σ (list_conj FS) = true ↔ (∀ (F : Formula_), F ∈ FS → eval σ F = true) :=
  by
  constructor
  · apply eval_list_conj_eq_true_imp_forall_eval_eq_true
  · apply forall_eval_eq_true_imp_eval_list_conj_eq_true


-------------------------------------------------------------------------------


theorem eval_list_conj_union
  (σ : ValuationAsTotalFunction)
  (PS QS : List Formula_) :
  eval σ (list_conj (PS ∪ QS)) = true ↔
    (eval σ (list_conj PS) = true ∧ eval σ (list_conj QS) = true) :=
  by
  simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true]
  simp only [List.mem_union_iff]
  constructor
  · intro a1
    constructor
    · intro F a2
      apply a1
      left
      exact a2
    · intro F a2
      apply a1
      right
      exact a2
  · intro a1 F a2
    obtain ⟨a1_left, a1_right⟩ := a1
    cases a2
    case inl a2 =>
      apply a1_left
      exact a2
    case inr a2 =>
      apply a1_right
      exact a2


theorem eval_list_conj_subset
  (σ : ValuationAsTotalFunction)
  (PS QS : List Formula_)
  (h1 : PS ⊆ QS)
  (h2 : eval σ (list_conj QS) = true) :
  eval σ (list_conj PS) = true :=
  by
  simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true] at h2

  simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true]
  intro F a1
  apply h2
  exact h1 a1


#lint
