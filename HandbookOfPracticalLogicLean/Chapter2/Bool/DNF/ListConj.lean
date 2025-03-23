import MathlibExtraLean.FunctionUpdateFromListOfPairsITE

import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.IsDNF

import Mathlib.Tactic


set_option autoImplicit false


namespace Bool_


open Formula_


def list_conj :
  List Formula_ → Formula_
  | [] => true_
  | [P] => P
  | hd :: tl => and_ hd (list_conj tl)


lemma list_conj_of_is_literal_ind_is_conj_ind
  (l : List Formula_)
  (h1 : ∀ (F : Formula_), F ∈ l → is_literal_ind F) :
  is_conj_ind (list_conj l) :=
  by
  induction l
  case nil =>
    unfold list_conj
    apply is_conj_ind.rule_3
    apply is_constant_ind.rule_2
  case cons hd tl ih =>
    cases tl
    case nil =>
      unfold list_conj
      apply is_conj_ind.rule_4
      apply h1
      simp only [List.mem_singleton]
    case cons tl_hd tl_tl =>
      unfold list_conj
      apply is_conj_ind.rule_2
      · apply h1
        simp only [List.mem_cons]
        left
        exact trivial
      · apply ih
        intro F a1
        simp only [List.mem_cons] at a1
        apply h1
        simp only [List.mem_cons]
        right
        exact a1


lemma list_conj_of_is_constant_ind_or_is_literal_ind_is_conj_ind
  (l : List Formula_)
  (h1 : ∀ (F : Formula_), F ∈ l → (is_constant_ind F ∨ is_literal_ind F)) :
  is_conj_ind (list_conj l) :=
  by
  induction l
  case nil =>
    unfold list_conj
    apply is_conj_ind.rule_3
    apply is_constant_ind.rule_2
  case cons hd tl ih =>
    cases tl
    case nil =>
      unfold list_conj
      simp only [List.mem_singleton] at h1

      have s1 : is_constant_ind hd ∨ is_literal_ind hd :=
      by
        apply h1
        rfl

      cases s1
      case inl s1 =>
        apply is_conj_ind.rule_3
        exact s1
      case inr s1 =>
        apply is_conj_ind.rule_4
        exact s1
    case cons tl_hd tl_tl =>
      simp only [List.mem_cons] at h1

      have s1 : is_constant_ind hd ∨ is_literal_ind hd :=
      by
        apply h1
        left
        rfl

      unfold list_conj
      cases s1
      case inl s1 =>
        apply is_conj_ind.rule_1
        · exact s1
        · apply ih
          intro F a1
          simp only [List.mem_cons] at a1
          apply h1
          right
          exact a1
      case inr s1 =>
        apply is_conj_ind.rule_2
        · exact s1
        · apply ih
          intro F a1
          simp only [List.mem_cons] at a1
          apply h1
          right
          exact a1


lemma eval_all_eq_true_imp_eval_list_conj_eq_true
  (V : ValuationAsTotalFunction)
  (l : List Formula_)
  (h1 : ∀ (F : Formula_), F ∈ l → eval V F = true) :
  eval V (list_conj l) = true :=
  by
  induction l
  case nil =>
    unfold list_conj
    unfold eval
    rfl
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
        exact trivial
      · apply ih
        intro F a1
        apply h1
        simp only [List.mem_cons] at a1
        simp only [List.mem_cons]
        right
        exact a1


lemma eval_list_conj_eq_true_imp_eval_all_eq_true
  (V : ValuationAsTotalFunction)
  (l : List Formula_)
  (h1 : eval V (list_conj l) = true) :
  ∀ (F : Formula_), F ∈ l → eval V F = true :=
  by
  intro F a1
  induction l
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

      simp only [List.mem_cons] at a1
      cases a1
      case inl a1_left =>
        rewrite [a1_left]
        tauto
      case inr a1_right =>
        apply ih
        · tauto
        · simp only [List.mem_cons]
          exact a1_right


lemma eval_all_eq_true_iff_eval_list_conj_eq_true
  (V : ValuationAsTotalFunction)
  (l : List Formula_) :
  (∀ (F : Formula_), F ∈ l → eval V F = true) ↔ eval V (list_conj l) = true :=
  by
  constructor
  · apply eval_all_eq_true_imp_eval_list_conj_eq_true
  · apply eval_list_conj_eq_true_imp_eval_all_eq_true


lemma eval_list_conj_union
  (V : ValuationAsTotalFunction)
  (l1 l2 : List Formula_) :
  eval V (list_conj (l1 ∪ l2)) = true ↔ (eval V (list_conj l1) = true ∧ eval V (list_conj l2) = true) :=
  by
  simp only [← eval_all_eq_true_iff_eval_list_conj_eq_true]
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
