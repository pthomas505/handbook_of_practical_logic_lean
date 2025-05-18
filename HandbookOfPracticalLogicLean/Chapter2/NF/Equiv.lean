import HandbookOfPracticalLogicLean.Chapter2.NF.ListConj.Semantics


import Mathlib.Tactic


set_option autoImplicit false


open Formula_


example
  (A : Formula_)
  (BS : List Formula_) :
  are_logically_equivalent
    (or_ A (list_conj BS))
    (list_conj (BS.map (fun (B : Formula_) => or_ A B))) :=
  by
  unfold are_logically_equivalent
  unfold is_tautology
  intro V
  unfold satisfies
  simp only [eval]
  simp only [bool_iff_prop_iff]
  simp only [bool_iff_prop_or]
  simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true]
  simp only [List.mem_map]
  constructor
  · intro a1 F a2
    obtain ⟨B, a2_left, a2_right⟩ := a2
    rewrite [← a2_right]
    simp only [eval]
    simp only [bool_iff_prop_or]
    cases a1
    case inl c1 =>
      left
      exact c1
    case inr c1 =>
      right
      apply c1
      exact a2_left
  · intro a1
    by_cases c1 : eval V A = true
    case pos =>
      left
      exact c1
    case neg =>
      right
      intro F a2
      specialize a1 (or_ A F)
      unfold eval at a1
      simp only [bool_iff_prop_or] at a1

      have s1 : eval V A = true ∨ eval V F = true :=
      by
        apply a1
        apply Exists.intro F
        constructor
        · exact a2
        · rfl

      cases s1
      case inl s1 =>
        contradiction
      case inr s1 =>
        exact s1
