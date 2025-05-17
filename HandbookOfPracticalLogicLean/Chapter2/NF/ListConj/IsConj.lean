import HandbookOfPracticalLogicLean.Chapter2.NF.ListConj.ListConj
import HandbookOfPracticalLogicLean.Chapter2.NF.NF


set_option autoImplicit false


open Formula_


lemma list_conj_of_list_of_is_constant_ind_or_is_literal_ind_is_conj_ind_v1
  (l : List Formula_)
  (h1 : ∀ (F : Formula_), F ∈ l → (is_constant_ind F ∨ is_literal_ind F)) :
  is_conj_ind_v1 (list_conj l) :=
  by
  induction l
  case nil =>
    unfold list_conj
    apply is_conj_ind_v1.rule_1
    apply is_constant_ind.rule_2
  case cons hd tl ih =>
    cases tl
    case nil =>
      simp only [List.mem_singleton] at h1

      unfold list_conj

      have s1 : is_constant_ind hd ∨ is_literal_ind hd :=
      by
        apply h1
        rfl

      cases s1
      case inl s1 =>
        apply is_conj_ind_v1.rule_1
        exact s1
      case inr s1 =>
        apply is_conj_ind_v1.rule_2
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
        apply is_conj_ind_v1.rule_3
        · exact s1
        · apply ih
          intro F a1
          simp only [List.mem_cons] at a1
          apply h1
          right
          exact a1
      case inr s1 =>
        apply is_conj_ind_v1.rule_4
        · exact s1
        · apply ih
          intro F a1
          simp only [List.mem_cons] at a1
          apply h1
          right
          exact a1


example
  (F : Formula_)
  (l : List Formula_)
  (h1 : is_conj_ind_v1 (list_conj l))
  (h2 : F ∈ l) :
  is_conj_ind_v1 F :=
  by
  induction l
  case nil =>
    simp only [List.not_mem_nil] at h2
  case cons hd tl ih =>
    simp only [List.mem_cons] at h2

    cases tl
    case nil =>
      simp only [list_conj] at h1

      cases h2
      case inl h2 =>
        rewrite [h2]
        exact h1
      case inr h2 =>
        simp only [List.not_mem_nil] at h2
    case cons tl_hd tl_tl =>
      simp only [list_conj] at h1

      cases h1
      case rule_1 ih_1 | rule_2 ih_1 =>
        contradiction
      case rule_3 ih_1 ih_2 =>
        cases h2
        case inl h2 =>
          rewrite [h2]
          apply is_conj_ind_v1.rule_1
          exact ih_1
        case inr h2 =>
          apply ih
          · exact ih_2
          · exact h2
      case rule_4 ih_1 ih_2 =>
        cases h2
        case inl h2 =>
          rewrite [h2]
          apply is_conj_ind_v1.rule_2
          exact ih_1
        case inr h2 =>
          apply ih
          · exact ih_2
          · exact h2


#lint
