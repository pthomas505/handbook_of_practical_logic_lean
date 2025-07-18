import HandbookOfPracticalLogicLean.Chapter2.NF.ListDisj.ListDisj
import HandbookOfPracticalLogicLean.Chapter2.NF.NF


set_option autoImplicit false


open Formula_


lemma list_disj_of_is_conj_ind_v1_is_dnf_ind_v1
  (FS : List Formula_)
  (h1 : ∀ (F : Formula_), F ∈ FS → is_conj_ind_v1 F) :
  is_dnf_ind_v1 (list_disj FS) :=
  by
  induction FS
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
  (FS : List Formula_)
  (h1 : is_dnf_ind_v1 (list_disj FS))
  (h2 : F ∈ FS) :
  is_dnf_ind_v1 F :=
  by
  induction FS
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


lemma list_disj_cons_is_dnf_ind_v1_imp_list_disj_tail_is_dnf_ind_v1
  (F : Formula_)
  (FS : List Formula_)
  (h1 : is_dnf_ind_v1 (list_disj (F :: FS))) :
  is_dnf_ind_v1 (list_disj FS) :=
  by
  cases FS
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


lemma hd_is_conj_ind_v1_and_list_disj_tail_is_dnf_ind_v1_imp_list_disj_cons_is_dnf_ind_v1
  (F : Formula_)
  (FS : List Formula_)
  (h1 : is_conj_ind_v1 F)
  (h2 : is_dnf_ind_v1 (list_disj FS)) :
  is_dnf_ind_v1 (list_disj (F :: FS)) :=
  by
  cases FS
  case nil =>
    unfold list_disj
    apply is_dnf_ind_v1.rule_1
    exact h1
  case cons hd tl =>
    unfold list_disj
    apply is_dnf_ind_v1.rule_2
    · exact h1
    · exact h2


lemma list_disj_is_dnf_ind_v1_imp_list_disj_of_filter_is_dnf_ind_v1
  (FS : List Formula_)
  (pred : Formula_ → Bool)
  (h1 : is_dnf_ind_v1 (list_disj FS)) :
  is_dnf_ind_v1 (list_disj (List.filter pred FS)) :=
  by
  induction FS
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
          apply hd_is_conj_ind_v1_and_list_disj_tail_is_dnf_ind_v1_imp_list_disj_cons_is_dnf_ind_v1
          · exact ih_1
          · apply ih
            exact ih_2
    case neg c1 =>
      apply ih
      exact list_disj_cons_is_dnf_ind_v1_imp_list_disj_tail_is_dnf_ind_v1 hd tl h1


#lint
