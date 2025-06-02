import HandbookOfPracticalLogicLean.Chapter2.NF.NF
import HandbookOfPracticalLogicLean.Chapter2.NF.ListConj.IsConj
import HandbookOfPracticalLogicLean.Chapter2.NF.ListConj.Semantics


set_option autoImplicit false


open Formula_


/--
  `mk_lits atom_list V` := Returns a formula that is a conjunction of literals that is only satisfied by valuations that map each atom in `atom_list` to the same boolean value as the valuation `V`.
-/
def mk_lits
  (atom_list : List String)
  (V : ValuationAsTotalFunction) :
  Formula_ :=
  let f : String → Formula_ := fun (A : String) =>
    if V A = true
    then atom_ A
    else not_ (atom_ A)
  list_conj (atom_list.map f)


-------------------------------------------------------------------------------


example
  (atom_list : List String)
  (V : ValuationAsTotalFunction) :
  let f : String → Formula_ := fun (A : String) =>
    if V A = true
    then atom_ A
    else not_ (atom_ A)
  ∀ (F : Formula_), F ∈ (atom_list.map f) → eval V F = true :=
  by
  simp only
  intro F a1
  simp only [List.mem_map] at a1
  obtain ⟨A, a1_left, a1_right⟩ := a1
  rewrite [← a1_right]
  split_ifs
  case pos c1 =>
    unfold eval
    exact c1
  case neg c1 =>
    simp only [eval]
    simp only [bool_iff_prop_not]
    exact c1


-------------------------------------------------------------------------------


lemma mk_lits_atom_list
  (atom_list : List String)
  (V : ValuationAsTotalFunction) :
  Formula_.atom_list (mk_lits atom_list V) = atom_list :=
  by
  simp only [mk_lits]
  induction atom_list
  case nil =>
    simp only [List.map_nil]
    unfold list_conj
    unfold atom_list
    rfl
  case cons hd tl ih =>
    cases tl
    case nil =>
      simp only [List.map_cons, List.map_nil]
      unfold list_conj
      split_ifs
      all_goals
        simp only [atom_list]
    case cons tl_hd tl_tl =>
      simp only [List.map_cons] at ih

      simp only [List.map_cons]
      unfold list_conj
      split_ifs
      all_goals
        simp only [atom_list]
        split_ifs at ih
        rewrite [ih]
        simp only [List.singleton_append]


-------------------------------------------------------------------------------


lemma mk_lits_is_conj_ind_v1
  (atom_list : List String)
  (V : ValuationAsTotalFunction) :
  is_conj_ind_v1 (mk_lits atom_list V) :=
  by
  unfold mk_lits
  apply list_conj_of_list_of_is_constant_ind_or_is_literal_ind_is_conj_ind_v1
  intro F a1
  right
  simp only [List.mem_map] at a1
  obtain ⟨A, ⟨a1_left, a1_right⟩⟩ := a1
  split_ifs at a1_right
  case pos c1 =>
    rewrite [← a1_right]
    apply is_literal_ind.rule_1
  case neg c1 =>
    rewrite [← a1_right]
    apply is_literal_ind.rule_2


-------------------------------------------------------------------------------


lemma eval_mk_lits_eq_true_imp_valuations_eq_on_atom_list
  (V_1 V_2 : ValuationAsTotalFunction)
  (atom_list : List String)
  (h1 : eval V_1 (mk_lits atom_list V_2) = true) :
  ∀ (A : String), A ∈ atom_list → V_1 A = V_2 A :=
  by
  simp only [mk_lits] at h1
  simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true] at h1
  simp only [List.mem_map] at h1
  intro A a1
  by_cases c1 : V_2 A = true
  case pos =>
    have s1 : ∃ (B : String), B ∈ atom_list ∧ (if V_2 B = true then atom_ B else not_ (atom_ B)) = atom_ A :=
    by
      apply Exists.intro A
      split_ifs
      exact ⟨a1, rfl⟩

    specialize h1 (atom_ A) s1
    simp only [eval] at h1
    rewrite [c1]
    rewrite [h1]
    rfl
  case neg =>
    have s1 : ∃ (B : String), B ∈ atom_list ∧ (if V_2 B = true then atom_ B else not_ (atom_ B)) = not_ (atom_ A) :=
    by
      apply Exists.intro A
      split_ifs
      exact ⟨a1, rfl⟩

    specialize h1 (not_ (atom_ A)) s1
    simp only [eval] at h1
    simp only [bool_iff_prop_not] at h1

    simp only [Bool.not_eq_true] at c1
    simp only [Bool.not_eq_true] at h1
    rewrite [c1]
    rewrite [h1]
    rfl

  intro A a1
  induction atom_list
  case nil =>
    simp only [List.not_mem_nil] at a1
  case cons hd tl ih =>
    cases tl
    case nil =>
      unfold mk_lits at h1
      simp only [List.map_cons, List.map_nil] at h1
      unfold list_conj at h1

      simp only [List.mem_singleton] at a1
      rewrite [a1]

      split_ifs at h1
      case pos c1 =>
        rewrite [c1]
        unfold eval at h1
        exact h1
      case neg c1 =>
        simp only [Bool.not_eq_true] at c1
        rewrite [c1]

        unfold eval at h1
        simp only [bool_iff_prop_not] at h1
        unfold eval at h1
        simp only [Bool.not_eq_true] at h1
        exact h1
    case cons tl_hd tl_tl =>
      unfold mk_lits at ih
      simp only [List.map_cons, List.mem_cons] at ih

      unfold mk_lits at h1
      simp only [List.map_cons] at h1
      unfold list_conj at h1
      unfold eval at h1
      simp only [bool_iff_prop_and] at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      simp only [List.mem_cons] at a1
      specialize ih h1_right

      cases a1
      case inl a1 =>
        rewrite [a1]
        split_ifs at h1_left
        case pos c1 =>
          rewrite [c1]
          unfold eval at h1_left
          exact h1_left
        case neg c1 =>
          simp only [Bool.not_eq_true] at c1
          rewrite [c1]

          unfold eval at h1_left
          simp only [bool_iff_prop_not] at h1_left
          unfold eval at h1_left
          simp only [Bool.not_eq_true] at h1_left
          exact h1_left
      case inr a1 =>
        apply ih
        exact a1


lemma valuations_eq_on_atom_list_imp_eval_mk_lits_eq_true
  (V_1 V_2 : ValuationAsTotalFunction)
  (atom_list : List String)
  (h1 : ∀ (A : String), A ∈ atom_list → V_1 A = V_2 A) :
  eval V_1 (mk_lits atom_list V_2) = true :=
  by
  induction atom_list
  case nil =>
    unfold mk_lits
    simp only [List.map_nil]
    unfold list_conj
    unfold eval
    rfl
  case cons hd tl ih =>
    cases tl
    case nil =>
      simp only [List.mem_singleton] at h1

      unfold mk_lits
      simp only [List.map_cons, List.map_nil]
      unfold list_conj
      split_ifs
      case pos c1 =>
        rewrite [← c1]
        unfold eval
        apply h1
        rfl
      case neg c1 =>
        unfold eval
        simp only [bool_iff_prop_not]
        unfold eval
        intro contra
        apply c1
        rewrite [← contra]
        rewrite [h1]
        · rfl
        · rfl
    case cons tl_hd tl_tl =>
      unfold mk_lits at ih
      simp only [List.mem_cons, List.map_cons] at ih

      simp only [List.mem_cons] at h1

      unfold mk_lits
      simp only [List.map_cons]
      unfold list_conj
      unfold eval
      simp only [bool_iff_prop_and]
      constructor
      · split_ifs
        case pos c1 =>
          unfold eval
          rewrite [← c1]
          apply h1
          left
          rfl
        case neg c1 =>
          unfold eval
          simp only [bool_iff_prop_not]
          unfold eval
          intro contra
          apply c1
          rewrite [← contra]
          rewrite [h1]
          · rfl
          · left
            rfl
      · apply ih
        intro X a1
        apply h1
        right
        exact a1


lemma eval_mk_lits_eq_true_iff_valuations_eq_on_atom_list
  (V_1 V_2 : ValuationAsTotalFunction)
  (atom_list : List String) :
  eval V_1 (mk_lits atom_list V_2) = true ↔
    ∀ (A : String), A ∈ atom_list → V_1 A = V_2 A :=
  by
  constructor
  · apply eval_mk_lits_eq_true_imp_valuations_eq_on_atom_list
  · apply valuations_eq_on_atom_list_imp_eval_mk_lits_eq_true


-------------------------------------------------------------------------------


theorem eval_of_mk_lits_same_valuation_eq_true
  (V : ValuationAsTotalFunction)
  (atom_list : List String) :
  eval V (mk_lits atom_list V) = true :=
  by
  apply valuations_eq_on_atom_list_imp_eval_mk_lits_eq_true
  intro X a1
  rfl


-------------------------------------------------------------------------------


lemma eq_on_mem_imp_mk_lits_eq
  (V_1 V_2 : ValuationAsTotalFunction)
  (atom_list : List String)
  (h1 : ∀ (A : String), A ∈ atom_list → V_1 A = V_2 A) :
  mk_lits atom_list V_1 = mk_lits atom_list V_2 :=
  by
  unfold mk_lits
  simp only
  congr 1
  simp only [List.map_inj_left]
  intro A a1
  rewrite [h1 A a1]
  rfl


lemma mk_lits_eq_imp_eq_on_mem
  (V_1 V_2 : ValuationAsTotalFunction)
  (atom_list : List String)
  (h1 : mk_lits atom_list V_1 = mk_lits atom_list V_2) :
  ∀ (A : String), A ∈ atom_list → V_1 A = V_2 A :=
  by
  induction atom_list
  case nil =>
    simp only [List.not_mem_nil]
    intro A a1
    contradiction
  case cons hd tl ih =>
    cases tl
    case nil =>
      unfold mk_lits at h1
      simp only [List.map_cons, List.map_nil] at h1
      unfold list_conj at h1

      intro A a1
      simp only [List.mem_singleton] at a1
      rewrite [a1]
      split_ifs at h1
      case pos c1 c2 =>
        rewrite [c1]
        rewrite [c2]
        rfl
      case neg c1 c2 =>
        simp only [Bool.not_eq_true] at c1
        simp only [Bool.not_eq_true] at c2
        rewrite [c1]
        rewrite [c2]
        rfl
    case cons tl_hd tl_tl =>
      unfold mk_lits at ih
      simp only [List.map_cons, List.mem_cons] at ih

      unfold mk_lits at h1
      simp only [List.map_cons] at h1
      unfold list_conj at h1
      simp only [and_.injEq] at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      intro A a1
      simp only [List.mem_cons] at a1
      cases a1
      case inl a1 =>
        rewrite [a1]
        split_ifs at h1_left
        case pos c1 c2 =>
          rewrite [c1]
          rewrite [c2]
          rfl
        case neg c1 c2 =>
          simp only [Bool.not_eq_true] at c1
          simp only [Bool.not_eq_true] at c2
          rewrite [c1]
          rewrite [c2]
          rfl
      case inr a1 =>
        apply ih
        · exact h1_right
        · exact a1


lemma eq_on_mem_iff_mk_lits_eq
  (V_1 V_2 : ValuationAsTotalFunction)
  (atom_list : List String) :
  (∀ (A : String), A ∈ atom_list → V_1 A = V_2 A) ↔
    mk_lits atom_list V_1 = mk_lits atom_list V_2 :=
  by
  constructor
  · apply eq_on_mem_imp_mk_lits_eq
  · apply mk_lits_eq_imp_eq_on_mem


#lint
