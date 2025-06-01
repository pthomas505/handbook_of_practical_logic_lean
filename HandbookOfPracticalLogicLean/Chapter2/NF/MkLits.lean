import HandbookOfPracticalLogicLean.Chapter2.NF.NF
import HandbookOfPracticalLogicLean.Chapter2.NF.ListConj.IsConj


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
  obtain ⟨X, ⟨a1_left, a1_right⟩⟩ := a1
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
      case inl a1_left =>
        rewrite [a1_left]
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
      case inr a1_right =>
        apply ih
        exact a1_right


lemma valuations_eq_on_atom_list_imp_eval_mk_lits_eq_true
  (V_1 V_2 : ValuationAsTotalFunction)
  (atom_list : List String)
  (h1 : ∀ (X : String), X ∈ atom_list → V_1 X = V_2 X) :
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
    ∀ (X : String), X ∈ atom_list → V_1 X = V_2 X :=
  by
  constructor
  · apply eval_mk_lits_eq_true_imp_valuations_eq_on_atom_list
  · apply valuations_eq_on_atom_list_imp_eval_mk_lits_eq_true


-------------------------------------------------------------------------------


theorem eval_of_mk_lits_with_same_valuation_eq_true
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
  (h1 : ∀ (X : String), X ∈ atom_list → V_1 X = V_2 X) :
  mk_lits atom_list V_1 = mk_lits atom_list V_2 :=
  by
  unfold mk_lits
  simp only
  congr! 1
  simp only [List.map_inj_left]
  intro X a1
  rewrite [h1 X a1]
  rfl


lemma mk_lits_eq_imp_eq_on_mem
  (V_1 V_2 : ValuationAsTotalFunction)
  (atom_list : List String)
  (h1 : mk_lits atom_list V_1 = mk_lits atom_list V_2) :
  ∀ (X : String), X ∈ atom_list → V_1 X = V_2 X :=
  by
  induction atom_list
  case nil =>
    simp only [List.not_mem_nil]
    intro X a1
    contradiction
  case cons hd tl ih =>
    cases tl
    case nil =>
      unfold mk_lits at h1
      simp only [List.map_cons, List.map_nil] at h1
      unfold list_conj at h1

      intro X a1
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

      intro X a1
      simp only [List.mem_cons] at a1
      cases a1
      case inl c1 =>
        rewrite [c1]
        split_ifs at h1_left
        case pos c2 c3 =>
          rewrite [c2]
          rewrite [c3]
          rfl
        case neg c2 c3 =>
          simp only [Bool.not_eq_true] at c2
          simp only [Bool.not_eq_true] at c3
          rewrite [c2]
          rewrite [c3]
          rfl
      case inr c1 =>
        apply ih
        · exact h1_right
        · exact c1


lemma eq_on_mem_iff_mk_lits_eq
  (V_1 V_2 : ValuationAsTotalFunction)
  (atom_list : List String) :
  (∀ (X : String), X ∈ atom_list → V_1 X = V_2 X) ↔
    mk_lits atom_list V_1 = mk_lits atom_list V_2 :=
  by
  constructor
  · apply eq_on_mem_imp_mk_lits_eq
  · apply mk_lits_eq_imp_eq_on_mem


#lint
