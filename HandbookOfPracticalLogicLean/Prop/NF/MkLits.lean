import HandbookOfPracticalLogicLean.Prop.NF.NF
import HandbookOfPracticalLogicLean.Prop.NF.ListConj.IsConj
import HandbookOfPracticalLogicLean.Prop.NF.ListConj.Semantics


set_option autoImplicit false


open Formula_


/--
  `mk_lits var_list V` := Returns a formula in conjunctive normal form that is only satisfied by valuations that map each var in `var_list` to the same boolean value as the valuation `V`.
-/
def mk_lits
  (var_list : List String)
  (V : ValuationAsTotalFunction) :
  Formula_ :=
  let f : String → Formula_ := fun (A : String) =>
    if V A = true
    then var_ A
    else not_ (var_ A)
  list_conj (var_list.map f)


-------------------------------------------------------------------------------


example
  (var_list : List String)
  (V : ValuationAsTotalFunction) :
  let f : String → Formula_ := fun (A : String) =>
    if V A = true
    then var_ A
    else not_ (var_ A)
  ∀ (F : Formula_), F ∈ (var_list.map f) → eval V F = true :=
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


example
  (var_list : List String)
  (V : ValuationAsTotalFunction) :
  Formula_.var_list (mk_lits var_list V) = var_list :=
  by
  simp only [mk_lits]
  induction var_list
  case nil =>
    simp only [List.map_nil]
    unfold list_conj
    unfold var_list
    rfl
  case cons hd tl ih =>
    cases tl
    case nil =>
      simp only [List.map_cons, List.map_nil]
      unfold list_conj
      split_ifs
      case pos c1 =>
        simp only [var_list]
      case neg c1 =>
        simp only [var_list]
    case cons tl_hd tl_tl =>
      simp only [List.map_cons] at ih

      simp only [List.map_cons]
      unfold list_conj
      split_ifs
      all_goals
        simp only [var_list]
        split_ifs at ih
        rewrite [ih]
        simp only [List.singleton_append]


-------------------------------------------------------------------------------


lemma mk_lits_is_conj_ind_v1
  (var_list : List String)
  (V : ValuationAsTotalFunction) :
  is_conj_ind_v1 (mk_lits var_list V) :=
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


lemma eval_mk_lits_eq_true_imp_valuations_eq_on_var_list
  (var_list : List String)
  (V_1 V_2 : ValuationAsTotalFunction)
  (h1 : eval V_1 (mk_lits var_list V_2) = true) :
  ∀ (A : String), A ∈ var_list → V_1 A = V_2 A :=
  by
  simp only [mk_lits] at h1
  simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true] at h1
  simp only [List.mem_map] at h1

  intro A a1
  by_cases c1 : V_2 A = true
  case pos =>
    have s1 : ∃ (B : String), B ∈ var_list ∧ (if V_2 B = true then var_ B else not_ (var_ B)) = var_ A :=
    by
      apply Exists.intro A
      split_ifs
      exact ⟨a1, rfl⟩

    specialize h1 (var_ A) s1
    simp only [eval] at h1
    rewrite [c1]
    rewrite [h1]
    rfl
  case neg =>
    have s1 : ∃ (B : String), B ∈ var_list ∧ (if V_2 B = true then var_ B else not_ (var_ B)) = not_ (var_ A) :=
    by
      apply Exists.intro A
      split_ifs
      exact ⟨a1, rfl⟩

    specialize h1 (not_ (var_ A)) s1
    simp only [eval] at h1
    simp only [bool_iff_prop_not] at h1

    simp only [Bool.not_eq_true] at c1
    simp only [Bool.not_eq_true] at h1
    rewrite [c1]
    rewrite [h1]
    rfl


lemma valuations_eq_on_var_list_imp_eval_mk_lits_eq_true
  (var_list : List String)
  (V_1 V_2 : ValuationAsTotalFunction)
  (h1 : ∀ (A : String), A ∈ var_list → V_1 A = V_2 A) :
  eval V_1 (mk_lits var_list V_2) = true :=
  by
  simp only [mk_lits]
  simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true]
  simp only [List.mem_map]
  intro F a1
  obtain ⟨A, a1_left, a1_right⟩ := a1
  split_ifs at a1_right
  case pos c1 =>
    rewrite [← a1_right]
    unfold eval
    rewrite [h1 A a1_left]
    exact c1
  case neg c1 =>
    rewrite [← a1_right]
    simp only [eval]
    rewrite [h1 A a1_left]
    simp only [bool_iff_prop_not]
    exact c1


lemma eval_mk_lits_eq_true_iff_valuations_eq_on_var_list
  (var_list : List String)
  (V_1 V_2 : ValuationAsTotalFunction) :
  eval V_1 (mk_lits var_list V_2) = true ↔
    ∀ (A : String), A ∈ var_list → V_1 A = V_2 A :=
  by
  constructor
  · apply eval_mk_lits_eq_true_imp_valuations_eq_on_var_list
  · apply valuations_eq_on_var_list_imp_eval_mk_lits_eq_true


-------------------------------------------------------------------------------


theorem eval_of_mk_lits_same_valuation_eq_true
  (var_list : List String)
  (V : ValuationAsTotalFunction) :
  eval V (mk_lits var_list V) = true :=
  by
  apply valuations_eq_on_var_list_imp_eval_mk_lits_eq_true
  intro X a1
  rfl


-------------------------------------------------------------------------------


lemma eq_on_mem_imp_mk_lits_eq
  (var_list : List String)
  (V_1 V_2 : ValuationAsTotalFunction)
  (h1 : ∀ (A : String), A ∈ var_list → V_1 A = V_2 A) :
  mk_lits var_list V_1 = mk_lits var_list V_2 :=
  by
  unfold mk_lits
  simp only
  congr 1
  simp only [List.map_inj_left]
  intro A a1
  rewrite [h1 A a1]
  rfl


lemma mk_lits_eq_imp_eq_on_mem
  (var_list : List String)
  (V_1 V_2 : ValuationAsTotalFunction)
  (h1 : mk_lits var_list V_1 = mk_lits var_list V_2) :
  ∀ (A : String), A ∈ var_list → V_1 A = V_2 A :=
  by
  apply eval_mk_lits_eq_true_imp_valuations_eq_on_var_list
  rewrite [← h1]
  apply eval_of_mk_lits_same_valuation_eq_true


lemma eq_on_mem_iff_mk_lits_eq
  (var_list : List String)
  (V_1 V_2 : ValuationAsTotalFunction) :
  (∀ (A : String), A ∈ var_list → V_1 A = V_2 A) ↔
    mk_lits var_list V_1 = mk_lits var_list V_2 :=
  by
  constructor
  · apply eq_on_mem_imp_mk_lits_eq
  · apply mk_lits_eq_imp_eq_on_mem


#lint
