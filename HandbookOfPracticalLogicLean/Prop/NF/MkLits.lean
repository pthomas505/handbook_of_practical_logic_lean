import HandbookOfPracticalLogicLean.Prop.NF.NF
import HandbookOfPracticalLogicLean.Prop.NF.ListConj.IsConj
import HandbookOfPracticalLogicLean.Prop.NF.ListConj.Semantics


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


open Formula_


/--
  `mk_lits var_list σ` := Returns a formula in conjunctive normal form that is only satisfied by valuations that map each variable in `var_list` to the same boolean value as the valuation `σ`.
-/
@[nolint defsWithUnderscore]
def mk_lits
  (var_list : List String)
  (σ : ValuationAsTotalFunction) :
  Formula_ :=
  let f : String → Formula_ := fun (V : String) =>
    if σ V = true
    then var_ V
    else not_ (var_ V)
  list_conj (var_list.map f)


-------------------------------------------------------------------------------


example
  (var_list : List String)
  (σ : ValuationAsTotalFunction) :
  let f : String → Formula_ := fun (V : String) =>
    if σ V = true
    then var_ V
    else not_ (var_ V)
  ∀ (F : Formula_), F ∈ (var_list.map f) → eval σ F = true :=
  by
  simp only
  intro F a1
  simp only [List.mem_map] at a1
  obtain ⟨V, a1_left, a1_right⟩ := a1
  rewrite [← a1_right]
  split
  case isTrue c1 =>
    unfold eval
    exact c1
  case isFalse c1 =>
    simp only [eval]
    simp only [bool_iff_prop_not]
    exact c1


-------------------------------------------------------------------------------


example
  (var_list : List String)
  (σ : ValuationAsTotalFunction) :
  Formula_.var_list (mk_lits var_list σ) = var_list :=
  by
  simp only [mk_lits]
  induction var_list
  case nil =>
    simp only [List.map_nil]
    unfold list_conj
    unfold var_list
    apply Eq.refl
  case cons hd tl ih =>
    cases tl
    case nil =>
      simp only [List.map_cons, List.map_nil]
      unfold list_conj
      split
      case isTrue c1 =>
        simp only [var_list]
      case isFalse c1 =>
        simp only [var_list]
    case cons tl_hd tl_tl =>
      simp only [List.map_cons] at ih

      simp only [List.map_cons]
      unfold list_conj
      split
      case isTrue c1 =>
        split
        case isTrue c2 =>
          simp only [var_list]
          split at ih
          case isTrue c3 =>
            rewrite [ih]
            exact List.singleton_append
          case isFalse c3 =>
            contradiction
        case isFalse c2 =>
          simp only [var_list]
          split at ih
          case isTrue c3 =>
            contradiction
          case isFalse c3 =>
            rewrite [ih]
            exact List.singleton_append
      case isFalse c1 =>
        split
        case isTrue c2 =>
          simp only [var_list]
          split at ih
          case isTrue c3 =>
            rewrite [ih]
            exact List.singleton_append
          case isFalse c3 =>
            contradiction
        case isFalse c2 =>
          simp only [var_list]
          split at ih
          case isTrue c3 =>
            contradiction
          case isFalse c3 =>
            rewrite [ih]
            exact List.singleton_append


-------------------------------------------------------------------------------


theorem mk_lits_is_conj_ind_v1
  (var_list : List String)
  (σ : ValuationAsTotalFunction) :
  is_conj_ind_v1 (mk_lits var_list σ) :=
  by
  unfold mk_lits
  apply list_conj_of_list_of_is_constant_ind_or_is_literal_ind_is_conj_ind_v1
  intro F a1
  right
  simp only [List.mem_map] at a1
  obtain ⟨V, ⟨a1_left, a1_right⟩⟩ := a1
  split at a1_right
  case isTrue c1 =>
    rewrite [← a1_right]
    apply is_literal_ind.rule_1
  case isFalse c1 =>
    rewrite [← a1_right]
    apply is_literal_ind.rule_2


-------------------------------------------------------------------------------


theorem eval_mk_lits_eq_true_imp_valuations_eq_on_var_list
  (var_list : List String)
  (σ_1 σ_2 : ValuationAsTotalFunction)
  (h1 : eval σ_1 (mk_lits var_list σ_2) = true) :
  ∀ (V : String), V ∈ var_list → σ_1 V = σ_2 V :=
  by
  simp only [mk_lits] at h1
  simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true] at h1
  simp only [List.mem_map] at h1

  intro V a1
  by_cases c1 : σ_2 V = true
  · have s1 : ∃ (U : String), U ∈ var_list ∧ (if σ_2 U = true then var_ U else not_ (var_ U)) = var_ V :=
    by
      apply Exists.intro V
      split
      case isTrue c2 =>
        exact ⟨a1, rfl⟩
      case isFalse c2 =>
        contradiction

    specialize h1 (var_ V) s1
    simp only [eval] at h1
    rewrite [c1]
    rewrite [h1]
    apply Eq.refl
  · have s1 : ∃ (U : String), U ∈ var_list ∧ (if σ_2 U = true then var_ U else not_ (var_ U)) = not_ (var_ V) :=
    by
      apply Exists.intro V
      split
      case isTrue c2 =>
        contradiction
      case isFalse c2 =>
        exact ⟨a1, rfl⟩

    specialize h1 (not_ (var_ V)) s1
    simp only [eval] at h1
    simp only [bool_iff_prop_not] at h1

    simp only [Bool.not_eq_true] at c1
    simp only [Bool.not_eq_true] at h1
    rewrite [c1]
    rewrite [h1]
    apply Eq.refl


theorem valuations_eq_on_var_list_imp_eval_mk_lits_eq_true
  (var_list : List String)
  (σ_1 σ_2 : ValuationAsTotalFunction)
  (h1 : ∀ (A : String), A ∈ var_list → σ_1 A = σ_2 A) :
  eval σ_1 (mk_lits var_list σ_2) = true :=
  by
  simp only [mk_lits]
  simp only [eval_list_conj_eq_true_iff_forall_eval_eq_true]
  simp only [List.mem_map]
  intro F a1
  obtain ⟨V, a1_left, a1_right⟩ := a1
  split at a1_right
  case isTrue c1 =>
    rewrite [← a1_right]
    unfold eval
    rewrite [h1 V a1_left]
    exact c1
  case isFalse c1 =>
    rewrite [← a1_right]
    simp only [eval]
    rewrite [h1 V a1_left]
    simp only [bool_iff_prop_not]
    exact c1


theorem eval_mk_lits_eq_true_iff_valuations_eq_on_var_list
  (var_list : List String)
  (σ_1 σ_2 : ValuationAsTotalFunction) :
  eval σ_1 (mk_lits var_list σ_2) = true ↔
    ∀ (V : String), V ∈ var_list → σ_1 V = σ_2 V :=
  by
  constructor
  · apply eval_mk_lits_eq_true_imp_valuations_eq_on_var_list
  · apply valuations_eq_on_var_list_imp_eval_mk_lits_eq_true


-------------------------------------------------------------------------------


theorem eval_of_mk_lits_same_valuation_eq_true
  (var_list : List String)
  (σ : ValuationAsTotalFunction) :
  eval σ (mk_lits var_list σ) = true :=
  by
  apply valuations_eq_on_var_list_imp_eval_mk_lits_eq_true
  intro V a1
  apply Eq.refl


-------------------------------------------------------------------------------


theorem eq_on_mem_imp_mk_lits_eq
  (var_list : List String)
  (σ_1 σ_2 : ValuationAsTotalFunction)
  (h1 : ∀ (V : String), V ∈ var_list → σ_1 V = σ_2 V) :
  mk_lits var_list σ_1 = mk_lits var_list σ_2 :=
  by
  unfold mk_lits
  simp only
  congr 1
  simp only [List.map_inj_left]
  intro V a1
  rewrite [h1 V a1]
  apply Eq.refl


theorem mk_lits_eq_imp_eq_on_mem
  (var_list : List String)
  (σ_1 σ_2 : ValuationAsTotalFunction)
  (h1 : mk_lits var_list σ_1 = mk_lits var_list σ_2) :
  ∀ (V : String), V ∈ var_list → σ_1 V = σ_2 V :=
  by
  apply eval_mk_lits_eq_true_imp_valuations_eq_on_var_list
  rewrite [← h1]
  apply eval_of_mk_lits_same_valuation_eq_true


theorem eq_on_mem_iff_mk_lits_eq
  (var_list : List String)
  (σ_1 σ_2 : ValuationAsTotalFunction) :
  (∀ (V : String), V ∈ var_list → σ_1 V = σ_2 V) ↔
    mk_lits var_list σ_1 = mk_lits var_list σ_2 :=
  by
  constructor
  · apply eq_on_mem_imp_mk_lits_eq
  · apply mk_lits_eq_imp_eq_on_mem


#lint
