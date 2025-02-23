import MathlibExtraLean.FunctionUpdateFromListOfPairsITE

import HandbookOfPracticalLogicLean.Chapter2.Bool.NNF

import Mathlib.Tactic


set_option autoImplicit false


namespace Bool_


open Formula_


inductive is_constant_ind : Formula_ → Prop
| rule_1 :
  is_constant_ind false_

| rule_2 :
  is_constant_ind true_


inductive is_literal_ind : Formula_ → Prop
| rule_1
  (X : String) :
  is_literal_ind (atom_ X)

| rule_2
  (X : String) :
  is_literal_ind (not_ (atom_ X))


inductive is_conj_ind : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_constant_ind phi →
  is_conj_ind psi →
  is_conj_ind (and_ phi psi)

| rule_2
  (phi psi : Formula_) :
  is_literal_ind phi →
  is_conj_ind psi →
  is_conj_ind (and_ phi psi)

| rule_3
  (F : Formula_) :
  is_constant_ind F →
  is_conj_ind F

| rule_4
  (F : Formula_) :
  is_literal_ind F →
  is_conj_ind F


inductive is_dnf_ind : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_conj_ind phi →
  is_dnf_ind psi →
  is_dnf_ind (or_ phi psi)

| rule_2
  (F : Formula_) :
  is_conj_ind F →
  is_dnf_ind F


-------------------------------------------------------------------------------


lemma is_literal_ind_imp_is_literal
  (F : Formula_)
  (h1 : is_literal_ind F) :
  F.is_literal :=
  by
  cases h1
  all_goals
    simp only [is_literal]


lemma is_literal_imp_is_literal_ind
  (F : Formula_)
  (h1 : F.is_literal) :
  is_literal_ind F :=
  by
  cases F
  case atom_ X =>
    apply is_literal_ind.rule_1
  case not_ phi =>
    cases phi
    case atom_ X =>
      apply is_literal_ind.rule_2
    all_goals
      simp only [is_literal] at h1
  all_goals
    simp only [is_literal] at h1


lemma is_literal_ind_iff_is_literal
  (F : Formula_) :
  is_literal_ind F ↔ F.is_literal:=
  by
  constructor
  · intro a1
    exact is_literal_ind_imp_is_literal F a1
  · intro a1
    exact is_literal_imp_is_literal_ind F a1


-------------------------------------------------------------------------------


def Formula_.is_conj_rec_v1 :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | and_ phi psi => phi.is_conj_rec_v1 ∧ psi.is_conj_rec_v1
  | _ => False


instance
  (F : Formula_) :
  Decidable (Formula_.is_conj_rec_v1 F) :=
  by
  induction F
  case not_ phi ih =>
    cases phi
    all_goals
      simp only [is_conj_rec_v1]
      infer_instance
  all_goals
    simp only [is_conj_rec_v1]
    infer_instance


lemma is_conj_rec_v1_imp_is_nnf
  (F : Formula_)
  (h1 : F.is_conj_rec_v1) :
  F.is_nnf :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    simp only [is_nnf]
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      simp only [is_nnf]
    all_goals
      simp only [is_conj_rec_v1] at h1
  case and_ phi psi phi_ih psi_ih =>
    simp only [is_conj_rec_v1] at h1

    simp only [is_nnf]
    tauto
  all_goals
    simp only [is_conj_rec_v1] at h1


-------------------------------------------------------------------------------


def Formula_.is_conj_rec_v2 :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | and_ (false_) psi => psi.is_conj_rec_v2
  | and_ (true_) psi => psi.is_conj_rec_v2
  | and_ (atom_ _) psi => psi.is_conj_rec_v2
  | and_ (not_ (atom_ _)) psi => psi.is_conj_rec_v2
  | _ => False


instance
  (F : Formula_) :
  Decidable (Formula_.is_conj_rec_v2 F) :=
  by
  induction F
  case not_ phi ih =>
    cases phi
    all_goals
      simp only [is_conj_rec_v2]
      infer_instance
  case and_ phi psi phi_ih psi_ih =>
    cases phi
    case not_ phi =>
      cases phi
      all_goals
        simp only [is_conj_rec_v2]
        infer_instance
    all_goals
      simp only [is_conj_rec_v2]
      infer_instance
  all_goals
    simp only [is_conj_rec_v2]
    infer_instance


example
  (F : Formula_)
  (h1 : is_conj_rec_v2 F) :
  is_conj_rec_v1 F :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    simp only [is_conj_rec_v1]
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      simp only [is_conj_rec_v1]
    all_goals
      simp only [is_conj_rec_v2] at h1
  case and_ phi psi phi_ih psi_ih =>
    cases phi
    case false_ | true_ | atom_ X =>
      simp only [is_conj_rec_v2] at h1

      simp only [is_conj_rec_v1]
      tauto
    case not_ phi =>
      cases phi
      case atom_ X =>
        simp only [is_conj_rec_v1]
        simp only [is_conj_rec_v2] at h1
        tauto
      all_goals
        simp only [is_conj_rec_v2] at h1
    all_goals
      simp only [is_conj_rec_v2] at h1
  all_goals
    simp only [is_conj_rec_v2] at h1


lemma is_conj_rec_v2_imp_is_conj_ind
  (F : Formula_)
  (h1 : is_conj_rec_v2 F) :
  is_conj_ind F :=
  by
  induction F
  case false_ =>
    apply is_conj_ind.rule_3
    apply is_constant_ind.rule_1
  case true_ =>
    apply is_conj_ind.rule_3
    apply is_constant_ind.rule_2
  case atom_ X =>
    apply is_conj_ind.rule_4
    apply is_literal_ind.rule_1
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      apply is_conj_ind.rule_4
      apply is_literal_ind.rule_2
    all_goals
      simp only [is_conj_rec_v2] at h1
  case and_ phi psi phi_ih psi_ih =>
    cases phi
    case false_ =>
      simp only [is_conj_rec_v2] at h1
      apply is_conj_ind.rule_1
      · apply is_constant_ind.rule_1
      · apply psi_ih
        exact h1
    case true_ =>
      simp only [is_conj_rec_v2] at h1
      apply is_conj_ind.rule_1
      · apply is_constant_ind.rule_2
      · apply psi_ih
        exact h1
    case atom_ X =>
      simp only [is_conj_rec_v2] at h1
      apply is_conj_ind.rule_2
      · apply is_literal_ind.rule_1
      · apply psi_ih
        exact h1
    case not_ phi =>
      cases phi
      case atom_ X =>
        simp only [is_conj_rec_v2] at h1
        simp only [is_conj_rec_v2] at phi_ih
        apply is_conj_ind.rule_2
        · apply is_literal_ind.rule_2
        · apply psi_ih
          exact h1
      all_goals
        simp only [is_conj_rec_v2] at h1
    all_goals
      simp only [is_conj_rec_v2] at h1
  all_goals
    simp only [is_conj_rec_v2] at h1


lemma is_conj_ind_imp_is_conj_rec_v2
  (F : Formula_)
  (h1 : is_conj_ind F) :
  is_conj_rec_v2 F :=
  by
  induction h1
  case rule_1 phi psi ih_1 ih_2 ih_3 =>
    cases ih_1
    case rule_1 =>
      simp only [is_conj_rec_v2]
      exact ih_3
    case rule_2 =>
      simp only [is_conj_rec_v2]
      exact ih_3
  case rule_2 phi psi ih_1 ih_2 ih_3 =>
    cases ih_1
    case rule_1 X =>
      simp only [is_conj_rec_v2]
      exact ih_3
    case rule_2 X =>
      simp only [is_conj_rec_v2]
      exact ih_3
  case rule_3 phi ih_1 =>
    cases ih_1
    case rule_1 =>
      simp only [is_conj_rec_v2]
    case rule_2 =>
      simp only [is_conj_rec_v2]
  case rule_4 phi ih_1 =>
    cases ih_1
    case rule_1 X =>
      simp only [is_conj_rec_v2]
    case rule_2 X =>
      simp only [is_conj_rec_v2]


lemma is_conj_rec_v2_iff_is_conj_ind
  (F : Formula_) :
  is_conj_rec_v2 F ↔ is_conj_ind F :=
  by
  constructor
  · apply is_conj_rec_v2_imp_is_conj_ind
  · apply is_conj_ind_imp_is_conj_rec_v2


-------------------------------------------------------------------------------


def Formula_.is_dnf_rec :
  Formula_ → Prop
  | or_ phi psi => phi.is_conj_rec_v2 ∧ psi.is_dnf_rec
  | F => is_conj_rec_v2 F


instance
  (F : Formula_) :
  Decidable (Formula_.is_dnf_rec F) :=
  by
  induction F
  all_goals
    simp only [is_dnf_rec]
    infer_instance


lemma is_dnf_rec_imp_is_dnf_ind
  (F : Formula_)
  (h1 : is_dnf_rec F) :
  is_dnf_ind F :=
  by
  induction F
  case false_ =>
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_3
    apply is_constant_ind.rule_1
  case true_ =>
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_3
    apply is_constant_ind.rule_2
  case atom_ X =>
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_4
    apply is_literal_ind.rule_1
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      apply is_dnf_ind.rule_2
      apply is_conj_ind.rule_4
      apply is_literal_ind.rule_2
    all_goals
      simp only [is_dnf_rec] at h1
      simp only [is_conj_rec_v2] at h1
  case or_ phi psi phi_ih psi_ih =>
    unfold is_dnf_rec at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    apply is_dnf_ind.rule_1
    · apply is_conj_rec_v2_imp_is_conj_ind
      exact h1_left
    · apply psi_ih
      exact h1_right
  case and_ phi psi phi_ih psi_ih =>
    unfold is_dnf_rec at h1
    apply is_dnf_ind.rule_2
    apply is_conj_rec_v2_imp_is_conj_ind
    exact h1
  all_goals
    simp only [is_dnf_rec] at h1
    simp only [is_conj_rec_v2] at h1


lemma is_dnf_ind_imp_is_dnf_rec
  (F : Formula_)
  (h1 : is_dnf_ind F) :
  is_dnf_rec F :=
  by
  induction h1
  case rule_1 phi psi ih_1 ih_2 ih_3 =>
    unfold is_dnf_rec
    constructor
    · apply is_conj_ind_imp_is_conj_rec_v2
      exact ih_1
    · exact ih_3
  case rule_2 phi ih_1 =>
    cases ih_1
    case rule_1 phi psi phi_ih psi_ih =>
      unfold is_dnf_rec
      apply is_conj_ind_imp_is_conj_rec_v2
      apply is_conj_ind.rule_1
      · exact phi_ih
      · exact psi_ih
    case rule_2 phi psi phi_ih psi_ih =>
      unfold is_dnf_rec
      apply is_conj_ind_imp_is_conj_rec_v2
      apply is_conj_ind.rule_2
      · exact phi_ih
      · exact psi_ih
    case rule_3 ih =>
      cases ih
      all_goals
        unfold is_dnf_rec
        unfold is_conj_rec_v2
        exact trivial
    case rule_4 ih =>
      cases ih
      all_goals
        unfold is_dnf_rec
        unfold is_conj_rec_v2
        exact trivial


lemma is_dnf_rec_iff_is_dnf_ind
  (F : Formula_) :
  is_dnf_rec F ↔ is_dnf_ind F :=
  by
  constructor
  · apply is_dnf_rec_imp_is_dnf_ind
  · apply is_dnf_ind_imp_is_dnf_rec


-------------------------------------------------------------------------------


def list_conj :
  List Formula_ → Formula_
  | [] => true_
  | [P] => P
  | hd :: tl => and_ hd (list_conj tl)


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


-------------------------------------------------------------------------------


def list_disj :
  List Formula_ → Formula_
  | [] => false_
  | [P] => P
  | hd :: tl => or_ hd (list_disj tl)


lemma eval_exists_eq_true_imp_eval_list_disj_eq_true
  (V : ValuationAsTotalFunction)
  (l : List Formula_)
  (h1 : ∃ (F : Formula_), F ∈ l ∧ eval V F = true) :
  eval V (list_disj l) = true :=
  by
  induction l
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
      case inl h1_left_left =>
        rewrite [← h1_left_left]
        tauto
      case inr h1_left_right =>
        right
        apply ih
        apply Exists.intro F
        simp only [List.mem_cons]
        tauto


lemma eval_list_disj_eq_true_imp_eval_exists_eq_true
  (V : ValuationAsTotalFunction)
  (l : List Formula_)
  (h1 : eval V (list_disj l) = true) :
  ∃ (F : Formula_), F ∈ l ∧ eval V F = true :=
  by
  induction l
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
      tauto
    case cons tl_hd tl_tl =>
      unfold list_disj at h1
      unfold eval at h1
      simp only [bool_iff_prop_or] at h1
      cases h1
      case inl h1_left =>
        apply Exists.intro hd
        simp only [List.mem_cons]
        tauto
      case inr h1_right =>
        specialize ih h1_right
        obtain ⟨F, ⟨ih_left, ih_right⟩⟩ := ih
        simp only [List.mem_cons] at ih_left

        apply Exists.intro F
        simp only [List.mem_cons]
        tauto


lemma eval_exists_eq_true_iff_eval_list_disj_eq_true
  (V : ValuationAsTotalFunction)
  (l : List Formula_) :
  (∃ (F : Formula_), F ∈ l ∧ eval V F = true) ↔ eval V (list_disj l) = true :=
  by
  constructor
  · apply eval_exists_eq_true_imp_eval_list_disj_eq_true
  · apply eval_list_disj_eq_true_imp_eval_exists_eq_true


-------------------------------------------------------------------------------


def Function.toListOfPairs
  {α β : Type}
  [DecidableEq α]
  (f : α → β)
  (l : List α) :
  List (α × β) :=
  l.map (fun (x : α) => (x, f x))


lemma updateFromListOfPairsITE_of_toListOfPairs_mem
  {α β : Type}
  [DecidableEq α]
  [Inhabited β]
  (f : α → β)
  (l : List α)
  (x : α)
  (h1 : x ∈ l) :
  (Function.updateFromListOfPairsITE (fun _ => default) (Function.toListOfPairs f l)) x = f x :=
  by
  induction l
  case nil =>
    simp only [List.not_mem_nil] at h1
  case cons hd tl ih =>
    unfold Function.toListOfPairs at ih

    simp only [List.mem_cons] at h1

    unfold Function.toListOfPairs
    simp only [List.map_cons]
    unfold Function.updateFromListOfPairsITE
    simp only
    unfold Function.updateITE
    split_ifs
    case pos c1 =>
      rewrite [c1]
      rfl
    case neg c1 =>
      apply ih
      tauto


lemma updateFromListOfPairsITE_of_toListOfPairs_not_mem
  {α β : Type}
  [DecidableEq α]
  [Inhabited β]
  (f : α → β)
  (l : List α)
  (x : α)
  (h1 : x ∉ l) :
  (Function.updateFromListOfPairsITE (fun _ => default) (Function.toListOfPairs f l)) x = default :=
  by
  induction l
  case nil =>
    unfold Function.toListOfPairs
    simp only [List.map_nil]
    unfold Function.updateFromListOfPairsITE
    rfl
  case cons hd tl ih =>
    simp only [List.mem_cons] at h1

    unfold Function.toListOfPairs
    simp only [List.map_cons]
    unfold Function.updateFromListOfPairsITE
    simp only
    unfold Function.updateITE
    have s1 : ¬ x = hd ∧ x ∉ tl :=
    by
      tauto
    obtain ⟨s1_left, s1_right⟩ := s1
    split_ifs
    apply ih
    exact s1_right


lemma all_not_mem_are_default_imp_updateFromListOfPairsITE_of_toListOfPairs
  {α β : Type}
  [DecidableEq α]
  [Inhabited β]
  (f : α → β)
  (l : List α)
  (h1 : ∀ x ∉ l, f x = default) :
  (Function.updateFromListOfPairsITE (fun _ => default) (Function.toListOfPairs f l)) = f :=
  by
  funext x
  by_cases c1 : x ∈ l
  case pos =>
    apply updateFromListOfPairsITE_of_toListOfPairs_mem
    exact c1
  case neg =>
    specialize h1 x c1
    rewrite [h1]
    apply updateFromListOfPairsITE_of_toListOfPairs_not_mem
    exact c1


lemma updateFromListOfPairsITE_of_toListOfPairs_imp_all_not_mem_are_default
  {α β : Type}
  [DecidableEq α]
  [Inhabited β]
  (f : α → β)
  (l : List α)
  (h1 : (Function.updateFromListOfPairsITE (fun _ => default) (Function.toListOfPairs f l)) = f) :
  ∀ x ∉ l, f x = default :=
  by
  intro x a1
  rewrite [← h1]
  apply updateFromListOfPairsITE_of_toListOfPairs_not_mem
  exact a1


-------------------------------------------------------------------------------


def ValuationAsListOfPairs : Type := List (String × Bool)
  deriving Inhabited


def gen_all_valuation_as_list_of_pairs :
  List String → List (ValuationAsListOfPairs)
| [] => [[]]
| hd :: tl =>
  let left := List.map (fun (l : ValuationAsListOfPairs) => (hd, false) :: l) (gen_all_valuation_as_list_of_pairs tl)

  let right := List.map (fun (l : ValuationAsListOfPairs) => (hd, true) :: l) (gen_all_valuation_as_list_of_pairs tl)

  left ++ right


def valuation_as_list_of_pairs_to_valuation_as_total_function
  (l : ValuationAsListOfPairs) :
  ValuationAsTotalFunction :=
  Function.updateFromListOfPairsITE (fun _ => default) l


def valuation_as_total_function_to_valuation_as_list_of_pairs
  (V : ValuationAsTotalFunction)
  (atoms : List String) :
  ValuationAsListOfPairs :=
  Function.toListOfPairs V atoms


lemma gen_all_valuation_as_list_of_pairs_is_complete
  (f : String → Bool)
  (xs : List String) :
  Function.toListOfPairs f xs ∈ gen_all_valuation_as_list_of_pairs xs :=
  by
  induction xs
  case nil =>
    unfold gen_all_valuation_as_list_of_pairs
    unfold Function.toListOfPairs
    simp only [List.map_nil, List.mem_singleton]
  case cons hd tl ih =>
    unfold gen_all_valuation_as_list_of_pairs
    unfold Function.toListOfPairs
    simp only [List.map_cons]
    simp only [List.mem_append, List.mem_map]
    cases c1 : f hd
    case false =>
      left
      apply Exists.intro (Function.toListOfPairs f tl)
      constructor
      · exact ih
      · rfl
    case true =>
      right
      apply Exists.intro (Function.toListOfPairs f tl)
      constructor
      · exact ih
      · rfl


-------------------------------------------------------------------------------


def gen_all_valuation_as_total_functions
  (atoms : List String) :
  List ValuationAsTotalFunction :=
  (gen_all_valuation_as_list_of_pairs atoms).map valuation_as_list_of_pairs_to_valuation_as_total_function


lemma gen_all_valuation_as_total_functions_nil :
  gen_all_valuation_as_total_functions [] = [fun _ => default] :=
  by
  unfold gen_all_valuation_as_total_functions
  unfold valuation_as_list_of_pairs_to_valuation_as_total_function
  unfold gen_all_valuation_as_list_of_pairs
  unfold List.map
  simp only [List.map_nil]
  unfold Function.updateFromListOfPairsITE
  rfl


lemma all_not_mem_is_default_imp_mem_gen_all_valuation_as_total_functions
  (V : ValuationAsTotalFunction)
  (atoms : List String)
  (h1 : ∀ (s : String), s ∉ atoms → V s = default) :
  V ∈ gen_all_valuation_as_total_functions atoms :=
  by
  unfold gen_all_valuation_as_total_functions
  simp only [List.mem_map]
  apply Exists.intro (Function.toListOfPairs V atoms)
  constructor
  · apply gen_all_valuation_as_list_of_pairs_is_complete
  · unfold valuation_as_list_of_pairs_to_valuation_as_total_function
    apply all_not_mem_are_default_imp_updateFromListOfPairsITE_of_toListOfPairs
    exact h1


lemma mem_gen_all_valuation_as_total_functions_imp_all_not_mem_is_default
  (V : ValuationAsTotalFunction)
  (atoms : List String)
  (h1 : V ∈ gen_all_valuation_as_total_functions atoms) :
  ∀ (s : String), s ∉ atoms → V s = default :=
  by
  unfold gen_all_valuation_as_total_functions at h1
  simp only [List.mem_map] at h1
  obtain ⟨l, ⟨h1_left, h1_right⟩⟩ := h1

  unfold valuation_as_list_of_pairs_to_valuation_as_total_function at h1_right

  rewrite [← h1_right]

  sorry


-------------------------------------------------------------------------------


def gen_all_satisfying_valuations
  (F : Formula_) :
  List ValuationAsTotalFunction :=
  -- let atoms := List.insertionSort (fun (s1 s2 : String) => s1 < s2) F.atom_list.dedup
  -- let atoms := F.atom_list.dedup
  -- (gen_all_valuation_as_total_functions atoms).filter (fun (V : ValuationAsTotalFunction) => satisfies V F)
  (gen_all_valuation_as_total_functions F.atom_list.dedup).filter (fun (V : ValuationAsTotalFunction) => satisfies V F)


lemma mem_gen_all_satisfying_valuations
  (V : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : ∀ (s : String), s ∉ F.atom_list.dedup → V s = default)
  (h2 : satisfies V F) :
  V ∈ gen_all_satisfying_valuations F :=
  by
  unfold gen_all_satisfying_valuations
  simp only [List.mem_filter]
  simp only [decide_eq_true_eq]
  constructor
  · apply all_not_mem_is_default_imp_mem_gen_all_valuation_as_total_functions
    exact h1
  · exact h2


lemma gen_all_satisfying_valuations_false_ :
  gen_all_satisfying_valuations false_ = [] :=
  by
  unfold gen_all_satisfying_valuations
  unfold satisfies
  simp only [eval]
  simp only [Bool.false_eq_true, decide_false, List.filter_false]


lemma gen_all_satisfying_valuations_true_ :
  gen_all_satisfying_valuations true_ = [fun _ => default] :=
  by
  unfold gen_all_satisfying_valuations
  unfold satisfies
  simp only [eval]
  unfold atom_list
  simp only [List.dedup_nil]
  simp only [gen_all_valuation_as_total_functions_nil]
  simp only [decide_true, List.filter_true]


-------------------------------------------------------------------------------


def mk_lits
  (atoms : List String)
  (V : ValuationAsTotalFunction) :
  Formula_ :=
  let f : String → Formula_ := fun (A : String) =>
    if V A = true
    then atom_ A
    else not_ (atom_ A)
  list_conj (atoms.map f)


lemma mk_lits_nil
  (V : ValuationAsTotalFunction) :
  mk_lits [] V = true_ :=
  by
  unfold mk_lits
  simp only [List.map_nil]
  unfold list_conj
  rfl


lemma mk_lits_is_conj_ind
  (atoms : List String)
  (V : ValuationAsTotalFunction) :
  is_conj_ind (mk_lits atoms V) :=
  by
  induction atoms
  case nil =>
    simp only [mk_lits_nil]
    apply is_conj_ind.rule_3
    exact is_constant_ind.rule_2
  case cons hd tl ih =>
    cases tl
    case nil =>
      simp only [mk_lits]
      simp only [List.map_cons, List.map_nil]
      simp only [list_conj]
      split_ifs
      case pos c1 =>
        apply is_conj_ind.rule_4
        apply is_literal_ind.rule_1
      case neg c1 =>
        apply is_conj_ind.rule_4
        apply is_literal_ind.rule_2
    case cons tl_hd tl_tl =>
      simp only [mk_lits] at ih

      simp only [mk_lits]

      simp only [list_conj]
      apply is_conj_ind.rule_2
      · split_ifs
        case pos c1 =>
          apply is_literal_ind.rule_1
        case neg c1 =>
          apply is_literal_ind.rule_2
      · simp only [List.map_cons] at ih
        apply ih


lemma mem_list_map_mk_lits_is_conj_ind
  (atoms : List String)
  (vs : List ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : F ∈ (List.map (mk_lits atoms) vs)) :
  is_conj_ind F :=
  by
    simp only [List.mem_map] at h1
    obtain ⟨V, h1⟩ := h1
    obtain ⟨h1_left, h1_right⟩ := h1
    rewrite [← h1_right]
    apply mk_lits_is_conj_ind


-------------------------------------------------------------------------------


def to_dnf_v1
  (F : Formula_) :
  Formula_ :=
  -- let atoms := List.insertionSort (fun (s1 s2 : String) => s1 < s2) F.atom_list.dedup
  -- let atoms := F.atom_list.dedup
  -- list_disj ((gen_all_satisfying_valuations F).map (mk_lits atoms))
  list_disj ((gen_all_satisfying_valuations F).map (mk_lits F.atom_list.dedup))


#eval (to_dnf_v1 (Formula_| ((P \/ (Q /\ R)) /\ (~ P \/ ~ R)))).toString


lemma list_disj_of_is_conj_ind_is_dnf_ind
  (xs : List Formula_)
  (h1 : ∀ (F : Formula_), F ∈ xs → is_conj_ind F) :
  is_dnf_ind (list_disj xs) :=
  by
  induction xs
  case nil =>
    unfold list_disj
    apply is_dnf_ind.rule_2 false_
    apply is_conj_ind.rule_3 false_
    exact is_constant_ind.rule_1
  case cons hd tl ih =>
    cases tl
    case nil =>
      unfold list_disj
      apply is_dnf_ind.rule_2 hd
      apply h1
      simp
    case cons tl_hd tl_tl =>
      unfold list_disj
      apply is_dnf_ind.rule_1
      · apply h1
        simp only [List.mem_cons]
        left
        trivial
      · apply ih
        intro F a1
        apply h1
        simp only [List.mem_cons]
        right
        simp only [List.mem_cons] at a1
        exact a1


example
  (F : Formula_) :
  is_dnf_ind (to_dnf_v1 F) :=
  by
  unfold to_dnf_v1
  apply list_disj_of_is_conj_ind_is_dnf_ind
  apply mem_list_map_mk_lits_is_conj_ind


example
  (V : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : satisfies V F) :
  satisfies V (to_dnf_v1 F) :=
  by
  unfold to_dnf_v1
  induction gen_all_satisfying_valuations F
  case nil =>
    simp
    sorry
  case cons hd tl ih =>
    cases tl
    case nil =>
      simp at ih
      simp only [list_disj] at ih
      unfold satisfies at ih
      unfold eval at ih
      contradiction
    case cons tl_hd tl_tl =>
      simp only [List.map_cons] at ih
      simp only [mk_lits] at ih
      unfold satisfies at ih

      simp only [List.map_cons]
      simp only [list_disj]
      unfold satisfies
      unfold eval
      simp only [bool_iff_prop_or]
      simp only [mk_lits]
      right
      exact ih
