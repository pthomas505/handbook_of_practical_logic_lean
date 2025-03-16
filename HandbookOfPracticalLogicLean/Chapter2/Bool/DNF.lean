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


def Formula_.is_conj_rec :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | and_ (false_) psi => psi.is_conj_rec
  | and_ (true_) psi => psi.is_conj_rec
  | and_ (atom_ _) psi => psi.is_conj_rec
  | and_ (not_ (atom_ _)) psi => psi.is_conj_rec
  | _ => False


instance
  (F : Formula_) :
  Decidable (Formula_.is_conj_rec F) :=
  by
  induction F
  case not_ phi ih =>
    cases phi
    all_goals
      simp only [is_conj_rec]
      infer_instance
  case and_ phi psi phi_ih psi_ih =>
    cases phi
    case not_ phi =>
      cases phi
      all_goals
        simp only [is_conj_rec]
        infer_instance
    all_goals
      simp only [is_conj_rec]
      infer_instance
  all_goals
    simp only [is_conj_rec]
    infer_instance


lemma is_conj_rec_imp_is_nnf
  (F : Formula_)
  (h1 : F.is_conj_rec) :
  F.is_nnf :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold is_nnf
    exact trivial
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      unfold is_nnf
      exact trivial
    all_goals
      unfold is_conj_rec at h1
      contradiction
  case and_ phi psi phi_ih psi_ih =>
    unfold is_nnf
    cases phi
    case false_ | true_ | atom_ X =>
      unfold is_conj_rec at h1
      constructor
      · unfold is_nnf
        exact trivial
      · apply psi_ih
        exact h1
    case not_ phi =>
      cases phi
      case atom_ X =>
        unfold is_conj_rec at h1
        constructor
        · unfold is_nnf
          exact trivial
        · apply psi_ih
          exact h1
      all_goals
        unfold is_conj_rec at h1
        contradiction
    all_goals
      unfold is_conj_rec at h1
      contradiction
  all_goals
    unfold is_conj_rec at h1
    contradiction


lemma is_conj_rec_imp_is_conj_ind
  (F : Formula_)
  (h1 : is_conj_rec F) :
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
      simp only [is_conj_rec] at h1
  case and_ phi psi phi_ih psi_ih =>
    cases phi
    case false_ =>
      simp only [is_conj_rec] at h1
      apply is_conj_ind.rule_1
      · apply is_constant_ind.rule_1
      · apply psi_ih
        exact h1
    case true_ =>
      simp only [is_conj_rec] at h1
      apply is_conj_ind.rule_1
      · apply is_constant_ind.rule_2
      · apply psi_ih
        exact h1
    case atom_ X =>
      simp only [is_conj_rec] at h1
      apply is_conj_ind.rule_2
      · apply is_literal_ind.rule_1
      · apply psi_ih
        exact h1
    case not_ phi =>
      cases phi
      case atom_ X =>
        simp only [is_conj_rec] at h1
        simp only [is_conj_rec] at phi_ih
        apply is_conj_ind.rule_2
        · apply is_literal_ind.rule_2
        · apply psi_ih
          exact h1
      all_goals
        simp only [is_conj_rec] at h1
    all_goals
      simp only [is_conj_rec] at h1
  all_goals
    simp only [is_conj_rec] at h1


lemma is_conj_ind_imp_is_conj_rec
  (F : Formula_)
  (h1 : is_conj_ind F) :
  is_conj_rec F :=
  by
  induction h1
  case rule_1 phi psi ih_1 ih_2 ih_3 =>
    cases ih_1
    case rule_1 =>
      simp only [is_conj_rec]
      exact ih_3
    case rule_2 =>
      simp only [is_conj_rec]
      exact ih_3
  case rule_2 phi psi ih_1 ih_2 ih_3 =>
    cases ih_1
    case rule_1 X =>
      simp only [is_conj_rec]
      exact ih_3
    case rule_2 X =>
      simp only [is_conj_rec]
      exact ih_3
  case rule_3 phi ih_1 =>
    cases ih_1
    case rule_1 =>
      simp only [is_conj_rec]
    case rule_2 =>
      simp only [is_conj_rec]
  case rule_4 phi ih_1 =>
    cases ih_1
    case rule_1 X =>
      simp only [is_conj_rec]
    case rule_2 X =>
      simp only [is_conj_rec]


lemma is_conj_rec_iff_is_conj_ind
  (F : Formula_) :
  is_conj_rec F ↔ is_conj_ind F :=
  by
  constructor
  · apply is_conj_rec_imp_is_conj_ind
  · apply is_conj_ind_imp_is_conj_rec


-------------------------------------------------------------------------------


def Formula_.is_dnf_rec :
  Formula_ → Prop
  | or_ phi psi => phi.is_conj_rec ∧ psi.is_dnf_rec
  | F => is_conj_rec F


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
      simp only [is_conj_rec] at h1
  case or_ phi psi phi_ih psi_ih =>
    unfold is_dnf_rec at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    apply is_dnf_ind.rule_1
    · apply is_conj_rec_imp_is_conj_ind
      exact h1_left
    · apply psi_ih
      exact h1_right
  case and_ phi psi phi_ih psi_ih =>
    unfold is_dnf_rec at h1
    apply is_dnf_ind.rule_2
    apply is_conj_rec_imp_is_conj_ind
    exact h1
  all_goals
    simp only [is_dnf_rec] at h1
    simp only [is_conj_rec] at h1


lemma is_dnf_ind_imp_is_dnf_rec
  (F : Formula_)
  (h1 : is_dnf_ind F) :
  is_dnf_rec F :=
  by
  induction h1
  case rule_1 phi psi ih_1 ih_2 ih_3 =>
    unfold is_dnf_rec
    constructor
    · apply is_conj_ind_imp_is_conj_rec
      exact ih_1
    · exact ih_3
  case rule_2 phi ih_1 =>
    cases ih_1
    case rule_1 phi psi phi_ih psi_ih =>
      unfold is_dnf_rec
      apply is_conj_ind_imp_is_conj_rec
      apply is_conj_ind.rule_1
      · exact phi_ih
      · exact psi_ih
    case rule_2 phi psi phi_ih psi_ih =>
      unfold is_dnf_rec
      apply is_conj_ind_imp_is_conj_rec
      apply is_conj_ind.rule_2
      · exact phi_ih
      · exact psi_ih
    case rule_3 ih =>
      cases ih
      all_goals
        unfold is_dnf_rec
        unfold is_conj_rec
        exact trivial
    case rule_4 ih =>
      cases ih
      all_goals
        unfold is_dnf_rec
        unfold is_conj_rec
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


def mk_lits
  (atoms : List String)
  (V : ValuationAsTotalFunction) :
  Formula_ :=
  let f : String → Formula_ := fun (A : String) =>
    if V A = true
    then atom_ A
    else not_ (atom_ A)
  list_conj (atoms.map f)


lemma mk_lits_is_conj_ind
  (atoms : List String)
  (V : ValuationAsTotalFunction) :
  is_conj_ind (mk_lits atoms V) :=
  by
  unfold mk_lits
  apply list_conj_of_is_literal_ind_is_conj_ind
  intro F a1
  simp only [List.mem_map] at a1
  obtain ⟨X, ⟨a1_left, a1_right⟩⟩ := a1
  split_ifs at a1_right
  case pos c1 =>
    rewrite [← a1_right]
    apply is_literal_ind.rule_1
  case neg c1 =>
    rewrite [← a1_right]
    apply is_literal_ind.rule_2


lemma eval_mk_lits_eq_true_imp_valuations_eq_on_atom_list
  (V_1 V_2 : ValuationAsTotalFunction)
  (atom_list : List String)
  (h1 : eval V_1 (mk_lits atom_list V_2) = true) :
  ∀ (X : String), X ∈ atom_list → V_1 X = V_2 X :=
  by
  intro X a1
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


theorem eval_mk_lits_eq_true
  (V : ValuationAsTotalFunction)
  (atom_list : List String) :
  eval V (mk_lits atom_list V) = true :=
  by
  apply valuations_eq_on_atom_list_imp_eval_mk_lits_eq_true
  intro X a1
  rfl


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


example
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


-------------------------------------------------------------------------------


def list_disj :
  List Formula_ → Formula_
  | [] => false_
  | [P] => P
  | hd :: tl => or_ hd (list_disj tl)


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


def ValuationAsListOfPairs : Type := List (String × Bool)
  deriving Inhabited


def gen_all_valuations_as_list_of_list_of_pairs :
  List String → List (ValuationAsListOfPairs)
| [] => [[]]
| hd :: tl =>
  let left := List.map (fun (l : ValuationAsListOfPairs) => (hd, false) :: l) (gen_all_valuations_as_list_of_list_of_pairs tl)

  let right := List.map (fun (l : ValuationAsListOfPairs) => (hd, true) :: l) (gen_all_valuations_as_list_of_list_of_pairs tl)

  left ++ right


def gen_all_valuations_as_list_of_total_functions
  (init : ValuationAsTotalFunction) :
  List String → List (ValuationAsTotalFunction)
| [] => [init]
| hd :: tl =>
  let left := List.map (fun (V : ValuationAsTotalFunction) => Function.updateITE V hd false) (gen_all_valuations_as_list_of_total_functions init tl)

  let right := List.map (fun (V : ValuationAsTotalFunction) => Function.updateITE V hd true) (gen_all_valuations_as_list_of_total_functions init tl)

  left ++ right


-------------------------------------------------------------------------------


lemma gen_all_valuations_as_list_of_list_of_pairs_is_complete
  (atom_list : List String)
  (f : String → Bool) :
  Function.toListOfPairs atom_list f ∈ gen_all_valuations_as_list_of_list_of_pairs atom_list :=
  by
  induction atom_list
  case nil =>
    unfold Function.toListOfPairs
    unfold gen_all_valuations_as_list_of_list_of_pairs
    simp only [List.map_nil, List.mem_singleton]
  case cons hd tl ih =>
    unfold Function.toListOfPairs at ih

    unfold Function.toListOfPairs
    unfold gen_all_valuations_as_list_of_list_of_pairs
    simp only [List.map_cons, List.mem_append, List.mem_map, List.cons.injEq, Prod.mk.injEq]
    cases f hd
    case false =>
      left
      apply Exists.intro (List.map (fun x => (x, f x)) tl)
      constructor
      · exact ih
      · constructor
        · constructor
          · exact trivial
          · rfl
        · rfl
    case true =>
      right
      apply Exists.intro (List.map (fun x => (x, f x)) tl)
      constructor
      · exact ih
      · constructor
        · constructor
          · exact trivial
          · rfl
        · rfl


lemma gen_all_valuations_as_list_of_total_functions_is_complete
  (init : String → Bool)
  (atom_list : List String)
  (V : ValuationAsTotalFunction)
  (h1 : ∀ (X : String), X ∉ atom_list → V X = init X) :
  V ∈ gen_all_valuations_as_list_of_total_functions init atom_list :=
  by
  induction atom_list generalizing V
  case nil =>
    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.mem_singleton]
    funext X
    apply h1
    simp only [List.not_mem_nil]
    intro contra
    exact contra
  case cons hd tl ih =>
    simp only [List.mem_cons, not_or] at h1

    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.mem_append, List.mem_map]
    cases c1 : V hd
    case false =>
      left
      apply Exists.intro (fun (X : String) => if X ∈ tl then V X else init X)
      constructor
      · apply ih
        intro X a2
        split_ifs
        rfl
      · funext X
        unfold Function.updateITE
        split_ifs
        case pos c2 =>
          rewrite [← c1]
          rewrite [c2]
          rfl
        case neg c2 =>
          simp only
          split_ifs
          case pos c3 =>
            rfl
          case neg c3 =>
            rewrite [h1]
            · rfl
            · exact ⟨c2, c3⟩
    case true =>
      right
      apply Exists.intro (fun (X : String) => if X ∈ tl then V X else init X)
      constructor
      · apply ih
        intro X a2
        split_ifs
        rfl
      · funext X
        unfold Function.updateITE
        split_ifs
        case pos c2 =>
          rewrite [← c1]
          rewrite [c2]
          rfl
        case neg c2 =>
          simp only
          split_ifs
          case pos c3 =>
            rfl
          case neg c3 =>
            rewrite [h1]
            · rfl
            · exact ⟨c2, c3⟩


-------------------------------------------------------------------------------


lemma gen_all_valuations_as_list_of_total_functions_length_pos
  (init : String → Bool)
  (atom_list : List String) :
  0 < (gen_all_valuations_as_list_of_total_functions init atom_list).length :=
  by
  induction atom_list
  case nil =>
    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.length_singleton]
    exact Nat.one_pos
  case cons hd tl ih =>
    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.length_append, List.length_map]
    apply Nat.add_pos_left
    exact ih


lemma gen_all_valuations_as_list_of_total_functions_length_cons
  (init : String → Bool)
  (X : String)
  (atom_list : List String) :
  (gen_all_valuations_as_list_of_total_functions init atom_list).length < (gen_all_valuations_as_list_of_total_functions init (X :: atom_list)).length :=
  by
  conv => right; unfold gen_all_valuations_as_list_of_total_functions
  simp only [List.length_append, List.length_map]
  apply Nat.lt_add_of_pos_left
  apply gen_all_valuations_as_list_of_total_functions_length_pos


lemma gen_all_valuations_as_list_of_total_functions_length_eq
  (init_1 init_2 : String → Bool)
  (atom_list : List String) :
  (gen_all_valuations_as_list_of_total_functions init_1 atom_list).length = (gen_all_valuations_as_list_of_total_functions init_2 atom_list).length :=
  by
  induction atom_list
  case nil =>
    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.length_singleton]
  case cons hd tl ih =>
    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.length_append, List.length_map]
    rewrite [ih]
    rfl


-------------------------------------------------------------------------------


def valuation_as_list_of_pairs_to_valuation_as_total_function
  (init : ValuationAsTotalFunction)
  (l : ValuationAsListOfPairs) :
  ValuationAsTotalFunction :=
  Function.updateFromListOfPairsITE init l


def valuation_as_total_function_to_valuation_as_list_of_pairs
  (atom_list : List String)
  (V : ValuationAsTotalFunction) :
  ValuationAsListOfPairs :=
  Function.toListOfPairs atom_list V


-------------------------------------------------------------------------------


example
  (init : ValuationAsTotalFunction)
  (atom_list : List String) :
  (gen_all_valuations_as_list_of_list_of_pairs atom_list).map (valuation_as_list_of_pairs_to_valuation_as_total_function init) = gen_all_valuations_as_list_of_total_functions init atom_list :=
  by
  induction atom_list
  case nil =>
    unfold gen_all_valuations_as_list_of_list_of_pairs
    simp only [List.map_cons, List.map_nil]
    unfold valuation_as_list_of_pairs_to_valuation_as_total_function
    unfold Function.updateFromListOfPairsITE
    unfold gen_all_valuations_as_list_of_total_functions
    rfl
  case cons hd tl ih =>
    unfold valuation_as_list_of_pairs_to_valuation_as_total_function at ih

    unfold gen_all_valuations_as_list_of_list_of_pairs
    simp only [List.map_append, List.map_map]
    unfold valuation_as_list_of_pairs_to_valuation_as_total_function
    unfold gen_all_valuations_as_list_of_total_functions
    simp only
    congr 1
    all_goals
      rewrite [← ih]
      simp only [List.map_map, List.map_inj_left, Function.comp_apply]
      intro l a1
      funext X
      unfold Function.updateITE
      split_ifs
      case pos c1 =>
        unfold Function.updateFromListOfPairsITE
        simp only
        unfold Function.updateITE
        split_ifs
        rfl
      case neg c1 =>
        conv => left; unfold Function.updateFromListOfPairsITE
        simp only
        unfold Function.updateITE
        split_ifs
        rfl


example
  (init : ValuationAsTotalFunction)
  (atom_list : List String)
  (h1 : atom_list.Nodup) :
  (gen_all_valuations_as_list_of_total_functions init atom_list).map (valuation_as_total_function_to_valuation_as_list_of_pairs atom_list) = gen_all_valuations_as_list_of_list_of_pairs atom_list :=
  by
  induction atom_list
  case nil =>
    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.map_cons, List.map_nil]
    unfold valuation_as_total_function_to_valuation_as_list_of_pairs
    unfold Function.toListOfPairs
    simp only [List.map_nil]
    unfold gen_all_valuations_as_list_of_list_of_pairs
    rfl
  case cons hd tl ih =>
    unfold valuation_as_total_function_to_valuation_as_list_of_pairs at ih

    simp only [List.nodup_cons] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold gen_all_valuations_as_list_of_total_functions
    simp only [List.map_append, List.map_map]
    unfold valuation_as_total_function_to_valuation_as_list_of_pairs
    unfold gen_all_valuations_as_list_of_list_of_pairs
    simp only
    congr 1
    all_goals
      rewrite [← ih h1_right]
      simp only [List.map_map, List.map_inj_left, Function.comp_apply]
      intro V a1
      unfold Function.toListOfPairs
      simp only [List.map_cons]
      congr! 1
      · unfold Function.updateITE
        simp only [if_pos]
      · simp only [List.map_inj_left]
        intro X a2
        simp only [Prod.mk.injEq]
        constructor
        · exact trivial
        · unfold Function.updateITE
          split_ifs
          case pos c1 =>
            rewrite [c1] at a2
            contradiction
          case neg c1 =>
            rfl


-------------------------------------------------------------------------------


lemma gen_all_valuations_as_list_of_total_functions_eq_on_atom_list
  (init_1 init_2 : ValuationAsTotalFunction)
  (atom_list : List String)
  (p : ValuationAsTotalFunction × ValuationAsTotalFunction)
  (X : String)
  (h1 : p ∈ List.zip
    (gen_all_valuations_as_list_of_total_functions init_1 atom_list)
    (gen_all_valuations_as_list_of_total_functions init_2 atom_list))
  (h2 : X ∈ atom_list) :
  p.1 X = p.2 X :=
  by
  induction atom_list generalizing p
  case nil =>
    simp only [List.not_mem_nil] at h2
  case cons hd tl ih =>
    simp only [List.mem_cons] at h2

    unfold gen_all_valuations_as_list_of_total_functions at h1
    simp only at h1

    rewrite [List.zip_append] at h1
    · simp only [List.mem_append] at h1

      cases h2
      case inl h2 =>
        cases h1
        case inl h1 | inr h1 =>
          obtain s1 := List.of_mem_zip h1
          obtain ⟨s1_left, s1_right⟩ := s1

          simp only [List.mem_map] at s1_left
          obtain ⟨V_1, ⟨s1_left_left, s1_left_right⟩⟩ := s1_left

          simp only [List.mem_map] at s1_right
          obtain ⟨V_2, ⟨s1_right_left, s1_right_right⟩⟩ := s1_right

          rewrite [← s1_left_right]
          rewrite [← s1_right_right]
          unfold Function.updateITE
          split_ifs
          rfl
      case inr h2 =>
        cases h1
        case inl h1 | inr h1 =>
          simp only [List.zip_map] at h1
          simp only [List.mem_map, Prod.exists, Prod.map_apply] at h1
          obtain ⟨a, b, ⟨h1_left, h1_right⟩⟩ := h1
          rewrite [← h1_right]
          simp only
          unfold Function.updateITE
          split_ifs
          case pos c1 =>
            rfl
          case neg c1 =>
            specialize ih (a, b)
            simp only at ih
            apply ih
            · exact h1_left
            · exact h2
    · simp only [List.length_map]
      apply gen_all_valuations_as_list_of_total_functions_length_eq


lemma mem_zip_gen_all_valuations_as_list_of_total_functions_imp_eval_eq
  (init_1 init_2 : ValuationAsTotalFunction)
  (F : Formula_)
  (p : ValuationAsTotalFunction × ValuationAsTotalFunction)
  (h1 : p ∈ List.zip
    (gen_all_valuations_as_list_of_total_functions init_1 F.atom_list.dedup)
    (gen_all_valuations_as_list_of_total_functions init_2 F.atom_list.dedup)) :
  eval p.1 F = eval p.2 F :=
  by
  apply theorem_2_2
  intro X a1
  apply gen_all_valuations_as_list_of_total_functions_eq_on_atom_list init_1 init_2 F.atom_list.dedup
  · exact h1
  · simp only [List.mem_dedup]
    rewrite [← atom_occurs_in_iff_mem_atom_list]
    exact a1


-------------------------------------------------------------------------------


def gen_all_satisfying_valuations_as_list_of_total_functions
  (init : ValuationAsTotalFunction)
  (F : Formula_) :
  List ValuationAsTotalFunction :=
  (gen_all_valuations_as_list_of_total_functions init F.atom_list.dedup).filter (fun (V : ValuationAsTotalFunction) => eval V F = true)


-------------------------------------------------------------------------------


def to_dnf
  (init : ValuationAsTotalFunction)
  (F : Formula_) :
  Formula_ :=
  list_disj ((gen_all_satisfying_valuations_as_list_of_total_functions init F).map (mk_lits F.atom_list.dedup))


#eval (to_dnf (fun _ => false) (Formula_| ((P \/ (Q /\ R)) /\ (~P \/ ~R)))).toString

#eval (to_dnf (fun _ => true) (Formula_| ((P \/ (Q /\ R)) /\ (~P \/ ~R)))).toString


example
  (init : ValuationAsTotalFunction)
  (F : Formula_) :
  is_dnf_ind (to_dnf init F) :=
  by
  unfold to_dnf
  apply list_disj_of_is_conj_ind_is_dnf_ind
  intro F' a1
  simp only [List.mem_map] at a1
  obtain ⟨V, ⟨a1_left, a1_right⟩⟩ := a1
  rewrite [← a1_right]
  apply mk_lits_is_conj_ind


lemma eval_eq_true_imp_eval_to_dnf_eq_true
  (init : ValuationAsTotalFunction)
  (V : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : ∀ (X : String), X ∉ F.atom_list.dedup → V X = init X)
  (h2 : eval V F = true) :
  eval V (to_dnf init F) = true :=
  by
  unfold to_dnf
  apply eval_exists_eq_true_imp_eval_list_disj_eq_true
  simp only [List.mem_map]
  apply Exists.intro (mk_lits F.atom_list.dedup V)
  constructor
  · apply Exists.intro V
    constructor
    · unfold gen_all_satisfying_valuations_as_list_of_total_functions
      simp only [List.mem_filter]
      constructor
      · apply gen_all_valuations_as_list_of_total_functions_is_complete
        exact h1
      · simp only [Bool.decide_eq_true]
        exact h2
    · rfl
  · apply eval_mk_lits_eq_true


lemma eval_to_dnf_eq_true_imp_eval_eq_true
  (init : ValuationAsTotalFunction)
  (V : ValuationAsTotalFunction)
  (F : Formula_)
  (h1 : eval V (to_dnf init F) = true) :
  eval V F = true :=
  by
  unfold to_dnf at h1
  rewrite [← eval_exists_eq_true_iff_eval_list_disj_eq_true] at h1
  obtain ⟨F', ⟨h1_left, h1_right⟩⟩ := h1
  unfold gen_all_satisfying_valuations_as_list_of_total_functions at h1_left
  simp only [Bool.decide_eq_true, List.mem_map, List.mem_filter] at h1_left
  obtain ⟨V', ⟨h1_left_left_left, h1_left_left_right⟩, h1_left_right⟩ := h1_left
  rewrite [← h1_left_right] at h1_right
  clear h1_left_right
  obtain s1 := eval_mk_lits_eq_true_imp_valuations_eq_on_atom_list V V' F.atom_list.dedup h1_right
  rewrite [← h1_left_left_right]
  apply theorem_2_2
  intro X a1
  apply s1
  simp only [List.mem_dedup]
  rewrite [← atom_occurs_in_iff_mem_atom_list]
  exact a1


lemma aux_1
  {α β : Type}
  (f : α → β)
  (xs ys : List α)
  (h1 : xs.length = ys.length)
  (h1 : ∀ (n : ℕ), (h : (n < xs.length ∧ n < ys.length)) → f (xs[n]) = f (ys[n])) :
  List.map f xs = List.map f ys :=
  by
  sorry


lemma aux_2
  {α β γ : Type}
  (f : α → γ)
  (g : β → γ)
  (xs : List α)
  (ys : List β)
  (h1 : xs.length = ys.length)
  (h2 : ∀ (p : α × β), p ∈ List.zip xs ys → f p.fst = g p.snd) :
  List.map f xs = List.map g ys :=
  by
  induction xs generalizing ys f g
  case nil =>
    cases ys
    case nil =>
      simp only [List.map_nil]
    case cons ys_hd ys_tl =>
      simp only [List.length_nil, List.length_cons] at h1
      simp only [Nat.zero_ne_add_one] at h1
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [List.length_cons, List.length_nil] at h1
      simp only [Nat.add_one_ne_zero] at h1
    case cons ys_hd ys_tl =>
      simp only [List.length_cons, add_left_inj] at h1

      simp only [List.zip_cons_cons, List.mem_cons] at h2

      simp only [List.map_cons, List.cons.injEq]
      constructor
      · specialize h2 (xs_hd, ys_hd)
        apply h2
        left
        rfl
      · apply xs_ih
        · exact h1
        · intro p a1
          apply h2
          right
          exact a1


lemma aux_3
  {α : Type}
  (xs ys : List α)
  (pred : α → Bool)
  (p : α × α)
  (h1 : p ∈ List.zip (List.filter pred xs) (List.filter pred ys))
  (h2 : ∀ (q : α × α), q ∈ List.zip xs ys → pred q.1 = pred q.2) :
  p ∈ List.zip xs ys :=
  by
  induction xs generalizing ys
  case nil =>
    simp only [List.filter_nil, List.zip_nil_left, List.not_mem_nil] at h1
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [List.filter_nil, List.zip_nil_right, List.not_mem_nil] at h1
    case cons ys_hd ys_tl =>
      simp only [List.filter_cons] at h1

      simp only [List.zip_cons_cons, List.mem_cons] at h2

      simp only [List.zip_cons_cons, List.mem_cons]
      split_ifs at h1
      case pos c1 c2 =>
        simp only [List.zip_cons_cons, List.mem_cons] at h1
        cases h1
        case inl h1 =>
          left
          exact h1
        case inr h1 =>
          right
          apply xs_ih
          · exact h1
          · intro q a1
            apply h2
            right
            exact a1
      case neg c1 c2 =>
        exfalso
        apply c2
        rewrite [← c1]
        specialize h2 (xs_hd, ys_hd)
        simp only at h2
        rewrite [← h2]
        · rfl
        · left
          exact trivial
      case pos c1 c2 =>
        exfalso
        apply c1
        rewrite [← c2]
        specialize h2 (xs_hd, ys_hd)
        simp only at h2
        apply h2
        left
        exact trivial
      case neg c1 c2 =>
        right
        apply xs_ih
        · exact h1
        · intro q a1
          apply h2
          right
          exact a1


lemma pred_eq_all_mem_zip_imp_filter_length_eq
  {α : Type}
  (xs ys : List α)
  (pred : α → Bool)
  (h1 : xs.length = ys.length)
  (h2 : ∀ (p : α × α), p ∈ List.zip xs ys → pred p.1 = pred p.2) :
  (List.filter pred xs).length = (List.filter pred ys).length :=
  by
  induction xs generalizing ys
  case nil =>
    cases ys
    case nil =>
      simp only [List.filter_nil, List.length_nil]
    case cons ys_hd ys_tl =>
      simp only [List.length_nil, List.length_cons] at h1
      simp only [Nat.zero_ne_add_one] at h1
  case cons xs_hd xs_tl xs_ih =>
    cases ys
    case nil =>
      simp only [List.length_cons, List.length_nil] at h1
      simp only [Nat.add_one_ne_zero] at h1
    case cons ys_hd ys_tl =>
      simp only [List.length_cons, add_left_inj] at h1

      simp only [List.zip_cons_cons, List.mem_cons] at h2

      simp only [List.filter_cons]
      split_ifs
      case pos c1 c2 =>
        simp only [List.length_cons, add_left_inj]
        apply xs_ih
        · exact h1
        · intro p a1
          apply h2
          right
          exact a1
      case neg c1 c2 =>
        exfalso
        apply c2
        rewrite [← c1]
        specialize h2 (xs_hd, ys_hd)
        simp only at h2
        rewrite [← h2]
        · rfl
        · left
          exact trivial
      case pos c1 c2 =>
        exfalso
        apply c1
        rewrite [← c2]
        specialize h2 (xs_hd, ys_hd)
        simp only at h2
        apply h2
        left
        exact trivial
      case neg c1 c2 =>
        apply xs_ih
        · exact h1
        · intro p a1
          apply h2
          right
          exact a1


example
  (init_1 init_2 : ValuationAsTotalFunction)
  (atom_list : List String) :
  List.map (mk_lits atom_list)
  (gen_all_valuations_as_list_of_total_functions init_1 atom_list) =
  List.map (mk_lits atom_list)
  (gen_all_valuations_as_list_of_total_functions init_2 atom_list) :=
  by
  apply aux_2
  · apply gen_all_valuations_as_list_of_total_functions_length_eq
  · intro p a1
    apply eq_on_mem_imp_mk_lits_eq
    intro X a2
    apply gen_all_valuations_as_list_of_total_functions_eq_on_atom_list init_1 init_2 atom_list
    · exact a1
    · exact a2


lemma aux_4
  (init_1 init_2 : ValuationAsTotalFunction)
  (F : Formula_) :
  List.map (mk_lits F.atom_list.dedup)
    (List.filter (fun V ↦ eval V F) (gen_all_valuations_as_list_of_total_functions init_1 F.atom_list.dedup)) =
  List.map (mk_lits F.atom_list.dedup)
    (List.filter (fun V ↦ eval V F) (gen_all_valuations_as_list_of_total_functions init_2 F.atom_list.dedup)) :=
  by
  apply aux_2
  · apply pred_eq_all_mem_zip_imp_filter_length_eq
    · apply gen_all_valuations_as_list_of_total_functions_length_eq
    · intro p a1
      apply theorem_2_2
      intro X a2
      apply gen_all_valuations_as_list_of_total_functions_eq_on_atom_list init_1 init_2 F.atom_list.dedup
      · exact a1
      · simp only [List.mem_dedup]
        simp only [← atom_occurs_in_iff_mem_atom_list]
        exact a2
  · intro p a1
    apply eq_on_mem_imp_mk_lits_eq
    intro X a2
    apply gen_all_valuations_as_list_of_total_functions_eq_on_atom_list init_1 init_2 F.atom_list.dedup
    · apply aux_3 (gen_all_valuations_as_list_of_total_functions init_1 F.atom_list.dedup) (gen_all_valuations_as_list_of_total_functions init_2 F.atom_list.dedup) (fun V => eval V F)
      · exact a1
      · intro q a3
        apply mem_zip_gen_all_valuations_as_list_of_total_functions_imp_eval_eq init_1 init_2
        exact a3
    · exact a2


example
  (init_1 init_2 : ValuationAsTotalFunction)
  (F : Formula_)
  (X : String)
  (p : ValuationAsTotalFunction × ValuationAsTotalFunction)
  (h1 : p ∈ List.zip
    (List.filter (fun (V : ValuationAsTotalFunction) => eval V F) (gen_all_valuations_as_list_of_total_functions init_1 F.atom_list.dedup))
    (List.filter (fun (V : ValuationAsTotalFunction) => eval V F) (gen_all_valuations_as_list_of_total_functions init_2 F.atom_list.dedup)))
  (h2 : X ∈ F.atom_list.dedup) :
  p.1 X = p.2 X :=
  by
  apply gen_all_valuations_as_list_of_total_functions_eq_on_atom_list init_1 init_2 F.atom_list.dedup
  · apply aux_3 (gen_all_valuations_as_list_of_total_functions init_1 F.atom_list.dedup) (gen_all_valuations_as_list_of_total_functions init_2 F.atom_list.dedup) (fun (V : ValuationAsTotalFunction) => eval V F)
    · exact h1
    · intro q a1
      apply mem_zip_gen_all_valuations_as_list_of_total_functions_imp_eval_eq
      exact a1
  · exact h2


example
  (init_1 init_2 : ValuationAsTotalFunction)
  (F : Formula_) :
  to_dnf init_1 F = to_dnf init_2 F :=
  by
  unfold to_dnf
  unfold gen_all_satisfying_valuations_as_list_of_total_functions
  congr 1
  simp only [Bool.decide_eq_true]
  apply aux_4


-------------------------------------------------------------------------------


def distrib :
  Formula_ → Formula_
  | and_ p (or_ q r) => or_ (distrib (and_ p q)) (distrib (and_ p r))
  | and_ (or_ p q) r => or_ (distrib (and_ p r)) (distrib (and_ q r))
  | F => F


def raw_dnf :
  Formula_ → Formula_
  | and_ p q => distrib (and_ (raw_dnf p) (raw_dnf q))
  | or_ p q => or_ (raw_dnf p) (raw_dnf q)
  | F => F


#eval (raw_dnf (Formula_| ((p \/ (q /\ r)) /\ (~p \/ ~ r)))).toString


/-
https://www.cl.cam.ac.uk/~jrh13/atp/OCaml/lib.ml

let rec itlist f l b =
  match l with
    [] -> b
  | (h::t) -> f h (itlist f t b);;
-/

def itlist
  {α β : Type}
  (f : α → β → β)
  (l : List α)
  (b : β) :
  β :=
  match l with
  | [] => b
  | h :: t => f h (itlist f t b)


example
  {α β : Type}
  (f : α → β → β)
  (l : List α)
  (b : β) :
  itlist f l b = List.foldr f b l :=
  by
  induction l
  case nil =>
    unfold itlist
    unfold List.foldr
    rfl
  case cons hd tl ih =>
    unfold itlist
    unfold List.foldr
    rewrite [ih]
    rfl


/-
https://www.cl.cam.ac.uk/~jrh13/atp/OCaml/lib.ml

let rec allpairs f l1 l2 =
  match l1 with
   h1::t1 ->  itlist (fun x a -> f h1 x :: a) l2 (allpairs f t1 l2)
  | [] -> [];;
-/

def all_pairs
  {α : Type}
  (f : List α → List α → List α)
  (l1 l2 : List (List α)) :
  List (List α) :=
  match l1 with
  | [] => []
  | hd :: tl =>
    List.foldr
      (fun (next : List α) (prev : List (List α)) => (f hd next) :: prev)
        (all_pairs f tl l2)
          l2


#eval all_pairs List.append [[1]] []
#eval all_pairs List.append [[1], [2]] []
#eval all_pairs List.append [[1]] [[4]]
#eval all_pairs List.append [[1], [2]] [[4]]
#eval all_pairs List.append [[1], [2]] [[4], [5]]
#eval all_pairs List.append [[1]] [[4], [5]]
#eval all_pairs List.append [[1]] [[4], [5], [6]]
#eval all_pairs List.append [] [[4], [5]]


-- (a + b) * (c + d)
-- a * c + a * d + b * c + b * d


lemma all_pairs_nil_right
  {α : Type}
  (f : List α → List α → List α)
  (l : List (List α)) :
  all_pairs f l [] = [] :=
  by
  induction l
  case nil =>
    unfold all_pairs
    rfl
  case cons hd tl ih =>
    unfold all_pairs
    simp only [List.foldr_nil]
    exact ih


lemma all_pairs_singleton_left_cons_right
  {α : Type}
  (f : List α → List α → List α)
  (xs : List α)
  (ys : List α)
  (yss : List (List α)) :
  all_pairs f [xs] (ys :: yss) = all_pairs f [xs] [ys] ++ all_pairs f [xs] yss :=
  by
  simp only [all_pairs]
  simp only [List.foldr_cons, List.foldr_nil, List.singleton_append]


def distrib_one
  {α : Type}
  (f : List α → List α → List α)
  (x : List α)
  (xs : List (List α)) :
  List (List α) :=
    List.foldr
      (fun (next : List α) (prev : List (List α)) => (f x next) :: prev) [] xs

#eval distrib_one List.append [0] [[1], [2], [3]]


def all_pairs_alt
  {α : Type}
  (f : List α → List α → List α)
  (l1 l2 : List (List α)) :
  List (List α) :=
  match l1 with
  | [] => []
  | hd :: tl => distrib_one f hd l2 ++ all_pairs_alt f tl l2


lemma List.foldr_cons_append_init
  {α β : Type}
  (f : α → β)
  (xs_left xs_right : List β)
  (ys : List α) :
  List.foldr (fun (next : α) (prev : List β) => (f next) :: prev) (xs_left ++ xs_right) ys =
    (List.foldr (fun (next : α) (prev : List β) => (f next) :: prev) xs_left ys) ++ xs_right :=
  by
  induction ys
  case nil =>
    simp only [List.foldr_nil]
  case cons hd tl ih =>
    simp only [List.foldr_cons, List.cons_append]
    rewrite [ih]
    rfl


example
  {α : Type}
  (f : List α → List α → List α)
  (l1 l2 : List (List α)) :
  all_pairs f l1 l2 = all_pairs_alt f l1 l2 :=
  by
  induction l1
  case nil =>
    unfold all_pairs
    unfold all_pairs_alt
    rfl
  case cons l1_hd l1_tl l1_ih =>
    unfold all_pairs
    unfold all_pairs_alt
    unfold distrib_one
    rewrite [l1_ih]

    obtain s1 := List.foldr_cons_append_init (f l1_hd) [] (all_pairs_alt f l1_tl l2) l2
    simp only [List.nil_append] at s1
    exact s1


def pure_dnf :
  Formula_ → List (List Formula_)
  | and_ p q => all_pairs List.union (pure_dnf p) (pure_dnf q)
  | or_ p q => List.union (pure_dnf p) (pure_dnf q)
  | F => [[F]]

#eval (pure_dnf (Formula_| ((p \/ (q /\ r)) /\ (~p \/ ~ r)))).toString


def dnf_list_of_list_to_formula
  (l : List (List Formula_)) :
  Formula_ :=
  list_disj (List.map list_conj l)


#eval (dnf_list_of_list_to_formula [[atom_ "P", atom_ "Q"], [not_ (atom_ "P"), atom_ "R"]]).toString


example
  {α : Type}
  [DecidableEq α]
  (xss yss : List (List α))
  (zs : List α)
  (z : α)
  (h1 : zs ∈ all_pairs List.union xss yss)
  (h2 : z ∈ zs) :
  (∃ (xs : List α), xs ∈ xss ∧ z ∈ xs) ∨
  (∃ (ys : List α), ys ∈ yss ∧ z ∈ ys) :=
  by
  induction xss generalizing yss
  case nil =>
    unfold all_pairs at h1
    simp only [List.not_mem_nil] at h1
  case cons xss_hd xss_tl xss_ih =>
    cases yss
    case nil =>
      unfold all_pairs at h1
      simp only [List.foldr_nil] at h1
      simp only [all_pairs_nil_right] at h1
      simp only [List.not_mem_nil] at h1
    case cons yss_hd yss_tl =>
      unfold all_pairs at h1
      simp only [List.foldr_cons, List.mem_cons] at h1
      cases h1
      case inl h1 =>
        sorry
      case inr h1 =>
        sorry


example
  (P Q : Formula_)
  (xs : List Formula_)
  (h1 : is_nnf P)
  (h2 : xs ∈ pure_dnf P)
  (h3 : Q ∈ xs) :
  is_constant_ind Q ∨ is_literal_ind Q :=
  by
  induction P generalizing xs
  case false_ =>
    unfold pure_dnf at h2
    sorry
  case and_ phi psi phi_ih psi_ih =>
    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold pure_dnf at h2
    sorry
  all_goals
    sorry


example
  (F : Formula_)
  (h1 : is_nnf F) :
  is_dnf_ind (dnf_list_of_list_to_formula (pure_dnf F)) :=
  by
  induction F
  case false_ =>
    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    simp only [List.map_cons, List.map_nil]
    unfold list_conj
    unfold list_disj
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_3
    apply is_constant_ind.rule_1
  case and_ phi psi phi_ih psi_ih =>
    unfold pure_dnf
    sorry
  case or_ phi psi phi_ih psi_ih =>
    unfold pure_dnf
    unfold dnf_list_of_list_to_formula
    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1
    sorry
  all_goals
    sorry
