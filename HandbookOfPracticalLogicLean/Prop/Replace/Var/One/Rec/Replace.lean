import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Prop.Semantics

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `replace_var_one_rec A F P` :=

  `A → F` in `P` for each occurrence of the variable `A` in the formula `P`

  The result of simultaneously replacing each occurrence of the variable `A` in the formula `P` by an occurrence of the formula `F`.
-/
def replace_var_one_rec
  (A : String)
  (F : Formula_ ) :
  Formula_ → Formula_
  | false_ => false_
  | true_ => true_
  | var_ X => if A = X then F else var_ X
  | not_ phi => not_ (replace_var_one_rec A F phi)
  | and_ phi psi => and_ (replace_var_one_rec A F phi) (replace_var_one_rec A F psi)
  | or_ phi psi => or_ (replace_var_one_rec A F phi) (replace_var_one_rec A F psi)
  | imp_ phi psi => imp_ (replace_var_one_rec A F phi) (replace_var_one_rec A F psi)
  | iff_ phi psi => iff_ (replace_var_one_rec A F phi) (replace_var_one_rec A F psi)


theorem theorem_2_3_one
  (V : ValuationAsTotalFunction)
  (A : String)
  (P : Formula_)
  (F : Formula_) :
  eval V (replace_var_one_rec A P F) = eval (Function.updateITE' V A (eval V P)) F :=
  by
  induction F
  case false_ | true_ =>
    simp only [eval]
  case var_ X =>
    simp only [eval]
    unfold replace_var_one_rec
    unfold Function.updateITE'
    split_ifs
    · rfl
    · unfold eval
      rfl
  case not_ phi ih =>
    simp only [eval]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


theorem corollary_2_4_one
  (A : String)
  (P : Formula_)
  (F : Formula_)
  (h1 : F.is_tautology) :
  ((replace_var_one_rec A P F)).is_tautology :=
  by
  unfold is_tautology at h1
  unfold satisfies at h1

  unfold is_tautology
  unfold satisfies
  intro V
  rewrite [theorem_2_3_one]
  apply h1


theorem theorem_2_5_one
  (V : ValuationAsTotalFunction)
  (A : String)
  (P Q : Formula_)
  (R : Formula_)
  (h1 : eval V P = eval V Q) :
  eval V (replace_var_one_rec A P R) = eval V (replace_var_one_rec A Q R) :=
  by
  simp only [theorem_2_3_one]
  rewrite [h1]
  rfl


theorem corollary_2_6_one
  (V : ValuationAsTotalFunction)
  (A : String)
  (P Q : Formula_)
  (R : Formula_)
  (h1 : are_logically_equivalent P Q) :
  eval V (replace_var_one_rec A P R) = eval V (replace_var_one_rec A Q R) :=
  by
  simp only [are_logically_equivalent_iff_eval_eq] at h1

  apply theorem_2_5_one
  apply h1


-------------------------------------------------------------------------------


theorem not_var_occurs_in_replace_var_one_rec_self
  (A : String)
  (P : Formula_)
  (F : Formula_)
  (h1 : ¬ var_occurs_in_formula A F) :
  replace_var_one_rec A P F = F :=
  by
  induction F
  case false_ | true_ =>
    unfold replace_var_one_rec
    rfl
  case var_ X =>
    unfold var_occurs_in_formula at h1

    unfold replace_var_one_rec
    split_ifs
    rfl
  case not_ phi ih =>
    unfold var_occurs_in_formula at h1

    unfold replace_var_one_rec
    congr
    apply ih
    exact h1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold var_occurs_in_formula at h1

    unfold replace_var_one_rec
    congr
    · apply phi_ih
      intro contra
      apply h1
      left
      exact contra
    · apply psi_ih
      intro contra
      apply h1
      right
      exact contra


lemma var_occurs_in_formula_replace_var_one_rec
  (A : String)
  (P : Formula_)
  (F : Formula_)
  (h1 : var_occurs_in_formula A (replace_var_one_rec A P F)) :
  var_occurs_in_formula A P :=
  by
  induction F
  case false_ | true_ =>
    unfold replace_var_one_rec at h1
    unfold var_occurs_in_formula at h1
    contradiction
  case var_ X =>
    unfold replace_var_one_rec at h1

    split_ifs at h1
    case pos c1 =>
      exact h1
    case neg c1 =>
      unfold var_occurs_in_formula at h1
      contradiction
  case not_ phi ih =>
    unfold replace_var_one_rec at h1
    unfold var_occurs_in_formula at h1

    apply ih
    exact h1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replace_var_one_rec at h1
    unfold var_occurs_in_formula at h1

    cases h1
    case inl h1 =>
      apply phi_ih
      exact h1
    case inr h1 =>
      apply psi_ih
      exact h1


example
  (A : String)
  (P : Formula_)
  (F : Formula_) :
  F.var_set \ {A} ⊆ (replace_var_one_rec A P F).var_set :=
  by
  induction F
  case false_ | true_ =>
    unfold replace_var_one_rec
    unfold Formula_.var_set
    simp only [Finset.empty_sdiff]
    rfl
  case var_ X =>
    unfold replace_var_one_rec
    split_ifs
    case pos c1 =>
      rewrite [c1]
      simp only [Formula_.var_set]
      simp only [Finset.sdiff_self]
      apply Finset.empty_subset
    case neg c1 =>
      unfold Formula_.var_set
      exact Finset.sdiff_subset
  case not_ phi ih =>
    unfold replace_var_one_rec
    unfold Formula_.var_set
    exact ih
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replace_var_one_rec
    unfold Formula_.var_set
    simp only [Finset.union_sdiff_distrib]
    apply Finset.union_subset_union
    · apply phi_ih
    · apply psi_ih


example
  (A : String)
  (P : Formula_)
  (F : Formula_)
  (h1 : var_occurs_in_formula A F) :
  P.var_set ⊆ (replace_var_one_rec A P F).var_set :=
  by
  induction F
  case false_ | true_ =>
    unfold var_occurs_in_formula at h1
    contradiction
  case var_ X =>
    unfold var_occurs_in_formula at h1

    unfold replace_var_one_rec
    split_ifs
    rfl
  case not_ phi ih =>
    unfold var_occurs_in_formula at h1

    unfold replace_var_one_rec
    simp only [Formula_.var_set]
    apply ih
    exact h1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold var_occurs_in_formula at h1

    unfold replace_var_one_rec
    simp only [Formula_.var_set]
    cases h1
    case inl h1 =>
      trans (replace_var_one_rec A P phi).var_set
      · apply phi_ih
        exact h1
      · exact Finset.subset_union_left
    case inr h1 =>
      trans (replace_var_one_rec A P psi).var_set
      · apply psi_ih
        exact h1
      · exact Finset.subset_union_right


lemma replace_var_one_rec_var_set_subset
  (A : String)
  (P : Formula_)
  (F : Formula_) :
  (replace_var_one_rec A P F).var_set ⊆ P.var_set ∪ F.var_set :=
  by
  induction F
  case false_ | true_ =>
    unfold replace_var_one_rec
    simp only [Formula_.var_set]
    apply Finset.empty_subset
  case var_ X =>
    unfold replace_var_one_rec
    split_ifs
    case pos c1 =>
      simp only [Formula_.var_set]
      exact Finset.subset_union_left
    case neg c1 =>
      simp only [Formula_.var_set]
      exact Finset.subset_union_right
  case not_ phi ih =>
    unfold replace_var_one_rec
    simp only [Formula_.var_set]
    exact ih
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold replace_var_one_rec
    simp only [Formula_.var_set]
    rewrite [Finset.union_union_distrib_left]
    apply Finset.union_subset_union
    · exact phi_ih
    · exact psi_ih


#lint
