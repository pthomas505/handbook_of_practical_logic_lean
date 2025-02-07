import MathlibExtraLean.FunctionUpdateITE

import HandbookOfPracticalLogicLean.Chapter2.NNF

import Mathlib.Tactic


set_option autoImplicit false


namespace Prop_


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


def Formula_.is_conj_rec_v1 :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | and_ phi psi => phi.is_conj_rec_v1 ∧ psi.is_conj_rec_v1
  | _ => False


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


example
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


example
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


-------------------------------------------------------------------------------


def list_conj :
  List Formula_ → Formula_
  | [] => true_
  | [P] => P
  | hd :: tl => and_ hd (list_conj tl)


def list_disj :
  List Formula_ → Formula_
  | [] => false_
  | [P] => P
  | hd :: tl => or_ hd (list_disj tl)


def gen_all_assignments :
  List String → List (List (String × Prop))
| [] => [[]]
| hd :: tl =>
  let left := List.map (fun (l : List (String × Prop)) => (hd, False) :: l) (gen_all_assignments tl)

  let right := List.map (fun (l : List (String × Prop)) => (hd, True) :: l) (gen_all_assignments tl)

  left ++ right


def gen_valuation
  (default : Valuation) :
  List (String × Prop) → Valuation
  | [] => default
  | hd :: tl => Function.updateITE (gen_valuation default tl) hd.fst hd.snd


instance
  (V : Valuation)
  [DecidablePred V]
  (l : List (String × Prop))
  (h1 : ∀ (el : String × Prop), el ∈ l → Decidable el.2) :
  DecidablePred (gen_valuation V l) :=
  by
  induction l
  case nil =>
    simp only [gen_valuation]
    infer_instance
  case cons hd tl ih =>
    simp only [gen_valuation]
    unfold DecidablePred
    intro a
    simp only [Function.updateITE]
    split_ifs
    case pos c1 =>
      apply h1
      simp
    case neg c1 =>
      apply ih
      intro el a1
      apply h1
      simp
      tauto


instance
  (V : Valuation)
  [DecidablePred V]
  (l : List (String × Prop))
  (F : Formula_)
  (h1 : ∀ (el : String × Prop), el ∈ l → Decidable el.2) :
  Decidable (eval (gen_valuation V l) F) :=
  by
  have s1 : DecidablePred (gen_valuation V l) :=
  by
    induction l
    case nil =>
      simp only [gen_valuation]
      infer_instance
    case cons hd tl ih =>
      simp only [gen_valuation]
      unfold DecidablePred
      intro a
      simp only [Function.updateITE]
      split_ifs
      case pos c1 =>
        apply h1
        simp
      case neg c1 =>
        apply ih
        intro el a1
        apply h1
        simp
        tauto
  infer_instance
