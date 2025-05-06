import HandbookOfPracticalLogicLean.Chapter2.Formula

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  `Formula_.is_constant_rec F` := True if and only if the formula `F` is `false_` or `true_`.
-/
def Formula_.is_constant_rec :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_constant_rec F) :=
  by
  cases F
  all_goals
    unfold is_constant_rec
    infer_instance


/--
  `Formula_.is_literal_rec F` := True if and only if the formula `F` is an atomic formula or the negation of an atomic formula.
-/
def Formula_.is_literal_rec :
  Formula_ → Prop
  | atom_ _ => True
  | not_ (atom_ _) => True
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_literal_rec F) :=
  by
  cases F
  case not_ phi =>
    unfold is_literal_rec
    split
    all_goals
      infer_instance
  all_goals
    simp only [is_literal_rec]
    infer_instance


/--
  `Formula_.is_negative_literal_rec F` := True if and only if the formula `F` is a negative literal.
-/
def Formula_.is_negative_literal_rec :
  Formula_ → Prop
  | not_ (atom_ _) => True
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_negative_literal_rec F) :=
  by
  cases F
  case not_ phi =>
    unfold is_negative_literal_rec
    split
    all_goals
      infer_instance
  all_goals
    simp only [is_negative_literal_rec]
    infer_instance


/--
  `Formula_.is_positive_literal_rec F` := True if and only if the formula `F` is a positive literal.
-/
def Formula_.is_positive_literal_rec :
  Formula_ → Prop
  | atom_ _ => True
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_positive_literal_rec F) :=
  by
  cases F
  all_goals
    simp only [is_positive_literal_rec]
    infer_instance


/--
  `Formula_.is_nnf_rec_v1 F` := True if and only if the formula `F` is in negation normal form.
-/
def Formula_.is_nnf_rec_v1 :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | and_ phi psi => phi.is_nnf_rec_v1 ∧ psi.is_nnf_rec_v1
  | or_ phi psi => phi.is_nnf_rec_v1 ∧ psi.is_nnf_rec_v1
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_nnf_rec_v1 F) :=
  by
  induction F
  case not_ phi ih =>
    cases phi
    all_goals
      unfold is_nnf_rec_v1
      infer_instance
  all_goals
    unfold is_nnf_rec_v1
    infer_instance


-------------------------------------------------------------------------------


/--
  `Formula_.is_nnf_rec_v2 F` := True if and only if the formula `F` is in negation normal form.
-/
def Formula_.is_nnf_rec_v2 :
  Formula_ → Prop
  | false_ => True
  | not_ false_ => True
  | true_ => True
  | not_ true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | and_ phi psi => phi.is_nnf_rec_v2 ∧ psi.is_nnf_rec_v2
  | or_ phi psi => phi.is_nnf_rec_v2 ∧ psi.is_nnf_rec_v2
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_nnf_rec_v2 F) :=
  by
  induction F
  case not_ phi ih =>
    cases phi
    all_goals
      unfold is_nnf_rec_v2
      infer_instance
  all_goals
    unfold is_nnf_rec_v2
    infer_instance


-------------------------------------------------------------------------------


/--
  `Formula_.is_pos_nnf_rec F` := True if and only if the formula `F` is in negation normal form and every atom in `F` occurs unnegated.
-/
def Formula_.is_pos_nnf_rec :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => False
  | and_ phi psi => phi.is_pos_nnf_rec ∧ psi.is_pos_nnf_rec
  | or_ phi psi => phi.is_pos_nnf_rec ∧ psi.is_pos_nnf_rec
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_pos_nnf_rec F) :=
  by
  induction F
  case not_ phi ih =>
    cases phi
    all_goals
      unfold is_pos_nnf_rec
      infer_instance
  all_goals
    unfold is_pos_nnf_rec
    infer_instance


-------------------------------------------------------------------------------


/--
  `Formula_.is_neg_nnf_rec F` := True if and only if the formula `F` is in negation normal form and every atom in `F` occurs negated.
-/
def Formula_.is_neg_nnf_rec :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => False
  | not_ (atom_ _) => True
  | and_ phi psi => phi.is_neg_nnf_rec ∧ psi.is_neg_nnf_rec
  | or_ phi psi => phi.is_neg_nnf_rec ∧ psi.is_neg_nnf_rec
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_neg_nnf_rec F) :=
  by
  induction F
  case not_ phi ih =>
    cases phi
    all_goals
      unfold is_neg_nnf_rec
      infer_instance
  all_goals
    unfold is_neg_nnf_rec
    infer_instance


-------------------------------------------------------------------------------


def Formula_.is_conj_rec_v1 :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | and_ (false_) psi => psi.is_conj_rec_v1
  | and_ (true_) psi => psi.is_conj_rec_v1
  | and_ (atom_ _) psi => psi.is_conj_rec_v1
  | and_ (not_ (atom_ _)) psi => psi.is_conj_rec_v1
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
  case and_ phi psi phi_ih psi_ih =>
    cases phi
    case not_ phi =>
      cases phi
      all_goals
        simp only [is_conj_rec_v1]
        infer_instance
    all_goals
      simp only [is_conj_rec_v1]
      infer_instance
  all_goals
    simp only [is_conj_rec_v1]
    infer_instance


-------------------------------------------------------------------------------


def Formula_.is_dnf_rec_v1 :
  Formula_ → Prop
  | or_ phi psi => phi.is_conj_rec_v1 ∧ psi.is_dnf_rec_v1
  | F => is_conj_rec_v1 F


instance
  (F : Formula_) :
  Decidable (Formula_.is_dnf_rec_v1 F) :=
  by
  induction F
  all_goals
    simp only [is_dnf_rec_v1]
    infer_instance


-------------------------------------------------------------------------------


inductive is_constant_ind : Formula_ → Prop
| rule_1 :
  is_constant_ind false_

| rule_2 :
  is_constant_ind true_


-------------------------------------------------------------------------------


inductive is_literal_ind : Formula_ → Prop
| rule_1
  (X : String) :
  is_literal_ind (atom_ X)

| rule_2
  (X : String) :
  is_literal_ind (not_ (atom_ X))


-------------------------------------------------------------------------------


inductive is_disj_ind_v1 : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_constant_ind phi →
  is_disj_ind_v1 psi →
  is_disj_ind_v1 (or_ phi psi)

| rule_2
  (phi psi : Formula_) :
  is_literal_ind phi →
  is_disj_ind_v1 psi →
  is_disj_ind_v1 (or_ phi psi)

| rule_3
  (F : Formula_) :
  is_constant_ind F →
  is_disj_ind_v1 F

| rule_4
  (F : Formula_) :
  is_literal_ind F →
  is_disj_ind_v1 F


inductive is_disj_ind_v2 : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_disj_ind_v2 phi →
  is_disj_ind_v2 psi →
  is_disj_ind_v2 (or_ phi psi)

| rule_2
  (F : Formula_) :
  is_constant_ind F →
  is_disj_ind_v2 F

| rule_3
  (F : Formula_) :
  is_literal_ind F →
  is_disj_ind_v2 F


-------------------------------------------------------------------------------


inductive is_conj_ind_v1 : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_constant_ind phi →
  is_conj_ind_v1 psi →
  is_conj_ind_v1 (and_ phi psi)

| rule_2
  (phi psi : Formula_) :
  is_literal_ind phi →
  is_conj_ind_v1 psi →
  is_conj_ind_v1 (and_ phi psi)

| rule_3
  (F : Formula_) :
  is_constant_ind F →
  is_conj_ind_v1 F

| rule_4
  (F : Formula_) :
  is_literal_ind F →
  is_conj_ind_v1 F


inductive is_conj_ind_v2 : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_conj_ind_v2 phi →
  is_conj_ind_v2 psi →
  is_conj_ind_v2 (and_ phi psi)

| rule_2
  (F : Formula_) :
  is_constant_ind F →
  is_conj_ind_v2 F

| rule_3
  (F : Formula_) :
  is_literal_ind F →
  is_conj_ind_v2 F


-------------------------------------------------------------------------------


inductive is_dnf_ind_v1 : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_conj_ind_v1 phi →
  is_dnf_ind_v1 psi →
  is_dnf_ind_v1 (or_ phi psi)

| rule_2
  (F : Formula_) :
  is_conj_ind_v1 F →
  is_dnf_ind_v1 F


inductive is_dnf_ind_v2 : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_dnf_ind_v2 phi →
  is_dnf_ind_v2 psi →
  is_dnf_ind_v2 (or_ phi psi)

| rule_2
  (F : Formula_) :
  is_conj_ind_v2 F →
  is_dnf_ind_v2 F


-------------------------------------------------------------------------------


inductive is_cnf_ind_v1 : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_disj_ind_v1 phi →
  is_cnf_ind_v1 psi →
  is_cnf_ind_v1 (and_ phi psi)

| rule_2
  (F : Formula_) :
  is_disj_ind_v1 F →
  is_cnf_ind_v1 F


inductive is_cnf_ind_v2 : Formula_ → Prop
| rule_1
  (phi psi : Formula_) :
  is_cnf_ind_v2 phi →
  is_cnf_ind_v2 psi →
  is_cnf_ind_v2 (and_ phi psi)

| rule_2
  (F : Formula_) :
  is_disj_ind_v2 F →
  is_cnf_ind_v2 F


-------------------------------------------------------------------------------
