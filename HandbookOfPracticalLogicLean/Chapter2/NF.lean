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
    simp only [is_constant_rec]
    infer_instance


-------------------------------------------------------------------------------


/--
  `Formula_.is_literal_rec F` := True if and only if the formula `F` is an atom or the negation of an atom.
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
    cases phi
    all_goals
      simp only [is_literal_rec]
      infer_instance
  all_goals
    simp only [is_literal_rec]
    infer_instance


/--
  `Formula_.is_pos_literal_rec F` := True if and only if the formula `F` is a positive literal.
-/
def Formula_.is_pos_literal_rec :
  Formula_ → Prop
  | atom_ _ => True
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_pos_literal_rec F) :=
  by
  cases F
  all_goals
    simp only [is_pos_literal_rec]
    infer_instance


/--
  `Formula_.is_neg_literal_rec F` := True if and only if the formula `F` is a negative literal.
-/
def Formula_.is_neg_literal_rec :
  Formula_ → Prop
  | not_ (atom_ _) => True
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_neg_literal_rec F) :=
  by
  cases F
  case not_ phi =>
    cases phi
    all_goals
      simp only [is_neg_literal_rec]
      infer_instance
  all_goals
    simp only [is_neg_literal_rec]
    infer_instance


-------------------------------------------------------------------------------


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
  `Formula_.is_pos_nnf_rec F` := True if and only if the formula `F` is in negation normal form and every atom in `F` is positive.
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
  `Formula_.is_neg_nnf_rec F` := True if and only if the formula `F` is in negation normal form and every atom in `F` is negative.
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


/--
  `Formula_.is_disj_rec_v1 F` := True if and only if the formula `F` is a disjunction of an arbitrary number of elements and every left disjunct is a constant or a literal.
-/
def Formula_.is_disj_rec_v1 :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | or_ false_ psi => psi.is_disj_rec_v1
  | or_ true_ psi => psi.is_disj_rec_v1
  | or_ (atom_ _) psi => psi.is_disj_rec_v1
  | or_ (not_ (atom_ _)) psi => psi.is_disj_rec_v1
  | _ => False


instance
  (F : Formula_) :
  Decidable (Formula_.is_disj_rec_v1 F) :=
  by
  induction F
  case not_ phi ih =>
    cases phi
    all_goals
      unfold is_disj_rec_v1
      infer_instance
  case or_ phi psi phi_ih psi_ih =>
    cases phi
    case not_ phi =>
      cases phi
      all_goals
        unfold is_disj_rec_v1
        infer_instance
    all_goals
      unfold is_disj_rec_v1
      infer_instance
  all_goals
    unfold is_disj_rec_v1
    infer_instance


/--
  `Formula_.is_disj_rec_v2 F` := True if and only if the formula `F` is a disjunction of an arbitrary number of elements.
-/
def Formula_.is_disj_rec_v2 :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | or_ phi psi => phi.is_disj_rec_v2 ∧ psi.is_disj_rec_v2
  | _ => False


instance
  (F : Formula_) :
  Decidable (Formula_.is_disj_rec_v2 F) :=
  by
  induction F
  case not_ phi ih =>
    cases phi
    all_goals
      unfold is_disj_rec_v2
      infer_instance
  all_goals
    unfold is_disj_rec_v2
    infer_instance


-------------------------------------------------------------------------------


/--
  `Formula_.is_conj_rec_v1 F` := True if and only if the formula `F` is a conjunction of an arbitrary number of elements and every left conjunct is a constant or a literal.
-/
def Formula_.is_conj_rec_v1 :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | and_ false_ psi => psi.is_conj_rec_v1
  | and_ true_ psi => psi.is_conj_rec_v1
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
      unfold is_conj_rec_v1
      infer_instance
  case and_ phi psi phi_ih psi_ih =>
    cases phi
    case not_ phi =>
      cases phi
      all_goals
        unfold is_conj_rec_v1
        infer_instance
    all_goals
      unfold is_conj_rec_v1
      infer_instance
  all_goals
    unfold is_conj_rec_v1
    infer_instance


/--
  `Formula_.is_conj_rec_v2 F` := True if and only if the formula `F` is a conjunction of an arbitrary number of elements.
-/
def Formula_.is_conj_rec_v2 :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | and_ phi psi => phi.is_conj_rec_v2 ∧ psi.is_conj_rec_v2
  | _ => False


instance
  (F : Formula_) :
  Decidable (Formula_.is_conj_rec_v2 F) :=
  by
  induction F
  case not_ phi ih =>
    cases phi
    all_goals
      unfold is_conj_rec_v2
      infer_instance
  all_goals
    unfold is_conj_rec_v2
    infer_instance


-------------------------------------------------------------------------------


/--
  `Formula_.is_dnf_rec_v1 F` := True if and only if the formula `F` is in disjunction normal form.
-/
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
    unfold is_dnf_rec_v1
    infer_instance


/--
  `Formula_.is_dnf_rec_v2 F` := True if and only if the formula `F` is in disjunction normal form.
-/
def Formula_.is_dnf_rec_v2 :
  Formula_ → Prop
  | or_ phi psi => phi.is_dnf_rec_v2 ∧ psi.is_dnf_rec_v2
  | F => is_conj_rec_v2 F


instance
  (F : Formula_) :
  Decidable (Formula_.is_dnf_rec_v2 F) :=
  by
  induction F
  all_goals
    unfold is_dnf_rec_v2
    infer_instance


-------------------------------------------------------------------------------


/--
  `Formula_.is_cnf_rec_v1 F` := True if and only if the formula `F` is in conjunction normal form.
-/
def Formula_.is_cnf_rec_v1 :
  Formula_ → Prop
  | and_ phi psi => phi.is_disj_rec_v1 ∧ psi.is_cnf_rec_v1
  | F => is_disj_rec_v1 F


instance
  (F : Formula_) :
  Decidable (Formula_.is_cnf_rec_v1 F) :=
  by
  induction F
  all_goals
    unfold is_cnf_rec_v1
    infer_instance


/--
  `Formula_.is_cnf_rec_v2 F` := True if and only if the formula `F` is in conjunction normal form.
-/
def Formula_.is_cnf_rec_v2 :
  Formula_ → Prop
  | and_ phi psi => phi.is_cnf_rec_v2 ∧ psi.is_cnf_rec_v2
  | F => is_disj_rec_v2 F


instance
  (F : Formula_) :
  Decidable (Formula_.is_cnf_rec_v2 F) :=
  by
  induction F
  all_goals
    unfold is_cnf_rec_v2
    infer_instance


-------------------------------------------------------------------------------


/--
  `is_constant_ind F` := True if and only if the formula `F` is `false_` or `true_`.
-/
inductive is_constant_ind : Formula_ → Prop
| rule_1 :
  is_constant_ind false_

| rule_2 :
  is_constant_ind true_


-------------------------------------------------------------------------------


/--
  `is_literal_ind F` := True if and only if the formula `F` is an atom or the negation of an atom.
-/
inductive is_literal_ind : Formula_ → Prop
| rule_1
  (X : String) :
  is_literal_ind (atom_ X)

| rule_2
  (X : String) :
  is_literal_ind (not_ (atom_ X))


-------------------------------------------------------------------------------


/--
  `is_disj_ind_v1 F` := True if and only if the formula `F` is a disjunction of an arbitrary number of elements and every left disjunct is a constant or a literal.
-/
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


/--
  `is_disj_ind_v2 F` := True if and only if the formula `F` is a disjunction of an arbitrary number of elements.
-/
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


/--
  `is_conj_ind_v1 F` := True if and only if the formula `F` is a conjunction of an arbitrary number of elements and every left conjunct is a constant or a literal.
-/
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


/--
  `is_conj_ind_v2 F` := True if and only if the formula `F` is a conjunction of an arbitrary number of elements.
-/
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


/--
  `is_dnf_ind_v1 F` := True if and only if the formula `F` is in disjunction normal form.
-/
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


/--
  `is_dnf_ind_v2 F` := True if and only if the formula `F` is in disjunction normal form.
-/
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


/--
  `is_cnf_ind_v1 F` := True if and only if the formula `F` is in conjunction normal form.
-/
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


/--
  `is_cnf_ind_v2 F` := True if and only if the formula `F` is in conjunction normal form.
-/
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


lemma is_constant_ind_imp_is_constant_rec
  (F : Formula_)
  (h1 : is_constant_ind F) :
  F.is_constant_rec :=
  by
  cases h1
  all_goals
    simp only [is_constant_rec]


lemma is_constant_rec_imp_is_constant_ind
  (F : Formula_)
  (h1 : F.is_constant_rec) :
  is_constant_ind F :=
  by
  cases F
  case false_ =>
    apply is_constant_ind.rule_1
  case true_ =>
    apply is_constant_ind.rule_2
  all_goals
    simp only [is_constant_rec] at h1


lemma is_constant_ind_iff_is_constant_rec
  (F : Formula_) :
  is_constant_ind F ↔ F.is_constant_rec :=
  by
  constructor
  · apply is_constant_ind_imp_is_constant_rec
  · apply is_constant_rec_imp_is_constant_ind


-------------------------------------------------------------------------------


lemma is_literal_ind_imp_is_literal_rec
  (F : Formula_)
  (h1 : is_literal_ind F) :
  F.is_literal_rec :=
  by
  cases h1
  all_goals
    simp only [is_literal_rec]


lemma is_literal_rec_imp_is_literal_ind
  (F : Formula_)
  (h1 : F.is_literal_rec) :
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
      simp only [is_literal_rec] at h1
  all_goals
    simp only [is_literal_rec] at h1


lemma is_literal_ind_iff_is_literal_rec
  (F : Formula_) :
  is_literal_ind F ↔ F.is_literal_rec :=
  by
  constructor
  · apply is_literal_ind_imp_is_literal_rec
  · apply is_literal_rec_imp_is_literal_ind


-------------------------------------------------------------------------------


lemma is_disj_rec_v1_imp_is_nnf_rec_v1
  (F : Formula_)
  (h1 : F.is_disj_rec_v1) :
  F.is_nnf_rec_v1 :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold is_nnf_rec_v1
    exact trivial
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      unfold is_nnf_rec_v1
      exact trivial
    all_goals
      unfold is_disj_rec_v1 at h1
      contradiction
  case or_ phi psi phi_ih psi_ih =>
    unfold is_nnf_rec_v1
    cases phi
    case false_ | true_ | atom_ X =>
      unfold is_disj_rec_v1 at h1
      constructor
      · unfold is_nnf_rec_v1
        exact trivial
      · apply psi_ih
        exact h1
    case not_ phi =>
      cases phi
      case atom_ X =>
        unfold is_disj_rec_v1 at h1
        constructor
        · unfold is_nnf_rec_v1
          exact trivial
        · apply psi_ih
          exact h1
      all_goals
        unfold is_disj_rec_v1 at h1
        contradiction
    all_goals
      unfold is_disj_rec_v1 at h1
      contradiction
  all_goals
    unfold is_disj_rec_v1 at h1
    contradiction


-------------------------------------------------------------------------------


lemma is_disj_rec_v1_imp_is_disj_ind_v1
  (F : Formula_)
  (h1 : is_disj_rec_v1 F) :
  is_disj_ind_v1 F :=
  by
  induction F
  case false_ =>
    apply is_disj_ind_v1.rule_3
    apply is_constant_ind.rule_1
  case true_ =>
    apply is_disj_ind_v1.rule_3
    apply is_constant_ind.rule_2
  case atom_ X =>
    apply is_disj_ind_v1.rule_4
    apply is_literal_ind.rule_1
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      apply is_disj_ind_v1.rule_4
      apply is_literal_ind.rule_2
    all_goals
      simp only [is_disj_rec_v1] at h1
  case or_ phi psi phi_ih psi_ih =>
    cases phi
    case false_ =>
      simp only [is_disj_rec_v1] at h1
      apply is_disj_ind_v1.rule_1
      · apply is_constant_ind.rule_1
      · apply psi_ih
        exact h1
    case true_ =>
      simp only [is_disj_rec_v1] at h1
      apply is_disj_ind_v1.rule_1
      · apply is_constant_ind.rule_2
      · apply psi_ih
        exact h1
    case atom_ X =>
      simp only [is_disj_rec_v1] at h1
      apply is_disj_ind_v1.rule_2
      · apply is_literal_ind.rule_1
      · apply psi_ih
        exact h1
    case not_ phi =>
      cases phi
      case atom_ X =>
        simp only [is_disj_rec_v1] at h1
        simp only [is_disj_rec_v1] at phi_ih
        apply is_disj_ind_v1.rule_2
        · apply is_literal_ind.rule_2
        · apply psi_ih
          exact h1
      all_goals
        simp only [is_disj_rec_v1] at h1
    all_goals
      simp only [is_disj_rec_v1] at h1
  all_goals
    simp only [is_disj_rec_v1] at h1


lemma is_disj_ind_v1_imp_is_disj_rec_v1
  (F : Formula_)
  (h1 : is_disj_ind_v1 F) :
  is_disj_rec_v1 F :=
  by
  induction h1
  case rule_1 phi psi ih_1 ih_2 ih_3 =>
    cases ih_1
    case rule_1 =>
      simp only [is_disj_rec_v1]
      exact ih_3
    case rule_2 =>
      simp only [is_disj_rec_v1]
      exact ih_3
  case rule_2 phi psi ih_1 ih_2 ih_3 =>
    cases ih_1
    case rule_1 X =>
      simp only [is_disj_rec_v1]
      exact ih_3
    case rule_2 X =>
      simp only [is_disj_rec_v1]
      exact ih_3
  case rule_3 phi ih_1 =>
    cases ih_1
    case rule_1 =>
      simp only [is_disj_rec_v1]
    case rule_2 =>
      simp only [is_disj_rec_v1]
  case rule_4 phi ih_1 =>
    cases ih_1
    case rule_1 X =>
      simp only [is_disj_rec_v1]
    case rule_2 X =>
      simp only [is_disj_rec_v1]


lemma is_disj_rec_v1_iff_is_disj_ind_v1
  (F : Formula_) :
  is_disj_rec_v1 F ↔ is_disj_ind_v1 F :=
  by
  constructor
  · apply is_disj_rec_v1_imp_is_disj_ind_v1
  · apply is_disj_ind_v1_imp_is_disj_rec_v1


-------------------------------------------------------------------------------


lemma is_disj_rec_v2_imp_is_disj_ind_v2
  (F : Formula_)
  (h1 : is_disj_rec_v2 F) :
  is_disj_ind_v2 F :=
  by
  induction F
  case false_ =>
    apply is_disj_ind_v2.rule_2
    apply is_constant_ind.rule_1
  case true_ =>
    apply is_disj_ind_v2.rule_2
    apply is_constant_ind.rule_2
  case atom_ X =>
    apply is_disj_ind_v2.rule_3
    apply is_literal_ind.rule_1
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      apply is_disj_ind_v2.rule_3
      apply is_literal_ind.rule_2
    all_goals
      simp only [is_disj_rec_v2] at h1
  case or_ phi psi phi_ih psi_ih =>
    unfold is_disj_rec_v2 at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    apply is_disj_ind_v2.rule_1
    · apply phi_ih
      exact h1_left
    · apply psi_ih
      exact h1_right
  all_goals
    simp only [is_disj_rec_v2] at h1


lemma is_disj_ind_v2_imp_is_disj_rec_v2
  (F : Formula_)
  (h1 : is_disj_ind_v2 F) :
  is_disj_rec_v2 F :=
  by
  induction h1
  case rule_1 phi psi ih_1 ih_2 ih_3 ih_4 =>
    unfold is_disj_rec_v2
    exact ⟨ih_3, ih_4⟩
  case rule_2 phi ih_1 =>
    cases ih_1
    case rule_1 =>
      simp only [is_disj_rec_v2]
    case rule_2 =>
      simp only [is_disj_rec_v2]
  case rule_3 phi ih_1 =>
    cases ih_1
    case rule_1 X =>
      simp only [is_disj_rec_v2]
    case rule_2 X =>
      simp only [is_disj_rec_v2]


lemma is_disj_rec_v2_iff_is_disj_ind_v2
  (F : Formula_) :
  is_disj_rec_v2 F ↔ is_disj_ind_v2 F :=
  by
  constructor
  · apply is_disj_rec_v2_imp_is_disj_ind_v2
  · apply is_disj_ind_v2_imp_is_disj_rec_v2


-------------------------------------------------------------------------------


lemma is_conj_rec_v1_imp_is_nnf_rec_v1
  (F : Formula_)
  (h1 : F.is_conj_rec_v1) :
  F.is_nnf_rec_v1 :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold is_nnf_rec_v1
    exact trivial
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      unfold is_nnf_rec_v1
      exact trivial
    all_goals
      unfold is_conj_rec_v1 at h1
      contradiction
  case and_ phi psi phi_ih psi_ih =>
    unfold is_nnf_rec_v1
    cases phi
    case false_ | true_ | atom_ X =>
      unfold is_conj_rec_v1 at h1
      constructor
      · unfold is_nnf_rec_v1
        exact trivial
      · apply psi_ih
        exact h1
    case not_ phi =>
      cases phi
      case atom_ X =>
        unfold is_conj_rec_v1 at h1
        constructor
        · unfold is_nnf_rec_v1
          exact trivial
        · apply psi_ih
          exact h1
      all_goals
        unfold is_conj_rec_v1 at h1
        contradiction
    all_goals
      unfold is_conj_rec_v1 at h1
      contradiction
  all_goals
    unfold is_conj_rec_v1 at h1
    contradiction


-------------------------------------------------------------------------------


lemma is_conj_rec_v1_imp_is_conj_ind_v1
  (F : Formula_)
  (h1 : is_conj_rec_v1 F) :
  is_conj_ind_v1 F :=
  by
  induction F
  case false_ =>
    apply is_conj_ind_v1.rule_3
    apply is_constant_ind.rule_1
  case true_ =>
    apply is_conj_ind_v1.rule_3
    apply is_constant_ind.rule_2
  case atom_ X =>
    apply is_conj_ind_v1.rule_4
    apply is_literal_ind.rule_1
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      apply is_conj_ind_v1.rule_4
      apply is_literal_ind.rule_2
    all_goals
      simp only [is_conj_rec_v1] at h1
  case and_ phi psi phi_ih psi_ih =>
    cases phi
    case false_ =>
      simp only [is_conj_rec_v1] at h1
      apply is_conj_ind_v1.rule_1
      · apply is_constant_ind.rule_1
      · apply psi_ih
        exact h1
    case true_ =>
      simp only [is_conj_rec_v1] at h1
      apply is_conj_ind_v1.rule_1
      · apply is_constant_ind.rule_2
      · apply psi_ih
        exact h1
    case atom_ X =>
      simp only [is_conj_rec_v1] at h1
      apply is_conj_ind_v1.rule_2
      · apply is_literal_ind.rule_1
      · apply psi_ih
        exact h1
    case not_ phi =>
      cases phi
      case atom_ X =>
        simp only [is_conj_rec_v1] at h1
        simp only [is_conj_rec_v1] at phi_ih
        apply is_conj_ind_v1.rule_2
        · apply is_literal_ind.rule_2
        · apply psi_ih
          exact h1
      all_goals
        simp only [is_conj_rec_v1] at h1
    all_goals
      simp only [is_conj_rec_v1] at h1
  all_goals
    simp only [is_conj_rec_v1] at h1


lemma is_conj_ind_v1_imp_is_conj_rec_v1
  (F : Formula_)
  (h1 : is_conj_ind_v1 F) :
  is_conj_rec_v1 F :=
  by
  induction h1
  case rule_1 phi psi ih_1 ih_2 ih_3 =>
    cases ih_1
    case rule_1 =>
      simp only [is_conj_rec_v1]
      exact ih_3
    case rule_2 =>
      simp only [is_conj_rec_v1]
      exact ih_3
  case rule_2 phi psi ih_1 ih_2 ih_3 =>
    cases ih_1
    case rule_1 X =>
      simp only [is_conj_rec_v1]
      exact ih_3
    case rule_2 X =>
      simp only [is_conj_rec_v1]
      exact ih_3
  case rule_3 phi ih_1 =>
    cases ih_1
    case rule_1 =>
      simp only [is_conj_rec_v1]
    case rule_2 =>
      simp only [is_conj_rec_v1]
  case rule_4 phi ih_1 =>
    cases ih_1
    case rule_1 X =>
      simp only [is_conj_rec_v1]
    case rule_2 X =>
      simp only [is_conj_rec_v1]


lemma is_conj_rec_v1_iff_is_conj_ind_v1
  (F : Formula_) :
  is_conj_rec_v1 F ↔ is_conj_ind_v1 F :=
  by
  constructor
  · apply is_conj_rec_v1_imp_is_conj_ind_v1
  · apply is_conj_ind_v1_imp_is_conj_rec_v1


-------------------------------------------------------------------------------


lemma is_conj_rec_v2_imp_is_conj_ind_v2
  (F : Formula_)
  (h1 : is_conj_rec_v2 F) :
  is_conj_ind_v2 F :=
  by
  induction F
  case false_ =>
    apply is_conj_ind_v2.rule_2
    apply is_constant_ind.rule_1
  case true_ =>
    apply is_conj_ind_v2.rule_2
    apply is_constant_ind.rule_2
  case atom_ X =>
    apply is_conj_ind_v2.rule_3
    apply is_literal_ind.rule_1
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      apply is_conj_ind_v2.rule_3
      apply is_literal_ind.rule_2
    all_goals
      simp only [is_conj_rec_v2] at h1
  case and_ phi psi phi_ih psi_ih =>
    unfold is_conj_rec_v2 at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    apply is_conj_ind_v2.rule_1
    · apply phi_ih
      exact h1_left
    · apply psi_ih
      exact h1_right
  all_goals
    simp only [is_conj_rec_v2] at h1


lemma is_conj_ind_v2_imp_is_conj_rec_v2
  (F : Formula_)
  (h1 : is_conj_ind_v2 F) :
  is_conj_rec_v2 F :=
  by
  induction h1
  case rule_1 phi psi ih_1 ih_2 ih_3 ih_4 =>
    unfold is_conj_rec_v2
    exact ⟨ih_3, ih_4⟩
  case rule_2 phi ih_1 =>
    cases ih_1
    case rule_1 =>
      simp only [is_conj_rec_v2]
    case rule_2 =>
      simp only [is_conj_rec_v2]
  case rule_3 phi ih_1 =>
    cases ih_1
    case rule_1 X =>
      simp only [is_conj_rec_v2]
    case rule_2 X =>
      simp only [is_conj_rec_v2]


lemma is_conj_rec_v2_iff_is_conj_ind_v2
  (F : Formula_) :
  is_conj_rec_v2 F ↔ is_conj_ind_v2 F :=
  by
  constructor
  · apply is_conj_rec_v2_imp_is_conj_ind_v2
  · apply is_conj_ind_v2_imp_is_conj_rec_v2


-------------------------------------------------------------------------------


lemma is_dnf_rec_v1_imp_is_dnf_ind_v1
  (F : Formula_)
  (h1 : is_dnf_rec_v1 F) :
  is_dnf_ind_v1 F :=
  by
  induction F
  case false_ =>
    apply is_dnf_ind_v1.rule_2
    apply is_conj_ind_v1.rule_3
    apply is_constant_ind.rule_1
  case true_ =>
    apply is_dnf_ind_v1.rule_2
    apply is_conj_ind_v1.rule_3
    apply is_constant_ind.rule_2
  case atom_ X =>
    apply is_dnf_ind_v1.rule_2
    apply is_conj_ind_v1.rule_4
    apply is_literal_ind.rule_1
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      apply is_dnf_ind_v1.rule_2
      apply is_conj_ind_v1.rule_4
      apply is_literal_ind.rule_2
    all_goals
      simp only [is_dnf_rec_v1] at h1
      simp only [is_conj_rec_v1] at h1
  case and_ phi psi phi_ih psi_ih =>
    unfold is_dnf_rec_v1 at h1
    apply is_dnf_ind_v1.rule_2
    apply is_conj_rec_v1_imp_is_conj_ind_v1
    exact h1
  case or_ phi psi phi_ih psi_ih =>
    unfold is_dnf_rec_v1 at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    apply is_dnf_ind_v1.rule_1
    · apply is_conj_rec_v1_imp_is_conj_ind_v1
      exact h1_left
    · apply psi_ih
      exact h1_right
  all_goals
    simp only [is_dnf_rec_v1] at h1
    simp only [is_conj_rec_v1] at h1


lemma is_dnf_ind_v1_imp_is_dnf_rec_v1
  (F : Formula_)
  (h1 : is_dnf_ind_v1 F) :
  is_dnf_rec_v1 F :=
  by
  induction h1
  case rule_1 phi psi ih_1 ih_2 ih_3 =>
    unfold is_dnf_rec_v1
    constructor
    · apply is_conj_ind_v1_imp_is_conj_rec_v1
      exact ih_1
    · exact ih_3
  case rule_2 phi ih_1 =>
    cases ih_1
    case rule_1 phi psi phi_ih psi_ih =>
      unfold is_dnf_rec_v1
      apply is_conj_ind_v1_imp_is_conj_rec_v1
      apply is_conj_ind_v1.rule_1
      · exact phi_ih
      · exact psi_ih
    case rule_2 phi psi phi_ih psi_ih =>
      unfold is_dnf_rec_v1
      apply is_conj_ind_v1_imp_is_conj_rec_v1
      apply is_conj_ind_v1.rule_2
      · exact phi_ih
      · exact psi_ih
    case rule_3 ih =>
      cases ih
      all_goals
        unfold is_dnf_rec_v1
        unfold is_conj_rec_v1
        exact trivial
    case rule_4 ih =>
      cases ih
      all_goals
        unfold is_dnf_rec_v1
        unfold is_conj_rec_v1
        exact trivial


lemma is_dnf_rec_v1_iff_is_dnf_ind_v1
  (F : Formula_) :
  is_dnf_rec_v1 F ↔ is_dnf_ind_v1 F :=
  by
  constructor
  · apply is_dnf_rec_v1_imp_is_dnf_ind_v1
  · apply is_dnf_ind_v1_imp_is_dnf_rec_v1


-------------------------------------------------------------------------------


lemma is_dnf_rec_v2_imp_is_dnf_ind_v2
  (F : Formula_)
  (h1 : is_dnf_rec_v2 F) :
  is_dnf_ind_v2 F :=
  by
  induction F
  case false_ =>
    apply is_dnf_ind_v2.rule_2
    apply is_conj_ind_v2.rule_2
    apply is_constant_ind.rule_1
  case true_ =>
    apply is_dnf_ind_v2.rule_2
    apply is_conj_ind_v2.rule_2
    apply is_constant_ind.rule_2
  case atom_ X =>
    apply is_dnf_ind_v2.rule_2
    apply is_conj_ind_v2.rule_3
    apply is_literal_ind.rule_1
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      apply is_dnf_ind_v2.rule_2
      apply is_conj_ind_v2.rule_3
      apply is_literal_ind.rule_2
    all_goals
      simp only [is_dnf_rec_v2] at h1
      simp only [is_conj_rec_v2] at h1
  case and_ phi psi phi_ih psi_ih =>
    unfold is_dnf_rec_v2 at h1
    apply is_dnf_ind_v2.rule_2
    apply is_conj_rec_v2_imp_is_conj_ind_v2
    exact h1
  case or_ phi psi phi_ih psi_ih =>
    unfold is_dnf_rec_v2 at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    apply is_dnf_ind_v2.rule_1
    · apply phi_ih
      exact h1_left
    · apply psi_ih
      exact h1_right
  all_goals
    simp only [is_dnf_rec_v2] at h1
    simp only [is_conj_rec_v2] at h1


lemma is_dnf_ind_v2_imp_is_dnf_rec_v2
  (F : Formula_)
  (h1 : is_dnf_ind_v2 F) :
  is_dnf_rec_v2 F :=
  by
  induction h1
  case rule_1 phi psi ih_1 ih_2 ih_3 ih_4 =>
    unfold is_dnf_rec_v2
    exact ⟨ih_3, ih_4⟩
  case rule_2 phi ih_1 =>
    cases ih_1
    case rule_1 phi psi phi_ih psi_ih =>
      unfold is_dnf_rec_v2
      apply is_conj_ind_v2_imp_is_conj_rec_v2
      apply is_conj_ind_v2.rule_1
      · exact phi_ih
      · exact psi_ih
    case rule_2 ih =>
      cases ih
      all_goals
        unfold is_dnf_rec_v2
        unfold is_conj_rec_v2
        exact trivial
    case rule_3 ih =>
      cases ih
      all_goals
        unfold is_dnf_rec_v2
        unfold is_conj_rec_v2
        exact trivial


lemma is_dnf_rec_v2_iff_is_dnf_ind_v2
  (F : Formula_) :
  is_dnf_rec_v2 F ↔ is_dnf_ind_v2 F :=
  by
  constructor
  · apply is_dnf_rec_v2_imp_is_dnf_ind_v2
  · apply is_dnf_ind_v2_imp_is_dnf_rec_v2


-------------------------------------------------------------------------------


lemma is_cnf_rec_v1_imp_is_cnf_ind_v1
  (F : Formula_)
  (h1 : is_cnf_rec_v1 F) :
  is_cnf_ind_v1 F :=
  by
  induction F
  case false_ =>
    apply is_cnf_ind_v1.rule_2
    apply is_disj_ind_v1.rule_3
    apply is_constant_ind.rule_1
  case true_ =>
    apply is_cnf_ind_v1.rule_2
    apply is_disj_ind_v1.rule_3
    apply is_constant_ind.rule_2
  case atom_ X =>
    apply is_cnf_ind_v1.rule_2
    apply is_disj_ind_v1.rule_4
    apply is_literal_ind.rule_1
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      apply is_cnf_ind_v1.rule_2
      apply is_disj_ind_v1.rule_4
      apply is_literal_ind.rule_2
    all_goals
      simp only [is_cnf_rec_v1] at h1
      simp only [is_disj_rec_v1] at h1
  case and_ phi psi phi_ih psi_ih =>
    unfold is_cnf_rec_v1 at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    apply is_cnf_ind_v1.rule_1
    · apply is_disj_rec_v1_imp_is_disj_ind_v1
      exact h1_left
    · apply psi_ih
      exact h1_right
  case or_ phi psi phi_ih psi_ih =>
    unfold is_cnf_rec_v1 at h1
    apply is_cnf_ind_v1.rule_2
    apply is_disj_rec_v1_imp_is_disj_ind_v1
    exact h1
  all_goals
    simp only [is_cnf_rec_v1] at h1
    simp only [is_disj_rec_v1] at h1


lemma is_cnf_ind_v1_imp_is_cnf_rec_v1
  (F : Formula_)
  (h1 : is_cnf_ind_v1 F) :
  is_cnf_rec_v1 F :=
  by
  induction h1
  case rule_1 phi psi ih_1 ih_2 ih_3 =>
    unfold is_cnf_rec_v1
    constructor
    · apply is_disj_ind_v1_imp_is_disj_rec_v1
      exact ih_1
    · exact ih_3
  case rule_2 phi ih_1 =>
    cases ih_1
    case rule_1 phi psi phi_ih psi_ih =>
      unfold is_cnf_rec_v1
      apply is_disj_ind_v1_imp_is_disj_rec_v1
      apply is_disj_ind_v1.rule_1
      · exact phi_ih
      · exact psi_ih
    case rule_2 phi psi phi_ih psi_ih =>
      unfold is_cnf_rec_v1
      apply is_disj_ind_v1_imp_is_disj_rec_v1
      apply is_disj_ind_v1.rule_2
      · exact phi_ih
      · exact psi_ih
    case rule_3 ih =>
      cases ih
      all_goals
        unfold is_cnf_rec_v1
        unfold is_disj_rec_v1
        exact trivial
    case rule_4 ih =>
      cases ih
      all_goals
        unfold is_cnf_rec_v1
        unfold is_disj_rec_v1
        exact trivial


lemma is_cnf_rec_v1_iff_is_cnf_ind_v1
  (F : Formula_) :
  is_cnf_rec_v1 F ↔ is_cnf_ind_v1 F :=
  by
  constructor
  · apply is_cnf_rec_v1_imp_is_cnf_ind_v1
  · apply is_cnf_ind_v1_imp_is_cnf_rec_v1


#lint
