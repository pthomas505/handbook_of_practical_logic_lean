import HandbookOfPracticalLogicLean.Chapter2.NNF


set_option autoImplicit false


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


lemma is_conj_ind_and_imp
  (P Q : Formula_)
  (h1 : is_conj_ind (and_ P Q)) :
  is_conj_ind P ∧ is_conj_ind Q :=
  by
  cases h1
  case rule_1 ih_1 ih_2 =>
    constructor
    · apply is_conj_ind.rule_3
      exact ih_1
    · exact ih_2
  case rule_2 ih_1 ih_2 =>
    constructor
    · apply is_conj_ind.rule_4
      exact ih_1
    · exact ih_2
  case rule_3 ih =>
    contradiction
  case rule_4 ih =>
    contradiction


lemma not_is_conj_ind_or
  (P Q : Formula_) :
  ¬ is_conj_ind (or_ P Q) :=
  by
  intro contra
  cases contra
  case rule_3 ih =>
    contradiction
  case rule_4 ih =>
    contradiction


lemma is_dnf_ind_or_iff
  (P Q : Formula_) :
  is_dnf_ind (or_ P Q) ↔ (is_conj_ind P ∧ is_dnf_ind Q) :=
  by
  constructor
  · intro a1
    cases a1
    case rule_1 ih_1 ih_2 =>
      exact ⟨ih_1, ih_2⟩
    case rule_2 ih =>
      simp only [not_is_conj_ind_or] at ih
  · intro a1
    obtain ⟨a1_left, a1_right⟩ := a1
    apply is_dnf_ind.rule_1
    · exact a1_left
    · exact a1_right


lemma is_dnf_ind_and_imp
  (P Q : Formula_)
  (h1 : is_dnf_ind (and_ P Q)) :
  is_conj_ind P ∧ is_conj_ind Q :=
  by
  cases h1
  case rule_2 ih =>
    apply is_conj_ind_and_imp
    exact ih
