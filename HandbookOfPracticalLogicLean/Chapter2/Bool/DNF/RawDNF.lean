import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.IsDNF_2


set_option autoImplicit false


namespace Bool_


open Formula_


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


-------------------------------------------------------------------------------


lemma is_dnf_ind_distrib_and
  (P Q : Formula_)
  (h1 : is_nnf P)
  (h2 : is_nnf Q)
  (h3 : is_dnf_ind P)
  (h4 : is_dnf_ind Q) :
  is_dnf_ind (distrib (and_ P Q)) :=
  by
  induction Q generalizing P
  case or_ T U T_ih U_ih =>
    unfold is_nnf at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    simp only [distrib]
    apply is_dnf_ind.rule_1
    · apply T_ih
      · exact h1
      · exact h2_left
      · exact h3
      · cases h4
        case rule_1 h4_ih_1 h4_ih_2 =>
          exact h4_ih_1
        case rule_2 h4_ih =>
          contradiction
    · apply U_ih
      · exact h1
      · exact h2_right
      · exact h3
      · cases h4
        case rule_1 h4_ih_1 h4_ih_2 =>
          exact h4_ih_2
        case rule_2 h4_ih =>
          contradiction
  all_goals
    induction P
    case or_ R S R_ih S_ih =>
      unfold is_nnf at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      simp only [distrib]
      apply is_dnf_ind.rule_1
      · apply R_ih
        · exact h1_left
        · cases h3
          case rule_1 h3_ih_1 h3_ih_2 =>
            exact h3_ih_1
          case rule_2 h3_ih =>
            contradiction
      · apply S_ih
        · exact h1_right
        · cases h3
          case rule_1 h3_ih_1 h3_ih_2 =>
            exact h3_ih_2
          case rule_2 h3_ih =>
            contradiction
    any_goals
      simp only [distrib]
      apply is_dnf_ind.rule_2
      apply is_conj_ind.rule_1
    any_goals
      cases h3
      cases h4
      assumption


lemma is_nnf_distrib_and
  (P Q : Formula_)
  (h1 : is_nnf P)
  (h2 : is_nnf Q) :
  is_nnf (distrib (and_ P Q)) :=
  by
  induction Q generalizing P
  case or_ T U T_ih U_ih =>
    unfold is_nnf at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    simp only [distrib]
    unfold is_nnf
    constructor
    · apply T_ih
      · exact h1
      · exact h2_left
    · apply U_ih
      · exact h1
      · exact h2_right
  case and_ T U T_ih Q_ih =>
    induction P
    case or_ R S R_ih S_ih =>
      unfold is_nnf at h1
      obtain ⟨h1_left, h1_right⟩ := h1

      simp only [distrib]
      unfold is_nnf
      constructor
      · apply R_ih
        exact h1_left
      · apply S_ih
        exact h1_right
    all_goals
      sorry
  all_goals
    sorry


lemma is_nnf_raw_dnf
  (F : Formula_)
  (h1 : is_nnf F) :
  is_nnf (raw_dnf F) :=
  by
  induction F
  case and_ phi psi phi_ih psi_ih =>
    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold raw_dnf
    apply is_nnf_distrib_and
    · apply phi_ih
      exact h1_left
    · apply psi_ih
      exact h1_right
  case or_ phi psi phi_ih psi_ih =>
    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold raw_dnf
    unfold is_nnf
    constructor
    · apply phi_ih
      exact h1_left
    · apply psi_ih
      exact h1_right
  all_goals
    unfold raw_dnf
    exact h1


example
  (F : Formula_)
  (h1 : is_nnf F) :
  is_dnf_ind (raw_dnf F) :=
  by
  induction F
  case false_ =>
    unfold raw_dnf
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_2
    exact is_constant_ind.rule_1
  case true_ =>
    unfold raw_dnf
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_2
    exact is_constant_ind.rule_2
  case atom_ X =>
    unfold raw_dnf
    apply is_dnf_ind.rule_2
    apply is_conj_ind.rule_3
    apply is_literal_ind.rule_1
  case not_ phi ih =>
    unfold raw_dnf
    cases phi
    case atom_ X =>
      apply is_dnf_ind.rule_2
      apply is_conj_ind.rule_3
      apply is_literal_ind.rule_2
    all_goals
      unfold is_nnf at h1
      contradiction
  case and_ P Q P_ih Q_ih =>
    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold raw_dnf
    specialize P_ih h1_left
    specialize Q_ih h1_right
    apply is_dnf_ind_distrib_and
    · apply is_nnf_raw_dnf
      exact h1_left
    · apply is_nnf_raw_dnf
      exact h1_right
    · exact P_ih
    · exact Q_ih
  case or_ P Q P_ih Q_ih =>
    unfold is_nnf at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    unfold raw_dnf
    apply is_dnf_ind.rule_1
    · apply P_ih
      exact h1_left
    · apply Q_ih
      exact h1_right
  all_goals
    simp only [is_nnf] at h1


-------------------------------------------------------------------------------


example
  (V : ValuationAsTotalFunction)
  (P Q R : Formula_) :
  eval V (and_ (or_ P Q) R) = true ↔ eval V (or_ (and_ P R) (and_ Q R)) = true :=
  by
  simp only [eval]
  simp only [bool_iff_prop_and]
  simp only [bool_iff_prop_or]
  simp only [bool_iff_prop_and]
  exact or_and_right


example
  (V : ValuationAsTotalFunction)
  (P Q R : Formula_) :
  eval V (and_ P (or_ Q R)) = true ↔
    eval V (or_ (and_ P Q) (and_ P R)) = true :=
  by
  simp only [eval]
  simp only [bool_iff_prop_and]
  simp only [bool_iff_prop_or]
  simp only [bool_iff_prop_and]
  exact and_or_left


lemma eval_distrib_and
  (V : ValuationAsTotalFunction)
  (P Q : Formula_) :
  eval V (and_ P Q) = true ↔ eval V (distrib (and_ P Q)) :=
  by
  induction P generalizing Q
  case or_ R S R_ih S_ih =>
    induction Q
    case or_ T U T_ih U_ih =>
      simp only [distrib]
      simp only [eval]
      simp only [bool_iff_prop_and]
      simp only [bool_iff_prop_or]
      rewrite [← T_ih]
      rewrite [← U_ih]
      simp only [eval]
      simp only [bool_iff_prop_and]
      simp only [bool_iff_prop_or]
      exact and_or_left
    all_goals
      simp only [distrib]
      simp only [eval]
      simp only [bool_iff_prop_and]
      simp only [bool_iff_prop_or]
      rewrite [← R_ih]
      rewrite [← S_ih]
      simp only [eval]
      simp only [bool_iff_prop_and]
      exact or_and_right
  all_goals
    induction Q
    case or_ T U T_ih U_ih =>
      simp only [distrib]
      simp only [eval]
      simp only [bool_iff_prop_and]
      simp only [bool_iff_prop_or]
      rewrite [← T_ih]
      rewrite [← U_ih]
      simp only [eval]
      simp only [bool_iff_prop_and]
      exact and_or_left
    all_goals
      simp only [distrib]


example
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = true ↔ eval V (raw_dnf F) = true :=
  by
  induction F
  case and_ phi psi phi_ih psi_ih =>
    unfold raw_dnf
    simp only [← eval_distrib_and]
    simp only [eval]
    simp only [bool_iff_prop_and]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case or_ phi psi phi_ih psi_ih =>
    unfold raw_dnf
    simp only [eval]
    simp only [bool_iff_prop_or]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  all_goals
    unfold raw_dnf
    rfl
