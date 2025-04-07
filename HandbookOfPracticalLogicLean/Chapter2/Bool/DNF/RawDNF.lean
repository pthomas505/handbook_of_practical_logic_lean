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


example
  (P Q : Formula_)
  (h1 : is_dnf_ind P)
  (h2 : is_dnf_ind Q) :
  is_dnf_ind (distrib (and_ P Q)) := sorry


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
    unfold raw_dnf
    sorry
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
