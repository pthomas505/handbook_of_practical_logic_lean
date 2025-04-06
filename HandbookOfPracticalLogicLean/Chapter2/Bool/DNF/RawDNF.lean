import HandbookOfPracticalLogicLean.Chapter2.Bool.DNF.IsDNF


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
#eval is_dnf_rec (raw_dnf (Formula_| ((p \/ (q /\ r)) /\ (~p \/ ~ r))))


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
