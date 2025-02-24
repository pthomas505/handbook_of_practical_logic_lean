import HandbookOfPracticalLogicLean.Chapter2.Bool.Replace
import HandbookOfPracticalLogicLean.Chapter2.Bool.Semantics
import HandbookOfPracticalLogicLean.Chapter2.Bool.SubFormula

import Mathlib.Tactic


set_option autoImplicit false


namespace Bool_


open Formula_


/--
  `Formula_.is_literal F` := True if and only if the formula `F` is an atomic formula or the negation of an atomic formula.
-/
def Formula_.is_literal :
  Formula_ → Prop
  | atom_ _ => True
  | not_ (atom_ _) => True
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_literal F) :=
  by
  induction F
  case not_ phi ih =>
    unfold is_literal
    split
    all_goals
      infer_instance
  all_goals
    simp only [is_literal]
    infer_instance


/--
  `Formula_.is_negative_literal F` := True if and only if the formula `F` is a negative literal.
-/
def Formula_.is_negative_literal :
  Formula_ → Prop
  | not_ (atom_ _) => True
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_negative_literal F) :=
  by
  induction F
  case not_ phi ih =>
    unfold is_negative_literal
    split
    all_goals
      infer_instance
  all_goals
    simp only [is_negative_literal]
    infer_instance


/--
  `Formula_.is_positive_literal F` := True if and only if the formula `F` is a positive literal.
-/
def Formula_.is_positive_literal :
  Formula_ → Prop
  | atom_ _ => True
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_positive_literal F) :=
  by
  induction F
  all_goals
    simp only [is_positive_literal]
    infer_instance


/--
  `negate_literal F` := The result of negating the formula `F` if `F` is a literal.
-/
def negate_literal :
  Formula_ → Formula_
  | atom_ X => not_ (atom_ X)
  | not_ (atom_ X) => atom_ X
  | phi => phi


/--
  `Formula_.is_nnf F` := True if and only if the formula `F` is in negation normal form.
-/
def Formula_.is_nnf :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => True
  | and_ phi psi => phi.is_nnf ∧ psi.is_nnf
  | or_ phi psi => phi.is_nnf ∧ psi.is_nnf
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_nnf F) :=
  by
  induction F
  case not_ phi ih =>
    cases phi
    all_goals
      simp only [is_nnf]
      infer_instance
  all_goals
    simp only [is_nnf]
    infer_instance


-------------------------------------------------------------------------------


mutual
/--
  `to_nnf_v1 F` := The result of translating the formula `F` to a logically equivalent formula in negation normal form.
-/
def to_nnf_v1 :
  Formula_ → Formula_
  | not_ phi => to_nnf_neg_v1 phi
  | and_ phi psi => and_ (to_nnf_v1 phi) (to_nnf_v1 psi)
  | or_ phi psi => or_ (to_nnf_v1 phi) (to_nnf_v1 psi)
  | imp_ phi psi => or_ (to_nnf_neg_v1 phi) (to_nnf_v1 psi)
  | iff_ phi psi => or_ (and_ (to_nnf_v1 phi) (to_nnf_v1 psi)) (and_ (to_nnf_neg_v1 phi) (to_nnf_neg_v1 psi))
  | phi => phi

/--
  `to_nnf_neg_v1 F` := The result of translating the formula `not_ F` to a logically equivalent formula in negation normal form.
-/
def to_nnf_neg_v1 :
  Formula_ → Formula_
  | false_ => true_
  | true_ => false_
  | not_ phi => to_nnf_v1 phi
  | and_ phi psi => or_ (to_nnf_neg_v1 phi) (to_nnf_neg_v1 psi)
  | or_ phi psi => and_ (to_nnf_neg_v1 phi) (to_nnf_neg_v1 psi)
  | imp_ phi psi => and_ (to_nnf_v1 phi) (to_nnf_neg_v1 psi)
  | iff_ phi psi => or_ (and_ (to_nnf_v1 phi) (to_nnf_neg_v1 psi)) (and_ (to_nnf_neg_v1 phi) (to_nnf_v1 psi))
  | phi => not_ phi
end

#eval to_nnf_v1 false_
#eval to_nnf_v1 (not_ false_)
#eval to_nnf_v1 (not_ (not_ false_))
#eval to_nnf_v1 (not_ (not_ (not_ false_)))
#eval to_nnf_v1 (not_ (not_ (not_ (not_ false_))))


theorem eval_to_nnf_neg_iff_not_eval_to_nnf_v1
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V (to_nnf_neg_v1 F) = b_not (eval V (to_nnf_v1 F)) :=
  by
  induction F
  case false_ | true_ =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    simp only [eval]
    tauto
  case atom_ X =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    simp only [eval]
  case not_ phi ih =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    rewrite [ih]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto


example
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = eval V (to_nnf_v1 F) :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v1
    rfl
  case not_ phi ih =>
    simp only [to_nnf_v1]
    simp only [eval]
    rewrite [ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v1 V phi]
    rfl
  case and_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case or_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case imp_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v1 V phi]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto
  case iff_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v1 V phi]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v1 V psi]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto


lemma to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v1
  (F : Formula_) :
  (to_nnf_neg_v1 F).is_nnf ↔ (to_nnf_v1 F).is_nnf :=
  by
  induction F
  case true_ | false_ | atom_ X =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    simp only [is_nnf]
  case not_ phi ih =>
    simp only [to_nnf_v1]
    simp only [to_nnf_neg_v1]
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [is_nnf]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


example
  (F : Formula_) :
  (to_nnf_v1 F).is_nnf :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v1
    unfold is_nnf
    exact trivial
  case not_ phi ih =>
    simp only [to_nnf_v1]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v1]
    apply ih
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [is_nnf]
    tauto
  case imp_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [is_nnf]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v1]
    tauto
  case iff_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v1]
    simp only [is_nnf]
    simp only [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v1]
    tauto


-------------------------------------------------------------------------------


mutual
/--
  `to_nnf_v2 F` := The result of translating the formula `F` to a logically equivalent formula in negation normal form.
-/
def to_nnf_v2 :
  Formula_ → Formula_
  | not_ phi => to_nnf_neg_v2 phi
  | and_ phi psi => and_ (to_nnf_v2 phi) (to_nnf_v2 psi)
  | or_ phi psi => or_ (to_nnf_v2 phi) (to_nnf_v2 psi)
  | imp_ phi psi => or_ (to_nnf_neg_v2 phi) (to_nnf_v2 psi)
  | iff_ phi psi => or_ (and_ (to_nnf_v2 phi) (to_nnf_v2 psi)) (and_ (to_nnf_neg_v2 phi) (to_nnf_neg_v2 psi))
  | phi => phi

/--
  `to_nnf_neg_v2 F` := The result of translating the formula `not_ F` to a logically equivalent formula in negation normal form.
-/
def to_nnf_neg_v2 :
  Formula_ → Formula_
  | not_ phi => to_nnf_v2 phi
  | and_ phi psi => or_ (to_nnf_neg_v2 phi) (to_nnf_neg_v2 psi)
  | or_ phi psi => and_ (to_nnf_neg_v2 phi) (to_nnf_neg_v2 psi)
  | imp_ phi psi => and_ (to_nnf_v2 phi) (to_nnf_neg_v2 psi)
  | iff_ phi psi => or_ (and_ (to_nnf_v2 phi) (to_nnf_neg_v2 psi)) (and_ (to_nnf_neg_v2 phi) (to_nnf_v2 psi))
  | phi => not_ phi
end

#eval to_nnf_v2 false_
#eval to_nnf_v2 (not_ false_)
#eval to_nnf_v2 (not_ (not_ false_))
#eval to_nnf_v2 (not_ (not_ (not_ false_)))
#eval to_nnf_v2 (not_ (not_ (not_ (not_ false_))))


theorem eval_to_nnf_neg_iff_not_eval_to_nnf_v2
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V (to_nnf_neg_v2 F) = b_not (eval V (to_nnf_v2 F)) :=
  by
  induction F
  case false_ | true_ =>
    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    simp only [eval]
  case atom_ X =>
    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    simp only [eval]
  case not_ phi ih =>
    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    rewrite [ih]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto


example
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = eval V (to_nnf_v2 F) :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v2
    rfl
  case not_ phi ih =>
    simp only [to_nnf_v2]
    simp only [eval]
    rewrite [ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v2 V phi]
    rfl
  case and_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case or_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl
  case imp_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v2 V phi]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto
  case iff_ phi psi phi_ih psi_ih =>
    simp only [to_nnf_v2]
    simp only [eval]
    rewrite [phi_ih]
    rewrite [psi_ih]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v2 V phi]
    rewrite [eval_to_nnf_neg_iff_not_eval_to_nnf_v2 V psi]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto


lemma to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v2
  (F : Formula_)
  (h1 : ¬ is_subformula false_ F)
  (h2 : ¬ is_subformula true_ F) :
  (to_nnf_neg_v2 F).is_nnf ↔ (to_nnf_v2 F).is_nnf :=
  by
  induction F
  case false_ =>
    simp only [is_subformula] at h1
    contradiction
  case true_ =>
    simp only [is_subformula] at h2
    contradiction
  case atom_ X =>
    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    simp only [is_nnf]
  case not_ phi ih =>
    simp only [is_subformula] at h1
    simp only [is_subformula] at h2

    simp only [to_nnf_v2]
    simp only [to_nnf_neg_v2]
    tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    simp only [is_subformula] at h1
    simp only [is_subformula] at h2

    simp only [is_nnf]
    tauto


example
  (F : Formula_)
  (h2 : ¬ is_proper_subformula false_ F)
  (h3 : ¬ is_proper_subformula true_ F) :
  (to_nnf_v2 F).is_nnf :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    unfold to_nnf_v2
    unfold is_nnf
    exact trivial
  case not_ phi ih =>
    simp only [is_proper_subformula] at h2
    simp only [is_subformula] at h2

    simp only [is_proper_subformula] at h3
    simp only [is_subformula] at h3

    simp only [to_nnf_v2]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v2]
    apply ih
    · simp only [is_proper_subformula]
      tauto
    · simp only [is_proper_subformula]
      tauto
    · tauto
    · tauto
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    simp only [is_proper_subformula] at h2
    simp only [is_subformula] at h2

    simp only [is_proper_subformula] at h3
    simp only [is_subformula] at h3

    simp only [is_proper_subformula] at phi_ih
    simp only [is_proper_subformula] at psi_ih

    simp only [to_nnf_v2]
    simp only [is_nnf]
    tauto
  case imp_ phi psi phi_ih psi_ih =>
    simp only [is_proper_subformula] at h2
    simp only [is_subformula] at h2

    simp only [is_proper_subformula] at h3
    simp only [is_subformula] at h3

    simp only [is_proper_subformula] at phi_ih
    simp only [is_proper_subformula] at psi_ih

    simp only [to_nnf_v2]
    simp only [is_nnf]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v2]
    all_goals
      tauto
  case iff_ phi psi phi_ih psi_ih =>
    simp only [is_proper_subformula] at h2
    simp only [is_subformula] at h2

    simp only [is_proper_subformula] at h3
    simp only [is_subformula] at h3

    simp only [is_proper_subformula] at phi_ih
    simp only [is_proper_subformula] at psi_ih

    simp only [to_nnf_v2]
    simp only [is_nnf]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v2]
    rewrite [to_nnf_neg_is_nnf_iff_to_nnf_is_nnf_v2]
    all_goals
      tauto


-------------------------------------------------------------------------------


/--
  `Formula_.is_pos_nnf F` := True if and only if the formula `F` is in negation normal form and every atom in `F` occurs unnegated.
-/
def Formula_.is_pos_nnf :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => True
  | not_ (atom_ _) => False
  | and_ phi psi => phi.is_pos_nnf ∧ psi.is_pos_nnf
  | or_ phi psi => phi.is_pos_nnf ∧ psi.is_pos_nnf
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_pos_nnf F) :=
  by
  induction F
  case not_ phi ih =>
    cases phi
    all_goals
      simp only [is_pos_nnf]
      infer_instance
  all_goals
    simp only [is_pos_nnf]
    infer_instance


example
  (F : Formula_)
  (h1 : F.is_pos_nnf) :
  F.is_nnf :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    simp only [is_nnf]
  case not_ phi ih =>
    cases phi
    all_goals
      simp only [is_pos_nnf] at h1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    simp only [is_pos_nnf] at h1

    simp only [is_nnf]
    tauto
  all_goals
    simp only [is_pos_nnf] at h1


-------------------------------------------------------------------------------


/--
  `Formula_.is_neg_nnf F` := True if and only if the formula `F` is in negation normal form and every atom in `F` occurs negated.
-/
def Formula_.is_neg_nnf :
  Formula_ → Prop
  | false_ => True
  | true_ => True
  | atom_ _ => False
  | not_ (atom_ _) => True
  | and_ phi psi => phi.is_neg_nnf ∧ psi.is_neg_nnf
  | or_ phi psi => phi.is_neg_nnf ∧ psi.is_neg_nnf
  | _ => False

instance
  (F : Formula_) :
  Decidable (Formula_.is_neg_nnf F) :=
  by
  induction F
  case not_ phi ih =>
    cases phi
    all_goals
      simp only [is_neg_nnf]
      infer_instance
  all_goals
    simp only [is_neg_nnf]
    infer_instance


example
  (F : Formula_)
  (h1 : F.is_neg_nnf) :
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
      simp only [is_neg_nnf] at h1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    simp only [is_neg_nnf] at h1

    simp only [is_nnf]
    tauto
  all_goals
    simp only [is_neg_nnf] at h1


-------------------------------------------------------------------------------


/--
  `is_pos_literal_in A F` := True if and only if there is an occurrence of the atom `A` as a positive literal in the formula `F`.
-/
def is_pos_literal_in
  (A : String) :
  Formula_ → Prop
  | false_ => False
  | true_ => False
  | atom_ X => A = X
  | not_ (atom_ _) => False
  | not_ phi => is_pos_literal_in A phi
  | and_ phi psi => is_pos_literal_in A phi ∨ is_pos_literal_in A psi
  | or_ phi psi => is_pos_literal_in A phi ∨ is_pos_literal_in A psi
  | imp_ phi psi => is_pos_literal_in A phi ∨ is_pos_literal_in A psi
  | iff_ phi psi => is_pos_literal_in A phi ∨ is_pos_literal_in A psi


/--
  `is_neg_literal_in A F` := True if and only if there is an occurrence of the atom `A` as a negative literal in the formula `F`.
-/
def is_neg_literal_in
  (A : String) :
  Formula_ → Prop
  | false_ => False
  | true_ => False
  | atom_ _ => False
  | not_ (atom_ X) => A = X
  | not_ phi => is_neg_literal_in A phi
  | and_ phi psi => is_neg_literal_in A phi ∨ is_neg_literal_in A psi
  | or_ phi psi => is_neg_literal_in A phi ∨ is_neg_literal_in A psi
  | imp_ phi psi => is_neg_literal_in A phi ∨ is_neg_literal_in A psi
  | iff_ phi psi => is_neg_literal_in A phi ∨ is_neg_literal_in A psi


example
  (A A' : String)
  (F : Formula_)
  (h1 : F.is_nnf)
  (h2 : ¬ is_neg_literal_in A F) :
  ∀ (V : ValuationAsTotalFunction), eval V (((atom_ A).imp_ (atom_ A')).imp_ (F.imp_ (replace_atom_one_rec A (atom_ A') F))) :=
  by
  intro V
  induction F
  case false_ | true_ =>
    unfold replace_atom_one_rec
    simp only [eval]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto
  case atom_ X =>
    unfold replace_atom_one_rec
    simp only [eval]
    split_ifs
    case pos c1 =>
      rewrite [c1]
      unfold eval
      rewrite [Bool.eq_iff_iff]
      simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
      tauto
    case neg c1 =>
      unfold eval
      rewrite [Bool.eq_iff_iff]
      simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
      tauto
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      simp only [is_neg_literal_in] at h2
      simp only [replace_atom_one_rec]
      split_ifs
      simp only [eval]
      rewrite [Bool.eq_iff_iff]
      simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
      tauto
    all_goals
      simp only [is_nnf] at h1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    simp only [is_nnf] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [is_neg_literal_in] at h2
    simp at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    simp only [eval] at phi_ih
    simp only [eval] at psi_ih

    simp only [replace_atom_one_rec]
    simp only [eval]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff] at *
    tauto
  all_goals
    simp only [is_nnf] at h1


example
  (A A' : String)
  (F : Formula_)
  (h1 : F.is_nnf)
  (h2 : ¬ is_pos_literal_in A F) :
  ∀ (V : ValuationAsTotalFunction), eval V (((atom_ A).imp_ (atom_ A')).imp_ ((replace_atom_one_rec A (atom_ A') F).imp_ F)) = true :=
  by
  intro V
  induction F
  case false_ | true_ =>
    unfold replace_atom_one_rec
    simp only [eval]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto
  case atom_ X =>
    simp only [is_pos_literal_in] at h2
    unfold replace_atom_one_rec
    split_ifs
    simp only [eval]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
    tauto
  case not_ phi ih =>
    cases phi
    case atom_ X =>
      simp only [replace_atom_one_rec]
      split_ifs
      case pos c1 =>
        simp only [eval]
        rewrite [c1]
        rewrite [Bool.eq_iff_iff]
        simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
        tauto
      case neg c1 =>
        simp only [eval]
        rewrite [Bool.eq_iff_iff]
        simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
        tauto
    all_goals
      simp only [is_nnf] at h1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih =>
    simp only [is_nnf] at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [is_pos_literal_in] at h2
    simp at h2
    obtain ⟨h2_left, h2_right⟩ := h2

    simp only [eval] at phi_ih
    simp only [eval] at psi_ih

    simp only [replace_atom_one_rec]
    simp only [eval]
    rewrite [Bool.eq_iff_iff]
    simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff] at *
    tauto
  all_goals
    simp only [is_nnf] at h1


#lint
