import HandbookOfPracticalLogicLean.Chapter2.Semantics

import Mathlib.Tactic


set_option autoImplicit false


open Formula_


/--
  Helper function for `simplify`.
-/
def simplify_aux :
  Formula_ → Formula_
  | not_ false_ => true_
  | not_ true_ => false_
  | not_ (not_ phi) => phi
  | and_ _ false_ => false_
  | and_ false_ _ => false_
  | and_ phi true_ => phi
  | and_ true_ psi => psi
  | or_ phi false_ => phi
  | or_ false_ psi => psi
  | or_ _ true_ => true_
  | or_ true_ _ => true_
  | imp_ false_ _ => true_
  | imp_ _ true_ => true_
  | imp_ true_ psi => psi
  | imp_ phi false_ => not_ phi
  | iff_ phi true_ => phi
  | iff_ true_ psi => psi
  | iff_ phi false_ => not_ phi
  | iff_ false_ psi => not_ psi
  | phi => phi


/--
  `simplify F` := Translates the formula `F` to a semantically equivalent formula with less than or equal to the number of subformulas as `F`.
-/
def simplify :
  Formula_ → Formula_
  | not_ phi => simplify_aux (not_ (simplify phi))
  | and_ phi psi => simplify_aux (and_ (simplify phi) (simplify psi))
  | or_ phi psi => simplify_aux (or_ (simplify phi) (simplify psi))
  | imp_ phi psi => simplify_aux (imp_ (simplify phi) (simplify psi))
  | iff_ phi psi => simplify_aux (iff_ (simplify phi) (simplify psi))
  | phi => phi


#eval simplify (Formula_| (((P -> Q) -> T.) \/ ~ F.))


-------------------------------------------------------------------------------


/--
  `simplify_aux_not F` := If the formula `F` is of the form `not_ _` then `simplify_aux F`. If the formula `F` is not of the form `not_ _` then `F`.
-/
def simplify_aux_not :
  Formula_ → Formula_
  | not_ false_ => true_
  | not_ true_ => false_
  | not_ (not_ phi) => phi
  | phi => phi


example :
  simplify_aux_not (not_ false_) = true_ :=
  by
  simp only [simplify_aux_not]


example :
  simplify_aux_not (not_ true_) = false_ :=
  by
  simp only [simplify_aux_not]


example
  (F : Formula_) :
  simplify_aux_not (not_ (not_ F)) = F :=
  by
  simp only [simplify_aux_not]


-------------------------------------------------------------------------------


/--
  `simplify_aux_and F` := If the formula `F` is of the form `and_ _ _` then `simplify_aux F`. If the formula `F` is not of the form `and_ _ _` then `F`.
-/
def simplify_aux_and :
  Formula_ → Formula_
  | and_ _ false_ => false_
  | and_ false_ _ => false_
  | and_ phi true_ => phi
  | and_ true_ phi => phi
  | phi => phi


example
  (F : Formula_) :
  simplify_aux_and (and_ F false_) = false_ :=
  by
  simp only [simplify_aux_and]


example
  (F : Formula_) :
  simplify_aux_and (and_ false_ F) = false_ :=
  by
  unfold simplify_aux_and
  split
  case _ phi psi ih_1 =>
    rfl
  case _ phi psi ih_1 ih_2 =>
    rfl
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    rfl
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
  · tauto


example
  (F : Formula_) :
  simplify_aux_and (and_ F true_) = F :=
  by
  unfold simplify_aux_and
  split
  case _ phi psi ih_1 =>
    cases ih_1
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    rfl
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    rfl
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
    rfl
  · tauto


example
  (F : Formula_) :
  simplify_aux_and (and_ true_ F) = F :=
  by
  unfold simplify_aux_and
  split
  case _ phi psi ih_1 =>
    cases ih_1
    rfl
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    rfl
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
    rfl
  · tauto


example
  (P Q : Formula_)
  (h1 : ¬ P = false_)
  (h2 : ¬ P = true_)
  (h3 : ¬ Q = false_)
  (h4 : ¬ Q = true_) :
  simplify_aux_and (and_ P Q) = and_ P Q :=
  by
  unfold simplify_aux_and
  split
  case _ phi psi ih_1 =>
    cases ih_1
    contradiction
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    contradiction
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    contradiction
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
    contradiction
  · tauto


lemma simplify_aux_and_cases
  (P Q : Formula_) :
  simplify_aux (and_ P Q) = P ∨
  simplify_aux (and_ P Q) = Q ∨
  simplify_aux (and_ P Q) = and_ P Q :=
  by
  unfold simplify_aux
  split
  any_goals
    contradiction
  any_goals
    tauto
  case _ phi psi ih_1 =>
    cases ih_1
    tauto
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    tauto
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    tauto
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
    tauto


-------------------------------------------------------------------------------


def simplify_aux_or :
  Formula_ → Formula_
  | or_ phi false_ => phi
  | or_ false_ phi => phi
  | or_ _ true_ => true_
  | or_ true_ _ => true_
  | phi => phi


example
  (F : Formula_) :
  simplify_aux_or (or_ F false_) = F :=
  by
  simp only [simplify_aux_or]


example
  (F : Formula_) :
  simplify_aux_or (or_ false_ F) = F :=
  by
  unfold simplify_aux_or
  split
  case _ phi psi ih_1 =>
    cases ih_1
    rfl
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    rfl
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    rfl
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
  · tauto


example
  (F : Formula_) :
  simplify_aux_or (or_ F true_) = true_ :=
  by
  unfold simplify_aux_or
  split
  case _ phi psi ih_1 =>
    cases ih_1
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    rfl
  case _ phi psi ih_1 ih_2 =>
    rfl
  case _ phi psi ih_1 ih_2 ih_3 =>
    rfl
  · tauto


example
  (F : Formula_) :
  simplify_aux_or (or_ true_ F) = true_ :=
  by
  unfold simplify_aux_or
  split
  case _ phi psi ih_1 =>
    cases ih_1
    rfl
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
  case _ phi psi ih_1 ih_2 =>
    rfl
  case _ phi psi ih_1 ih_2 ih_3 =>
    rfl
  · tauto


example
  (P Q : Formula_)
  (h1 : ¬ P = false_)
  (h2 : ¬ P = true_)
  (h3 : ¬ Q = false_)
  (h4 : ¬ Q = true_) :
  simplify_aux_or (or_ P Q) = or_ P Q :=
  by
  unfold simplify_aux_or
  split
  case _ phi psi ih_1 =>
    cases ih_1
    contradiction
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    contradiction
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    contradiction
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
    contradiction
  · tauto


lemma simplify_aux_or_cases
  (P Q : Formula_) :
  simplify_aux (or_ P Q) = P ∨
  simplify_aux (or_ P Q) = Q ∨
  simplify_aux (or_ P Q) = or_ P Q :=
  by
  unfold simplify_aux
  split
  any_goals
    contradiction
  any_goals
    tauto
  case _ phi psi ih_1 =>
    cases ih_1
    tauto
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    tauto
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    tauto
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
    tauto


-------------------------------------------------------------------------------


def simplify_aux_imp :
  Formula_ → Formula_
  | imp_ false_ _ => true_
  | imp_ _ true_ => true_
  | imp_ true_ phi => phi
  | imp_ phi false_ => not_ phi
  | phi => phi


example
  (F : Formula_) :
  simplify_aux_imp (imp_ false_ F) = true_ :=
  by
  simp only [simplify_aux_imp]


example
  (F : Formula_) :
  simplify_aux_imp (imp_ F true_) = true_ :=
  by
  unfold simplify_aux_imp
  split
  case _ phi psi ih_1 =>
    rfl
  case _ phi psi ih_1 ih_2 =>
    rfl
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    rfl
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
  · tauto


example
  (F : Formula_) :
  simplify_aux_imp (imp_ true_ F) = F :=
  by
  unfold simplify_aux_imp
  split
  case _ phi psi ih_1 =>
    cases ih_1
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    rfl
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    rfl
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
    exfalso
    apply ih_2
    rfl
  · tauto


example
  (F : Formula_)
  (h1 : ¬ F = false_)
  (h2 : ¬ F = true_) :
  simplify_aux_imp (imp_ F false_) = not_ F :=
  by
  unfold simplify_aux_imp
  split
  case _ phi psi ih_1 =>
    cases ih_1
    contradiction
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    contradiction
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
    rfl
  · tauto


example
  (P Q : Formula_)
  (h1 : ¬ P = false_)
  (h2 : ¬ P = true_)
  (h3 : ¬ Q = false_)
  (h4 : ¬ Q = true_) :
  simplify_aux_imp (imp_ P Q) = imp_ P Q :=
  by
  unfold simplify_aux_imp
  split
  case _ phi psi ih_1 =>
    cases ih_1
    contradiction
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    contradiction
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    contradiction
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
    contradiction
  · tauto


lemma simplify_aux_imp_cases
  (P Q : Formula_) :
  simplify_aux (imp_ P Q) = true_ ∨
  simplify_aux (imp_ P Q) = Q ∨
  simplify_aux (imp_ P Q) = not_ P ∨
  simplify_aux (imp_ P Q) = imp_ P Q :=
  by
  unfold simplify_aux
  split
  any_goals
    contradiction
  any_goals
    tauto
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    tauto
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
    tauto


-------------------------------------------------------------------------------


def simplify_aux_iff :
  Formula_ → Formula_
  | iff_ phi true_ => phi
  | iff_ true_ phi => phi
  | iff_ phi false_ => not_ phi
  | iff_ false_ phi => not_ phi
  | phi => phi


lemma simplify_aux_iff_cases
  (P Q : Formula_) :
  simplify_aux (iff_ P Q) = P ∨
  simplify_aux (iff_ P Q) = Q ∨
  simplify_aux (iff_ P Q) = not_ P ∨
  simplify_aux (iff_ P Q) = not_ Q ∨
  simplify_aux (iff_ P Q) = iff_ P Q :=
  by
  unfold simplify_aux
  split
  any_goals
    contradiction
  case _ phi psi ih_1 =>
    cases ih_1
    tauto
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    tauto
  case _ phi psi ih_1 ih_2 =>
    cases ih_2
    tauto
  case _ phi psi ih_1 ih_2 ih_3 =>
    cases ih_3
    tauto
  · tauto


-------------------------------------------------------------------------------


lemma simplify_aux_is_logically_equivalent
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = eval V (simplify_aux F) :=
  by
  cases F
  case false_ | true_ | atom_ X =>
    simp only [simplify_aux]
  case not_ phi =>
    cases phi
    all_goals
      simp only [simplify_aux]
    all_goals
      simp only [eval]
      rewrite [Bool.eq_iff_iff]
      simp only [bool_iff_prop_not]
    all_goals
      tauto
  case
      and_ phi psi
    | or_ phi psi
    | imp_ phi psi
    | iff_ phi psi =>
    cases phi
    all_goals
      cases psi
      all_goals
        simp only [simplify_aux]
      all_goals
        simp only [eval]
        rewrite [Bool.eq_iff_iff]
        simp only [bool_iff_prop_not, bool_iff_prop_and, bool_iff_prop_or, bool_iff_prop_imp, bool_iff_prop_iff]
      all_goals
        tauto


lemma simplify_is_logically_equivalent
  (V : ValuationAsTotalFunction)
  (F : Formula_) :
  eval V F = eval V (simplify F) :=
  by
  induction F
  case false_ | true_ | atom_ X =>
    rfl
  case not_ phi ih =>
    unfold simplify
    rewrite [← simplify_aux_is_logically_equivalent]
    unfold eval
    rewrite [ih]
    rfl
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold simplify
    rewrite [← simplify_aux_is_logically_equivalent]
    unfold eval
    rewrite [phi_ih]
    rewrite [psi_ih]
    rfl


example
  (F : Formula_) :
  are_logically_equivalent F (simplify F) :=
  by
  simp only [are_logically_equivalent_iff_eval_eq]
  intro V
  apply simplify_is_logically_equivalent
