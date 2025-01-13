import MathlibExtraLean.FunctionUpdateITE

import Lean
import Batteries.Tactic.Lint.Frontend
import Mathlib.Util.CompileInductive
import Mathlib.Tactic


set_option autoImplicit false


namespace prop


/--
  The type of formulas.
-/
inductive Formula_ : Type
  | false_ : Formula_
  | true_ : Formula_
  | atom_ : String → Formula_
  | not_ : Formula_ → Formula_
  | and_ : Formula_ → Formula_ → Formula_
  | or_ : Formula_ → Formula_ → Formula_
  | imp_ : Formula_ → Formula_ → Formula_
  | iff_ : Formula_ → Formula_ → Formula_
  deriving Inhabited, DecidableEq, Repr

compile_inductive% Formula_


/--
  The string representation of formulas.
-/
def Formula_.toString :
  Formula_ → String
  | false_ => "F"
  | true_ => "T"
  | atom_ X => s! "{X}"
  | not_ phi => s! "(¬ {phi.toString})"
  | and_ phi psi => s! "({phi.toString} ∧ {psi.toString})"
  | or_ phi psi => s! "({phi.toString} ∨ {psi.toString})"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"
  | iff_ phi psi => s! "({phi.toString} ↔ {psi.toString})"

instance : ToString Formula_ :=
  { toString := Formula_.toString }

#check Formula_.atom_ "P"


open Lean Elab Meta

declare_syntax_cat formula


syntax "F." : formula
syntax "T." : formula
syntax ident : formula
syntax "~" formula : formula
syntax "(" formula "->" formula ")" : formula
syntax "(" formula "/\\" formula ")" : formula
syntax "(" formula "\\/" formula ")" : formula
syntax "(" formula "<->" formula ")" : formula


partial def elabFormula : Syntax → MetaM Expr
  | `(formula| F.) => mkAppM ``Formula_.false_ #[]

  | `(formula| T.) => mkAppM ``Formula_.true_ #[]

  | `(formula| $X:ident) => do
    let X' : Expr := Lean.mkStrLit X.getId.toString
    mkAppM ``Formula_.atom_ #[X']

  | `(formula| ~ $phi) => do
    let phi' : Expr ← elabFormula phi
    mkAppM ``Formula_.not_ #[phi']

  | `(formula| ($phi:formula /\ $psi:formula)) => do
    let phi' : Expr ← elabFormula phi
    let psi' : Expr ← elabFormula psi
    mkAppM ``Formula_.and_ #[phi', psi']

  | `(formula| ($phi:formula \/ $psi:formula)) => do
    let phi' : Expr ← elabFormula phi
    let psi' : Expr ← elabFormula psi
    mkAppM ``Formula_.or_ #[phi', psi']

  | `(formula| ($phi:formula -> $psi:formula)) => do
    let phi' : Expr ← elabFormula phi
    let psi' : Expr ← elabFormula psi
    mkAppM ``Formula_.imp_ #[phi', psi']

  | `(formula| ($phi:formula <-> $psi:formula)) => do
    let phi' : Expr ← elabFormula phi
    let psi' : Expr ← elabFormula psi
    mkAppM ``Formula_.iff_ #[phi', psi']

  | _ => throwUnsupportedSyntax


elab "(Formula_|" p:formula ")" : term => elabFormula p


#check (Formula_| F. )
#check (Formula_| T. )
#check (Formula_| P )
#check (Formula_| ~ P )
#check (Formula_| (P /\ Q) )
#check (Formula_| (P \/ Q) )
#check (Formula_| (P -> Q) )
#check (Formula_| (P <-> Q) )


open Formula_

def Formula_.map_atoms
  (f : String → Formula_) :
  Formula_ → Formula_
  | false_ => false_
  | true_ => true_
  | atom_ X => f X
  | not_ phi => not_ (phi.map_atoms f)
  | and_ phi psi => and_ (phi.map_atoms f) (psi.map_atoms f)
  | or_ phi psi => or_ (phi.map_atoms f) (psi.map_atoms f)
  | imp_ phi psi => imp_ (phi.map_atoms f) (psi.map_atoms f)
  | iff_ phi psi => iff_ (phi.map_atoms f) (psi.map_atoms f)


-- Applies function f to all of the atoms of the formula, from right to left.
def Formula_.foldr_atoms
  {α : Type}
  (f : String → α → α)
  (init : α) :
  Formula_ → α
  | false_
  | true_ => init
  | atom_ X => f X init
  | not_ phi => phi.foldr_atoms f init
  | and_ phi psi
  | or_ phi psi
  | imp_ phi psi
  | iff_ phi psi => phi.foldr_atoms f (psi.foldr_atoms f init)


def atom_occurs_in
  (A : String) :
  Formula_ → Prop
  | false_
  | true_ => False
  | atom_ X => A = X
  | not_ phi => atom_occurs_in A phi
  | and_ phi psi
  | or_ phi psi
  | imp_ phi psi
  | iff_ phi psi => atom_occurs_in A phi ∨ atom_occurs_in A psi


def Valuation : Type := String → Prop
  deriving Inhabited


def eval
  (V : Valuation) :
  Formula_ → Prop
  | false_ => False
  | true_ => True
  | atom_ X => V X
  | not_ phi => ¬ eval V phi
  | and_ phi psi => eval V phi ∧ eval V psi
  | or_ phi psi => eval V phi ∨ eval V psi
  | imp_ phi psi => eval V phi → eval V psi
  | iff_ phi psi => eval V phi ↔ eval V psi

instance
  (V : Valuation)
  [DecidablePred V]
  (F : Formula_) :
  Decidable (eval V F) :=
  by
  induction F
  all_goals
    simp only [eval]
    infer_instance


theorem theorem_2_2
  (V V' : Valuation)
  (F : Formula_)
  (h1 : ∀ (A : String), atom_occurs_in A F → V A = V' A) :
  eval V F = eval V' F :=
  by
  induction F
  all_goals
    unfold eval
  case false_ | true_ =>
    rfl
  case atom_ X =>
    apply h1
    unfold atom_occurs_in
    rfl
  case not_ phi ih =>
    congr 1
    apply ih
    intro X a1
    apply h1
    unfold atom_occurs_in
    exact a1
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    congr 1
    · apply phi_ih
      intro X a1
      apply h1
      unfold atom_occurs_in
      left
      exact a1
    · apply psi_ih
      intro X a1
      apply h1
      unfold atom_occurs_in
      right
      exact a1


def satisfies
  (V : Valuation)
  (F : Formula_) :
  Prop :=
  eval V F

def Formula_.is_tautology
  (F : Formula_) :
  Prop :=
  ∀ (V : Valuation), satisfies V F

def Formula_.is_satisfiable
  (F : Formula_) :
  Prop :=
  ∃ (V : Valuation), satisfies V F

def Formula_.is_unsatisfiable
  (F : Formula_) :
  Prop :=
  ¬ ∃ (V : Valuation), satisfies V F


example
  (F : Formula_)
  (h1 : F.is_tautology) :
  F.is_satisfiable :=
  by
  unfold is_tautology at h1

  unfold is_satisfiable
  apply Exists.intro default
  apply h1


def set_is_satisfiable
  (Γ : Set Formula_) :
  Prop :=
  ∃ (V : Valuation), ∀ (F : Formula_), F ∈ Γ → satisfies V F


example
  (F : Formula_) :
  (not_ F).is_unsatisfiable ↔ F.is_tautology :=
  by
  unfold is_tautology
  unfold is_unsatisfiable
  unfold satisfies
  simp only [eval]
  exact not_exists_not


example
  (F : Formula_) :
  F.is_unsatisfiable ↔ (not_ F).is_tautology :=
  by
  unfold is_unsatisfiable
  unfold is_tautology
  unfold satisfies
  simp only [eval]
  exact not_exists


example
  (F : Formula_) :
  ¬ F.is_unsatisfiable ↔ F.is_satisfiable :=
  by
  unfold is_satisfiable
  unfold is_unsatisfiable
  exact not_not


def replace_atom_all_rec
  (τ : String → Formula_) :
  Formula_ → Formula_
  | false_ => false_
  | true_ => true_
  | atom_ X => τ X
  | not_ phi => not_ (replace_atom_all_rec τ phi)
  | and_ phi psi => and_ (replace_atom_all_rec τ phi) (replace_atom_all_rec τ psi)
  | or_ phi psi => or_ (replace_atom_all_rec τ phi) (replace_atom_all_rec τ psi)
  | imp_ phi psi => imp_ (replace_atom_all_rec τ phi) (replace_atom_all_rec τ psi)
  | iff_ phi psi => iff_ (replace_atom_all_rec τ phi) (replace_atom_all_rec τ psi)


theorem theorem_2_3
  (V : Valuation)
  (τ : String → Formula_)
  (F : Formula_) :
  eval V (replace_atom_all_rec τ F) ↔ eval (eval V ∘ τ) F :=
  by
  induction F
  case false_ | true_ =>
    simp only [eval]
  case atom_ X =>
    unfold replace_atom_all_rec
    simp only [eval]
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


theorem corollary_2_4
  (τ : String → Formula_)
  (F : Formula_)
  (h1 : F.is_tautology) :
  (replace_atom_all_rec τ F).is_tautology :=
  by
  unfold is_tautology at h1
  unfold satisfies at h1

  unfold is_tautology
  unfold satisfies
  intro V
  rewrite [theorem_2_3]
  apply h1


/--
  `is_logical_consequence P Q` := True if and only if `Q` is a logical consequence of `P`.
-/
def is_logical_consequence
  (P Q : Formula_) :
  Prop :=
  (P.imp_ Q).is_tautology


/--
  `are_logically_equivalent P Q` := True if and only if `P` and `Q` are logically equivalent.
-/
def are_logically_equivalent
  (P Q : Formula_) :
  Prop :=
  (P.iff_ Q).is_tautology


def replace_atom_one_rec
  (A : String)
  (F : Formula_ ):
  Formula_ → Formula_
  | false_ => false_
  | true_ => true_
  | atom_ X => if A = X then F else atom_ X
  | not_ phi => not_ (replace_atom_one_rec A F phi)
  | and_ phi psi => and_ (replace_atom_one_rec A F phi) (replace_atom_one_rec A F psi)
  | or_ phi psi => or_ (replace_atom_one_rec A F phi) (replace_atom_one_rec A F psi)
  | imp_ phi psi => imp_ (replace_atom_one_rec A F phi) (replace_atom_one_rec A F psi)
  | iff_ phi psi => iff_ (replace_atom_one_rec A F phi) (replace_atom_one_rec A F psi)


theorem theorem_2_3_one
  (V : Valuation)
  (A : String)
  (P : Formula_)
  (F : Formula_) :
  eval V (replace_atom_one_rec A P F) ↔ eval (Function.updateITE' V A (eval V P)) F :=
  by
  induction F
  case false_ | true_ =>
    simp only [eval]
  case atom_ X =>
    simp only [eval]
    unfold replace_atom_one_rec
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


theorem theorem_2_5_one
  (V : Valuation)
  (P Q : Formula_)
  (X : String)
  (R : Formula_)
  (h1 : eval V P ↔ eval V Q) :
  eval V (replace_atom_one_rec X P R) ↔ eval V (replace_atom_one_rec X Q R) :=
  by
  simp only [theorem_2_3_one]
  rewrite [h1]
  rfl


theorem theorem_2_5
  (V : Valuation)
  (τ1 τ2 : String → Formula_)
  (F : Formula_)
  (h1 : ∀ (X : String), eval V (τ1 X) ↔ eval V (τ2 X)) :
  eval V (replace_atom_all_rec τ1 F) ↔ eval V (replace_atom_all_rec τ2 F) :=
  by
    simp only [theorem_2_3]
    congr! 1
    funext X
    simp only [Function.comp_apply]
    ext
    apply h1
