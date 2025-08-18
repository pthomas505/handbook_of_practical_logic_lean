import Lean
import Batteries.Tactic.Lint.Frontend
import Mathlib.Util.CompileInductive
import Mathlib.Tactic


set_option autoImplicit false


/--
  The type of formulas.
-/
inductive Formula_ : Type
  | false_ : Formula_
  | true_ : Formula_
  | var_ : String → Formula_
  | not_ : Formula_ → Formula_
  | and_ : Formula_ → Formula_ → Formula_
  | or_ : Formula_ → Formula_ → Formula_
  | imp_ : Formula_ → Formula_ → Formula_
  | iff_ : Formula_ → Formula_ → Formula_
  | forall_ : String → Formula_ → Formula_
  | exists_ : String → Formula_ → Formula_
  deriving Inhabited, DecidableEq, Repr

compile_inductive% Formula_


/--
  The string representation of formulas.
-/
def Formula_.toString :
  Formula_ → String
  | false_ => "F."
  | true_ => "T."
  | var_ X => s! "{X}"
  | not_ phi => s! "¬ {phi.toString}"
  | and_ phi psi => s! "({phi.toString} ∧ {psi.toString})"
  | or_ phi psi => s! "({phi.toString} ∨ {psi.toString})"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"
  | iff_ phi psi => s! "({phi.toString} ↔ {psi.toString})"
  | forall_ x phi => s! "(∀. {x} {phi.toString})"
  | exists_ x phi => s! "(∃. {x} {phi.toString})"

instance : ToString Formula_ :=
  { toString := Formula_.toString }

#eval (Formula_.var_ "P").toString


open Lean Elab Meta

declare_syntax_cat formula


syntax "F." : formula
syntax "T." : formula
syntax ident : formula
syntax "~" formula : formula
syntax "(" formula "/\\" formula ")" : formula
syntax "(" formula "\\/" formula ")" : formula
syntax "(" formula "->" formula ")" : formula
syntax "(" formula "<->" formula ")" : formula
syntax "(" "A." ident formula ")" : formula
syntax "(" "E." ident formula ")" : formula


partial def elabFormula : Syntax → MetaM Expr
  | `(formula| F.) => mkAppM ``Formula_.false_ #[]

  | `(formula| T.) => mkAppM ``Formula_.true_ #[]

  | `(formula| $X:ident) => do
    let X' : Expr := Lean.mkStrLit X.getId.toString
    mkAppM ``Formula_.var_ #[X']

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

  | `(formula| (A. $x:ident $phi)) => do
    let x' : Expr := Lean.mkStrLit x.getId.toString
    let phi' : Expr ← elabFormula phi
    mkAppM ``Formula_.forall_ #[x', phi']

  | `(formula| (E. $x:ident $phi)) => do
    let x' : Expr := Lean.mkStrLit x.getId.toString
    let phi' : Expr ← elabFormula phi
    mkAppM ``Formula_.exists_ #[x', phi']

  | _ => throwUnsupportedSyntax


elab "(Formula_|" F:formula ")" : term => elabFormula F


#check (Formula_| F. )
#check (Formula_| T. )
#check (Formula_| P )
#check (Formula_| ~ P )
#check (Formula_| (P /\ Q) )
#check (Formula_| (P \/ Q) )
#check (Formula_| (P -> Q) )
#check (Formula_| (P <-> Q) )
#check (Formula_| ( A. x P ) )
#check (Formula_| ( E. x P ) )



open Formula_

def Formula_.map_vars
  (f : String → Formula_) :
  Formula_ → Formula_
  | false_ => false_
  | true_ => true_
  | var_ X => f X
  | not_ phi => not_ (phi.map_vars f)
  | and_ phi psi => and_ (phi.map_vars f) (psi.map_vars f)
  | or_ phi psi => or_ (phi.map_vars f) (psi.map_vars f)
  | imp_ phi psi => imp_ (phi.map_vars f) (psi.map_vars f)
  | iff_ phi psi => iff_ (phi.map_vars f) (psi.map_vars f)
  | forall_ x phi => forall_ x (phi.map_vars f)
  | exists_ x phi => forall_ x (phi.map_vars f)


-- Applies the function f to all of the variables of the formula, from right to left.
def Formula_.foldr_vars
  {α : Type}
  (f : String → α → α)
  (init : α) :
  Formula_ → α
  | false_
  | true_ => init
  | var_ X => f X init
  | not_ phi => phi.foldr_vars f init
  | and_ phi psi
  | or_ phi psi
  | imp_ phi psi
  | iff_ phi psi => phi.foldr_vars f (psi.foldr_vars f init)
  | forall_ _ phi
  | exists_ _ phi => phi.foldr_vars f init


def var_occurs_in_formula
  (A : String) :
  Formula_ → Prop
  | false_
  | true_ => False
  | var_ X => A = X
  | not_ phi => var_occurs_in_formula A phi
  | and_ phi psi
  | or_ phi psi
  | imp_ phi psi
  | iff_ phi psi => var_occurs_in_formula A phi ∨ var_occurs_in_formula A psi
  | forall_ _ phi
  | exists_ _ phi => var_occurs_in_formula A phi


def PropValuation : Type := String → Prop
  deriving Inhabited


def eval
  (V : PropValuation) :
  Formula_ → Prop
  | false_ => False
  | true_ => True
  | var_ X => V X
  | not_ phi => ¬ eval V phi
  | and_ phi psi => eval V phi ∧ eval V psi
  | or_ phi psi => eval V phi ∨ eval V psi
  | imp_ phi psi => eval V phi → eval V psi
  | iff_ phi psi => eval V phi ↔ eval V psi
  | forall_ _ phi
  | exists_ _ phi => eval V phi

instance
  (V : PropValuation)
  [DecidablePred V]
  (F : Formula_) :
  Decidable (eval V F) :=
  by
  induction F
  all_goals
    simp only [eval]
    infer_instance


def eval_opt
  (V : PropValuation) :
  Formula_ → Option Prop
  | false_ => some False
  | true_ => some True
  | var_ X => some (V X)
  | not_ phi => do
    let val_phi ← eval_opt V phi
    ¬ val_phi
  | and_ phi psi => do
    let val_phi ← eval_opt V phi
    let val_psi ← eval_opt V psi
    val_phi ∧ val_psi
  | or_ phi psi => do
    let val_phi ← eval_opt V phi
    let val_psi ← eval_opt V psi
    val_phi ∨ val_psi
  | imp_ phi psi => do
    let val_phi ← eval_opt V phi
    let val_psi ← eval_opt V psi
    val_phi → val_psi
  | iff_ phi psi => do
    let val_phi ← eval_opt V phi
    let val_psi ← eval_opt V psi
    val_phi ↔ val_psi
  | forall_ _ _
  | exists_ _ _ => none


def Formula_.is_prop :
  Formula_ → Prop
  | false_
  | true_
  | var_ _ => True
  | not_ phi => phi.is_prop
  | and_ phi psi
  | or_ phi psi
  | imp_ phi psi
  | iff_ phi psi => phi.is_prop ∧ psi.is_prop
  | forall_ _ _
  | exists_ _ _ => False


lemma is_prop_imp_eval_opt_eq_some_eval
  (F : Formula_)
  (V : PropValuation)
  (h1 : F.is_prop) :
  eval_opt V F = some (eval V F) :=
  by
  induction F
  case false_ | true_ | var_ X =>
    unfold eval_opt
    unfold eval
    rfl
  case not_ phi ih =>
    unfold is_prop at h1

    simp only [eval_opt]
    rewrite [ih h1]
    simp only [eval]
    simp
  case
      and_ phi psi phi_ih psi_ih
    | or_ phi psi phi_ih psi_ih
    | imp_ phi psi phi_ih psi_ih
    | iff_ phi psi phi_ih psi_ih =>
    unfold is_prop at h1
    obtain ⟨h1_left, h1_right⟩ := h1

    simp only [eval_opt]
    rewrite [phi_ih h1_left]
    rewrite [psi_ih h1_right]
    simp only [eval]
    simp
  case
      forall_ x phi ih
    | exists_ x phi ih =>
      unfold is_prop at h1
      contradiction
