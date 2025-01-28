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
  | false_ => "F."
  | true_ => "T."
  | atom_ X => s! "{X}"
  | not_ phi => s! "¬ {phi.toString}"
  | and_ phi psi => s! "({phi.toString} ∧ {psi.toString})"
  | or_ phi psi => s! "({phi.toString} ∨ {psi.toString})"
  | imp_ phi psi => s! "({phi.toString} → {psi.toString})"
  | iff_ phi psi => s! "({phi.toString} ↔ {psi.toString})"

instance : ToString Formula_ :=
  { toString := Formula_.toString }


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

#eval (Formula_| F. ).toString
#eval (Formula_| T. ).toString
#eval (Formula_| P ).toString
#eval (Formula_| ~ P ).toString
#eval (Formula_| (P /\ Q) ).toString
#eval (Formula_| (P \/ Q) ).toString
#eval (Formula_| (P -> Q) ).toString
#eval (Formula_| (P <-> Q) ).toString
