import Lean
import Mathlib.Util.CompileInductive


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
  deriving Inhabited, DecidableEq, Hashable, Repr

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

instance : ToString Formula_ :=
  { toString := Formula_.toString }


open Lean Elab Meta

/--
  The syntax category of formulas.
-/
declare_syntax_cat formula


/-- false -/
syntax "F." : formula

/-- true -/
syntax "T." : formula

/-- var -/
syntax ident : formula

/-- not -/
syntax "~" formula : formula

/-- and -/
syntax "(" formula "/\\" formula ")" : formula

/-- or -/
syntax "(" formula "\\/" formula ")" : formula

/-- imp -/
syntax "(" formula "->" formula ")" : formula

/-- iff -/
syntax "(" formula "<->" formula ")" : formula


/--
  The elaboration of formulas.
-/
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

  | _ => throwUnsupportedSyntax


/--
  The elaboration of formulas.
-/
elab "(Formula_|" F:formula ")" : term => elabFormula F


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


#lint
