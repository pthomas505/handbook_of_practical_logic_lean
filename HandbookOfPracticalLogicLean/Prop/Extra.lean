import Lean
import Batteries.Tactic.Lint.Frontend
import Mathlib.Util.CompileInductive
import Mathlib.Tactic


set_option linter.style.docString false
set_option linter.style.emptyLine false
set_option linter.style.longLine false


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
  | forall_ x phi => s! "(∀. {x} {phi.toString})"
  | exists_ x phi => s! "(∃. {x} {phi.toString})"

instance : ToString Formula_ :=
  { toString := Formula_.toString }

#eval (Formula_.var_ "P").toString


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

/-- forall -/
syntax "(" "A." ident formula ")" : formula

/-- exists -/
syntax "(" "E." ident formula ")" : formula


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

  | `(formula| (A. $x:ident $phi)) => do
    let x' : Expr := Lean.mkStrLit x.getId.toString
    let phi' : Expr ← elabFormula phi
    mkAppM ``Formula_.forall_ #[x', phi']

  | `(formula| (E. $x:ident $phi)) => do
    let x' : Expr := Lean.mkStrLit x.getId.toString
    let phi' : Expr ← elabFormula phi
    mkAppM ``Formula_.exists_ #[x', phi']

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
#check (Formula_| ( A. x P ) )
#check (Formula_| ( E. x P ) )

#eval (Formula_| F. ).toString
#eval (Formula_| T. ).toString
#eval (Formula_| P ).toString
#eval (Formula_| ~ P ).toString
#eval (Formula_| (P /\ Q) ).toString
#eval (Formula_| (P \/ Q) ).toString
#eval (Formula_| (P -> Q) ).toString
#eval (Formula_| (P <-> Q) ).toString
#eval (Formula_| ( A. x P ) ).toString
#eval (Formula_| ( E. x P ) ).toString


open Formula_


/--
  `Formula_.map_vars f F` := Applies the function `f` to each of the propositional variables in the formula `F`.
-/
@[nolint defsWithUnderscore]
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


/--
  `Formula_.foldr_vars f init F` := Folds the function `f` over each of the propositional variables in the formula `F`, from right to left.
-/
@[nolint defsWithUnderscore]
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


/--
  `var_occurs_in_formula V F` := True if and only if there is an occurrence of the variable `V` in the formula `F`.
-/
@[nolint defsWithUnderscore]
def var_occurs_in_formula
  (V : String) :
  Formula_ → Prop
  | false_
  | true_ => False
  | var_ X => V = X
  | not_ phi => var_occurs_in_formula V phi
  | and_ phi psi
  | or_ phi psi
  | imp_ phi psi
  | iff_ phi psi => var_occurs_in_formula V phi ∨ var_occurs_in_formula V psi
  | forall_ _ phi
  | exists_ _ phi => var_occurs_in_formula V phi


/--
  The valuation of a formula.
-/
def PropValuation : Type := String → Prop
  deriving Inhabited


/--
  `eval V F` := The evaluation of a formula `F` given the valuation `V`.
-/
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


/--
  `eval_opt V F` := The evaluation of a formula `F` given the valuation `V`.
-/
@[nolint defsWithUnderscore]
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


/--
  `Formula_.is_prop F` := True if and only if `F` is a formula in propositional logic.
-/
@[nolint defsWithUnderscore]
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


theorem is_prop_imp_eval_opt_eq_some_eval
  (F : Formula_)
  (V : PropValuation)
  (h1 : F.is_prop) :
  eval_opt V F = some (eval V F) :=
  by
  induction F
  case false_ | true_ | var_ X =>
    unfold eval_opt
    unfold eval
    apply Eq.refl
  case not_ phi ih =>
    unfold is_prop at h1

    simp only [eval_opt]
    rewrite [ih h1]
    simp only [eval]
    simp only [Option.bind_eq_bind, Option.bind_some]
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
    simp only [Option.bind_eq_bind, Option.bind_some]
  case
      forall_ x phi ih
    | exists_ x phi ih =>
      unfold is_prop at h1
      contradiction


#lint
