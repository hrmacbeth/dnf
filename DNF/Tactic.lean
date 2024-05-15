/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import DNF.Theory.ProveFalseFromSAT
import Mathlib.Logic.Basic

open Lean Elab Tactic Meta

/-- Identify the atoms in a propositional logic expression. -/
def Lean.Expr.atoms (a : HashSet Expr) : Expr → HashSet Expr
  | Expr.app (Expr.app (Expr.const ``And _) e₁) e₂ => (e₁.atoms a).insertMany (e₂.atoms a)
  | Expr.app (Expr.app (Expr.const ``Or _) e₁) e₂ => (e₁.atoms a).insertMany (e₂.atoms a)
  | Expr.app (Expr.const ``Not _) e => e.atoms a
  | e => a.insert e

/-- Given an array of expressions which ought to contain all the atoms in a propositional logic
expression, build up the SAT formula with atoms indexed by that array.  Fail if an atom is missing
from the array. -/
def Lean.Expr.toSAT [Monad m] [MonadError m] (a : Array Expr) : Expr → m (SAT (Fin a.size))
  | Expr.app (Expr.app (Expr.const ``And _) e₁) e₂ => do
    let p₁ ← e₁.toSAT a
    let p₂ ← e₂.toSAT a
    pure (p₁.and p₂)
  | Expr.app (Expr.app (Expr.const ``Or _) e₁) e₂ => do
    let p₁ ← e₁.toSAT a
    let p₂ ← e₂.toSAT a
    pure (p₁.or p₂)
  | Expr.app (Expr.const ``Not _) e => do
    let p ← e.toSAT a
    pure p.not
  | e =>
    match a.indexOf? e with
    | some i => pure (SAT.atom i)
    | none => throwError "error in parsing atoms of hypotheses"

/-- Given proofs of the items in a list, prove `List.Forall` of the list. -/
def proveForall : List Expr → MetaM Expr
  | [] => pure <| mkConst `trivial
  | [pf] => pure pf
  | hd :: tl => do mkAppM `And.intro #[hd, ← proveForall tl]

def emptyArrayProp : Array Prop := #[]

/-- Filter the nontrivial Prop hypotheses, build an expr-/
def Lean.MVarId.atomsAndSATStructure (g : MVarId) : MetaM (Expr × Expr × Array Expr × Expr) := do
  -- collect the nontrivial Prop hypotheses
  let mut hs := #[]
  let mut hs_types := #[]
  for h in ← getLCtx do
    if !h.isImplementationDetail ∧ (← isProp h.type) then
      hs := hs.push (.fvar h.fvarId)
      hs_types := hs_types.push (← whnfR h.type)
  trace `Meta.tauto2 (fun _ => m!"found {hs.size} hypotheses, {hs_types}")

  -- identify the atoms
  let atoms : Array Expr := (hs_types.foldl Lean.Expr.atoms {}).toArray
  trace `Meta.tauto2 (fun _ => m!"found atoms {atoms}")
  let atomsE : Expr ← atoms.foldlM (fun a b => mkAppM `Array.push #[a, b]) (mkConst `emptyArrayProp)
  let atomsE : Expr ← mkAppM `Array.get #[atomsE]

  -- write the hypotheses as SAT formulas in these atoms
  let satsE : Expr := toExpr (← hs_types.mapM (Lean.Expr.toSAT atoms)).toList
  trace `Meta.tauto2 (fun _ => m!"identified sat formulas {satsE}")

  let hE : Expr ← proveForall hs.toList
  pure (satsE, hE, atoms, atomsE)

/-- Tactic which proves `False`, if possible, from the pure propositional logic structure of the
hypotheses.  Implementation is a proof by reflection from a naive computation of the hypotheses'
disjunctive normal form. -/
elab "prove_false_from_sat" : tactic => liftMetaTactic <| fun g => do
  guard ((← g.getType) == mkConst `False) <|> throwError "tactic tauto2 only proves False"

  let (satsE, hE, _, atomsE) ← g.atomsAndSATStructure

  -- build proof of False
  try
    let determineSAT_E ← mkAppM `Eq.refl #[← mkAppM `determineSAT #[satsE]]
    mkAppM `proveFalseFromSAT #[satsE, determineSAT_E, atomsE, hE] >>= g.assign
    trace `Meta.tauto2 (fun _ => m!"found contradiction from these formulas")
    pure []
  catch _ =>
    throwError "hypotheses are not mutually contradictory"

macro "tauto2" : tactic => `(tactic | (by_contra; prove_false_from_sat))
