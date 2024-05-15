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

/-- Identify the type, LHS and RHS of an expression which may represent an equality. -/
def Lean.Expr.eqAtoms (eqAtomsByType : HashMap Expr (HashSet Expr)) (e : Expr) :
    HashMap Expr (HashSet Expr) :=
  match e.eq? with
  | some (ty, a, b) => eqAtomsByType.insert ty (((eqAtomsByType.findD ty {}).insert a).insert b)
  | none => eqAtomsByType

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

/-- Given an array of pairs `(ty, a) : Expr × Array Expr`, which ought to be such that each entry of
`a` represents something of type `ty`, ... FIXME. -/
def Lean.Expr.toEdge [Monad m] [MonadError m] (eqAtomsByType : Array (Expr × Array Expr))
    (e : Expr) :
    m <| Option (Σ i : Fin eqAtomsByType.size,
      Fin (eqAtomsByType.get i).2.size × Fin (eqAtomsByType.get i).2.size) :=
  match e.eq? with
  | some (ty, a, b) =>
    match (eqAtomsByType.map Prod.fst).indexOf? ty with
    | some i₀ =>
      let i : Fin eqAtomsByType.size := Fin.cast (eqAtomsByType.size_map Prod.fst) i₀
      let eqAtoms : Array Expr := (eqAtomsByType.get i).snd
      match eqAtoms.indexOf? a, eqAtoms.indexOf? b with
      | some ia, some ib => pure <| some ⟨i, (ia, ib)⟩
      | _, _ => throwError "error in parsing atoms of equality hypotheses"
    | none => throwError "error in parsing atoms of equality hypotheses"
  | none => pure none

/-- Given proofs of the items in a list, prove `List.Forall` of the list. -/
def proveForall : List Expr → MetaM Expr
  | [] => pure <| mkConst `trivial
  | [pf] => pure pf
  | hd :: tl => do mkAppM `And.intro #[hd, ← proveForall tl]

/-- Given an expression which is the proof of `n` propositions chained together, build a length-`n`
list comprising proofs of the indivitual expressions. -/
def proofsOfProofForall (e : Expr) : Nat → MetaM (List Expr)
  | 0 => pure []
  | 1 => pure [e]
  | n + 2 => do
    let hd ← mkAppM ``And.left #[e]
    let tl ← proofsOfProofForall (← mkAppM ``And.right #[e]) (n + 1)
    pure (hd :: tl)

-- def extract (e : Expr) :
def emptyArrayProp : Array Prop := #[]
def emptyListSAT (n : Nat) : List (SAT (Fin n)) := []

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
  -- trace `Meta.tauto2 (fun _ => m!"made atoms list {atomsE}")

  -- write the hypotheses as SAT formulas in these atoms
  let satsE : Expr := toExpr (← hs_types.mapM (Lean.Expr.toSAT atoms)).toList
  trace `Meta.tauto2 (fun _ => m!"identified sat formulas {satsE}")

  let hE : Expr ← proveForall hs.toList
  pure (satsE, hE, atoms, atomsE)

def foo (p : Expr × Expr × Array Expr × Expr) : MetaM Expr := do

  let (satsE, hE, atoms, atomsE) := p

  -- identify the atoms
  let eqAtomsByType : HashMap Expr (HashSet Expr) := (atoms.foldl Lean.Expr.eqAtoms {})
  let eqAtomsByTypeA : Array (Expr × Array Expr) :=
    eqAtomsByType.toArray.map (fun (a, b) => (a, HashSet.toArray b))
  trace `Meta.tauto2 (fun _ => m!"found equality atoms {eqAtomsByTypeA}")

  let n : Nat := eqAtomsByTypeA.size
  let tys (i : Fin n) : Expr := (eqAtomsByTypeA.get i).1
  let m (i : Fin n) : Nat := (eqAtomsByTypeA.get i).2.size
  let eqAtoms (i : Fin n) (j : Fin (m i)) : Expr := (eqAtomsByTypeA.get i).2.get j

  let b : Array (Option (Σ i : Fin n, Fin (m i) × Fin (m i))) ← atoms.mapM (Lean.Expr.toEdge eqAtomsByTypeA)



  let a ← mkAppM `List.dnf #[satsE]
  mkAppM `List.interpretDNF_of_interpret #[satsE, atomsE, hE]


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
