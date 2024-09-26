/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import DNF.Theory.List

/-- A formula such as `P ∧ (Q ∨ (¬ P ∧ R))`, comprised of ∧, ∨, ¬ and some atoms indexed by a type
`α`. -/
inductive SAT (α : Type)
  | atom : α → SAT α
  | not : SAT α → SAT α
  | and : SAT α → SAT α → SAT α
  | or : SAT α → SAT α → SAT α
  deriving Repr, Lean.ToExpr

variable [DecidableEq α]

def insertAndDedup (p : α × Bool) : List (α × Bool) → Option (List (α × Bool))
  | [] => some [p]
  | hd :: tl =>
    (insertAndDedup p tl).elim none <| fun l =>
    (l.find? (fun p => p.1 == hd.1)).elim (hd :: l) fun p => if p.2 == hd.2 then l else none

def interpretBool (P : α → Prop) (p : α × Bool) : Prop := if p.2 then P p.1 else ¬ P p.1

def combineAux : List (α × Bool) → List (α × Bool) → Option (List (α × Bool))
  | [], l => pure l
  | hd :: tl, l => (combineAux tl l).bind <| insertAndDedup hd

def combine : List (α × Bool) × List (α × Bool) → Option (List (α × Bool)) :=
  Function.uncurry combineAux

def negate : List (List (α × Bool)) → List (List (α × Bool))
  | [] => [[]]
  | hd :: tl => hd ×ˢ (negate tl) |>.map
    (fun ((a, bool), l) => insertAndDedup (a, !bool) l) |>.reduceOption

/-- Disjunctive normal form of a list of SAT formulas. -/
def SAT.dnf : SAT α → List (List (α × Bool))
  | SAT.atom a => [[(a, true)]]
  | SAT.or s₁ s₂ => dnf s₁ ++ dnf s₂
  | SAT.and s₁ s₂ => dnf s₁ ×ˢ dnf s₂ |>.map combine |>.reduceOption
  | SAT.not s => negate (dnf s)

/-- Given an `α`-indexed family of `Prop`s and a SAT formula on atoms indexed by `α`, construct the
corresponding combination of the `Prop`s with `¬`, `∨`, `∧`. -/
def interpret (P : α → Prop) : SAT α → Prop
  | SAT.atom a => P a
  | SAT.not s => ¬ interpret P s
  | SAT.and s₁ s₂ => interpret P s₁ ∧ interpret P s₂
  | SAT.or s₁ s₂ => interpret P s₁ ∨ interpret P s₂

/-- Given an `α`-indexed family of `Prop`s and a list of list of pairs in `α × Bool`, construct the
corresponding disjunctive normal form combination of the `Prop`s: an "or" of "and"s of the props or
their negations. -/
def interpretDNF (P : α → Prop) (ors : List (List (α × Bool))) : Prop :=
  ors.Exists <| List.Forall (interpretBool P)

/-- Disjunctive normal form of a list of SAT formulas. -/
def List.dnf : List (SAT α) → List (List (α × Bool))
  | [] => [[]]
  | hd :: tl => hd.dnf ×ˢ tl.dnf |>.map combine |>.reduceOption

/-- Compute a boolean from a list of SAT formulas which should be `true` if it is satisfiable (i.e.
there is a truth assignment which makes them simultaneously true), and `false` if they are
unsatisfiable. -/
def determineSAT (l : List (SAT α)) : Bool := !l.dnf.isEmpty

/-- The `determineSAT` algorithm on a list of SAT formulas behaves as expected: if its value is
`false`, then `False` can be proved from the list of formulas. -/
theorem proveFalseFromSAT (l : List (SAT α)) (hl : determineSAT l = false) (P : α → Prop)
    (H : l.Forall (interpret P)) :
    False :=
  sorry
