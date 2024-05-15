/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Batteries.Data.List.Basic
import Mathlib.Data.SProd

-- from `Mathlib.Data.List.Defs`
instance instSProd : SProd (List α) (List β) (List (α × β)) where
  sprod := List.product

/-- `l.Forall p` is equivalent to `∀ a ∈ l, p a`, but unfolds directly to a conjunction, i.e.
`List.Forall p [0, 1, 2] = p 0 ∧ p 1 ∧ p 2`. -/
-- from `Mathlib.Data.List.Defs`
@[simp]
def List.Forall (p : α → Prop) : List α → Prop
  | [] => True
  | x :: [] => p x
  | x :: l => p x ∧ Forall p l

def List.Exists (p : α → Prop) : List α → Prop
  | [] => False
  | x :: l => p x ∨ Exists p l
