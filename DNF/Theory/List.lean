/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Batteries.Data.List.Basic
import Mathlib.Data.List.Defs
import Mathlib.Data.SProd

-- from `Mathlib.Data.List.Defs`
instance instSProd : SProd (List α) (List β) (List (α × β)) where
  sprod := List.product

def List.Exists (p : α → Prop) : List α → Prop
  | [] => False
  | x :: l => p x ∨ Exists p l
