/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import Mathlib.Data.List.ProdSigma

@[ext] theorem BEq.ext {x y : BEq α} (h : x.beq = y.beq) : x = y := by
  cases x
  simp at h
  rw [h]


theorem beq_prod_diamond [DecidableEq α] [DecidableEq β] : instBEqOfDecidableEq (α := α × β) = instBEqProd := by
  ext ⟨a1, b1⟩ ⟨a2, b2⟩
  simp [instBEqProd, instBEqOfDecidableEq]

theorem beq_list_diamond_aux [DecidableEq α] (l1 l2 : List α) : decide (l1 = l2) = List.beq l1 l2 := by
  match l1, l2 with
  | [], [] => rw [List.beq]; simp
  | a::as, b::bs =>
    rw [List.beq, ← beq_list_diamond_aux as bs]
    simp only [List.cons.injEq, Bool.decide_and]
    rfl
  | _, _ => sorry

theorem beq_list_diamond [DecidableEq α] : instBEqOfDecidableEq (α := List α) = List.instBEq := by
  ext l1 l2
  exact beq_list_diamond_aux l1 l2

def List.Exists (p : α → Prop) : List α → Prop
  | [] => False
  | x :: l => p x ∨ Exists p l

@[simp] theorem List.exists_nil (p : α → Prop) : ¬ [].Exists p := not_false

@[simp] theorem List.exists_cons (p : α → Prop) (l : List α) (x : α) :
    (x :: l).Exists p ↔ p x ∨ Exists p l :=
  Iff.rfl

@[simp] theorem List.exists_append (p : α → Prop) (l₁ l₂ : List α) :
    (l₁ ++ l₂).Exists p ↔ l₁.Exists p ∨ l₂.Exists p := by
  induction l₁ with
  | nil => simp
  | cons _ _ IH => simp [or_assoc, IH]

theorem List.exists_iff_mem (p : α → Prop) (l : List α) :
    l.Exists p ↔ ∃ x ∈ l, p x := by
  induction l with
  | nil => simp
  | cons _ _ IH => simp [IH]

@[simp] theorem List.not_exists (p : α → Prop) (l : List α) :
    ¬ l.Exists p ↔ l.Forall (fun a ↦ ¬ p a) := by
  simp [List.exists_iff_mem, List.forall_iff_forall_mem]

@[simp] theorem List.not_forall (p : α → Prop) (l : List α) :
    ¬ l.Forall p ↔ l.Exists (fun a ↦ ¬ p a) := by
  simp [List.exists_iff_mem, List.forall_iff_forall_mem]

theorem List.of_forall_of_mem {p : α → Prop} {l : List α} {x : α} (hx : x ∈ l) (hp : l.Forall p) :
    p x := by
  rw [List.forall_iff_forall_mem] at hp
  exact hp x hx

@[simp] theorem List.forall_append {l1 l2 : List α} :
    (l1 ++ l2).Forall p ↔ l1.Forall p ∧ l2.Forall p := by
  simp [List.forall_iff_forall_mem]
  aesop

theorem List.forall_of_forall_erase [DecidableEq α] {p : α → Prop} {l : List α} {x : α}
    (hp : (l.erase x).Forall p) (hx : p x) :
    l.Forall p := by
  induction l with
  | nil => simp
  | cons head tail IH =>
    rw [List.erase_cons] at hp
    split at hp
    next h =>
      sorry
      -- rw [h]
      -- simp
      -- exact ⟨hx, hp⟩
    simp at hp ⊢
    refine ⟨hp.1, IH hp.2⟩

theorem List.find?_of_forall {l : List α} {q : α → Bool} (hq : l.find? q = some a) {P : α → Prop}
    (hP : l.Forall P) :
    P a := by
  induction l with
  | nil => simp at hq
  | cons hd tl IH =>
    rw [List.find?] at hq
    simp only [forall_cons] at hP
    split at hq
    · simp only [Option.some.injEq] at hq
      obtain rfl := hq
      exact hP.1
    · exact IH hq hP.2

theorem List.mem_replace [BEq α] [LawfulBEq α] {l : List α} {a : α} (hal : a ∈ l) (b : α) :
    b ∈ l.replace a b := by
  induction l with
  | nil => simp at hal
  | cons head tail IH =>
    rw [replace_cons]
    split
    next => simp
    next h =>
      simp at hal
      obtain rfl | ha_tail := hal
      · simp at h
      right
      exact IH ha_tail

theorem List.forall_of_forall_replace [BEq α] [LawfulBEq α] {l : List α} {a : α}
    {b : α} {P : α → Prop} (hPa : P a) (hPl : (l.replace a b).Forall P) :
    l.Forall P := by
  induction l with
  | nil => simp
  | cons head tail IH =>
    rw [replace_cons] at hPl
    simp at IH
    split at hPl
    next ha_head =>
      simp at ha_head
      subst ha_head
      simp at hPl
      simpa using ⟨hPa, hPl.2⟩
    next =>
      simp at hPl
      simpa using ⟨hPl.1, IH hPl.2⟩

theorem Option.elim_false {α : Type*} {p : Option α} {P : α → Prop} (h : Option.elim p False P) :
    ∃ a, p = some a ∧ P a :=
  match p with
  | none => by simp at h
  | some a => ⟨a, rfl, h⟩

attribute [pp_dot] Option.elim
