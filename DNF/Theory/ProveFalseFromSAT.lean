/- Copyright (c) Heather Macbeth, 2023.  All rights reserved. -/
import DNF.Theory.List
import Mathlib.Tactic.ToExpr

/-! ## SAT solver -/

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

@[simp] theorem insertAndDedup_nil (p : α × Bool) : insertAndDedup p [] = some [p] := rfl

theorem insertAndDedup_cons_of_none {p : α × Bool} {l : List (α × Bool)}
    (hl : insertAndDedup p l = none) (hd : α × Bool) :
    insertAndDedup p (hd :: l) = none := by
  simp [insertAndDedup, hl]

theorem insertAndDedup_cons {p : α × Bool} {l l' : List (α × Bool)}
    (hl : insertAndDedup p l = some l') (hd : α × Bool) :
    insertAndDedup p (hd :: l)
    = (l'.find? (fun p => p.1 == hd.1)).elim (some (hd :: l'))
      fun p => if p.2 == hd.2 then some l' else none := by
  simp [insertAndDedup, hl]

theorem insertAndDedup_none_of_cons_of_none {p : α × Bool} {c pl : List (α × Bool)} {hd : α × Bool}
    (h : insertAndDedup p (hd :: c) = some pl) :
    (hd ∈ pl ∧ insertAndDedup p c = some pl) ∨ ∃ l, pl = hd :: l ∧ insertAndDedup p c = some l := by
  set iphd := insertAndDedup p c with h_iphd
  clear_value iphd
  cases iphd with
  | none => simp [insertAndDedup_cons_of_none h_iphd.symm hd] at h
  | some l =>
    have H := insertAndDedup_cons h_iphd.symm hd
    rw [H] at h
    clear H
    set search := l.find? (fun p ↦ p.1 == hd.1) with hp
    clear_value search
    cases search with
    | none =>
      simp at h
      rw [←h]
      right
      use l
    | some p' =>
      have hp' := List.find?_some hp.symm
      simp at h hp'
      sorry
      -- split at h
      -- next hp'2 =>
      --   left
      --   rw [← Prod.ext hp' hp'2]
      --   simp at h
      --   rw [← h]
      --   exact ⟨List.find?_mem hp.symm, rfl⟩
      -- · simp at h

def interpretBool (P : α → Prop) (p : α × Bool) : Prop := if p.2 then P p.1 else ¬ P p.1

theorem not_interpretBool (P : α → Prop) (p : α × Bool) :
    ¬ interpretBool P p ↔ interpretBool P (p.1, !p.2) := by
  obtain ⟨a, bool⟩ := p
  cases bool <;> simp [interpretBool]

theorem List.forall_insertAndDedup {P : α → Prop} {p : α × Bool} (h1 : interpretBool P p)
    {l : List (α × Bool)} (h2 : l.Forall (interpretBool P)) :
    (insertAndDedup p l).elim False (List.Forall (interpretBool P)) := by
  induction' l with head tail IH
  · simpa
  obtain ⟨hP_head, hP_tail⟩ :
      interpretBool P head ∧ List.Forall (interpretBool P) tail := by
    simpa only [List.forall_cons] using h2
  obtain ⟨l, hs, IH⟩ := Option.elim_false (IH hP_tail)
  rw [insertAndDedup_cons hs]
  set a := l.find? (fun p ↦ p.1 == head.1) with ha
  match a with
  | none => simpa using ⟨hP_head, IH⟩
  | some p' =>
    rw [Option.elim_some]
    have hp'_head : p'.1 = head.1 := by simpa using List.find?_some ha.symm
    have hp'_P := List.find?_of_forall ha.symm IH
    rw [interpretBool] at hp'_P hP_head
    split at hp'_P
    next hp' =>
      rw [hp']
      split at hP_head
      next h_head =>
        rw [h_head]
        simpa using IH
      next =>
        rw [← hp'_head] at hP_head
        contradiction
    next hp' =>
      simp at hp'
      rw [hp']
      split at hP_head
      next =>
        rw [← hp'_head] at hP_head
        contradiction
      next h_head =>
        simp at h_head
        rw [h_head]
        simpa using IH

theorem List.forall_of_forall_insertAndDedup {P : α → Prop} {p : α × Bool} {c l : List (α × Bool)}
    (h1 : insertAndDedup p c = some l) (h2 : l.Forall (interpretBool P)) :
    interpretBool P p ∧ c.Forall (interpretBool P) := by
  induction c generalizing l with
  | nil =>
    simp at h1
    subst h1
    simpa
  | cons head tail IH =>
    obtain ⟨h_hd_l, hl⟩ | ⟨l', hl'⟩ := insertAndDedup_none_of_cons_of_none h1
    · replace IH := IH hl h2
      simp only [forall_cons]
      exact ⟨IH.1, List.of_forall_of_mem h_hd_l h2, IH.2⟩
    · rw [hl'.1] at h2
      simp at h2
      have H := IH hl'.2 h2.2
      simp
      refine ⟨H.1, h2.1, H.2⟩

def combine : List (α × Bool) × List (α × Bool) → Option (List (α × Bool))
  | ([], l) => pure l
  | (hd :: tl, l) => (combine (tl, l)).bind <| insertAndDedup hd

theorem List.forall_combine {P : α → Prop} {l1 l2 : List (α × Bool)}
    (h1 : l1.Forall (interpretBool P)) (h2 : l2.Forall (interpretBool P)) :
    (combine (l1, l2)).elim False (List.Forall (interpretBool P)) := by
  induction l1 with
  | nil => simpa [combine]
  | cons head tail IH =>
    simp at h1
    obtain ⟨n, hn, hPn⟩ := Option.elim_false (IH h1.2)
    rw [combine, hn, Option.some_bind]
    exact List.forall_insertAndDedup h1.1 hPn

theorem List.forall_of_forall_combine {P : α → Prop} {l : List (α × Bool)}
    (hlP : l.Forall (interpretBool P)) {l₁ l₂ : List (α × Bool)} (hl : combine (l₁, l₂) = some l) :
    l₁.Forall (interpretBool P) ∧ l₂.Forall (interpretBool P) := by
  induction l₁ generalizing l with
  | nil =>
    have : some l₂ = some l := by
      show pure l₂ = some _
      simpa [combine] using hl
    obtain rfl : l₂ = l := by simpa using this
    simpa using hlP
  | cons _ _ IH =>
    simp [combine] at hl
    obtain ⟨n, hn, hnl⟩ := hl
    obtain ⟨hP, hPn⟩ := List.forall_of_forall_insertAndDedup hnl hlP
    have H := IH hPn hn
    simp
    exact ⟨⟨hP, H.1⟩, H.2⟩

def negate : List (List (α × Bool)) → List (List (α × Bool))
  | [] => [[]]
  | hd :: tl => hd ×ˢ (negate tl) |>.map
    (fun ((a, bool), l) => insertAndDedup (a, !bool) l) |>.reduceOption

theorem forall_exists_not_interpretBool_iff_exists_forall_interpretBool_negate
    (ors : List (List (α × Bool))) (P : α → Prop) :
    ors.Forall (List.Exists (fun p => ¬interpretBool P p))
    ↔ (negate ors).Exists (List.Forall (interpretBool P)) := by
  induction ors with
  | nil => simp [negate]
  | cons head tail IH =>
    simp only [negate, List.mem_cons, imp_false, List.forall_cons, IH, List.reduceOption]
    simp only [not_interpretBool, List.exists_iff_mem, List.mem_filterMap, List.mem_map,
      List.mem_product, Prod.exists (α := α × Bool), id_eq, exists_eq_right]
    constructor
    · rintro ⟨⟨q, hq, hqP⟩, ⟨ands, h_ands, hP_ands⟩⟩
      obtain ⟨l, hl⟩ := Option.elim_false (List.forall_insertAndDedup hqP hP_ands)
      exact ⟨l, ⟨q, ands, ⟨hq, h_ands⟩, hl.1⟩, hl.2⟩
    · rintro ⟨l, ⟨q, ands, ⟨hq, h_ands⟩, h_ands_l⟩, hlP⟩
      obtain ⟨H1, H2⟩ := List.forall_of_forall_insertAndDedup h_ands_l hlP
      exact ⟨⟨q, hq, H1⟩, ⟨ands, h_ands, H2⟩⟩

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

/-- A truth assignment to the atoms of a SAT formula makes it valid, if and only if that truth
assignment makes the formula's disjunctive normal form valid. -/
theorem SAT.interpret_iff_interpretDNF (s : SAT α) (P : α → Prop) :
    interpret P s ↔ interpretDNF P s.dnf := by
  induction s with
  | atom a =>
    simp [interpret, interpretDNF, SAT.dnf, interpretBool]
  | not s hs =>
    simpa [interpret, interpretDNF, SAT.dnf, hs] using
      forall_exists_not_interpretBool_iff_exists_forall_interpretBool_negate s.dnf P
  | and s₁ s₂ hs₁ hs₂ =>
    rw [interpret, hs₁, hs₂, SAT.dnf]
    simp [interpretDNF, List.exists_iff_mem, List.reduceOption]
    constructor
    · rintro ⟨⟨l₁, hl₁, hl₁P⟩, ⟨l₂, hl₂, hl₂P⟩⟩
      obtain ⟨l, hl, H⟩ := Option.elim_false (List.forall_combine hl₁P hl₂P)
      exact ⟨l, ⟨l₁, l₂, ⟨hl₁, hl₂⟩, hl⟩, H⟩
    · rintro ⟨l, ⟨l₁, l₂, hls, hl⟩, hlP⟩
      obtain ⟨hl₁P, hl₂P⟩ := List.forall_of_forall_combine hlP hl
      exact ⟨⟨_, hls.1, hl₁P⟩, ⟨_, hls.2, hl₂P⟩⟩
  | or s₁ s₂ hs₁ hs₂ =>
    rw [interpret, hs₁, hs₂]
    simp only [interpretDNF, SAT.dnf, List.exists_append]

/-- Disjunctive normal form of a list of SAT formulas. -/
def List.dnf : List (SAT α) → List (List (α × Bool))
  | [] => [[]]
  | hd :: tl => hd.dnf ×ˢ tl.dnf |>.map combine |>.reduceOption

/-- A truth assignment to the atoms of a list of SAT formulas makes them valid, if and only if that
truth assignment makes the list's disjunctive normal form valid. -/
theorem List.interpret_iff_interpretDNF (l : List (SAT α)) (P : α → Prop) :
    l.Forall (interpret P) ↔ interpretDNF P l.dnf := by
  induction l with
  | nil => simp [interpretDNF, dnf]
  | cons head tail IH =>
    simp [IH, interpretDNF, dnf, List.reduceOption, List.exists_iff_mem,
      SAT.interpret_iff_interpretDNF]
    constructor
    · rintro ⟨⟨a, ha, haP⟩, ⟨b, hb, hbP⟩⟩
      obtain ⟨l, hl, H⟩ := Option.elim_false (List.forall_combine haP hbP)
      exact ⟨l, ⟨a, b, ⟨ha, hb⟩, hl⟩, H⟩
    · rintro ⟨l, ⟨a, b, hls, hl⟩, hlP⟩
      obtain ⟨haP, hbP⟩ := List.forall_of_forall_combine hlP hl
      exact ⟨⟨_, hls.1, haP⟩, ⟨_, hls.2, hbP⟩⟩

alias ⟨List.interpretDNF_of_interpret, List.interpret_of_interpretDNF⟩ :=
  List.interpret_iff_interpretDNF

/-- Compute a boolean from a list of SAT formulas which should be `true` if it is satisfiable (i.e.
there is a truth assignment which makes them simultaneously true), and `false` if they are
unsatisfiable. -/
def determineSAT (l : List (SAT α)) : Bool := !l.dnf.isEmpty

/-- The `determineSAT` algorithm on a list of SAT formulas behaves as expected: if its value is
`false`, then `False` can be proved from the list of formulas. -/
theorem proveFalseFromSAT (l : List (SAT α)) (hl : determineSAT l = false) (P : α → Prop)
    (H : l.Forall (interpret P)) :
    False := by
  rw [determineSAT, Bool.not_eq_false', List.isEmpty_iff_eq_nil] at hl
  simp [List.interpret_iff_interpretDNF, hl, interpretDNF] at H

initialize Lean.registerTraceClass `Meta.tauto2
