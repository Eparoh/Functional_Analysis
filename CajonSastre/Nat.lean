import Mathlib.Analysis.RCLike.Basic

set_option trace.Meta.Tactic.simp false

open Set Filter Topology Function

/- ### Sub cancel ###-/

lemma Nat.sub_sub_cancel :
  ∀ {n m k: ℕ}, k ≤ n → k ≤ m → n - k = m - k → n = m := by
    intro n m k klen klem eq
    have := congr_arg (fun x ↦ x + k) eq
    dsimp at this
    rwa [Nat.sub_add_cancel klen, Nat.sub_add_cancel klem] at this

/- ### sInf and sSup ### -/

lemma Nat.le_sInf {s : Set ℕ} (snemp: s.Nonempty) {k : ℕ} :
(∀ n ∈ s, k ≤ n) → k ≤ sInf s := by
  classical
  intro h
  rw [Nat.sInf_def snemp, Nat.le_find_iff]
  intro m mltk
  by_contra!
  have := h m this
  linarith

lemma Nat.sInf_eq {s: Set ℕ} (snemp: s.Nonempty) {n : ℕ} :
  sInf s = n ↔ n ∈ s ∧ ∀ k ∈ s, n ≤ k := by
    constructor
    · intro eq
      rw [← eq]
      constructor
      · exact Nat.sInf_mem snemp
      · intro k kins
        exact Nat.sInf_le kins
    · intro ⟨nins, nles⟩
      apply le_antisymm
      · exact Nat.sInf_le nins
      · exact Nat.le_sInf snemp nles

lemma Nat.le_sSup {s: Set ℕ} (sbdd: BddAbove s) {k: ℕ} :
  k ∈ s → k ≤ sSup s := by
    classical
    intro kins
    have := Nat.find_spec (sbdd)
    rw [mem_upperBounds] at this
    rw [sSup_def sbdd]
    exact this k kins

lemma Nat.sSup_le {s: Set ℕ} (snemp : s.Nonempty) (sbdd: BddAbove s) {n: ℕ} :
  (∀ k ∈ s, k ≤ n) → sSup s ≤ n := by
    classical
    intro h
    exact h (sSup s) (Nat.sSup_mem snemp sbdd)
