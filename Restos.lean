import Topology.Nets.Theorems

open Set Filter Topology Function Net

/- Characterization of bounded set in metric space -/
lemma Metric.isBounded_iff' {X: Type*} [PseudoMetricSpace X] {s: Set X}:
  Bornology.IsBounded s ↔ ∀ (x: X), ∃ (r: ℝ), 0 < r ∧ s ⊆ Metric.ball x r := by
    rw [Metric.isBounded_iff]
    constructor
    · intro bounded x
      rcases bounded with ⟨C, eq⟩
      by_cases sempty: s = ∅
      · use 1
        rw [sempty]
        exact And.intro Real.zero_lt_one (empty_subset (Metric.ball x 1))
      · rw [← Ne, ← nonempty_iff_ne_empty, nonempty_def] at sempty
        rcases sempty with ⟨x₀, x₀ins⟩
        use C + dist x x₀ + 1
        constructor
        · have Clez: 0 ≤ C := by
            have := eq x₀ins x₀ins
            rw [dist_self] at this
            assumption
          have: 0 ≤ dist x x₀ := by
            exact dist_nonneg
          linarith [Clez, this]
        · intro y yins
          rw [Metric.mem_ball]
          calc
            dist y x ≤ dist y x₀ + dist x x₀ := by
              rw [dist_comm x x₀]
              exact dist_triangle y x₀ x
            _ ≤ C + dist x x₀ := by
              exact add_le_add_right (eq yins x₀ins) (dist x x₀)
            _ < C + dist x x₀ + 1 := by
              linarith
    · intro bounded
      by_cases sempty: s = ∅
      · use 1
        intro x xins
        rw [sempty] at xins
        contradiction
      · rw [← Ne, ← nonempty_iff_ne_empty, nonempty_def] at sempty
        rcases sempty with ⟨x₀, x₀ins⟩
        rcases bounded x₀ with ⟨r, rpos, ssubball⟩
        use 2*r
        intro x xins y yins
        calc
          dist x y ≤ dist x x₀ + dist x₀ y := by
            exact dist_triangle x x₀ y
          _ ≤ r + dist x₀ y := by
            apply add_le_add_right
            exact le_of_lt (ssubball xins)
          _ ≤ r + r := by
            apply add_le_add_left
            rw [dist_comm]
            exact le_of_lt (ssubball yins)
          _ = 2*r := by
            linarith

variable {M: Type*} [PseudoMetricSpace M]

theorem complete_iff_seqcomplete' :
  CompleteSpace M ↔ ∀ (s: ℕ → M), CauchyNet s → ∃ (x: M), Limit s x := by
    constructor
    · intro completeX s cauchys
      rw [cauchynet_iff_cauchyfilter] at cauchys
      rcases completeX.complete cauchys with ⟨x, limitFx⟩
      use x
      rw [limnet_iff_limfilter]
      assumption
    · intro cauchyconv
      rw [complete_iff_netcomplete]
      intro D h s cauchys
      let i: ℕ → ℝ := fun n ↦ 1/(n + 1)
      have ipos : ∀ (n: ℕ), 0 < i n := by
        intro n
        dsimp only [i]
        norm_num
        linarith
      have ilimitz : Limit i 0 := by
        rw [limit_metric_iff]
        intro ε εpos
        use Nat.ceil (1/ε)
        intro n flrlen
        unfold i
        rw [dist_eq_norm, Real.norm_eq_abs, sub_zero, abs_of_pos (ipos n),
            one_div_lt (by linarith) εpos]
        rw [Nat.ceil_le] at flrlen
        exact lt_of_le_of_lt flrlen (lt_add_one _)
      rcases cauchyconv (s ∘ (seq_of_net s i))
        (seq_of_net_cauchy s i ipos cauchys ilimitz) with ⟨x, limitsix⟩
      use x
      exact limnet_of_seq_of_net s i ipos cauchys ilimitz x limitsix
