import Topology.Nets.Theorems

set_option trace.Meta.Tactic.simp false

noncomputable section

open Set Filter Topology Classical Function DirectedSet

namespace Net

/- ### Summable = NetSummable ### -/

/- A function is summable iff it is net summable -/
theorem hassum_iff_hassumnet {I X: Type*}  [AddCommMonoid X] [TopologicalSpace X] (f: I → X) (x: X):
  HasSum f x ↔ HasSumNet f x := by
    unfold HasSum HasSumNet Limit
    simp only [tendsto_nhds, Filter.mem_atTop_sets, Finset.le_eq_subset, Set.mem_preimage, ge_iff_le]
    constructor
    · intro fhsum
      intro U Unhds
      rw [mem_nhds_iff] at Unhds
      rcases Unhds with ⟨V, VsubU, Vopen, xinV⟩
      rcases fhsum V Vopen xinV with ⟨d₀, eq⟩
      use d₀
      intro d d₀subd
      apply VsubU
      exact eq d d₀subd
    · intro fhsumnet
      intro U Uopen xinU
      exact fhsumnet U (by rw [mem_nhds_iff]; use U)

theorem summable_iff_summablenet {I X: Type*}  [AddCommMonoid X] [TopologicalSpace X] (f: I → X):
  Summable f ↔ SummableNet f := by
    unfold Summable SummableNet
    simp only [hassum_iff_hassumnet]

/- ### Archimedean property ### -/

theorem Real_archimedean (x y : ℝ) : (0 < x) → ∃ (n : ℕ), y < n * x := by
  intro x_pos
  have := exists_lt_nsmul x_pos y
  simp only [nsmul_eq_mul] at this
  assumption

/- ### Characterization of convergence and Cauchy in metric spaces ### -/

/- Characterization of convergence in a metric space -/
lemma limit_metric_iff {X D: Type*} [DirectedSet D] [PseudoMetricSpace X] (s: D → X) (x: X):
  Limit s x ↔ ∀ (ε: ℝ), (0 < ε → ∃ (d₀: D), (∀ (d: D), d₀ ≤ d → dist (s d) x < ε)) := by
    constructor
    · intro limitsx
      intro ε εpos
      have:= limitsx (Metric.ball x ε) (by exact Metric.ball_mem_nhds x εpos)
      simp only [Metric.mem_ball] at this
      exact this
    · intro cond U Unhds
      rw [Metric.mem_nhds_iff] at Unhds
      rcases Unhds with ⟨ε, εpos, ballsubU⟩
      rcases cond ε εpos with ⟨d₀, eq⟩
      use d₀
      intro d d₀led
      apply ballsubU
      rw [Metric.mem_ball]
      exact eq d d₀led

/- Characterization of a Cauchy net in a metric space -/
lemma cauchy_metric_iff {X D: Type*} [DirectedSet D] [PseudoMetricSpace X] (s: D → X):
  CauchyNet s ↔ ∀ (ε: ℝ), (0 < ε → ∃ (d₀: D), (∀ (d e: D), d₀ ≤ d → d₀ ≤ e → dist (s d) (s e) < ε)) := by
    constructor
    · intro sCauchy
      intro ε εpos
      have := sCauchy {p | dist p.1 p.2 < ε} (Metric.dist_mem_uniformity εpos)
      simp only [Set.mem_setOf_eq] at this
      assumption
    · intro cond
      intro U Uunif
      rw [Metric.mem_uniformity_dist] at Uunif
      rcases Uunif with ⟨ε, εpos, eq⟩
      rcases cond ε εpos with ⟨d₀, eq'⟩
      use d₀
      intro d e d₀led d₀lee
      exact eq (eq' d e d₀led d₀lee)

/- ### Constructions ### -/

/- Given a Cauchy net t: D → X in a metric space X and a positive sequence s: ℕ → ℝ, we can extract
   an (strictly) increasing sequence r : ℕ → D, such that for any d, e in D with r n ≤ d, e, we have that
   dist (t d) (t e) < s n. -/

def seqfromnet {X D: Type*} [PseudoMetricSpace X] [DirectedSet D] (t: D → X) (s: ℕ → ℝ): ℕ → D
  | 0 => if h: ∃ d₀, (∀ (d e : D), d₀ ≤ d → d₀ ≤ e → dist (t d) (t e) < s 0) then Classical.choose h else default' D
  | n + 1 => if h: ∃ (d₀: D), ((seqfromnet t s n) ≤ d₀ ∧ ((∀ (d e : D), d₀ ≤ d → d₀ ≤ e → dist (t d) (t e) < s (n + 1)))) then Classical.choose h else default' D

/- If the net t: D → X is Cauchy, then seqfromnet satisfies what we want -/
lemma seqfromnet_cond {X D: Type*} [PseudoMetricSpace X] [DirectedSet D] (t: D → X) (s: ℕ → ℝ) (spos: ∀ (n: ℕ), 0 < s n)
  (h: CauchyNet t):
    ∀ (n: ℕ), (∀ (d e : D), seqfromnet t s n ≤ d → seqfromnet t s n ≤ e → dist (t d) (t e) < s n) := by
      intro n d e led lee
      rw [cauchy_metric_iff] at h
      by_cases nz: n = 0
      · have cond := h (s 0) (spos 0)
        rw [nz] at led lee
        dsimp only [seqfromnet] at *
        rw [dif_pos cond] at *
        rw [nz]
        exact Classical.choose_spec cond d e led lee
      · rcases Nat.exists_eq_succ_of_ne_zero nz with ⟨m, neqm1⟩
        rw [Nat.succ_eq_add_one] at neqm1
        rw [neqm1] at led lee
        have cond : ∃ (d₀: D), ((seqfromnet t s m) ≤ d₀ ∧ ((∀ (d e : D), d₀ ≤ d → d₀ ≤ e → dist (t d) (t e) < s (m + 1)))) := by
          rcases h (s (m + 1)) (spos (m + 1)) with ⟨d₁, eq⟩
          rcases directed' d₁ (seqfromnet t s m) with ⟨d₀, d₁led₀, led₀⟩
          use d₀
          constructor
          · assumption
          · intro d e d₀led d₀lee
            exact eq d e (le_trans d₁led₀ d₀led) (le_trans d₁led₀ d₀lee)
        dsimp only [seqfromnet] at *
        rw [dif_pos cond] at *
        rw [neqm1]
        exact (Classical.choose_spec cond).2 d e led lee

/- The defined sequence is (strictly) increasing -/
lemma seqfromnet_incr' {X D: Type*} [PseudoMetricSpace X] [DirectedSet D] (t: D → X) (s: ℕ → ℝ) (spos: ∀ (n: ℕ), 0 < s n)
  (h: CauchyNet t):
    ∀ (n: ℕ), seqfromnet t s n ≤ seqfromnet t s (n + 1) := by
      intro n
      rw [cauchy_metric_iff] at h
      have cond : ∃ d₀, seqfromnet t s n ≤ d₀ ∧ ∀ (d e : D), d₀ ≤ d → d₀ ≤ e → dist (t d) (t e) < s (n + 1) := by
        rcases h (s (n + 1)) (spos (n + 1))  with ⟨d₁, eq⟩
        rcases directed' (seqfromnet t s n) d₁ with ⟨d₀, seqmled₀, d₁led₀⟩
        use d₀
        constructor
        · assumption
        · intro d e d₀led d₀lee
          exact eq d e (le_trans d₁led₀ d₀led) (le_trans d₁led₀ d₀lee)
      dsimp only [seqfromnet]
      rw [dif_pos cond]
      exact (Classical.choose_spec cond).1

lemma seqfromnet_incr {X D: Type*} [PseudoMetricSpace X] [DirectedSet D] (t: D → X) (s: ℕ → ℝ) (spos: ∀ (n: ℕ), 0 < s n)
  (h: CauchyNet t):
    Monotone (seqfromnet t s) := by
      intro n m nlem
      induction' m with m ih
      · rw [Nat.le_zero] at nlem
        rw [nlem]
      · rw [Nat.le_succ_iff_eq_or_le] at nlem
        rcases nlem with neqm1 | nlem
        · rw [Nat.succ_eq_add_one] at neqm1
          rw [← neqm1]
        · exact le_trans (ih nlem) (seqfromnet_incr' t s spos h m)

/- If if s has limit 0 , then the sequence t ∘ (seqfromnet t s) is a Cauchy sequence with the porperty that if
   it converges, then so does t and to the same point -/

lemma seqfromnet_cauchy {X D: Type*} [PseudoMetricSpace X] [DirectedSet D] (t: D → X) (s: ℕ → ℝ) (spos: ∀ (n: ℕ), 0 < s n)
  (h: CauchyNet t) (slimitz: Limit s 0):
    CauchyNet (t ∘ seqfromnet t s) := by
      rw [cauchy_metric_iff]
      intro ε εpos
      rw [limit_metric_iff] at slimitz
      rcases slimitz ε εpos with ⟨n₀, eq⟩
      have sn₀leε : s n₀ < ε := by
        have := eq n₀ (le_refl n₀)
        rw [dist_zero_right, Real.norm_eq_abs] at this
        exact lt_of_abs_lt this
      use n₀
      intro n m n₀len n₀lem
      have := seqfromnet_cond t s spos h n₀ (seqfromnet t s n) (seqfromnet t s m)
        (seqfromnet_incr t s spos h n₀len) (seqfromnet_incr t s spos h n₀lem)
      exact lt_trans this sn₀leε

lemma limit_of_seqfromnet_limit [PseudoMetricSpace X] [DirectedSet D] (t: D → X) (s: ℕ → ℝ) (spos: ∀ (n: ℕ), 0 < s n)
  (h: CauchyNet t) (slimitz: Limit s 0) (x: X):
    Limit (t ∘ seqfromnet t s) x → Limit t x := by
      intro tseqlimitx
      rw [limit_metric_iff] at *
      intro ε εpos
      rcases tseqlimitx (ε/2) (by linarith) with ⟨n₀, eq⟩
      rcases slimitz (ε/2) (by linarith) with ⟨n₁, eq'⟩
      have sleε2 : s (max n₀ n₁) < ε/2 := by
        have := eq' (max n₀ n₁) (le_max_right n₀ n₁)
        rw [dist_zero_right, Real.norm_eq_abs] at this
        exact lt_of_abs_lt this
      use seqfromnet t s (max n₀ n₁)
      intro d seqfled
      calc
        dist (t d) x ≤ dist (t d) (t (seqfromnet t s (max n₀ n₁))) + dist (t (seqfromnet t s (max n₀ n₁))) x := by
          exact dist_triangle (t d) (t (seqfromnet t s (max n₀ n₁))) x
        _ < ε/2 + dist (t (seqfromnet t s (max n₀ n₁))) x := by
          rw [add_lt_add_iff_right]
          have := seqfromnet_cond t s spos h (max n₀ n₁) d (seqfromnet t s (max n₀ n₁)) seqfled (le_refl (seqfromnet t s (max n₀ n₁)))
          exact lt_trans this sleε2
        _ < ε/2 + ε/2 := by
          rw [add_lt_add_iff_left]
          exact eq (max n₀ n₁) (le_max_left n₀ n₁)
        _ = ε := by
          linarith

/- ### Common limits of sequences and series ### -/

lemma limit_inv_n : ∀ (a: ℝ), Limit (fun (n: ℕ) ↦ 1/(n + a)) 0 := by
  intro a
  rw [limit_metric_iff]
  intro ε εpos
  rcases Real_archimedean 1 (1/ε - a) Real.zero_lt_one with ⟨n₀, lt1⟩
  rcases Real_archimedean 1 (- a) Real.zero_lt_one with ⟨n₁, lt2⟩
  use max n₀ n₁
  intro n maxlen
  rw [dist_zero_right, Real.norm_eq_abs]
  have napos : 0 < n + a := by
    calc
      0 < n₁ + a := by
        rw [mul_one, neg_lt_iff_pos_add] at lt2
        assumption
      _ ≤ n + a := by
        rw [add_le_add_iff_right, Nat.cast_le]
        exact le_trans (le_max_right n₀ n₁) maxlen
  have : |1 / (n + a)| = 1 / (n + a) := by
    rw [abs_eq_self, one_div, inv_nonneg]
    exact le_of_lt napos
  rw [this, one_div_lt napos εpos, ← sub_lt_iff_lt_add]
  calc
    1 / ε - a < n₀ := by
      rw [mul_one] at lt1
      assumption
    _ ≤ n := by
      rw [Nat.cast_le]
      exact le_trans (le_max_left n₀ n₁) maxlen

/- ### Completeness = SeqCompleteness ### -/

/- Completeness in metric spaces is equivalent to the statement that every Cauchy sequence is convergent -/
theorem Metric.complete_iff {X: Type*} [PseudoMetricSpace X]:
  CompleteSpace X ↔ ∀ (s: ℕ → X), CauchyNet s → ∃ (x: X), Limit s x := by
    constructor
    · intro completeX s cauchys
      rw [cauchy_net_iff_filter] at cauchys
      rcases completeX.complete cauchys with ⟨x, limitFx⟩
      use x
      rw [limit_net_iff_filter]
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
        exact limit_inv_n 1
      rcases cauchyconv (s ∘ (seqfromnet s i)) (seqfromnet_cauchy s i ipos cauchys ilimitz) with ⟨x, limitsix⟩
      use x
      exact limit_of_seqfromnet_limit s i ipos cauchys ilimitz x limitsix
