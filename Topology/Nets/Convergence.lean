import Topology.Nets.Theorems
import Mathlib.Analysis.SpecialFunctions.Log.Basic

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

lemma cauchy_metric_iff' {X: Type*}[PseudoMetricSpace X] (s: ℕ → X):
  CauchyNet s ↔ ∀ (ε: ℝ), (0 < ε → ∃ (n₀: ℕ), (∀ (n m: ℕ), n₀ ≤ n → n ≤ m → dist (s n) (s m) < ε)) := by
    rw [cauchy_metric_iff]
    constructor
    · intro cond ε εpos
      rcases cond ε εpos with ⟨n₀, eq⟩
      use n₀
      intro n m n₀len nlem
      exact eq n m n₀len (le_trans n₀len nlem)
    · intro cond ε εpos
      rcases cond ε εpos with ⟨n₀, eq⟩
      use n₀
      intro n m n₀len n₀lem
      by_cases h: n ≤ m
      · exact eq n m n₀len h
      · rw [Nat.not_le] at h
        rw [dist_comm]
        exact eq m n n₀lem (le_of_lt h)

/- ### Some properties ### -/

/- Any convergent net in a metric space is Cauchy -/
theorem conv_implies_cauchy {D X: Type*} [DirectedSet D] [UniformSpace X] {s: D → X} (h: ∃ (x: X), Limit s x):
  CauchyNet s := by
    intro U Uunif
    rcases comp_mem_uniformity_sets Uunif with ⟨V, Vunif, VoVsubU⟩
    rcases h with ⟨x, slimitx⟩
    rcases slimitx {y: X | (x, y) ∈ V} (by exact mem_nhds_left x Vunif) with ⟨d₁, eq1⟩
    rcases slimitx {y: X | (y, x) ∈ V} (by exact mem_nhds_right x Vunif) with ⟨d₂, eq2⟩
    rcases directed' d₁ d₂ with ⟨d₀, d₁led₀, d₂led₀⟩
    use d₀
    intro d e d₀led d₀lee
    apply VoVsubU
    rw [mem_compRel]
    use x
    constructor
    · have:= eq2 d (le_trans d₂led₀ d₀led)
      rw [Set.mem_setOf_eq] at this
      assumption
    · have:= eq1 e (le_trans d₁led₀ d₀lee)
      rw [Set.mem_setOf_eq] at this
      assumption

/- In particular, a summable family satisfies the Cauchy condition -/
/- A summable family satisfies the Cauchy condition in a normed space -/
theorem summable_implies_cauchysum {I X: Type*} [AddCommMonoid X] [UniformSpace X] {f: I → X} (h: Summable f):
  CauchySumNet f := by
    rw [summable_iff_summablenet] at h
    exact conv_implies_cauchy h

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

/- Any Cauchy sequence in a metric space is bounded -/
theorem cauchy_imp_bounded {X: Type*} [PseudoMetricSpace X] {s: ℕ → X}:
  CauchyNet s → Bornology.IsBounded (range s) := by
    intro cauchys
    rw [Metric.isBounded_iff']
    intro x
    rw [cauchy_metric_iff'] at cauchys
    rcases cauchys 1 Real.zero_lt_one with ⟨n₀, eq⟩
    let A : Set ℝ := {y | ∃ x, ∃ (_ : x ∈ Iio n₀), dist (s x) (s n₀) = y} ∪ {1}
    have Afin: Finite A := by
      rw [finite_coe_iff, finite_union]
      constructor
      · exact Set.Finite.dependent_image (finite_Iio n₀) (fun (n: ℕ) (h: n ∈ Iio n₀) ↦ dist (s n) (s n₀))
      · exact finite_singleton 1
    have Anempty: Nonempty A := by
      use 1
      exact mem_union_right {y | ∃ x, ∃ (_ : x ∈ Iio n₀), dist (s x) (s n₀) = y} rfl
    rcases Finite.exists_max (fun (a: A) ↦ a) with ⟨a, amax⟩
    use a + dist (s n₀) x + 1
    constructor
    · have : 0 ≤ dist (s n₀) x := by
        exact dist_nonneg
      have onelea : (1: ℝ) ≤ a := by
        exact amax ⟨1, mem_union_right {y | ∃ x, ∃ (_ : x ∈ Iio n₀), dist (s x) (s n₀) = y} rfl⟩
      linarith [onelea, this]
    · intro y yinranges
      rw [mem_range] at yinranges
      rcases yinranges with ⟨n, sneqy⟩
      rw [← sneqy, Metric.mem_ball]
      calc
          dist (s n) x ≤ dist (s n) (s n₀) + dist (s n₀) x := by
            exact dist_triangle (s n) (s n₀) x
          _ ≤ a + dist (s n₀) x := by
            apply add_le_add_right
            by_cases h: n₀ ≤ n
            · have : dist (s n) (s n₀) ≤ 1 := by
                rw [dist_comm]
                exact le_of_lt (eq n₀ n (le_refl n₀) h)
              exact le_trans this (amax ⟨1, mem_union_right {y | ∃ x, ∃ (_ : x ∈ Iio n₀), dist (s x) (s n₀) = y} rfl⟩)
            · have : dist (s n) (s n₀) ∈ A := by
                push_neg at h
                rw [mem_union, Set.mem_setOf_eq]
                apply Or.inl
                use n, mem_Iio.mpr h
              exact amax ⟨dist (s n) (s n₀), this⟩
          _ < a + dist (s n₀) x + 1 := by
            linarith

/- Limit of constant net -/
theorem limit_cte {X D: Type*} [DirectedSet D] [TopologicalSpace X] (x: X): Limit (fun (_: D) ↦ x) x := by
  intro U Unhds
  use default' D
  intro d defled
  exact mem_of_mem_nhds Unhds

/- Image of continuous function of convergent nets converges -/
theorem fun_conv {X Y Z D: Type*} [DirectedSet D] [AddCommGroup X] [TopologicalSpace X] [TopologicalSpace Y] [TopologicalSpace Z]
  {s: D → X} {t: D → Y} {x: X} {y: Y} {f: X × Y → Z}:
  ContinuousAt f (x,y) → Limit s x → Limit t y → Limit (fun (d: D) ↦ f ((s d), (t d))) (f (x, y)) := by
    intro contf slimitx tlimity
    let S: D → X × Y := fun (d: D) ↦ (s d, t d)
    have Slimitxy: Limit S (x,y) := by
      rw [prod_limit']
      exact And.intro slimitx tlimity
    exact apply_fun_net f (x,y) contf Slimitxy

/- Sum of convergent nets is convergent -/
theorem sum_conv {X D: Type*} [DirectedSet D] [AddCommGroup X] [TopologicalSpace X] [h: TopologicalAddGroup X]
  {s t: D → X} {x y: X}: Limit s x → Limit t y → Limit (fun (d: D) ↦ (s d) + (t d)) (x + y) := by
    exact fun_conv (continuous_iff_continuousAt.mp h.continuous_add (x, y))

/- Difference of convergent nets is convergent -/
theorem sub_conv {X D: Type*} [DirectedSet D] [AddCommGroup X] [TopologicalSpace X] [h: TopologicalAddGroup X]
  {s t: D → X} {x y: X}: Limit s x → Limit t y → Limit (fun (d: D) ↦ (s d) - (t d)) (x - y) := by
    have := (@TopologicalAddGroup.to_continuousSub X _ _ h).continuous_sub
    exact fun_conv (continuous_iff_continuousAt.mp this (x, y))

/- Product of scalar and convergent nets is convergent -/
theorem prod_num_conv {X D 𝕂: Type*} [DirectedSet D] [RCLike 𝕂] [AddCommGroup X] [Module 𝕂 X] [TopologicalSpace X]
  [h: ContinuousSMul 𝕂 X] {x: X} {s: D → X} (a: 𝕂):
  Limit s x → Limit (fun (d: D) ↦ a • (s d)) (a • x) := by
    intro slimitx
    exact fun_conv (continuous_iff_continuousAt.mp h.continuous_smul (a, x)) (limit_cte a) slimitx

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

/- The defined sequence is increasing -/
lemma seqfromnet_incr' {X D: Type*} [PseudoMetricSpace X] [DirectedSet D] (t: D → X) (s: ℕ → ℝ) (spos: ∀ (n: ℕ), 0 < s n)
  (h: CauchyNet t):
    ∀ (n: ℕ), seqfromnet t s n ≤ seqfromnet t s (n + 1) := by
      intro n
      rw [cauchy_metric_iff] at h
      have cond : ∃ d₀, seqfromnet t s n ≤ d₀ ∧ ∀ (d e : D), d₀ ≤ d → d₀ ≤ e → dist (t d) (t e) < s (n + 1) := by
        rcases h (s (n + 1)) (spos (n + 1)) with ⟨d₁, eq⟩
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

theorem limit_inv_n : ∀ (a: ℝ), Limit (fun (n: ℕ) ↦ 1/(n + a)) 0 := by
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

theorem limit_lessone_zero {𝕂: Type*} [RCLike 𝕂] {r: 𝕂} (rltone: ‖r‖ < 1): Limit (fun (n: ℕ) ↦ r^n) 0 := by
  rw [limit_metric_iff]
  intro ε εpos
  simp only [dist_eq_norm, sub_zero, norm_pow]
  by_cases h: 1 < ε
  · use 0
    intro d zled
    calc
      ‖r‖^d ≤ 1 := by
        exact pow_le_one₀ (norm_nonneg r) (le_of_lt rltone)
      _ < ε := by
        exact h
  · push_neg at h
    use Nat.floor ((Real.log ε)/(Real.log ‖r‖)) + 1
    intro n len
    by_cases h': r = 0
    · rw [h', norm_zero, zero_pow]
      · exact εpos
      · linarith
    · rw [← Real.log_lt_log_iff (pow_pos (norm_pos_iff.mpr h') n) εpos, Real.log_pow, ← div_lt_iff_of_neg]
      · calc
          Real.log ε / Real.log ‖r‖ < ⌊Real.log ε / Real.log ‖r‖⌋₊ + 1 := by
            exact Nat.lt_floor_add_one (Real.log ε / Real.log ‖r‖)
          _ ≤ n := by
            norm_cast
      · rw [Real.log_neg_iff]
        · exact rltone
        · exact norm_pos_iff'.mpr h'

lemma Finset.sum_Iic_zero {X: Type*} [AddCommMonoid X] (f: ℕ → X): ∑ n ≤ 0, f n = f 0 := by
  have : Finset.Iic 0 = {0} := by
    rfl
  rw [this]
  exact Finset.sum_singleton f 0

lemma Finset.sum_Iic_eq_sum_Ioc_add_Iic {M: Type*} [AddCommMonoid M] {f : ℕ → M} {n m : ℕ}
  (h : n ≤ m) : ∑ i ∈ Finset.Iic m, f i = ∑ i ∈ Finset.Ioc n m, f i + ∑ i ∈ Finset.Iic n, f i := by
    have inter: ∀ (m: ℕ), Finset.Iic m = Finset.Icc 0 m := by
      intro m
      exact rfl
    simp only [inter]
    induction' n with n ih
    · simp only [Finset.Icc_self, Finset.sum_singleton]
      rw [Finset.sum_Ioc_add_eq_sum_Icc h]
    · rw [Finset.sum_Icc_succ_top (Nat.le_add_left 0 (n + 1)), add_comm _ (f (n + 1)), ← add_assoc,
          Finset.sum_Ioc_add_eq_sum_Icc h]
      simp only [Nat.Icc_succ_left]
      exact ih (Nat.le_of_succ_le h)

lemma finite_geo_sum {𝕂: Type*} [RCLike 𝕂] {r: 𝕂} (rneone: r ≠ 1): (fun N ↦ ∑ n ∈ Finset.Iic N, (fun n ↦ r ^ n) n) = (fun N ↦ (r^(N + 1) - 1)/(r - 1)) := by
  ext N
  induction' N with N ih
  · rw [Finset.sum_Iic_zero, pow_zero, zero_add, pow_one, div_self (sub_ne_zero_of_ne rneone)]
  · rw [Finset.sum_Iic_eq_sum_Ioc_add_Iic (Nat.le_add_right N 1), Nat.Ioc_succ_singleton, Finset.sum_singleton, ih]
    nth_rw 1 [← one_mul (r ^ (N + 1)), ← div_self (sub_ne_zero_of_ne rneone)]
    rw [← mul_div_right_comm, div_add_div_same, sub_mul, add_sub, sub_add, one_mul, sub_self, sub_zero, ← pow_succ']

theorem geo_sum {𝕂: Type} [RCLike 𝕂] {r: 𝕂} (rltone: ‖r‖ < 1): conv_serie_to (fun (n: ℕ) ↦ r^n) (1-r)⁻¹ := by
  unfold conv_serie_to
  have: r ≠ 1 := by
    by_contra reqone
    rw [reqone, norm_one] at rltone
    linarith
  rw [finite_geo_sum this]
  have := prod_num_conv (r/(r-1)) (limit_lessone_zero rltone)
  simp only [smul_eq_mul, div_mul_eq_mul_div, ← pow_succ', mul_zero] at this
  have sol := sum_conv this (limit_cte (-1/(r-1)))
  simp only [div_add_div_same, zero_add, Mathlib.Tactic.RingNF.add_neg] at sol
  have : (-1/(r - 1)) = (1 - r)⁻¹ := by
    rw [inv_eq_one_div, neg_eq_neg_one_mul, mul_comm, ← div_mul_eq_mul_div, ← one_div_neg_one_eq_neg_one,
        div_mul_div_comm, mul_one, sub_mul, one_mul, mul_comm, ← neg_eq_neg_one_mul, neg_sub_neg]
  simp only [this] at sol
  exact sol

theorem geo_sum_inv {a: ℝ} (onelta: 1 < a): conv_serie_to (fun (n: ℕ) ↦ 1/(a^n)) (a/(a-1)) := by
  have: (fun (n: ℕ) ↦ 1/(a^n)) = (fun (n: ℕ) ↦ (1/a)^n) := by
    ext n
    norm_num
  rw[this]
  have rr: ‖1/a‖ < 1 := by
    rw [Real.norm_eq_abs]
    have : 1 < |a| := by
      exact lt_of_lt_of_le onelta (le_abs_self a)
    rw [← mul_lt_mul_right (lt_trans zero_lt_one this), abs_one_div, one_mul, one_div_mul_cancel]
    · assumption
    · linarith
  have : (1 - 1 / a)⁻¹ = a/(a-1) := by
    rw [one_sub_div, inv_div]
    linarith
  rw [← this]
  exact geo_sum rr

/- ### Convergence criterions ### -/

/- Monotone and bounded criterion -/

lemma exists_lt_LUB {s: Set ℝ} {a: ℝ} (h: IsLUB s a) (ε: ℝ) (εpos: 0 < ε) :
  ∃ b ∈ s, a - ε < b := by
    have := h.2
    rw [mem_lowerBounds] at this
    have : a - ε ∉ upperBounds s := by
      intro aεupb
      have := this (a - ε) aεupb
      linarith
    rw [mem_upperBounds] at this
    push_neg at this
    rcases this with ⟨b, bins, aεltb⟩
    use b

theorem mono_bounded_implies_conv (s: ℕ → ℝ): Monotone s → BddAbove (range s) → Limit s (sSup (range s)) := by
  intro smono sbdd
  have: (range s).Nonempty := by
    use s 0
    rw [mem_range]
    use 0
  rcases Real.exists_isLUB this sbdd with ⟨α, αLUB⟩
  rw [IsLUB.csSup_eq αLUB this, limit_metric_iff]
  intro ε εpos
  rcases exists_lt_LUB αLUB ε εpos with ⟨a, ains, αεlta⟩
  rw [mem_range] at ains
  rcases ains with ⟨n₀, sn₀eqa⟩
  use n₀
  intro n n₀len
  rw [dist_eq_norm, Real.norm_eq_abs, abs_sub_lt_iff]
  constructor
  · rw [sub_lt_iff_lt_add']
    have : s n ≤ α := by
      have := αLUB.1
      rw [mem_upperBounds] at this
      exact this (s n) (by rw [mem_range]; use n)
    exact lt_of_le_of_lt this (by linarith)
  · rw [sub_lt_comm]
    apply lt_of_lt_of_le αεlta
    rw [← sn₀eqa]
    exact smono n₀len

/- Comparation test -/
lemma pos_serie_incr (f: ℕ → ℝ) (fpos: ∀ (n: ℕ), 0 ≤ f n):
  Monotone (fun (N: ℕ) ↦ ∑ n ≤ N, f n) := by
    intro N M NleM
    simp
    rw [Finset.sum_Iic_eq_sum_Ioc_add_Iic NleM]
    nth_rw 1 [← zero_add (∑ n ∈ Finset.Iic N, f n)]
    rw [add_le_add_iff_right]
    apply Finset.sum_nonneg
    intro i iin
    exact fpos i

theorem comparation_test (f g: ℕ → ℝ) (fpos: ∀ (n: ℕ), 0 ≤ f n):
  (∀ (n: ℕ), f n ≤ g n) → conv_serie g → conv_serie f := by
    intro fleg convg
    use (sSup (range (fun N ↦ ∑ n ∈ Finset.Iic N, f n)))
    apply mono_bounded_implies_conv
    · exact pos_serie_incr f fpos
    · have : Bornology.IsBounded (range fun N ↦ ∑ n ∈ Finset.Iic N, g n) := by
        exact cauchy_imp_bounded (conv_implies_cauchy convg)
      rw [Metric.isBounded_iff'] at this
      rcases this 0 with ⟨r, rpos, rangebdd⟩
      use r
      rw [mem_upperBounds]
      intro x xinrange
      rw [mem_range] at xinrange
      rcases xinrange with ⟨N, sumNeqx⟩
      rw [← sumNeqx]
      calc
          ∑ n ∈ Finset.Iic N, f n ≤ ∑ n ∈ Finset.Iic N, g n := by
            apply Finset.sum_le_sum
            intro i iin
            exact fleg i
          _ ≤ r := by
            have : ∑ n ∈ Finset.Iic N, g n ∈ (range fun N ↦ ∑ n ∈ Finset.Iic N, g n) := by
              use N
            have := rangebdd this
            rw [Metric.mem_ball, dist_eq_norm, Real.norm_eq_abs, sub_zero] at this
            exact le_of_lt (lt_of_abs_lt this)

theorem comparation_test_abs {X 𝕂: Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X] {f: ℕ → X} (g: ℕ → ℝ):
  (∀ (n: ℕ), ‖f n‖ ≤ g n) → conv_serie g → conv_abs_serie 𝕂 f := by
    intro fleg convserieg
    have: conv_serie (fun n ↦ ‖f n‖) := by
      apply comparation_test (fun n ↦ ‖f n‖) g _ fleg convserieg
      intro n
      exact norm_nonneg (f n)
    rcases this with ⟨t, fconvseriet⟩
    use t
    exact fconvseriet

theorem comparation_test_abs_geo {X 𝕂: Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X] (f: ℕ → X) {a: ℝ}
  (onelta: 1 < a): (∀ (n: ℕ), ‖f n‖ ≤ 1 / (a^n)) → conv_abs_serie 𝕂 f := by
    intro cond
    apply comparation_test_abs (fun (n: ℕ) ↦ 1/(a^n))
    · assumption
    · use a/(a-1)
      exact geo_sum_inv onelta

/- Telescopic series -/
lemma Finset.Icc_union {m n k: ℕ} (mlek: m ≤ k) (klen: k ≤ n) :
  Finset.Icc m n = Finset.Icc m k ∪ Finset.Icc (k + 1) n := by
    ext x
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
    by_cases xlek: x ≤ k
    · constructor
      · intro xin
        left
        exact And.intro xin.1 xlek
      · intro xin
        rcases xin with h | h
        · exact And.intro h.1 (le_trans h.2 klen)
        · exact And.intro (le_trans (le_trans mlek (Nat.le_succ k)) h.1) h.2
    · push_neg at xlek
      constructor
      · intro xin
        right
        exact And.intro xlek xin.2
      · intro xin
        rcases xin with h | h
        · linarith
        · exact And.intro (le_trans (le_trans mlek (Nat.le_succ k)) h.1) h.2

lemma Finset.Icc_disjoint {m n p q: ℕ} (nltp: n < p):
  Disjoint (Finset.Icc m n) (Finset.Icc p q) := by
    rw [Finset.disjoint_left]
    intro x xinmn
    rw [Finset.mem_Icc] at *
    push_neg
    intro plex
    linarith

lemma Finset.sum_succ {M: Type*} [AddCommGroup M] {f : ℕ → M} {N : ℕ} (m: ℕ):
  ∑ x ∈ Finset.Iic N, f (x + m) = ∑ x ∈ Finset.Icc m (N + m), f (x) := by
    induction' N with N ih
    · rw [Finset.sum_Iic_zero, zero_add, Finset.Icc_self, Finset.sum_singleton]
    · rw [Finset.sum_Iic_eq_sum_Ioc_add_Iic (Nat.le_add_right N 1), Nat.Ioc_succ_singleton, Finset.sum_singleton, ih]
      have union: Finset.Icc m (N + 1 + m) = Finset.Icc (N + 1 + m) (N + 1 + m) ∪ Finset.Icc m (N + m) := by
        rw [add_comm, ← add_assoc, add_comm m N, Finset.union_comm]
        exact Finset.Icc_union (Nat.le_add_left m N) (Nat.le_succ (N + m))
      have disj: Disjoint (Finset.Icc (N + 1 + m) (N + 1 + m)) (Finset.Icc m (N + m)) := by
        rw [disjoint_comm]
        apply Finset.Icc_disjoint
        linarith
      rw [union, Finset.sum_union disj, add_right_cancel_iff, Finset.Icc_self, Finset.sum_singleton]

lemma Finset.sum_Icc_sub_Icc {M: Type*} [AddCommGroup M] {f : ℕ → M} {m n k : ℕ} (mlek: m ≤ k)
  (klen : k ≤ n) : ∑ i ∈ Finset.Icc m n, f i - ∑ i ∈ Finset.Icc m k, f i = ∑ i ∈ Finset.Ioc k n, f i := by
  rw [Finset.Icc_union mlek klen, Finset.sum_union (Finset.Icc_disjoint (lt_add_one k)),
      add_comm, ← add_sub, sub_self, add_zero]
  have : Finset.Icc (k + 1) n = Finset.Ioc k n := by
    exact Nat.Icc_succ_left k n
  rw [this]

lemma Finset.sum_Iic_telescopic {M: Type*} [AddCommGroup M] {f : ℕ → M} {N : ℕ}:
  ∑ x ∈ Finset.Iic N, (f (x + 1) - f x) = f (N + 1) - f 0 := by
    by_cases h: 1 ≤ N
    · rw [Finset.sum_sub_distrib, Finset.sum_succ, Finset.sum_Iic_eq_sum_Ioc_add_Iic (Nat.zero_le N),Finset.sum_Iic_zero,
        sub_add_eq_sub_sub, ← Nat.Icc_succ_left, Finset.sum_Icc_sub_Icc h (Nat.le_succ N), Nat.Ioc_succ_singleton,
        Finset.sum_singleton]
    · push_neg at h
      rw [Nat.lt_one_iff] at h
      rw [h, Finset.sum_Iic_zero]

theorem telescopic_conv_to {X: Type*} [AddCommGroup X] [TopologicalSpace X] [TopologicalAddGroup X] {f g: ℕ → X}
  (tlsc: ∀ (n: ℕ), f n = g (n + 1) - g n) {x: X} (limitg: Limit g x): conv_serie_to f (x - g 0) := by
    unfold conv_serie_to
    simp only [tlsc, Finset.sum_Iic_telescopic]
    apply sub_conv
    · exact shift_subsequence_conv g 1 limitg
    · exact limit_cte (g 0)

theorem telescopic_conv {X: Type*} [AddCommGroup X] [TopologicalSpace X] [TopologicalAddGroup X] {f g: ℕ → X}
  (tlsc: ∀ (n: ℕ), f n = g (n + 1) - g n) {x: X} (limitg: Limit g x): conv_serie f := by
    use x - g 0
    exact telescopic_conv_to tlsc limitg

theorem conv_telescopic_to {X: Type*} [AddCommGroup X] [TopologicalSpace X] [TopologicalAddGroup X] (f g: ℕ → X)
  (tlsc: ∀ (n: ℕ), f n = g (n + 1) - g n) {x: X} (fconvx: conv_serie_to f x): Limit g (x + g 0) := by
    sorry

theorem conv_telescopic {X: Type*} [AddCommGroup X] [TopologicalSpace X] [TopologicalAddGroup X] (f g: ℕ → X)
  (tlsc: ∀ (n: ℕ), f n = g (n + 1) - g n) (fconv: conv_serie f): ∃ (x: X), Limit g x := by
    sorry


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
