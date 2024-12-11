import Topology.Nets.Theorems
import CajonSastre.Finset

set_option trace.Meta.Tactic.simp false

noncomputable section

open Set Filter Topology Function DirectedSet Net

variable {D: Type*} [DirectedSet D]
variable {X: Type*} [TopologicalSpace X]
variable {Y: Type*} [TopologicalSpace Y] [LinearOrder Y] [DenselyOrdered Y] [OrderTopology Y]
variable {Z: Type*} [UniformSpace Z]
variable {W: Type*} [TopologicalSpace W] [LinearOrder W] [OrderTopology W]

/- ### Monotonic behaviour of nets ### -/

theorem limit_le {x y: Y} (s t: D → Y) (slx: Limit s x) (tly: Limit t y)
  (xlty: x < y) : ∃ (d₀: D), ∀ d ≥ d₀, s d < t d := by
    rcases exists_between xlty with ⟨z, xltz, zlty⟩
    have ltz_nhds : {u: Y | u < z} ∈ 𝓝 x := IsOpen.mem_nhds (isOpen_gt' z) xltz
    have gtz_nhds : {u: Y | z < u} ∈ 𝓝 y := IsOpen.mem_nhds (isOpen_lt' z) zlty
    rcases slx {u | u < z} ltz_nhds with ⟨d₁, eqx⟩
    rcases tly {u | z < u} gtz_nhds with ⟨d₂, eqy⟩
    simp only [Set.mem_setOf_eq] at *
    rcases directed' d₁ d₂ with ⟨d₀, d₀led₁, d₀led₂⟩
    use d₀
    intro d d₀led
    exact lt_trans (eqx d (le_trans d₀led₁ d₀led)) (eqy d (le_trans d₀led₂ d₀led))

theorem le_limit {x y: Y} (s t: D → Y) (slet: ∀ (d: D), s d ≤ t d)
  (slx: Limit s x) (tly: Limit t y) : x ≤ y := by
    by_contra! h
    rcases limit_le t s tly slx h with ⟨d₀, eq⟩
    have := lt_of_le_of_lt (slet d₀) (eq d₀ (le_refl d₀))
    exact (lt_self_iff_false (s d₀)).mp this

theorem le_limit' {x y: Y} (s t: D → Y) (sltt: ∀ (d: D), s d < t d)
  (slx: Limit s x) (tly: Limit t y) : x ≤ y := by
    have : ∀ (d: D), s d ≤ t d := by
      intro d
      exact le_of_lt (sltt d)
    exact le_limit s t this slx tly

theorem sandwich (s t u: D → W) (slet: ∀ (d: D), s d ≤ t d)
  (tleu: ∀ (d: D), t d ≤ u d) {x: W} (slx: Limit s x) (ulx: Limit u x) :
    Limit t x := by
      rw [limit_iff_tendsto] at *
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le slx ulx slet tleu

theorem sandwich' (s t u: D → W) (slet: ∃ (d₀: D), ∀ d ≥ d₀, s d ≤ t d)
  (tleu: ∃ (d₀: D), ∀ d ≥ d₀, t d ≤ u d) {x: W} (slx: Limit s x) (ulx: Limit u x) :
    Limit t x := by
      rw [limit_iff_tendsto] at *
      apply tendsto_of_tendsto_of_tendsto_of_le_of_le' slx ulx
      repeat
        simp only [eventually_atTop]
        assumption

/- ### Operations on limits ### -/

/- Limit of constant net -/
theorem lim_of_cte (x: X): Limit (fun (_: D) ↦ x) x := by
  intro U Unhds
  use default
  intro d defled
  exact mem_of_mem_nhds Unhds

/- Negation of convergent net is convergent -/
theorem lim_of_neg_eq_neg_of_lim [Neg X] [h: ContinuousNeg X]
  {s: D → X} {x: X}:
  Limit s x → Limit (fun (d: D) ↦ - (s d)) (-x) := by
    exact limfunnet_of_continuousAt (fun (z: X) ↦ -z) x
      (continuous_iff_continuousAt.mp h.continuous_neg x)

/- Limit of inverse -/
theorem lim_of_inv_eq_inv_of_lim [Inv X] [h: ContinuousInv X]
  {s: D → X} {x: X} :
  Limit s x  →  Limit (fun (d: D) ↦ (s d)⁻¹) (x⁻¹):= by
    exact limfunnet_of_continuousAt (fun (z: X) ↦ z⁻¹) x
      (continuous_iff_continuousAt.mp h.continuous_inv x)

theorem lim_of_inv_eq_inv_of_lim₀ [Inv X] [Zero X] [h: HasContinuousInv₀ X]
  {s: D → X} {x: X} (nez: x ≠ 0) :
  Limit s x  →  Limit (fun (d: D) ↦ (s d)⁻¹) (x⁻¹):= by
    exact limfunnet_of_continuousAt (fun (z: X) ↦ z⁻¹) x
      (h.continuousAt_inv₀ nez)

/- Sum of convergent nets is convergent -/
theorem lim_of_sums_eq_sums_of_lim  [AddCommMonoid X]
  [h: ContinuousAdd X] {f : J → D → X} {a : J → X} {s : Finset J} :
    (∀ j ∈ s, Limit (f j) (a j)) →
    Limit (fun (d : D) ↦ ∑ j ∈ s, f j d) (∑ j ∈ s, a j) := by
      simp only [limit_iff_tendsto]
      exact tendsto_finset_sum s

theorem lim_of_sum_eq_sum_of_lim [Add X] [h: ContinuousAdd X]
  {s t: D → X} {x y: X}:
  Limit s x → Limit t y → Limit (fun (d: D) ↦ (s d) + (t d)) (x + y) := by
    exact limfunnet_of_continuousAt'
      (continuous_iff_continuousAt.mp h.continuous_add (x, y))

theorem lim_of_mul_eq_mul_of_lim [Mul X] [h: ContinuousMul X]
  {s t: D → X} {x y: X}:
  Limit s x → Limit t y → Limit (fun (d: D) ↦ (s d) * (t d)) (x * y) := by
    exact limfunnet_of_continuousAt'
      (continuous_iff_continuousAt.mp h.continuous_mul (x, y))

/- Difference of convergent nets is convergent -/
theorem lim_of_sub_eq_sub_of_lim [Sub X] [h: ContinuousSub X]
  {s t: D → X} {x y: X} :
  Limit s x → Limit t y → Limit (fun (d: D) ↦ (s d) - (t d)) (x - y) := by
    exact limfunnet_of_continuousAt'
      (continuous_iff_continuousAt.mp h.continuous_sub (x, y))

/- Product of scalar and convergent nets is convergent -/
theorem prod_num_conv {R: Type*} [TopologicalSpace R] [SMul R X]
  [h: ContinuousSMul R X] {x: X} {s: D → X} (r: R):
  Limit s x → Limit (fun (d: D) ↦ r • (s d)) (r • x) := by
    intro slimitx
    exact limfunnet_of_continuousAt'
      (continuous_iff_continuousAt.mp h.continuous_smul (r, x))
        (lim_of_cte r) slimitx

/- Operations on CauchyNets -/

theorem cauchynet_neg {s: D → Z} [AddGroup Z] [UniformAddGroup Z] :
  CauchyNet s → CauchyNet (fun (d: D) ↦ - (s d)) := by
    simp only [← cauchySeq_iff_cauchynet]
    exact CauchySeq.neg

theorem cauchynet_inv {s: D → Z}  [Group Z] [UniformGroup Z] :
  CauchyNet s → CauchyNet (fun (d: D) ↦ (s d)⁻¹) := by
    simp only [← cauchySeq_iff_cauchynet]
    exact CauchySeq.inv

theorem cauchynet_add {s t: D → Z} [AddGroup Z] [UniformAddGroup Z] :
  CauchyNet s → CauchyNet t → CauchyNet (fun (d: D) ↦ s d + t d) := by
    simp only [← cauchySeq_iff_cauchynet]
    exact CauchySeq.add

theorem cauchynet_const_mul {s: D → Z} {x: Z} [Group Z] [UniformGroup Z] :
  CauchyNet s → CauchyNet (fun (d: D) ↦ x * s d) := by
    simp only [← cauchySeq_iff_cauchynet]
    exact CauchySeq.const_mul

theorem cauchynet_const_smul {Y: Type*} [SeminormedAddCommGroup Y] (𝕜: Type*)
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 Y] {s: D → Y} (a: 𝕜) :
  CauchyNet s → CauchyNet (fun (d: D) ↦ a • (s d)) := by
    simp only [cauchy_metric_iff, dist_eq_norm]
    intro cauchys
    by_cases h: a = 0
    · simp only [h, zero_smul, sub_zero, norm_zero]
      intro ε εpos
      use default
      intro d e _ _
      exact εpos
    · intro ε εpos
      rcases cauchys (ε * ‖a‖⁻¹)
        (mul_pos εpos (inv_pos_of_pos (norm_pos_iff.mpr h))) with ⟨d₀, eq⟩
      use d₀
      intro d e d₀led d₀lee
      rw [← smul_sub, norm_smul, ← lt_mul_inv_iff₀' (norm_pos_iff.mpr h)]
      exact eq d e d₀led d₀lee

theorem cauchynet_iff_cauchynet_const_smul {Y: Type*} [SeminormedAddCommGroup Y] (𝕜: Type*)
  [NontriviallyNormedField 𝕜] [NormedSpace 𝕜 Y] {s: D → Y} (a: 𝕜) (anezero: a ≠ 0) :
  CauchyNet s ↔ CauchyNet (fun (d: D) ↦ a • (s d)) := by
    constructor
    · exact cauchynet_const_smul 𝕜 a
    · intro cauchya
      have := cauchynet_const_smul 𝕜 a⁻¹ cauchya
      have : (fun d ↦ a⁻¹ • a • s d) = s := by
        ext d
        rw [← smul_assoc, smul_eq_mul, inv_mul_cancel₀ anezero, one_smul]
      rw [← this]
      assumption

/- ### Monotone convergence criterion ### -/

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

theorem mono_bounded_implies_conv (s: D → ℝ):
  Monotone s → BddAbove (range s) → Limit s (sSup (range s)) := by
    intro smono sbdd
    have: (range s).Nonempty := by
      use s default
      use default
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
