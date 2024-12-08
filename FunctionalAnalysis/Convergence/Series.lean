import FunctionalAnalysis.Convergence.Summability
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Completeness

set_option trace.Meta.Tactic.simp false

noncomputable section

open Set Filter Topology Function DirectedSet Net

variable {X: Type*} [AddCommMonoid X] [TopologicalSpace X]
variable {Y: Type*} [SeminormedAddCommGroup Y]
variable {Z: Type*} [AddCommMonoid Z] [UniformSpace Z]
variable {W: Type*} [NormedAddCommGroup W]
variable {M: Type*} [AddCommGroup M]

/- ### Definitions ### -/

def lim_serie (f: ℕ → X) (x: X): Prop :=
   Limit (fun (N: ℕ) ↦ ∑ n ≤ N, f n) x

def conv_serie (f: ℕ → X): Prop :=
   ∃ (x: X), lim_serie f x

def lim_abs_serie (f: ℕ → Y) (t: ℝ) : Prop :=
      lim_serie (fun (n: ℕ) ↦ ‖f n‖) t

def conv_abs_serie (f: ℕ → Y) : Prop :=
   ∃ (t: ℝ), lim_abs_serie f t

def CauchySerie (f: ℕ → Z): Prop :=
   CauchyNet (fun (N: ℕ) ↦ ∑ n ≤ N, f n)

/- ### Characterizations ### -/

theorem lim_serie_iff_tendsto (f: ℕ → X) (x: X) :
  lim_serie f x ↔ Tendsto (fun (n : ℕ) ↦ ∑ i ∈ Finset.range n, f i)
   Filter.atTop (nhds x) := by
    sorry

theorem conv_serie_iff_exists_tendsto (f: ℕ → X) :
  conv_serie f ↔ ∃ (x: X), Tendsto (fun (n : ℕ) ↦ ∑ i ∈ Finset.range n, f i)
   Filter.atTop (nhds x) := by
    unfold conv_serie
    simp only [lim_serie_iff_tendsto]

/- Characterization of convergence of a series in a normed space -/
theorem lim_serie_eps (f: ℕ → Y) (x: Y) :
  lim_serie f x ↔ ∀ ε, 0 < ε → (∃ (n₀: ℕ),
  ∀ (n: ℕ), (n₀ ≤ n → ‖(∑ i ≤ n, f i) - x‖ < ε)) := by
    unfold lim_serie Limit
    constructor
    · intro convf ε εpos
      have:= convf (Metric.ball x ε) (Metric.ball_mem_nhds x εpos)
      simp only [mem_ball_iff_norm] at this
      assumption
    · intro cond U Unhds
      rw [Metric.mem_nhds_iff] at Unhds
      rcases Unhds with ⟨ε, εpos, ballsubU⟩
      rcases cond ε εpos with ⟨n₀, eq⟩
      use n₀
      intro n n₀len
      apply ballsubU
      rw [mem_ball_iff_norm]
      exact eq n n₀len

/- Characterization of Cauchy condition for a series in a normed space -/

lemma Finset.sum_Iic_eq_sum_Ioc_add_Iic {f : ℕ → M} {n m : ℕ} (h : n ≤ m) :
  ∑ i ∈ Finset.Iic m, f i =
  ∑ i ∈ Finset.Ioc n m, f i + ∑ i ∈ Finset.Iic n, f i := by
    have inter: ∀ (m: ℕ), Finset.Iic m = Finset.Icc 0 m := by
      intro m
      exact rfl
    simp only [inter]
    induction' n with n ih
    · simp only [Finset.Icc_self, Finset.sum_singleton]
      rw [Finset.sum_Ioc_add_eq_sum_Icc h]
    · rw [Finset.sum_Icc_succ_top (Nat.le_add_left 0 (n + 1)),
          add_comm _ (f (n + 1)), ← add_assoc,
          Finset.sum_Ioc_add_eq_sum_Icc h]
      simp only [Nat.Icc_succ_left]
      exact ih (Nat.le_of_succ_le h)

lemma Finset.sum_Iic_sub_Iic_eq_sum_Ioc {f : ℕ → M} {n m : ℕ} (h : n ≤ m) :
    ∑ i ∈ Finset.Iic m, f i - ∑ i ∈ Finset.Iic n, f i =
    ∑ i ∈ Finset.Ioc n m, f i := by
    rw [sub_eq_iff_eq_add]
    exact Finset.sum_Iic_eq_sum_Ioc_add_Iic h

theorem cauchyserie_iff_vanishing_norm (f: ℕ → Y):
  CauchySerie f ↔ ∀ ε, 0 < ε → (∃ (n₀: ℕ),
  ∀ (n m: ℕ), (n₀ ≤ n → n ≤ m → ‖(∑ i ∈ Finset.Ioc n m, f i)‖ < ε)) := by
    unfold CauchySerie
    constructor
    · intro cauchyf ε εpos
      simp only [cauchy_metric_iff, dist_eq_norm] at cauchyf
      rcases cauchyf ε εpos with ⟨n₀, eq⟩
      use n₀
      intro n m n₀len nlem
      have := eq m n (le_trans n₀len nlem) n₀len
      rw [← Finset.sum_Iic_sub_Iic_eq_sum_Ioc nlem]
      assumption
    · intro cond
      rw [cauchy_metric_iff]
      intro ε εpos
      rcases cond ε εpos with ⟨n₀, eq⟩
      use n₀
      intro n m n₀len n₀lem
      rw [dist_eq_norm]
      by_cases h: n ≤ m
      · rw [norm_sub_rev, Finset.sum_Iic_sub_Iic_eq_sum_Ioc h]
        exact eq n m n₀len h
      · rw [not_le] at h
        have mlen: m ≤ n := by
          exact Nat.le_of_lt h
        rw [Finset.sum_Iic_sub_Iic_eq_sum_Ioc mlen]
        exact eq m n n₀lem mlen

/- ### Equivalence between Cauchy and convergence ### -/

theorem abssum_implies_sum [CompleteSpace Y] (f: I → Y):
  AbsSummable f → Summable f := by
    classical
    rw [cauchyabssum_iff_abssummable, summable_iff_summablenet,
        netsummable_iff_cauchNet_finset, cauchysum_iff_cauchySeqsum,
        cauchysum_iff_cauchySeqsum]
    sorry
    --intro cauchysum
    --unfold CauchySumNet at *
    --rw [cauchyserie_iff_vanishing_norm]
    --rw [cauchyserie_iff_vanishing_norm] at cauchysum
    --intro ε εpos
    --rcases cauchysum ε εpos with ⟨F₀, eq⟩
    --simp only [Real.norm_of_nonneg (Finset.sum_nonneg (fun i x ↦ norm_nonneg (f i)))] at eq
    --use F₀
    --intro F interem
    --calc
      --‖∑ i ∈ F, f i‖ ≤ ∑ i ∈ F, ‖f i‖ := by
        --exact norm_sum_le F f
      --_ < ε := by
        --exact eq F interem

theorem convserie_iff_cauchyserie [h: CompleteSpace Y] (f: ℕ → Y):
  conv_serie f ↔ CauchySerie f := by
    unfold conv_serie lim_serie
    constructor
    · intro convf
      exact cauchy_of_exists_lim convf
    · intro cauchyf
      apply complete_iff_seqcomplete.mp h
      unfold CauchySerie at cauchyf
      assumption

theorem convabsserie_iff_cauchyabsserie [CompleteSpace Y] (f: ℕ → Y):
  conv_abs_serie f ↔ CauchySerie (fun (n: ℕ) ↦ ‖f n‖) := by
    unfold conv_abs_serie lim_abs_serie lim_serie
    constructor
    · intro convabsf
      exact cauchy_of_exists_lim convabsf
    · intro cauchyabsf
      unfold CauchySerie at cauchyabsf
      apply complete_iff_seqcomplete.mp Real.instCompleteSpace
      assumption

/- ### Characterization of completeness in term of absolute convergence -/

theorem Real_conv_abs_serie_iff_summable (f: ℕ → ℝ) :
  conv_abs_serie f ↔ Summable f := by
    sorry

lemma conv_abs_serie_iff_conv_abs_serie_real (f: ℕ → Y) :
  conv_abs_serie f ↔ conv_abs_serie (fun (n : ℕ) => ‖f n‖) := by
    unfold conv_abs_serie lim_abs_serie lim_serie
    simp only [Real.norm_eq_abs, abs_norm]

theorem conv_abs_serie_iff_summable (f: ℕ → Y) :
  conv_abs_serie f ↔ Summable (fun (n : ℕ) => ‖f n‖) := by
    rw [conv_abs_serie_iff_conv_abs_serie_real, Real_conv_abs_serie_iff_summable]

theorem completespace_iff_conv_abs_imp_conv :
  CompleteSpace W ↔ ∀ (f: ℕ → W), conv_abs_serie f → conv_serie f := by
    simp only [conv_abs_serie_iff_summable, conv_serie_iff_exists_tendsto]
    exact Iff.symm NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace

theorem abs_conv_implies_summable {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  [CompleteSpace X] (f: ℕ → X): conv_abs_serie 𝕂 f → Summable f := by
    intro fconvabs
    apply abssum_implies_sum 𝕂
    rw [cauchyabssum_iff_abssummable, cauchysum_normed ℝ]
    rw [convabsserie_iff_cauchyabsserie, cauchy_serie_normed ℝ] at fconvabs
    intro ε εpos
    rcases fconvabs ε εpos with ⟨n₀, eq⟩
    use Finset.Icc 0 n₀
    intro F Fneint
    simp only [Real.norm_of_nonneg (Finset.sum_nonneg (fun i x ↦ norm_nonneg (f i)))] at *
    by_cases h: F.Nonempty
    · calc
        ∑ i ∈ F, ‖f i‖ ≤ ∑ i ∈ Finset.Ioc n₀ (Finset.max' F h), ‖f i‖ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n ninF
            rw [Finset.mem_Ioc]
            constructor
            · by_contra! nlen₀
              have: n ∈ Finset.Icc 0 n₀ ∩ F := by
                rw [Finset.mem_inter, Finset.mem_Icc]
                exact And.intro (And.intro (Nat.zero_le n) nlen₀) ninF
              rw [Fneint] at this
              contradiction
            · exact Finset.le_max' F n ninF
          · intro i _ _
            exact norm_nonneg (f i)
        _ < ε := by
          have: n₀ < F.max' h := by
            have: F.max' h ∉ Finset.Icc 0 n₀ := by
              by_contra h'
              have : F.max' h ∈ Finset.Icc 0 n₀ ∩ F := by
                exact Finset.mem_inter_of_mem h' (Finset.max'_mem F h)
              rw [Fneint] at this
              contradiction
            rw [Finset.mem_Icc] at this
            push_neg at this
            exact this (zero_le (F.max' h))
          exact eq n₀ (F.max' h) (le_refl n₀) (le_of_lt this)
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.sum_empty]
      exact εpos

/- Unconditional convergence -/

theorem BMCauchy_iff_ACauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : BMCauchy 𝕂 f ↔ ACauchy 𝕂 f := by
    sorry

theorem BMCauchy_of_SCauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : BMCauchy 𝕂 f → SCauchy 𝕂 f := by
    sorry

theorem CauchySum_of_SCauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : SCauchy 𝕂 f → CauchySumNet f := by
    sorry

theorem BMCauchy_of_CauchySum {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : CauchySumNet f → BMCauchy 𝕂 f := by
    sorry

theorem CauchySum_iff_RCauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : CauchySumNet f ↔ RCauchy 𝕂 f := by
    sorry

theorem BMCauchy_iff_SCauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : BMCauchy 𝕂 f ↔ SCauchy 𝕂 f := Iff.intro (BMCauchy_of_SCauchy 𝕂 f)
    (fun a ↦ BMCauchy_of_CauchySum 𝕂 f (CauchySum_of_SCauchy 𝕂 f a))

theorem BMCauchy_iff_CauchySum {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : BMCauchy 𝕂 f ↔ CauchySumNet f := Iff.intro
    (fun a ↦ CauchySum_of_SCauchy 𝕂 f (BMCauchy_of_SCauchy 𝕂 f a))
    (fun a ↦ BMCauchy_of_CauchySum 𝕂 f a)

theorem BMCauchy_iff_RCauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : BMCauchy 𝕂 f ↔ RCauchy 𝕂 f := by
    rw [← CauchySum_iff_RCauchy 𝕂]
    exact BMCauchy_iff_CauchySum 𝕂 f

theorem ACauchy_iff_SCauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : ACauchy 𝕂 f ↔ SCauchy 𝕂 f := by
    rw [← BMCauchy_iff_ACauchy 𝕂]
    exact BMCauchy_iff_SCauchy 𝕂 f

theorem ACauchy_iff_CauchySum {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : ACauchy 𝕂 f ↔ CauchySumNet f := by
    rw [← BMCauchy_iff_ACauchy 𝕂]
    exact BMCauchy_iff_CauchySum 𝕂 f

theorem ACauchy_iff_RCauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : ACauchy 𝕂 f ↔ RCauchy 𝕂 f := by
    rw [← BMCauchy_iff_ACauchy 𝕂]
    exact BMCauchy_iff_RCauchy 𝕂 f

theorem SCauchy_iff_CauchySum {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : SCauchy 𝕂 f ↔ CauchySumNet f := Iff.intro (CauchySum_of_SCauchy 𝕂 f)
    (fun a ↦ BMCauchy_of_SCauchy 𝕂 f (BMCauchy_of_CauchySum 𝕂 f a))

theorem SCauchy_iff_RCauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : SCauchy 𝕂 f ↔ RCauchy 𝕂 f := by
    rw [← CauchySum_iff_RCauchy 𝕂]
    exact SCauchy_iff_CauchySum 𝕂 f

theorem BMSerie_iff_BMCauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  [CompleteSpace X] (f: ℕ → X) : BMSerie 𝕂 f ↔ BMCauchy 𝕂 f := by
    unfold BMCauchy BMSerie
    simp only [convserie_iff_cauchyserie 𝕂]

theorem RSerie_iff_RCauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  [CompleteSpace X] (f: ℕ → X) : RSerie 𝕂 f ↔ RCauchy 𝕂 f := by
    unfold RCauchy RSerie
    simp only [convserie_iff_cauchyserie 𝕂]

theorem SSerie_iff_SCauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  [CompleteSpace X] (f: ℕ → X) : SSerie 𝕂 f ↔ SCauchy 𝕂 f := by
    unfold SCauchy SSerie
    simp only [convserie_iff_cauchyserie 𝕂]

theorem ASerie_iff_ACauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  [CompleteSpace X] (f: ℕ → X) : ASerie 𝕂 f ↔ ACauchy 𝕂 f := by
    unfold ACauchy ASerie
    simp only [convserie_iff_cauchyserie 𝕂]

theorem BMSerie_iff_SSerie {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  [CompleteSpace X] (f: ℕ → X) : BMSerie 𝕂 f ↔ SSerie 𝕂 f := by
    rw [BMSerie_iff_BMCauchy 𝕂, SSerie_iff_SCauchy 𝕂]
    exact BMCauchy_iff_SCauchy 𝕂 f

theorem BMSerie_iff_Summable {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  [CompleteSpace X] (f: ℕ → X) : BMSerie 𝕂 f ↔ Summable f := by
    rw [BMSerie_iff_BMCauchy 𝕂, summable_iff_summablenet, cauchysum_iff_summable 𝕂]
    exact BMCauchy_iff_CauchySum 𝕂 f
theorem BMSerie_iff_RSerie {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  [CompleteSpace X] (f: ℕ → X) : BMSerie 𝕂 f ↔ RSerie 𝕂 f := by
    rw [BMSerie_iff_BMCauchy 𝕂, RSerie_iff_RCauchy 𝕂]
    exact BMCauchy_iff_RCauchy 𝕂 f

theorem ASerie_iff_SSerie {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  [CompleteSpace X] (f: ℕ → X) : ASerie 𝕂 f ↔ SSerie 𝕂 f := by
    rw [ASerie_iff_ACauchy 𝕂, SSerie_iff_SCauchy 𝕂]
    exact ACauchy_iff_SCauchy 𝕂 f

theorem ASerie_iff_Summable {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  [CompleteSpace X] (f: ℕ → X) : ASerie 𝕂 f ↔ Summable f := by
    rw [ASerie_iff_ACauchy 𝕂, summable_iff_summablenet, cauchysum_iff_summable 𝕂]
    exact ACauchy_iff_CauchySum 𝕂 f

theorem ASerie_iff_RSerie {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  [CompleteSpace X] (f: ℕ → X) : ASerie 𝕂 f ↔ RSerie 𝕂 f := by
    rw [ASerie_iff_ACauchy 𝕂, RSerie_iff_RCauchy 𝕂]
    exact ACauchy_iff_RCauchy 𝕂 f

theorem SSerie_iff_Summable {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  [CompleteSpace X] (f: ℕ → X) : SSerie 𝕂 f ↔ Summable f := by
    rw [SSerie_iff_SCauchy 𝕂, summable_iff_summablenet, cauchysum_iff_summable 𝕂]
    exact SCauchy_iff_CauchySum 𝕂 f

theorem SSerie_iff_RSerie {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  [CompleteSpace X] (f: ℕ → X) : SSerie 𝕂 f ↔ RSerie 𝕂 f := by
    rw [SSerie_iff_SCauchy 𝕂, RSerie_iff_RCauchy 𝕂]
    exact SCauchy_iff_RCauchy 𝕂 f

theorem RSerie_iff_Summable {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  [CompleteSpace X] (f: ℕ → X) : RSerie 𝕂 f ↔ Summable f := by
    rw [RSerie_iff_RCauchy 𝕂, summable_iff_summablenet, cauchysum_iff_summable 𝕂]
    exact (CauchySum_iff_RCauchy 𝕂 f).symm
