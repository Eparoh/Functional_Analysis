import FunctionalAnalysis.Convergence.Summability
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.LocallyConvex.Bounded

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

lemma lim_serie_iff_lt (f: ℕ → X) (x: X):
  lim_serie f x ↔ Limit (fun (N: ℕ) ↦ ∑ n < N, f n) x := by
    unfold lim_serie
    have : ∀ (n: ℕ), Finset.Iio (n + 1) = Finset.Iic n := by
      intro n
      ext m
      rw [Finset.mem_Iio, Finset.mem_Iic]
      exact Nat.lt_add_one_iff
    simp only [← this, netlim_iff_shift_subsequence_lim
      (fun N ↦ ∑ n ∈ Finset.Iio N, f n) 1]

theorem lim_serie_iff_tendsto (f: ℕ → X) (x: X) :
  lim_serie f x ↔ Tendsto (fun (n : ℕ) ↦ ∑ i ∈ Finset.range n, f i)
  Filter.atTop (nhds x) := by
    rw [lim_serie_iff_lt, limit_iff_tendsto]
    have : ∀ (n: ℕ), Finset.Iio n = Finset.range n := by
      intro n
      ext m
      rw [Finset.mem_Iio, Finset.mem_range]
    simp only [this]

theorem conv_serie_iff_exists_tendsto (f: ℕ → X) :
  conv_serie f ↔ ∃ (x: X), Tendsto (fun (n : ℕ) ↦ ∑ i ∈ Finset.range n, f i)
   Filter.atTop (nhds x) := by
    unfold conv_serie
    simp only [lim_serie_iff_tendsto]

/- Characterization of convergence of a series in a normed space -/
theorem lim_serie_eps (f: ℕ → Y) (x: Y) :
  lim_serie f x ↔ ∀ ε >0, (∃ (n₀: ℕ), ∀ (n: ℕ),
    (n₀ ≤ n → ‖(∑ i ≤ n, f i) - x‖ < ε)) := by
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
  CauchySerie f ↔ ∀ ε >0, (∃ (n₀: ℕ), ∀ (n m: ℕ),
  (n₀ ≤ n → n ≤ m → ‖(∑ i ∈ Finset.Ioc n m, f i)‖ < ε)) := by
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

theorem conv_serie_iff_cauchyserie [h: CompleteSpace Y] (f: ℕ → Y):
  conv_serie f ↔ CauchySerie f := by
    unfold conv_serie lim_serie
    constructor
    · intro convf
      exact cauchy_of_exists_lim convf
    · intro cauchyf
      apply complete_iff_seqcomplete.mp h
      unfold CauchySerie at cauchyf
      assumption

theorem conv_abs_serie_iff_cauchyabsserie [CompleteSpace Y] (f: ℕ → Y):
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

theorem summable_of_conv_abs_serie [CompleteSpace Y] (f: ℕ → Y) :
  conv_abs_serie f → SummableNet f := by
    intro fconvabs
    apply summable_of_abssummable
    rw [cauchyabssum_iff_abssummable, cauchynet_finset_iff_vanishing_norm]
    rw [conv_abs_serie_iff_cauchyabsserie, cauchyserie_iff_vanishing_norm] at fconvabs
    intro ε εpos
    rcases fconvabs ε εpos with ⟨n₀, eq⟩
    use Finset.Icc 0 n₀
    intro F Fneint
    simp only [Real.norm_of_nonneg (Finset.sum_nonneg
      (fun i x ↦ norm_nonneg (f i)))] at *
    by_cases h: F.Nonempty
    · calc
        ∑ i ∈ F, ‖f i‖ ≤ ∑ i ∈ Finset.Ioc n₀ (Finset.max' F h), ‖f i‖ := by
          apply Finset.sum_le_sum_of_subset_of_nonneg
          · intro n ninF
            rw [Finset.mem_Ioc]
            constructor
            · by_contra! nlen₀
              rw [Finset.disjoint_left] at Fneint
              have := Fneint ninF
              have: n ∈ Finset.Icc 0 n₀ := by
                rw [Finset.mem_Icc]
                exact And.intro (Nat.zero_le n) nlen₀
              contradiction
            · exact Finset.le_max' F n ninF
          · intro i _ _
            exact norm_nonneg (f i)
        _ < ε := by
          have: n₀ < F.max' h := by
            have: F.max' h ∉ Finset.Icc 0 n₀ := by
              by_contra h'
              rw [Finset.disjoint_left] at Fneint
              have := Fneint (Finset.max'_mem F h)
              contradiction
            rw [Finset.mem_Icc] at this
            push_neg at this
            exact this (zero_le (F.max' h))
          exact eq n₀ (F.max' h) (le_refl n₀) (le_of_lt this)
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      rw [h, Finset.sum_empty]
      exact εpos

theorem Real_conv_abs_serie_iff_summable (f: ℕ → ℝ) :
  conv_abs_serie f ↔ SummableNet f := by
    constructor
    · exact summable_of_conv_abs_serie f
    · intro fsummable
      simp only [conv_abs_serie_iff_cauchyabsserie, Real.norm_eq_abs]
      have fcauchysum := cauchysum_of_summable fsummable
      rw [cauchyserie_iff_vanishing_norm]
      unfold CauchySumNet at fcauchysum
      rw [cauchy_metric_iff] at fcauchysum
      intro ε εpos
      rcases fcauchysum ε εpos with ⟨F₀, eq⟩
      simp only [Finset.le_eq_subset, dist_eq_norm, Real.norm_eq_abs] at eq
      simp only [Real.norm_eq_abs]
      have Ioceq : ∀ (n m : ℕ), Finset.Ioc n m = {k ∈ (Finset.Ioc n m) | f k ≥ 0} ∪
        {k ∈ (Finset.Ioc n m) | f k <0} := by
          intro n m
          ext k
          simp only [Finset.mem_union, Finset.mem_filter, Finset.mem_Ioc,
                     ← and_or_left]
          have : f k ≥ 0 ∨ f k < 0 ↔ True := by
            have := Classical.em (f k ≥ 0)
            push_neg at this
            rw [iff_true_right]
            · exact this
            · trivial
          simp only [this, and_true]
      have disj : ∀ (n m: ℕ), Disjoint {k ∈ (Finset.Ioc n m) | f k ≥ 0}
        {k ∈ (Finset.Ioc n m) | f k <0} := by
          intro n m
          rw [Finset.disjoint_left]
          simp only [Finset.mem_filter, Finset.mem_Ioc]
          intro k kin
          by_contra!
          linarith
      have pos : ∀ (n m: ℕ), ∑ i ∈ {k ∈ (Finset.Ioc n m) | f k ≥ 0}, |f i| =
        ∑ i ∈ {k ∈ (Finset.Ioc n m) | f k ≥ 0}, f i := by
          intro n m
          apply Finset.sum_congr rfl
          intro k kin
          rw [Finset.mem_filter, Finset.mem_Ioc] at kin
          rw [abs_of_nonneg kin.2]
      have neg : ∀ (n m: ℕ), ∑ i ∈ {k ∈ (Finset.Ioc n m) | f k < 0}, |f i| =
        ∑ i ∈ {k ∈ (Finset.Ioc n m) | f k < 0}, - (f i) := by
          intro n m
          apply Finset.sum_congr rfl
          intro k kin
          rw [Finset.mem_filter, Finset.mem_Ioc] at kin
          rw [abs_of_neg kin.2]
      by_cases h: F₀.Nonempty
      · use Finset.max' F₀ h
        intro n m F₀maxlen nlem
        let F : Finset ℕ := {k ∈ (Finset.Ioc n m) | f k ≥ 0} ∪ F₀
        let G : Finset ℕ := {k ∈ (Finset.Ioc n m) | f k < 0} ∪ F₀
        have : |∑ i ∈ F, f i - ∑ i ∈ G, f i| =
              @abs ℝ Real.lattice Real.instAddGroup
              (∑ i ∈ Finset.Ioc n m, |f i|) := by
            have h₁ : Disjoint {k ∈ (Finset.Ioc n m) | f k ≥ 0} F₀ := by
              rw [Finset.disjoint_left]
              intro k kin
              rw [Finset.mem_filter, Finset.mem_Ioc] at kin
              have : F₀.max' h < k := by
                exact lt_of_le_of_lt F₀maxlen kin.1.1
              by_contra kin
              linarith [Finset.le_max' F₀ k kin]
            have h₂ : Disjoint {k ∈ (Finset.Ioc n m) | f k < 0} F₀ := by
              rw [Finset.disjoint_left]
              intro k kin
              rw [Finset.mem_filter, Finset.mem_Ioc] at kin
              have : F₀.max' h < k := by
                exact lt_of_le_of_lt F₀maxlen kin.1.1
              by_contra kin
              linarith [Finset.le_max' F₀ k kin]
            simp only [Finset.sum_union h₁, Finset.sum_union h₂,
                       add_sub_add_right_eq_sub]
            nth_rw 3 [Ioceq]
            simp only [Finset.sum_union (disj n m), pos, neg, Finset.sum_neg_distrib]
            rfl
        rw [← this]
        exact eq F G (Finset.subset_union_right) (Finset.subset_union_right)
      · use 0
        intro n m F₀maxlen nlem
        let F : Finset ℕ := {k ∈ (Finset.Ioc n m) | f k ≥ 0}
        let G : Finset ℕ := {k ∈ (Finset.Ioc n m) | f k < 0}
        have : |∑ i ∈ F, f i - ∑ i ∈ G, f i| =
              @abs ℝ Real.lattice Real.instAddGroup
              (∑ i ∈ Finset.Ioc n m, |f i|) := by
            rw [Ioceq]
            simp only [Finset.sum_union (disj n m), pos, neg, Finset.sum_neg_distrib]
            rfl
        rw [← this]
        rw [Finset.not_nonempty_iff_eq_empty] at h
        simp only [h, Finset.empty_subset, forall_const] at eq
        exact eq F G

lemma conv_abs_serie_iff_conv_abs_serie_real (f: ℕ → Y) :
  conv_abs_serie f ↔ conv_abs_serie (fun (n : ℕ) => ‖f n‖) := by
    unfold conv_abs_serie lim_abs_serie lim_serie
    simp only [Real.norm_eq_abs, abs_norm]

theorem conv_abs_serie_iff_summable (f: ℕ → Y) :
  conv_abs_serie f ↔ SummableNet (fun (n : ℕ) => ‖f n‖) := by
    rw [conv_abs_serie_iff_conv_abs_serie_real, Real_conv_abs_serie_iff_summable]

theorem completespace_iff_conv_abs_imp_conv :
  CompleteSpace W ↔ ∀ (f: ℕ → W), conv_abs_serie f → conv_serie f := by
    simp only [conv_abs_serie_iff_summable, conv_serie_iff_exists_tendsto,
               ← summable_iff_summablenet]
    exact Iff.symm NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace

/- ### Unconditional convergence ### -/

variable [NormedSpace ℝ Y]

def RSerie (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℕ), Bijective g → conv_serie (f ∘ g)

def SSerie (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℕ), StrictMono g → conv_serie (f ∘ g)

def BMSerie (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℝ), Bornology.IsBounded (range g) →
    conv_serie (fun (n: ℕ) ↦ (g n) • (f n))

def ASerie (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℝ), range g ⊆ {1, -1} → conv_serie (fun (n: ℕ) ↦ (g n) • (f n))

def RCauchy (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℕ), Bijective g → CauchySerie (f ∘ g)

def SCauchy (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℕ), StrictMono g → CauchySerie (f ∘ g)

def BMCauchy (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℝ), Bornology.IsBounded (range g) →
    CauchySerie (fun (n: ℕ) ↦ (g n) • (f n))

def ACauchy (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℝ), range g ⊆ {1, -1} → CauchySerie (fun (n: ℕ) ↦ (g n) • (f n))

/- Equivalences -/

theorem BMCauchy_iff_ACauchy (f: ℕ → Y) :
  BMCauchy f ↔ ACauchy f := by
    unfold BMCauchy ACauchy
    constructor
    · intro BMcauchy g rgsub
      have : Bornology.IsBounded (range g) := by
        exact Bornology.IsBounded.subset
          (Set.Finite.isBounded (toFinite {1, -1})) rgsub
      exact BMcauchy g this
    · intro ACauchy g gbdd
      rw [NormedSpace.isBounded_iff_subset_smul_closedBall ℝ] at gbdd
      rcases gbdd with ⟨K, gsubK⟩
      have: ∀ (n: ℕ), |g n| ≤ K := by
        sorry
      have : CauchySerie (fun (n: ℕ) ↦ K • ‖f n‖) := by
        sorry
      rw [cauchyserie_iff_vanishing_norm] at *
      intro ε εpos
      rcases this ε εpos with ⟨n₀, eq⟩
      use n₀
      intro n m n₀len nlem
      calc
        ‖∑ i ∈ Finset.Ioc n m, g i • f i‖ ≤ ∑ i ∈ Finset.Ioc n m, ‖g i • f i‖ := by
          exact norm_sum_le (Finset.Ioc n m) fun i ↦ g i • f i
        _ = ∑ i ∈ Finset.Ioc n m, |g i| * ‖f i‖ := by
          apply Finset.sum_congr rfl
          intro k kin
          rw [norm_smul, Real.norm_eq_abs]
        _ ≤ ∑ i ∈ Finset.Ioc n m, K * ‖f i‖ := by
          apply Finset.sum_le_sum
          intro i iin
          sorry
      sorry


theorem BMCauchy_of_SCauchy (f: ℕ → Y) :
  BMCauchy f → SCauchy f := by
    sorry

theorem CauchySum_of_SCauchy  (f: ℕ → Y) :
  SCauchy f → CauchySumNet f := by
    sorry

theorem BMCauchy_of_CauchySum (f: ℕ → Y) :
  CauchySumNet f → BMCauchy f := by
    sorry

theorem CauchySum_iff_RCauchy (f: ℕ → Y) :
  CauchySumNet f ↔ RCauchy f := by
    sorry

theorem BMCauchy_iff_SCauchy (f: ℕ → Y) :
  BMCauchy f ↔ SCauchy f := Iff.intro (BMCauchy_of_SCauchy f)
    (fun a ↦ BMCauchy_of_CauchySum f (CauchySum_of_SCauchy f a))

theorem BMCauchy_iff_CauchySum (f: ℕ → Y) :
  BMCauchy f ↔ CauchySumNet f := Iff.intro
    (fun a ↦ CauchySum_of_SCauchy f (BMCauchy_of_SCauchy f a))
    (fun a ↦ BMCauchy_of_CauchySum f a)

theorem BMCauchy_iff_RCauchy (f: ℕ → Y) :
  BMCauchy f ↔ RCauchy f := by
    rw [← CauchySum_iff_RCauchy]
    exact BMCauchy_iff_CauchySum f

theorem ACauchy_iff_SCauchy (f: ℕ → Y) :
  ACauchy f ↔ SCauchy f := by
    rw [← BMCauchy_iff_ACauchy]
    exact BMCauchy_iff_SCauchy f

theorem ACauchy_iff_CauchySum (f: ℕ → Y) :
  ACauchy f ↔ CauchySumNet f := by
    rw [← BMCauchy_iff_ACauchy]
    exact BMCauchy_iff_CauchySum f

theorem ACauchy_iff_RCauchy (f: ℕ → Y) :
  ACauchy f ↔ RCauchy f := by
    rw [← BMCauchy_iff_ACauchy]
    exact BMCauchy_iff_RCauchy f

theorem SCauchy_iff_CauchySum (f: ℕ → Y) :
  SCauchy f ↔ CauchySumNet f := Iff.intro (CauchySum_of_SCauchy f)
    (fun a ↦ BMCauchy_of_SCauchy f (BMCauchy_of_CauchySum f a))

theorem SCauchy_iff_RCauchy (f: ℕ → Y) :
  SCauchy f ↔ RCauchy f := by
    rw [← CauchySum_iff_RCauchy]
    exact SCauchy_iff_CauchySum f

theorem BMSerie_iff_BMCauchy [CompleteSpace Y] (f: ℕ → Y) :
  BMSerie f ↔ BMCauchy f := by
    unfold BMCauchy BMSerie
    simp only [conv_serie_iff_cauchyserie]

theorem RSerie_iff_RCauchy [CompleteSpace Y] (f: ℕ → Y) :
  RSerie f ↔ RCauchy f := by
    unfold RCauchy RSerie
    simp only [conv_serie_iff_cauchyserie]

theorem SSerie_iff_SCauchy [CompleteSpace Y] (f: ℕ → Y) :
  SSerie f ↔ SCauchy f := by
    unfold SCauchy SSerie
    simp only [conv_serie_iff_cauchyserie]

theorem ASerie_iff_ACauchy [CompleteSpace Y] (f: ℕ → Y) :
  ASerie f ↔ ACauchy f := by
    unfold ACauchy ASerie
    simp only [conv_serie_iff_cauchyserie]

theorem BMSerie_iff_SSerie [CompleteSpace Y] (f: ℕ → Y) :
  BMSerie f ↔ SSerie f := by
    rw [BMSerie_iff_BMCauchy, SSerie_iff_SCauchy]
    exact BMCauchy_iff_SCauchy f

theorem BMSerie_iff_Summable [CompleteSpace Y] (f: ℕ → Y) :
  BMSerie f ↔ SummableNet f := by
    rw [BMSerie_iff_BMCauchy, netsummable_iff_cauchNet_finset]
    exact BMCauchy_iff_CauchySum f

theorem BMSerie_iff_RSerie [CompleteSpace Y] (f: ℕ → Y) :
  BMSerie f ↔ RSerie f := by
    rw [BMSerie_iff_BMCauchy, RSerie_iff_RCauchy]
    exact BMCauchy_iff_RCauchy f

theorem ASerie_iff_SSerie [CompleteSpace Y] (f: ℕ → Y) :
  ASerie f ↔ SSerie f := by
    rw [ASerie_iff_ACauchy, SSerie_iff_SCauchy]
    exact ACauchy_iff_SCauchy f

theorem ASerie_iff_Summable [CompleteSpace Y] (f: ℕ → Y) :
  ASerie f ↔ SummableNet f := by
    rw [ASerie_iff_ACauchy, netsummable_iff_cauchNet_finset]
    exact ACauchy_iff_CauchySum f

theorem ASerie_iff_RSerie [CompleteSpace Y] (f: ℕ → Y) :
  ASerie f ↔ RSerie f := by
    rw [ASerie_iff_ACauchy, RSerie_iff_RCauchy]
    exact ACauchy_iff_RCauchy f

theorem SSerie_iff_Summable [CompleteSpace Y] (f: ℕ → Y) :
  SSerie f ↔ SummableNet f := by
    rw [SSerie_iff_SCauchy, netsummable_iff_cauchNet_finset]
    exact SCauchy_iff_CauchySum f

theorem SSerie_iff_RSerie [CompleteSpace Y] (f: ℕ → Y) :
  SSerie f ↔ RSerie f := by
    rw [SSerie_iff_SCauchy, RSerie_iff_RCauchy]
    exact SCauchy_iff_RCauchy f

theorem RSerie_iff_Summable [CompleteSpace Y] (f: ℕ → Y) :
  RSerie f ↔ SummableNet f := by
    rw [RSerie_iff_RCauchy, netsummable_iff_cauchNet_finset]
    exact (CauchySum_iff_RCauchy f).symm
