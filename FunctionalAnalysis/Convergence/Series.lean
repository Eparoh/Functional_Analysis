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

/- ### Absolute convergence equivalence with convergence in ℝ ### -/

lemma conv_abs_serie_iff_conv_serie_real (f: ℕ → Y) :
  conv_abs_serie f ↔ conv_serie (fun (n : ℕ) => ‖f n‖) := by
    unfold conv_abs_serie lim_abs_serie conv_serie lim_serie
    simp only [Real.norm_eq_abs, abs_norm]

lemma conv_abs_serie_iff_conv_abs_serie_real (f: ℕ → Y) :
  conv_abs_serie f ↔ conv_abs_serie (fun (n : ℕ) => ‖f n‖) := by
    unfold conv_abs_serie lim_abs_serie lim_serie
    simp only [Real.norm_eq_abs, abs_norm]

/- ### Operations on series ### -/

theorem serie_neg {X: Type*} [SubtractionCommMonoid X] [TopologicalSpace X]
  [ContinuousNeg X] {f: ℕ → X} {x: X} :
  lim_serie f x → lim_serie (fun (i : ℕ) => - (f i)) (-x) := by
    unfold lim_serie
    have : (fun N ↦ ∑ n ∈ Finset.Iic N, -f n) =
      (fun N ↦ - ∑ n ∈ Finset.Iic N, f n) := by
        ext N
        exact Finset.sum_neg_distrib
    rw [this]
    exact lim_of_neg_eq_neg_of_lim

theorem conv_neg  {X: Type*} [SubtractionCommMonoid X] [TopologicalSpace X]
  [ContinuousNeg X] {f: ℕ → X} :
  conv_serie f → conv_serie (fun (i : ℕ) => - (f i)) := by
    unfold conv_serie
    intro limf
    rcases limf with ⟨x, flimx⟩
    use -x
    exact serie_neg flimx

theorem serie_sum [ContinuousAdd X] {f : J → ℕ → X} {a : J → X} {s : Finset J} :
  (∀ j ∈ s, lim_serie (f j) (a j)) →
  lim_serie (fun (i : ℕ) => ∑ j ∈ s, f j i) (∑ j ∈ s, a j) := by
    unfold lim_serie
    have : (fun (d: ℕ) ↦ ∑ j ∈ s, ∑ n ∈ Finset.Iic d, f j n) =
      (fun N ↦ ∑ n ∈ Finset.Iic N, ∑ j ∈ s, f j n) := by
        ext N
        exact Finset.sum_comm
    rw [← this]
    exact lim_of_sums_eq_sums_of_lim

theorem conv_sum [ContinuousAdd X] {f : J → ℕ → X} {s : Finset J} :
  (∀ j ∈ s, conv_serie (f j)) →
  conv_serie (fun (i : ℕ) => ∑ j ∈ s, f j i) := by
    classical
    unfold conv_serie
    intro convs
    have : ∃ (a: J → X), (∀ j ∈ s, lim_serie (f j) (a j)) := by
      let a : J → X := fun j ↦ if h: ∃ x, lim_serie (f j) x
        then Classical.choose h else 0
      use a
      intro j jins
      unfold a
      rw [dif_pos (convs j jins)]
      exact Classical.choose_spec (convs j jins)
    rcases this with ⟨a, eq⟩
    use ∑ j ∈ s, a j
    exact serie_sum eq

theorem serie_add [ContinuousAdd X] {f g: ℕ → X} {x y: X} :
  lim_serie f x → lim_serie g y → lim_serie (fun (i : ℕ) => f i + g i) (x + y) := by
    unfold lim_serie
    have : (fun N ↦ ∑ n ∈ Finset.Iic N, (f n + g n)) =
      (fun N ↦ (∑ n ∈ Finset.Iic N, f n) + (∑ n ∈ Finset.Iic N, g n)) := by
        ext N
        exact Finset.sum_add_distrib
    rw [this]
    exact lim_of_sum_eq_sum_of_lim

theorem conv_add [ContinuousAdd X] {f g: ℕ → X} :
  conv_serie f → conv_serie g → conv_serie (fun (i : ℕ) => f i + g i) := by
    unfold conv_serie
    intro limf limg
    rcases limf with ⟨x, flimx⟩
    rcases limg with ⟨y, glimy⟩
    use x + y
    exact serie_add flimx glimy

theorem serie_const_smul {R: Type*} [TopologicalSpace R] [DistribSMul R X]
  [h: ContinuousSMul R X] {f: ℕ → X} {x: X} (r: R) :
    lim_serie f x → lim_serie (fun (i: ℕ) ↦ r • (f i)) (r • x) := by
      classical
      unfold lim_serie
      have : (fun N ↦ ∑ n ∈ Finset.Iic N, (r • f n)) =
        (fun N ↦ r • ∑ n ∈ Finset.Iic N, f n) := by
          ext N
          exact Eq.symm Finset.smul_sum
      rw [this]
      exact prod_num_conv r

theorem conv_const_smul {R: Type*} [TopologicalSpace R] [DistribSMul R X]
  [h: ContinuousSMul R X] {f: ℕ → X} (r: R) :
    conv_serie f → conv_serie (fun (i: ℕ) ↦ r • (f i)) := by
      intro convf
      rcases convf with ⟨x, eq⟩
      use r • x
      exact serie_const_smul r eq

theorem cauchyserie_neg {f: ℕ → Y} :
  CauchySerie f → CauchySerie (fun (n: ℕ) ↦ - (f n)) := by
    unfold CauchySerie
    have : (fun N ↦ ∑ n ∈ Finset.Iic N, -f n) =
      (fun N ↦ - ∑ n ∈ Finset.Iic N, f n) := by
        ext N
        exact Finset.sum_neg_distrib
    rw [this]
    exact cauchynet_neg

theorem cauchyserie_add {f g: ℕ → Y} :
  CauchySerie f → CauchySerie g → CauchySerie (fun (n: ℕ) ↦ (f n) + (g n)) := by
    unfold CauchySerie
    have : (fun N ↦ ∑ n ∈ Finset.Iic N, (f n + g n)) =
      (fun N ↦ ∑ n ∈ Finset.Iic N, f n + ∑ n ∈ Finset.Iic N, g n) := by
        ext N
        exact Finset.sum_add_distrib
    rw [this]
    exact cauchynet_add

theorem cauchyserie_const_smul (𝕜: Type*) [NontriviallyNormedField 𝕜]
  [NormedSpace 𝕜 Y] {f: ℕ → Y} {a: 𝕜} :
  CauchySerie f → CauchySerie (fun (n: ℕ) ↦ a • (f n)) := by
    unfold CauchySerie
    have : (fun N ↦ ∑ n ∈ Finset.Iic N, (a • f n)) =
      (fun N ↦ a • ∑ n ∈ Finset.Iic N, f n) := by
        ext N
        exact Eq.symm Finset.smul_sum
    rw [this]
    exact @cauchynet_const_smul ℕ _ Y _ 𝕜 _ _ (fun N ↦ ∑ n ∈ Finset.Iic N, f n) a

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

theorem conv_serie_of_summable {f: ℕ → Y} :
  SummableNet f → conv_serie f := by
    intro fsumm
    rcases fsumm with ⟨x, hassumf⟩
    rw [hassumnet_eps] at hassumf
    use x
    rw [lim_serie_eps]
    intro ε εpos
    rcases hassumf ε εpos with ⟨F₀, eq⟩
    by_cases h: F₀.Nonempty
    · use F₀.max' h
      intro n len
      have : F₀ ⊆ Finset.Iic n := by
        intro m minF₀
        rw [Finset.mem_Iic]
        exact le_trans (Finset.le_max' F₀ m minF₀) len
      exact eq (Finset.Iic n) this
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      simp only [h, Finset.empty_subset, forall_const] at eq
      use 0
      intro n zlen
      exact eq (Finset.Iic n)

theorem summable_of_conv_abs_serie [CompleteSpace Y] {f: ℕ → Y} :
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

theorem conv_serie_of_conv_abs_serie [CompleteSpace Y] (f: ℕ → Y) :
  conv_abs_serie f → conv_serie f := by
    intro fabsconv
    exact conv_serie_of_summable (summable_of_conv_abs_serie fabsconv)

theorem Real_conv_abs_serie_iff_summable (f: ℕ → ℝ) :
  conv_abs_serie f ↔ SummableNet f := by
    constructor
    · exact summable_of_conv_abs_serie
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

lemma conv_abs_serie_iff_summable_abs (f: ℕ → Y) :
  conv_abs_serie f ↔ SummableNet (fun (n : ℕ) => ‖f n‖) := by
    rw [conv_abs_serie_iff_conv_abs_serie_real, Real_conv_abs_serie_iff_summable]

theorem conv_abs_serie_iff_summable [NormedSpace ℝ W] [FiniteDimensional ℝ W]
  (f: ℕ → W) : conv_abs_serie f ↔ SummableNet f := by
    rw [summablenet_iff_abssummable, abssummable_iff_summable_abs,
        conv_abs_serie_iff_conv_abs_serie_real, conv_abs_serie_iff_summable_abs,
        summable_iff_summablenet]
    simp only [norm_norm]

theorem completespace_iff_conv_abs_imp_conv :
  CompleteSpace W ↔ ∀ (f: ℕ → W), conv_abs_serie f → conv_serie f := by
    simp only [conv_abs_serie_iff_summable_abs, conv_serie_iff_exists_tendsto,
               ← summable_iff_summablenet]
    exact Iff.symm NormedAddCommGroup.summable_imp_tendsto_iff_completeSpace

/- ### Comparation criterion ### -/

theorem conv_serie_of_norm_bounded [CompleteSpace Y]
  {f : ℕ → Y} (g : ℕ → ℝ) (hg : conv_serie g) (h : ∀ (n : ℕ), ‖f n‖ ≤ g n) :
  conv_serie f := by
    apply conv_serie_of_conv_abs_serie
    rw [conv_abs_serie_iff_summable_abs]
    have gabsconv : conv_abs_serie g := by
      simp only [conv_abs_serie_iff_conv_serie_real, Real.norm_eq_abs,
                 fun (n: ℕ) ↦ abs_of_nonneg
                 (le_trans (norm_nonneg (f n)) (h n))]
      exact hg
    rw [conv_abs_serie_iff_summable] at gabsconv
    have : ∀ (n : ℕ), ‖‖f n‖‖ ≤ g n := by
      intro n
      rw [norm_norm]
      exact h n
    exact summablenet_of_norm_bounded g gabsconv this

theorem conv_abs_serie_of_norm_bounded
  {f : ℕ → Y} (g : ℕ → ℝ) (hg : conv_serie g) (h : ∀ (n : ℕ), ‖f n‖ ≤ g n) :
  conv_abs_serie f := by
    rw [conv_abs_serie_iff_summable_abs]
    have gabsconv : conv_abs_serie g := by
      simp only [conv_abs_serie_iff_conv_serie_real, Real.norm_eq_abs,
                 fun (n: ℕ) ↦ abs_of_nonneg
                 (le_trans (norm_nonneg (f n)) (h n))]
      exact hg
    rw [conv_abs_serie_iff_summable] at gabsconv
    have : ∀ (n : ℕ), ‖‖f n‖‖ ≤ g n := by
      intro n
      rw [norm_norm]
      exact h n
    exact summablenet_of_norm_bounded g gabsconv this

/- ### Operations on absolute convergent series ### -/

theorem absconv_sum {f : J → ℕ → Y} {s : Finset J} :
  (∀ j ∈ s, conv_abs_serie (f j)) →
  conv_abs_serie (fun (i : ℕ) => ∑ j ∈ s, f j i) := by
    intro absconv
    apply conv_abs_serie_of_norm_bounded _ (conv_sum absconv)
    intro n
    exact norm_sum_le s (fun j ↦ f j n)

theorem absconv_add {f g: ℕ → Y} :
  conv_abs_serie f → conv_abs_serie g →
  conv_abs_serie (fun (i : ℕ) => f i + g i) := by
    intro absconvf absconvg
    apply conv_abs_serie_of_norm_bounded _ (conv_add absconvf absconvg)
    intro n
    exact norm_add_le (f n) (g n)

theorem absserie_const_smul (𝕜: Type*) [NontriviallyNormedField 𝕜]
  [NormedSpace 𝕜 Y] {f: ℕ → Y} {t: ℝ} (r: 𝕜) :
  lim_abs_serie f t → lim_abs_serie (fun (i: ℕ) ↦ r • (f i)) (‖r‖ * t) := by
    unfold lim_abs_serie
    intro limabsf
    simp only [norm_smul, ← smul_eq_mul]
    exact serie_const_smul ‖r‖ limabsf

theorem absconv_const_smul (𝕜: Type*) [NontriviallyNormedField 𝕜]
  [NormedSpace 𝕜 Y] {f: ℕ → Y} (r: 𝕜) :
    conv_abs_serie f → conv_abs_serie (fun (i: ℕ) ↦ r • (f i)) := by
      intro convabsf
      rcases convabsf with ⟨t, eq⟩
      use ‖r‖ * t
      exact absserie_const_smul 𝕜 r eq

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

theorem NormedSpace.isBounded_iff_bounded_norm (𝕜 : Type*) {E : Type*}
  [NontriviallyNormedField 𝕜] [SeminormedAddCommGroup E]
  [NormedSpace 𝕜 E] {s : Set E} :
    Bornology.IsBounded s ↔ ∃ (k : 𝕜), k ≠ 0 ∧ ∀ e ∈ s, ‖e‖ ≤ ‖k‖ := by
      rw [NormedSpace.isBounded_iff_subset_smul_closedBall 𝕜]
      constructor
      · intro h
        rcases h with ⟨k, ssub⟩
        by_cases kz : k = 0
        · use k + 1
          constructor
          · rw [kz, zero_add]
            exact one_ne_zero
          · intro e eins
            rw [kz, zero_add, norm_one]
            have := ssub eins
            rw [Set.mem_smul_set] at this
            rcases this with ⟨x, xinball, eeq⟩
            rw [← eeq, norm_smul, kz, norm_zero, zero_mul]
            exact zero_le_one' ℝ
        · use k
          constructor
          · exact kz
          · intro e eins
            have := ssub eins
            rw [Set.mem_smul_set] at this
            rcases this with ⟨x, xinball, eeq⟩
            rw [← eeq, norm_smul]
            rw [mul_le_iff_le_one_right]
            · exact mem_closedBall_zero_iff.mp xinball
            · exact norm_pos_iff.mpr kz
      · intro h
        rcases h with ⟨k, eq⟩
        use k
        intro e eins
        rw [Set.mem_smul_set]
        use k⁻¹ • e
        constructor
        · rw [mem_closedBall_zero_iff, norm_smul, norm_inv]
          apply inv_mul_le_one_of_le₀ (eq.2 e eins) (norm_nonneg k)
        · rw [← smul_assoc, smul_eq_mul, mul_inv_cancel₀ eq.1, one_smul]

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
      rw [NormedSpace.isBounded_iff_bounded_norm ℝ] at gbdd
      rcases gbdd with ⟨K, Knez, gsubK⟩
      have gleK: ∀ (n: ℕ), |g n| ≤ |K| := by
        intro n
        have : g n ∈ range g := by
          use n
        rw [← Real.norm_eq_abs, ← Real.norm_eq_abs]
        exact gsubK (g n) this
      have : CauchySerie (fun (n: ℕ) ↦ |K| • ‖f n‖) := by
        apply cauchyserie_const_smul
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
        _ ≤ ∑ i ∈ Finset.Ioc n m, |K| * ‖f i‖ := by
          apply Finset.sum_le_sum
          intro i iin
          apply mul_le_mul_of_nonneg_right (gleK i) (norm_nonneg (f i))
        _ = ∑ i ∈ Finset.Ioc n m, |K| • ‖f i‖ := by
          rfl
        _ = ‖∑ i ∈ Finset.Ioc n m, |K| • ‖f i‖‖ := by
          rw [Real.norm_eq_abs]
          rw [Finset.abs_sum_of_nonneg']
          intro i
          rw [← Real.norm_eq_abs, smul_eq_mul, ← norm_smul]
          exact norm_nonneg (K • (f i))
        _ < ε := by
          exact eq n m n₀len nlem

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
