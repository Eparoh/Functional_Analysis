import FunctionalAnalysis.Convergence.Summability
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.Normed.Group.Completeness
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.LocallyConvex.Bounded
import Mathlib.Analysis.NormedSpace.HahnBanach.Extension
import CajonSastre.Finset

set_option trace.Meta.Tactic.simp false

noncomputable section

open Set Filter Topology Function DirectedSet Net

variable {X: Type*} [AddCommMonoid X] [TopologicalSpace X]
variable {Y: Type*} [SeminormedAddCommGroup Y]
variable {Z: Type*} [AddCommMonoid Z] [UniformSpace Z]
variable {W: Type*} [NormedAddCommGroup W]
variable {M: Type*} [AddCommGroup M]
variable {N: Type*} [AddCommGroup N] [TopologicalSpace N] [TopologicalAddGroup N]

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
  [NormedSpace 𝕜 Y] {f: ℕ → Y} (a: 𝕜) :
  CauchySerie f → CauchySerie (fun (n: ℕ) ↦ a • (f n)) := by
    unfold CauchySerie
    have : (fun N ↦ ∑ n ∈ Finset.Iic N, (a • f n)) =
      (fun N ↦ a • ∑ n ∈ Finset.Iic N, f n) := by
        ext N
        exact Eq.symm Finset.smul_sum
    rw [this]
    exact @cauchynet_const_smul ℕ _ Y _ 𝕜 _ _ (fun N ↦ ∑ n ∈ Finset.Iic N, f n) a

theorem cauchyserie_iff_cauchyserie_const_smul (𝕜: Type*) [NontriviallyNormedField 𝕜]
  [NormedSpace 𝕜 Y] {f: ℕ → Y} (a: 𝕜) (anezero: a ≠ 0) :
  CauchySerie f ↔ CauchySerie (fun (n: ℕ) ↦ a • (f n)) := by
    unfold CauchySerie
    have : (fun N ↦ ∑ n ∈ Finset.Iic N, (a • f n)) =
      (fun N ↦ a • ∑ n ∈ Finset.Iic N, f n) := by
        ext N
        exact Eq.symm Finset.smul_sum
    rw [this]
    exact @cauchynet_iff_cauchynet_const_smul ℕ _ Y _ 𝕜 _ _ (fun N ↦ ∑ n ∈ Finset.Iic N, f n) a anezero

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

/- A convergent series is a CauchySerie -/

theorem CauchySerie_of_conv_serie (f: ℕ → Y) :
  conv_serie f → CauchySerie f := by
    unfold conv_serie lim_serie CauchySerie
    exact cauchy_of_exists_lim

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

theorem cauchyserie_iff_vanishing_norm (f: ℕ → Y) :
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

theorem cauchyserie_iff_vanishing_norm' (f: ℕ → Y) :
  CauchySerie f ↔ ∀ ε >0, (∃ (n₀: ℕ), ∀ (n m: ℕ),
  (n₀ < n → n < m → ‖(∑ i ∈ Finset.Ioc n m, f i)‖ < ε)) := by
    rw [cauchyserie_iff_vanishing_norm]
    constructor
    · intro cond ε εpos
      rcases cond ε εpos with ⟨n₀, eq⟩
      use n₀
      intro n m n₀ltn nltm
      exact eq n m (le_of_lt n₀ltn) (le_of_lt nltm)
    · intro cond ε εpos
      rcases cond ε εpos with ⟨n₀, eq⟩
      use (n₀ + 1)
      intro n m n₀ltn nlem
      by_cases h: n = m
      · simp only [h, le_refl, Finset.Ioc_eq_empty_of_le,
                   Finset.sum_empty, norm_zero, εpos]
      · exact eq n m n₀ltn (Nat.lt_of_le_of_ne nlem h)

theorem cauchyserie_iff_vanishing_norm'' (f: ℕ → Y) :
  CauchySerie f ↔ ∀ ε >0, (∃ (n₀: ℕ), ∀ (n m: ℕ),
  (n₀ ≤ n → n < m → ‖(∑ i ∈ Finset.Ioc n m, f i)‖ < ε)) := by
    rw [cauchyserie_iff_vanishing_norm']
    constructor
    · intro cond ε εpos
      rcases cond ε εpos with ⟨n₀, eq⟩
      use n₀ + 1
      intro n m n₀ltn nltm
      exact eq n m (lt_of_lt_of_le (lt_add_one n₀) n₀ltn) nltm
    · intro cond ε εpos
      rcases cond ε εpos with ⟨n₀, eq⟩
      use n₀
      intro n m n₀ltn nlem
      exact eq n m (le_of_lt n₀ltn) nlem

theorem cauchyserie_iff_vanishing_norm''' (f: ℕ → Y) :
  CauchySerie f ↔ ∀ ε >0, (∃ (n₀: ℕ), ∀ (n m: ℕ),
  (n₀ ≤ n → n ≤ m → ‖(∑ i ∈ Finset.Ico n m, f i)‖ < ε)) := by
    rw [cauchyserie_iff_vanishing_norm]
    constructor
    · intro cond ε εpos
      rcases cond ε εpos with ⟨n₀, eq⟩
      use n₀ + 1
      intro n m n₀p1len nlem
      have := eq (n -1) (m - 1)
        (Nat.le_sub_one_of_lt n₀p1len)
        (Nat.sub_le_sub_right nlem 1)
      rw [Finset.Ioc_eq_Ico] at this
      · assumption
      · exact Nat.zero_lt_of_lt n₀p1len
      · exact Nat.zero_lt_of_lt (Nat.le_trans n₀p1len nlem)
    · intro cond ε εpos
      rcases cond ε εpos with ⟨n₀, eq⟩
      use n₀
      intro n m n₀len mlen
      have := eq (n + 1) (m + 1)
        (Nat.le_add_right_of_le n₀len)
        (Nat.add_le_add_right mlen 1)
      rw [Finset.Ico_eq_Ioc] at this
      assumption

def not_cauchyserie_imp_aux (p: ℕ → ℕ → Prop) : ℕ → ℕ × ℕ := fun k ↦ by
  classical
  exact match k with
  | 0 => if h: ∃ (n: ℕ × ℕ), n.1 < n.2 ∧ p n.1 n.2 then
    Classical.choose h else 0
  | k + 1 => if h: ∃ (n: ℕ × ℕ), n.1 < n.2 ∧
    (not_cauchyserie_imp_aux p k).2 < n.1 ∧ p n.1 n.2 then
    Classical.choose h else 0

lemma not_cauchyserie_imp_aux_def (p: ℕ → ℕ → Prop) (h: ∀ (k : ℕ), ∃ (N: ℕ × ℕ),
  k < N.1 ∧ N.1 < N.2 ∧ p N.1 N.2) : ∀ (n: ℕ), ((not_cauchyserie_imp_aux p n).1 <
  (not_cauchyserie_imp_aux p n).2 ∧ (not_cauchyserie_imp_aux p n).2 <
  (not_cauchyserie_imp_aux p (n + 1)).1 ∧
  p (not_cauchyserie_imp_aux p n).1 (not_cauchyserie_imp_aux p n).2):= by
    intro n
    induction' n with n ih
    · dsimp only [not_cauchyserie_imp_aux]
      have cond1 : ∃ (n: ℕ × ℕ), n.1 < n.2 ∧ p n.1 n.2 := by
        rcases h 0 with ⟨N, eq⟩
        use N
        exact eq.2
      rw [dif_pos cond1]
      have cond2 : ∃ (n: ℕ × ℕ), n.1 < n.2 ∧ (Classical.choose cond1).2 < n.1 ∧
        p n.1 n.2 := by
        rcases h ((Classical.choose cond1).2) with ⟨N, eq⟩
        use N
        exact And.intro (eq.2.1) (And.intro eq.1 eq.2.2)
      rw [dif_pos cond2]
      exact And.intro (Classical.choose_spec cond1).1 (And.intro
        (Classical.choose_spec cond2).2.1 (Classical.choose_spec cond1).2)
    · dsimp only [not_cauchyserie_imp_aux]
      have cond1 : ∃ (N: ℕ × ℕ), N.1 < N.2 ∧ (not_cauchyserie_imp_aux p n).2 < N.1 ∧
         p N.1 N.2 := by
        rcases h ((not_cauchyserie_imp_aux p n).2) with ⟨N, eq⟩
        use N
        exact And.intro eq.2.1 (And.intro eq.1 eq.2.2)
      rw [dif_pos cond1]
      have cond2 : ∃ (N: ℕ × ℕ), N.1 < N.2 ∧
        (Classical.choose cond1).2 < N.1 ∧ p N.1 N.2 := by
          rcases h ((Classical.choose cond1).2) with ⟨N, eq⟩
          use N
          exact And.intro eq.2.1 (And.intro eq.1 eq.2.2)
      rw [dif_pos cond2]
      exact And.intro (Classical.choose_spec cond1).1 (And.intro
        (Classical.choose_spec cond2).2.1 (Classical.choose_spec cond1).2.2)

lemma exists_pair_iff_exists_exists (p: ℕ → ℕ → ℕ → Prop) : (∀ (k: ℕ), ∃ (N: ℕ × ℕ), p N.1 N.2 k) ↔
  (∀ (k: ℕ), ∃ n m, p n m k) := by
    constructor
    · intro h k
      rcases h k with ⟨N, pc⟩
      use N.1, N.2
    · intro h k
      rcases h k with ⟨n, m, pc⟩
      use (n, m)

theorem not_cauchyserie_imp (f: ℕ → Y) :
  ¬ CauchySerie f → ∃ ε > 0, ∃ (g₁: ℕ → ℕ) (g₂: ℕ → ℕ),
    (∀ (n: ℕ), g₁ n < g₂ n ∧ g₂ n < g₁ (n + 1) ∧
    ε ≤ ‖∑ i ∈ Finset.Ioc (g₁ n) (g₂ n), f i‖) := by
      rw [cauchyserie_iff_vanishing_norm']
      push_neg
      intro cond
      rcases cond with ⟨ε₀, ε₀pos, eq⟩
      use ε₀
      constructor
      · exact ε₀pos
      · rw [← exists_pair_iff_exists_exists] at eq
        let G := not_cauchyserie_imp_aux (fun n m ↦ ε₀ ≤ ‖∑ i ∈ Finset.Ioc n m, f i‖)
        use (fun n ↦ (G n).1), (fun n ↦ (G n).2)
        intro n
        constructor
        · unfold G
          exact (not_cauchyserie_imp_aux_def
             (fun n m ↦ ε₀ ≤ ‖∑ i ∈ Finset.Ioc n m, f i‖) eq n).1
        · constructor
          · unfold G
            exact (not_cauchyserie_imp_aux_def
               (fun n m ↦ ε₀ ≤ ‖∑ i ∈ Finset.Ioc n m, f i‖) eq n).2.1
          · dsimp
            exact (not_cauchyserie_imp_aux_def
               (fun n m ↦ ε₀ ≤ ‖∑ i ∈ Finset.Ioc n m, f i‖) eq n).2.2

/- ### Series with zeros ### -/

theorem cauchyserie_extra_zeros_iff_cauchyserie {Y: Type*} [NormedAddCommGroup Y]
  (f f': ℕ → Y) (g: ℕ → ℕ) (incr: StrictMono g) (eqcomp: f ∘ g = f' ∘ g)
  (fz: ∀ (n: ℕ), n ∉ range g → f n = 0) :
  CauchySerie f ↔ CauchySerie (f' ∘ g) := by
    simp only [cauchyserie_iff_vanishing_norm'']
    constructor
    · intro h ε εpos
      rcases h ε εpos with ⟨n₀, eq⟩
      use n₀
      intro n m n₀len nlem
      simp only [comp_apply, ← Nat.Icc_succ_left n m, Nat.succ_eq_add_one,
                 sum_of_comp_eq (n + 1) m incr eqcomp fz]
      simp only [← Nat.Icc_succ_left] at eq
      have le1 : n₀ ≤ (g (n + 1)) -1 := by
        apply Nat.le_sub_of_add_le
        exact le_trans (StrictMono.le_apply incr)
          (StrictMono.monotone incr (Nat.add_le_add_right n₀len 1))
      have le2 : g (n + 1) - 1 < g m := by
        calc
          g (n + 1) - 1 < g (n + 1) := by
            apply Nat.sub_one_lt
            rw [Nat.ne_zero_iff_zero_lt]
            exact StrictMono.pos_add_one incr n
          _ ≤ g m := by
            exact StrictMono.monotone incr nlem
      have := eq (g (n + 1) - 1) (g m) le1 le2
      rw [Nat.succ_eq_add_one, Nat.sub_one_add_one_eq_of_pos
          (StrictMono.pos_add_one incr n)] at this
      assumption
    · intro h ε εpos
      rcases h ε εpos with ⟨n₀, eq⟩
      use g (n₀ + 1)
      intro n m len nltm
      by_cases fnez: ∃ k ∈ Finset.Icc (n + 1) m, f k ≠ 0
      · have fnez1 := (exists_le_and_ge_of_exists_Icc fnez).1
        have fnez2 := (exists_le_and_ge_of_exists_Icc fnez).2
        rw [← Nat.Icc_succ_left n m,
            sum_eq_sum_with_no_extra_zeros (n + 1) m incr eqcomp fz fnez]
        simp only [← Nat.Icc_succ_left, Nat.succ_eq_add_one] at eq
        have gzltn : g 0 < n := by
          apply lt_of_lt_of_le _ len
          rw [StrictMono.lt_iff_lt incr]
          exact Nat.zero_lt_succ n₀
        have le1 : n₀ ≤ invFun g (sInf {k | n + 1 ≤ k ∧ f k ≠ 0}) - 1 := by
          rw [Nat.le_sub_one_iff_lt]
          · have : g n₀ < n + 1 := by
              have := lt_of_lt_of_le (incr (lt_add_one n₀)) len
              exact lt_trans this (lt_add_one n)
            exact lt_invFun_sInf (n + 1) n₀ this incr fz fnez1
          · apply invFun_sInf_pos incr _ fz fnez1
            exact lt_trans gzltn (lt_add_one n)
        have le2 : invFun g (sInf {k | n + 1 ≤ k ∧ f k ≠ 0}) - 1 <
          invFun g (sSup {k | k ≤ m ∧ f k ≠ 0}) := by
            apply Nat.sub_one_lt_of_le
            · exact invFun_sInf_pos incr (Nat.lt_trans gzltn (lt_add_one n)) fz fnez1
            · rw [← StrictMono.le_iff_le incr, Function.invFun_eq
                 (sInf_in_range (n + 1) fz fnez1), Function.invFun_eq
                 (sSup_in_range m fz fnez2)]
              exact sInfge_le_sSuple (n + 1) m fnez
        have := eq (invFun g (sInf {k | n + 1 ≤ k ∧ f k ≠ 0}) - 1)
          (invFun g (sSup {k | k ≤ m ∧ f k ≠ 0})) le1 le2
        rw [Nat.sub_one_add_one_eq_of_pos _] at this
        · assumption
        · exact invFun_sInf_pos incr (Nat.lt_trans gzltn (lt_add_one n)) fz fnez1
      · push_neg at fnez
        rw [← Nat.Icc_succ_left, Nat.succ_eq_add_one, Finset.sum_eq_zero fnez,
            norm_zero]
        assumption

theorem limserie_extra_zeros_iff_limserie {Y: Type*} [NormedAddCommGroup Y]
  (f f': ℕ → Y) (g: ℕ → ℕ) (incr: StrictMono g) (eqcomp: f ∘ g = f' ∘ g)
  (fz: ∀ (n: ℕ), n ∉ range g → f n = 0) (x: Y) :
  lim_serie f x ↔ lim_serie (f' ∘ g) x := by
    simp only [lim_serie_eps]
    constructor
    · intro h ε εpos
      rcases h ε εpos with ⟨n₀, eq⟩
      use n₀
      intro n n₀len
      simp only [comp_apply, Nat.succ_eq_add_one, Finset.Icc_eq_Iic n,
                 sum_of_comp_eq 0 n incr eqcomp fz, sum_gz_eq_sum_zero incr fz]
      exact eq (g n) (Nat.le_trans n₀len (StrictMono.le_apply incr))
    · intro h ε εpos
      rcases h ε εpos with ⟨n₀, eq⟩
      by_cases h': ∃ n ≥ n₀, f (g n) ≠ 0
      · rcases h' with ⟨n₁, n₀len₁, fgn₁neqz⟩
        use g n₁
        intro n len
        have fnez : ∃ k ∈ Finset.Icc 0 n, f k ≠ 0 := by
          use g n₁
          rw [Finset.mem_Icc]
          exact And.intro (And.intro (zero_le (g n₁)) len) fgn₁neqz
        have fnez1 := (exists_le_and_ge_of_exists_Icc fnez).1
        have fnez2 := (exists_le_and_ge_of_exists_Icc fnez).2
        rw [Finset.Icc_eq_Iic,
            sum_eq_sum_with_no_extra_zeros 0 n incr eqcomp fz fnez]
        simp only [← @comp_apply _ _ _ f', ← eqcomp, @comp_apply _ _ _ f] at *
        simp only [sum_invFun_eq_sum_zero (invFun g (sSup {k | k ≤ n ∧ f k ≠ 0})) incr fz fnez1]
        exact eq (invFun g (sSup {k | k ≤ n ∧ f k ≠ 0}))
            (Nat.le_trans n₀len₁ (le_invFun_sSup n n₁ len incr fz fgn₁neqz fnez2))
      · push_neg at h'
        simp only [comp_apply, Finset.Icc_eq_Iic,
                   sum_of_comp_eq 0 _ incr eqcomp fz, sum_gz_eq_sum_zero incr fz] at eq
        have eqsum : ∀ n ≥ (g n₀), ∑ i ∈ Finset.Icc 0 n, f i =
          ∑ i ∈ Finset.Icc 0 (g n₀), f i := by
            intro n gn₀len
            rw [eq_comm]
            apply Finset.sum_subset
            · exact Finset.Icc_subset_Icc (le_refl 0) gn₀len
            · intro k kin knin
              by_cases kinran: k ∈ range g
              · rcases kinran with ⟨p, gpeqk⟩
                rw [← gpeqk]
                simp only [Finset.mem_Icc, zero_le, true_and,
                           not_le, ← gpeqk, StrictMono.lt_iff_lt incr] at knin
                exact h' p (le_of_lt knin)
              · exact fz k kinran
        use g n₀
        intro n len
        rw [Finset.Icc_eq_Iic, eqsum n len]
        exact eq n₀ (le_refl n₀)

/- ### Decomposition of serie into subseries ### -/

theorem lim_serie_of_lim_subseries {ι: Type*} (J: Finset ι) [h: Nonempty J]
  (f: ℕ → Y) (g: ι → ℕ → ℕ) (s: ι → Y) (gSM: ∀ j ∈ J, StrictMono (g j))
  (disj: ∀ j ∈ J, ∀ i ∈ J, i ≠ j →
   Disjoint (range (g j)) (range (g i)))
  (un: ∀ (m: ℕ), ∃ j ∈ J, ∃ (n: ℕ), m = (g j) n) :
   (∀ j ∈ J, lim_serie (f ∘ (g j)) (s j)) → lim_serie f (∑ j ∈ J, (s j)) := by
    classical
    simp only [lim_serie_eps]
    intro cond ε εpos
    have εJpos: 0 < ε / (J.card) := by
      apply div_pos εpos
      simp only [Nat.cast_pos, Finset.card_pos]
      exact Finset.nonempty_coe_sort.mp h
    have n_j : ∀ j ∈ J, ∃ (n₀: ℕ), ∀ (n : ℕ), n₀ ≤ n →
      ‖∑ i ∈ Finset.Iic n, (f ∘ g j) i - s j‖ < ε / (J.card) := by
      intro j jinJ
      rcases cond j jinJ (ε / (J.card)) εJpos with ⟨n₀, eq⟩
      use n₀
    let N : ι → ℕ := fun j ↦ if h: ∃ (n₀: ℕ), ∀ (n : ℕ), n₀ ≤ n →
      ‖∑ i ∈ Finset.Iic n, (f ∘ g j) i - s j‖ < ε / (J.card) then
      Classical.choose h else 0
    use Finset.max' (Finset.image (fun i: ι ↦ g i (N i)) J)
      (Finset.Nonempty.image (Finset.nonempty_coe_sort.mp h)
        (fun i: ι ↦ g i (N i)))
    intro n len
    have : sSup ((fun (i: ι) ↦ g i 0) '' J) ≤ n := by
      apply Nat.sSup_le
      · exact Nonempty.image (fun i ↦ g i 0) (Finset.nonempty_coe_sort.mp h)
      · apply Set.Finite.bddAbove
        exact toFinite ((fun i ↦ g i 0) '' J)
      · intro k kin
        rcases kin with ⟨j, jinJ, eqk⟩
        dsimp at eqk
        rw [← eqk]
        apply Nat.le_trans _ len
        have : g j 0 ≤ g j (N j) := by
          rw [StrictMono.le_iff_le (gSM j jinJ)]
          exact Nat.zero_le (N j)
        apply le_trans this
        apply Finset.le_max'
        rw [Finset.mem_image]
        use j, jinJ
    rw [Finset.sum_decomp J f g gSM disj un n, ← Finset.sum_sub_distrib]
    calc
      ‖∑ x ∈ J, (∑ i ∈ {i ∈ Finset.Iic n | g x i ≤ n},
      f (g x i) - s x)‖ ≤ ∑ x ∈ J,
      ‖∑ i ∈ {i ∈ Finset.Iic n | g x i ≤ n}, f (g x i) - s x‖ := by
        exact norm_sum_le J _
      _ < ∑ x ∈ J, (ε / J.card) := by
        apply Finset.sum_lt_sum_of_nonempty
          (Finset.nonempty_coe_sort.mp h)
        intro j jinJ
        have : {i ∈ Finset.Iic n | g j i ≤ n} =
          Finset.Iic (sSup {i ∈ Finset.Iic n | g j i ≤ n}) := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_Iic]
            constructor
            · intro kin
              apply Nat.le_sSup
              · use n
                rw [mem_upperBounds]
                intro m min
                exact min.1
              · assumption
            · intro kin
              constructor
              · apply Nat.le_trans kin
                apply Nat.sSup_le
                · use 0
                  constructor
                  · exact zero_le _
                  · apply Nat.le_trans _ this
                    apply Nat.le_sSup
                    · apply Set.Finite.bddAbove
                      exact toFinite ((fun i ↦ g i 0) '' J)
                    · use j, jinJ
                · use n
                  rw [mem_upperBounds]
                  intro m min
                  exact min.1
                · intro m min
                  exact min.1
              · by_cases keqz : k = 0
                · rw [keqz]
                  apply Nat.le_trans _ this
                  apply Nat.le_sSup
                  · apply Set.Finite.bddAbove
                    exact toFinite ((fun i ↦ g i 0) '' J)
                  · use j, jinJ
                · by_contra! h
                  have : sSup {i | i ≤ n ∧ g j i ≤ n} ≤ k - 1 := by
                    apply Nat.sSup_le
                    · use 0
                      constructor
                      · exact zero_le _
                      · apply Nat.le_trans _ this
                        apply Nat.le_sSup
                        · apply Set.Finite.bddAbove
                          exact toFinite ((fun i ↦ g i 0) '' J)
                        · use j, jinJ
                    · use n
                      rw [mem_upperBounds]
                      intro m min
                      exact min.1
                    · intro m min
                      have := lt_of_le_of_lt min.2 h
                      rw [StrictMono.lt_iff_lt (gSM j jinJ)] at this
                      rw [← Nat.lt_iff_le_pred (Nat.zero_lt_of_ne_zero keqz)]
                      assumption
                  have := Nat.le_trans kin this
                  rw [← Nat.lt_iff_le_pred (Nat.zero_lt_of_ne_zero keqz)] at this
                  linarith
        simp only [this, ← @comp_apply _ _ _ f (g j)]
        have : N j ≤ sSup {i ∈ Finset.Iic n | g j i ≤ n} := by
          apply Nat.le_sSup
          · use n
            simp only [mem_upperBounds, Finset.mem_Iic]
            intro m min
            exact min.1
          · have : (g j) (N j) ≤ n := by
              apply Nat.le_trans _ len
              apply Finset.le_max'
              rw [Finset.mem_image]
              use j
            constructor
            · rw [Finset.mem_Iic, ← StrictMono.le_iff_le (gSM j jinJ)]
              exact Nat.le_trans this (StrictMono.le_apply (gSM j jinJ))
            · assumption
        dsimp only [N] at this
        rw [dif_pos (n_j j jinJ)] at this
        exact Classical.choose_spec (n_j j jinJ)
          (sSup {i ∈ Finset.Iic n | g j i ≤ n}) this
      _ = ε := by
        rw [Finset.sum_const, nsmul_eq_mul, mul_div_cancel₀]
        simp only [Nat.cast_ne_zero, Finset.card_ne_zero]
        exact Finset.nonempty_coe_sort.mp h

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

theorem lim_serie_comp_of_hasnetsum {f: ℕ → Y} (g: ℕ → ℕ)
  (gbij: Bijective g) (x: Y) :
    HasSumNet f x → lim_serie (f ∘ g) x := by
    rw [hassumnet_eps, lim_serie_eps]
    intro fhassumx
    intro ε εpos
    rcases fhassumx ε εpos with ⟨F₀, eq⟩
    let J₀ := Finset.preimage F₀ g ((fun _ _ _ _ eq ↦ (gbij.1 eq)))
    by_cases h: J₀.Nonempty
    · use J₀.max' h
      intro n len
      simp only [Finset.Icc_eq_Iic, comp_apply, Finset.sum_image_inj gbij.1 0 n]
      have : F₀ ⊆ Finset.image g (Finset.Icc 0 n) := by
        intro m minJ₀
        rw [Finset.mem_image]
        rcases gbij.2 m with ⟨a, gaeqm⟩
        use a
        constructor
        · rw [Finset.mem_Icc]
          constructor
          · exact zero_le a
          · have : a ∈ J₀ := by
              rw [Finset.mem_preimage, gaeqm]
              assumption
            exact Nat.le_trans (Finset.le_max' J₀ a this) len
        · assumption
      exact eq (Finset.image g (Finset.Icc 0 n)) this
    · rw [Finset.not_nonempty_iff_eq_empty] at h
      have : F₀ = ∅ := by
        apply Finset.eq_empty_of_forall_not_mem
        intro n ninF₀
        rcases gbij.2 n with ⟨a, gaeqn⟩
        have : a ∈ J₀ := by
          rw [Finset.mem_preimage, gaeqn]
          assumption
        rw [h] at this
        contradiction
      simp only [this, Finset.empty_subset, forall_const] at eq
      use 0
      intro n zlen
      simp only [Finset.Icc_eq_Iic, comp_apply, Finset.sum_image_inj gbij.1 0 n]
      exact eq (Finset.image g (Finset.Icc 0 n))

theorem lim_serie_of_hasnetsum {f: ℕ → Y} (x: Y) :
  HasSumNet f x → lim_serie f x := by
    exact lim_serie_comp_of_hasnetsum _ bijective_id x

theorem conv_serie_comp_of_summable {f: ℕ → Y} (g: ℕ → ℕ)
  (gbij: Bijective g) :
    SummableNet f → conv_serie (f ∘ g) := by
      unfold SummableNet conv_serie
      intro fsumm
      rcases fsumm with ⟨x, fhassumx⟩
      use x
      exact lim_serie_comp_of_hasnetsum g gbij x fhassumx

theorem conv_serie_of_summable {f: ℕ → Y} :
  SummableNet f → conv_serie f := by
    exact conv_serie_comp_of_summable _ bijective_id

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

theorem conv_serie_of_norm_bounded [CompleteSpace Y]
  {f : ℕ → Y} (g : ℕ → ℝ) (hg : conv_serie g) (h : ∀ (n : ℕ), ‖f n‖ ≤ g n) :
  conv_serie f := by
    apply conv_serie_of_conv_abs_serie
    exact conv_abs_serie_of_norm_bounded g hg h

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

/- ### Telescopic series ### -/

theorem telescopic_conv_to {f g: ℕ → N}
  (tlsc: ∀ (n: ℕ), f n = g (n + 1) - g n) {x: N} (limitg: Limit g x): lim_serie f (x - g 0) := by
    unfold lim_serie
    simp only [tlsc, Finset.sum_Iic_telescopic]
    apply lim_of_sub_eq_sub_of_lim
    · exact (netlim_iff_shift_subsequence_lim g 1).mp limitg
    · exact lim_of_cte (g 0)

theorem telescopic_conv {f g: ℕ → N}
  (tlsc: ∀ (n: ℕ), f n = g (n + 1) - g n) {x: N} (limitg: Limit g x): conv_serie f := by
    use x - g 0
    exact telescopic_conv_to tlsc limitg

theorem conv_telescopic_to (f g: ℕ → N)
  (tlsc: ∀ (n: ℕ), f n = g (n + 1) - g n) {x: N} (fconvx: lim_serie f x): Limit g (x + g 0) := by
    unfold lim_serie at fconvx
    simp only [tlsc, Finset.sum_Iic_telescopic] at fconvx
    rw [netlim_iff_shift_subsequence_lim g 1]
    have : (fun n ↦ g (n + 1)) = (fun N ↦ g (N + 1) - g 0) + ((fun N ↦ g 0)) := by
      ext n
      rw [Pi.add_apply, sub_add, sub_self, sub_zero]
    rw [this]
    apply lim_of_sum_eq_sum_of_lim
    · exact fconvx
    · exact lim_of_cte (g 0)

theorem conv_telescopic (f g: ℕ → N)
  (tlsc: ∀ (n: ℕ), f n = g (n + 1) - g n) (fconv: conv_serie f): ∃ (x: N), Limit g x := by
    rcases fconv with ⟨x, eq⟩
    use x + g 0
    exact conv_telescopic_to f g tlsc eq

/- ### Unconditional convergence ### -/

section

variable {Y: Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]

def RSerie (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℕ), Bijective g → conv_serie (f ∘ g)

def SSerie (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℕ), StrictMono g → conv_serie (f ∘ g)

def BMSerie (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℝ), Bornology.IsBounded (range g) →
    conv_serie (fun (n: ℕ) ↦ (g n) • (f n))

def ASerie (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℝ), range g ⊆ {-1, 1} → conv_serie (fun (n: ℕ) ↦ (g n) • (f n))

def RCauchy (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℕ), Bijective g → CauchySerie (f ∘ g)

def SCauchy (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℕ), StrictMono g → CauchySerie (f ∘ g)

def BMCauchy (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℝ), Bornology.IsBounded (range g) →
    CauchySerie (fun (n: ℕ) ↦ (g n) • (f n))

def ACauchy (f: ℕ → Y) : Prop :=
  ∀ (g: ℕ → ℝ), range g ⊆ {-1, 1} → CauchySerie (fun (n: ℕ) ↦ (g n) • (f n))

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

lemma minusoneone_finite_sums_bddabove {A: Type*} (f: A → Y) (s: Finset A) :
  BddAbove {t: ℝ | ∃ g: A → ℝ, g '' s ⊆ Icc (-1) 1 ∧ t = ‖∑ a ∈ s, (g a) • f a‖} := by
    use ∑ a ∈ s, ‖f a‖
    rw [mem_upperBounds]
    intro t tin
    rw [Set.mem_setOf_eq] at tin
    rcases tin with ⟨g, g1m1, teq⟩
    have : ∀ a ∈ s, |g a| ≤ 1 := by
      intro a ains
      have : g a ∈ g '' s := by
        use a
        exact And.intro ains rfl
      have := g1m1 this
      rw [mem_Icc, ← abs_le] at this
      assumption
    rw [teq]
    calc
      ‖∑ a ∈ s, g a • f a‖ ≤ ∑ a ∈ s, ‖g a • f a‖ := by
        exact norm_sum_le s fun a ↦ g a • f a
      _ = ∑ a ∈ s, |g a| * ‖f a‖ := by
        simp only [norm_smul, Real.norm_eq_abs]
      _ ≤ ∑ a ∈ s, ‖f a‖ := by
        apply Finset.sum_le_sum
        intro i iins
        nth_rw 2 [← one_mul (‖f i‖)]
        exact mul_le_mul_of_nonneg_right (this i iins) (norm_nonneg (f i))

lemma pm_finite_sums_bddabove {A: Type*} (f: A → Y) (s: Finset A) :
  BddAbove {t: ℝ | ∃ g: A → ℝ, g '' s ⊆ {-1, 1} ∧ t = ‖∑ a ∈ s, (g a) • f a‖} := by
    apply BddAbove.mono _ (minusoneone_finite_sums_bddabove f s)
    intro t tin
    rw [Set.mem_setOf_eq] at *
    rcases tin with ⟨g, gimsub, teq⟩
    use g
    constructor
    · intro x xin
      rcases xin with ⟨a, ains, xeq⟩
      rw [← xeq]
      have : g a ∈ g '' s := by
        use a
      have := gimsub this
      simp only [mem_insert_iff, mem_singleton_iff] at this
      rcases this with h | h
      repeat
        rw [h]
        simp only [mem_Icc, le_refl, neg_le_self_iff, zero_le_one, and_self]
    · assumption

lemma sup_bdd_one_eq_sup_bdd_le_one {A: Type*} (f: A → Y) (s: Finset A) :
  sSup {t: ℝ | ∃ g: A → ℝ, g '' s ⊆ {-1, 1} ∧ t = ‖∑ i ∈ s, (g i) • (f i)‖} =
  sSup {t: ℝ | ∃ g: A → ℝ, g '' s ⊆ Icc (-1) 1 ∧ t = ‖∑ i ∈ s, (g i) • (f i)‖} := by
    apply csSup_eq_csSup_of_forall_exists_le
    · intro t tin
      use t
      rw [Set.mem_setOf_eq] at *
      constructor
      · rcases tin with ⟨g, g1m1, teq⟩
        use g
        constructor
        · apply subset_trans g1m1
          intro t tin
          rcases tin with h | h
          repeat
            rw [h]
            norm_num
        · assumption
      · rfl
    · intro t tin
      rw [Set.mem_setOf_eq] at tin
      rcases tin with ⟨g, gle1, teq⟩
      by_cases h: ∑ i ∈ s, g i • f i = 0
      · use ‖∑ i ∈ s, f i‖
        constructor
        · use (fun i ↦ 1)
          constructor
          · simp only [image_subset_iff, mem_insert_iff, mem_singleton_iff, or_true,
                       preimage_const_of_mem, subset_univ]
          · simp only [one_smul]
        · rw [teq, h, norm_zero]
          exact norm_nonneg (∑ i ∈ s, f i)
      · rcases exists_dual_vector ℝ (∑ i ∈ s, (g i) • (f i)) h with ⟨F, fnormone, feqnorm⟩
        let g': A → ℝ := fun i ↦ if F (f i) < 0 then -1 else 1
        use ‖∑ i ∈ s, (g' i) • (f i)‖
        constructor
        · rw [Set.mem_setOf_eq]
          use g'
          constructor
          · intro r rin
            rw [mem_image] at rin
            rcases rin with ⟨i, iins, req⟩
            rw [← req]
            simp only [mem_insert_iff, mem_singleton_iff]
            unfold g'
            by_cases h' : F (f i) < 0
            · left
              rw [if_pos h']
            · right
              rw [if_neg h']
          · rfl
        · have : F (∑ i ∈ s, g i • f i) = ‖∑ i ∈ s, g i • f i‖ := by
            rw [feqnorm]
            simp only [RCLike.ofReal_real_eq_id, id_eq]
          simp only [teq, ← this, map_sum, map_smul]
          calc
            ∑ x ∈ s, g x • F (f x) ≤ |∑ x ∈ s, g x • F (f x)| := by
              exact le_abs_self (∑ x ∈ s, g x • F (f x))
            _ ≤ ∑ x ∈ s, ‖g x • F (f x)‖ := by
              exact Finset.abs_sum_le_sum_abs (fun i ↦ g i • F (f i)) s
            _ = ∑ x ∈ s, |g x| * |F (f x)| := by
              simp only [norm_smul, Real.norm_eq_abs]
            _ ≤ ∑ x ∈ s, |F (f x)| := by
              apply Finset.sum_le_sum
              intro i iins
              nth_rw 2 [← one_mul (|F (f i)|)]
              apply mul_le_mul_of_nonneg_right _ (abs_nonneg (F (f i)))
              rw [abs_le, ← mem_Icc]
              apply gle1
              use i
              exact And.intro iins rfl
            _ = ∑ x ∈ s, g' x * F (f x) := by
              unfold g'
              apply Finset.sum_congr rfl
              intro i iins
              by_cases h': F (f i) < 0
              · rw [abs_of_neg h', if_pos h', neg_mul, one_mul]
              · rw [abs_of_nonneg (le_of_not_lt h'), if_neg h', one_mul]
            _ = F (∑ x ∈ s, g' x • f x) := by
              simp only [← smul_eq_mul, ← map_smul F, ← map_sum F]
            _ ≤ |F (∑ x ∈ s, g' x • f x)| := by
              exact le_abs_self (F (∑ x ∈ s, g' x • f x))
            _ ≤ ‖F‖ * ‖∑ x ∈ s, g' x • f x‖ := by
              exact ContinuousLinearMap.le_opNorm F (∑ x ∈ s, g' x • f x)
            _ = ‖∑ x ∈ s, g' x • f x‖ := by
              rw [fnormone, one_mul]

lemma sup_bdd_one_eq_sup_bdd_le_one' (s: Finset Y) :
  sSup {t: ℝ | ∃ g: Y → ℝ, g '' s ⊆ {-1, 1} ∧ t = ‖∑ w ∈ s, (g w) • w‖} =
  sSup {t: ℝ | ∃ g: Y → ℝ, g '' s ⊆ Icc (-1) 1 ∧ t = ‖∑ w ∈ s, (g w) • w‖} := by
     exact sup_bdd_one_eq_sup_bdd_le_one (fun (y: Y) ↦ y) s

lemma exists_pmone_gt {A: Type*} (f: A → Y) (s: Finset A) (g: A → ℝ)
  (absgle1: g '' s ⊆ Icc (-1) 1) :
    ∀ ε > 0, ∃ (p: A → ℝ), (range p ⊆ {-1, 1} ∧
    ‖∑ w ∈ s, (g w) • f w‖ < ‖∑ w ∈ s, (p w) • f w‖ + ε) := by
      classical
      intro ε εpos
      let T := {t: ℝ | ∃ g: A → ℝ, g '' s ⊆ {-1, 1} ∧
        t = ‖∑ i ∈ s, (g i) • (f i)‖}
      have Tnempty : T.Nonempty := by
        use ‖∑ i ∈ s, f i‖
        rw [Set.mem_setOf_eq]
        use (fun a ↦ 1)
        constructor
        · intro x xin
          rcases xin with ⟨a, ains, xeq⟩
          rw [← xeq]
          simp only [mem_insert_iff, mem_singleton_iff, or_true]
        · simp only [one_smul]
      have : sSup T - ε < sSup T := by
        norm_num [εpos]
      have := exists_lt_of_lt_csSup Tnempty this
      rcases this with ⟨t, tinT, eq⟩
      rw [sup_bdd_one_eq_sup_bdd_le_one, sub_lt_iff_lt_add] at eq
      rcases tinT with ⟨p, rangepsub, teq⟩
      use (fun a ↦ if a ∈ s then p a else 1)
      constructor
      · intro t tin
        rcases tin with ⟨a, eq⟩
        dsimp at eq
        by_cases h: a ∈ s
        · rw [if_pos h] at eq
          rw [← eq]
          have : p a ∈ p '' s := by
            use a
            exact And.intro h rfl
          exact rangepsub this
        · rw [if_neg h] at eq
          rw [← eq]
          simp only [mem_insert_iff, mem_singleton_iff, or_true]
      · have : ∑ w ∈ s, (if w ∈ s then p w else 1) • f w =
          ∑ w ∈ s, p w • f w := by
            apply Finset.sum_congr rfl
            intro x xins
            rw [if_pos xins]
        rw [this, ← teq]
        calc
          ‖∑ w ∈ s, g w • f w‖ ≤ sSup {t | ∃ (g: A → ℝ), g '' ↑s ⊆ Icc (-1) 1 ∧
             t = ‖∑ i ∈ s, g i • f i‖} := by
              apply le_csSup
              · exact minusoneone_finite_sums_bddabove f s
              · rw [Set.mem_setOf_eq]
                use g
          _ < t + ε := by
            exact eq

lemma exists_pmone_gt' (f: ℕ → Y) (g: ℕ → ℝ) :
    ∀ ε > 0, ∀ (n m: ℕ), (g '' (Finset.Ioc n m) ⊆ Icc (-1) 1) →
    ∃ (p: ℕ → ℝ), (range p ⊆ {-1, 1} ∧
    ‖∑ i ∈ Finset.Ioc n m, g i • f i‖ <
    ‖∑ i ∈ Finset.Ioc n m, p i • f i‖ + ε) := by
      intro ε εpos n m absgle1
      exact exists_pmone_gt f (Finset.Ioc n m) g absgle1 ε εpos

theorem BMCauchy_iff_ACauchy (f: ℕ → Y) :
  BMCauchy f ↔ ACauchy f := by
    classical
    unfold BMCauchy ACauchy
    constructor
    · intro BMcauchy g rgsub
      have : Bornology.IsBounded (range g) := by
        exact Bornology.IsBounded.subset
          (Set.Finite.isBounded (toFinite {-1, 1})) rgsub
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
      rw [cauchyserie_iff_cauchyserie_const_smul ℝ |K|⁻¹
          (inv_ne_zero (abs_ne_zero.mpr Knez))]
      simp only [← smul_assoc, smul_eq_mul]
      have inIcc : ∀ (n: ℕ), |K|⁻¹ * g n ∈ Icc (-1) 1 := by
        intro n
        rw [mem_Icc, ← abs_le, abs_mul, abs_inv, abs_abs]
        calc
          |K|⁻¹ * |g n| ≤ |K|⁻¹ * |K| := by
            exact mul_le_mul_of_nonneg (le_refl |K|⁻¹) (gleK n)
              (inv_nonneg_of_nonneg (abs_nonneg K)) (abs_nonneg K)
          _ = 1 := by
            rw [inv_mul_cancel₀ (abs_ne_zero.mpr Knez)]
      by_contra! h
      rcases (not_cauchyserie_imp _ h) with ⟨ε₀, ε₀pos, g₁, g₂, eq⟩
      have g₁incr : StrictMono g₁ := by
        have : ∀ (k: ℕ), g₁ k < g₁ (k + 1) := by
          intro k
          exact lt_trans (eq k).1 (eq k).2.1
        exact strictMono_nat_of_lt_succ this
      have g₂incr : StrictMono g₂ := by
        have : ∀ (k: ℕ), g₂ k < g₂ (k + 1) := by
          intro k
          exact lt_trans (eq k).2.1 (eq (k + 1)).1
        exact strictMono_nat_of_lt_succ this
      have nleg₁ : ∀ (n: ℕ), n ≤ g₁ n:= by
        intro n
        exact StrictMono.le_apply g₁incr
      have nleg₂ : ∀ (n: ℕ), n ≤ g₂ n:= by
        intro n
        exact StrictMono.le_apply g₂incr
      have exist_gpm1 : ∃ (h: ℕ → ℝ), range h ⊆ {-1, 1} ∧
        ∀ (n: ℕ), ‖∑ i ∈ Finset.Ioc (g₁ n) (g₂ n), (|K|⁻¹ * g i) • f i‖ <
        ‖∑ i ∈ Finset.Ioc (g₁ n) (g₂ n), h i • f i‖ + ε₀/2 := by
          have cond : ∀ (n: ℕ), ∃ (p: ℕ → ℝ), (range p ⊆ {-1, 1} ∧
            ‖∑ i ∈ Finset.Ioc (g₁ n) (g₂ n), (|K|⁻¹ * g i) • f i‖ <
            ‖∑ i ∈ Finset.Ioc (g₁ n) (g₂ n), p i • f i‖ + ε₀/2) := by
              intro n
              have : (fun i ↦ |K|⁻¹ * g i) '' (Finset.Ioc (g₁ n) (g₂ n))
                 ⊆ Icc (-1) 1 := by
                  intro x xin
                  rcases xin with ⟨i, iin, xeq⟩
                  rw [← xeq]
                  exact inIcc i
              exact exists_pmone_gt f (Finset.Ioc (g₁ n) (g₂ n))
                (fun (i: ℕ) ↦ |K|⁻¹ * g i) this (ε₀/2) (by linarith [ε₀pos])
          let F : ℕ → ℕ → ℝ := fun n ↦ if h: ∃ p, range p ⊆ {-1, 1} ∧
              ‖∑ i ∈ Finset.Ioc (g₁ n) (g₂ n), (|K|⁻¹ * g i) • f i‖ <
              ‖∑ i ∈ Finset.Ioc (g₁ n) (g₂ n), p i • f i‖ + ε₀ / 2 then
              Classical.choose h else (fun n ↦ 0)
          have rangeF : ∀ (n k: ℕ), (F n k) = -1  ∨ (F n k) = 1 := by
            intro n k
            unfold F
            rw [dif_pos (cond n)]
            have : Classical.choose (cond n) k ∈
              range (Classical.choose (cond n)) := by
              use k
            have := (Classical.choose_spec (cond n)).1 this
            simp only [mem_insert_iff, mem_singleton_iff] at this
            assumption
          let h: ℕ → ℝ := fun n ↦ if j: ∃ (k: ℕ), g₁ k < n ∧ n ≤ g₂ k then
            F (Classical.choose j) n else 1
          have : ∀ (n: ℕ), ∑ i ∈ Finset.Ioc (g₁ n) (g₂ n), h i • f i =
            ∑ i ∈ Finset.Ioc (g₁ n) (g₂ n), (F n i) • f i := by
              intro n
              apply Finset.sum_congr rfl
              · intro i iin
                have : h i = F n i := by
                  rw [Finset.mem_Ioc] at iin
                  have j : ∃ k, g₁ k < i ∧ i ≤ g₂ k := by
                    use n
                  have : Classical.choose j = n := by
                    by_contra!
                    rw [ne_iff_lt_or_gt] at this
                    rcases this with lt | gt
                    · have : i < i := by
                        calc
                          i ≤ g₂ (Classical.choose j) := by
                            exact (Classical.choose_spec j).2
                          _ < g₁ (Classical.choose j + 1) := by
                            exact (eq (Classical.choose j)).2.1
                          _ ≤ g₁ n := by
                            exact StrictMono.monotone g₁incr lt
                          _ < i := by
                            exact iin.1
                      linarith
                    · have : i < i := by
                        calc
                          i ≤ g₂ n := by
                            exact iin.2
                          _ < g₁ (n + 1) := by
                            exact (eq n).2.1
                          _ ≤ g₁ (Classical.choose j) := by
                            exact StrictMono.monotone g₁incr gt
                          _ < i := by
                            exact (Classical.choose_spec j).1
                      linarith
                  unfold h
                  rw [dif_pos j, this]
                apply congr_arg (fun (x: ℝ) ↦ x • (f i)) this
          use h
          constructor
          · intro t tinrh
            rw [mem_range]at tinrh
            rcases tinrh with ⟨n, hneqt⟩
            rw [← hneqt]
            simp only [mem_insert_iff, mem_singleton_iff]
            unfold h
            by_cases j : ∃ k, g₁ k < n ∧ n ≤ g₂ k
            · rw [dif_pos j]
              exact rangeF (Classical.choose j) n
            · rw [dif_neg j]
              right
              rfl
          · intro n
            simp only [this]
            unfold F
            rw [dif_pos (cond n)]
            exact (Classical.choose_spec (cond n)).2
      rcases exist_gpm1 with ⟨h, rhpm1, difltediv2⟩
      have hfcauchy := ACauchy h rhpm1
      rw [cauchyserie_iff_vanishing_norm] at hfcauchy
      rcases hfcauchy (ε₀/2) (by linarith [ε₀pos]) with ⟨n₀, eq'⟩
      have : ε₀ < ε₀ := by
        calc
          ε₀ ≤ ‖∑ i ∈ Finset.Ioc (g₁ n₀) (g₂ n₀), (|K|⁻¹ * g i) • f i‖ := by
            exact (eq n₀).2.2
          _  < ‖∑ i ∈ Finset.Ioc (g₁ n₀) (g₂ n₀), h i • f i‖ + ε₀ / 2 := by
            exact difltediv2 n₀
          _ < ε₀/2 + ε₀/2 := by
            rw [add_lt_add_iff_right (ε₀ / 2)]
            exact eq' (g₁ n₀) (g₂ n₀) (nleg₁ n₀) (le_of_lt (eq n₀).1)
          _ = ε₀ := by
            norm_num
      linarith

theorem BMCauchy_of_SCauchy (f: ℕ → Y) :
  BMCauchy f → SCauchy f := by
    classical
    unfold BMCauchy SCauchy
    intro BMcf g incrg
    let h: ℕ → ℝ := fun n ↦ if n ∈ range g then 1 else 0
    have ranhbdd : Bornology.IsBounded (range h) := by
      rw [NormedSpace.isBounded_iff_bounded_norm ℝ]
      use 1, one_ne_zero
      intro t tin
      rcases tin with ⟨n, hneqt⟩
      rw [← hneqt, Real.norm_eq_abs, Real.norm_eq_abs]
      dsimp only [h]
      by_cases h': n ∈ range g
      · rw [if_pos h']
      · rw [if_neg h']
        norm_num
    rw [← cauchyserie_extra_zeros_iff_cauchyserie (fun n ↦ h n • f n) f]
    · exact BMcf h ranhbdd
    · assumption
    · ext n
      simp only [comp_apply]
      unfold h
      rw [if_pos (by use n), one_smul]
    · intro n nnin
      unfold h
      rw [if_neg nnin, zero_smul]

theorem CauchySum_of_SCauchy  (f: ℕ → Y) :
  SCauchy f → CauchySumNet f := by
    intro fScauchy
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

theorem RSerie_iff_RCauchy {Y: Type*} [NormedAddCommGroup Y]
  [CompleteSpace Y] (f: ℕ → Y) :
  RSerie f ↔ RCauchy f := by
    unfold RCauchy RSerie
    simp only [conv_serie_iff_cauchyserie]

theorem SSerie_iff_SCauchy {Y: Type*} [NormedAddCommGroup Y]
  [CompleteSpace Y] (f: ℕ → Y) :
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

/- Summable is equivalent to RSerie without completeness -/

theorem RSerie_iff_Summable {Y: Type*} [NormedAddCommGroup Y] (f: ℕ → Y) :
  RSerie f ↔ SummableNet f := by
    classical
    constructor
    · intro Rsf
      unfold SummableNet
      by_contra!
      have := Rsf id bijective_id
      rw [comp_id] at this
      rcases this with ⟨x, flimx⟩
      have := this x
      rw [hassumnet_eps] at this
      push_neg at this
      rcases this with ⟨ε₀, ε₀pos, eq⟩
      rw [lim_serie_eps] at flimx
      rcases flimx (ε₀/2) (by norm_num [ε₀pos]) with ⟨m₀, eq'⟩
      have pevnt : ∀ (n : ℕ), ∃ k > n,
        ‖∑ i ∈ Finset.Iic k, f i - x‖ < ε₀ / 2 := by
        intro n
        by_cases h: m₀ < n
        · use n + 1, (lt_add_one n)
          exact eq' (n + 1) (le_of_lt
            (lt_of_lt_of_le h (Nat.le_add_right n 1)))
        · simp only [not_lt] at h
          use (m₀ + 1), (Nat.lt_add_one_iff.mpr h)
          exact eq' (m₀ + 1) (Nat.le_add_right m₀ 1)
      have eq : ∀ (F: Finset ℕ), ∃ G, G.Nonempty ∧ F ⊂ G ∧
        ε₀ ≤ ‖∑ i ∈ G, f i - x‖ := by
          intro F
          let n := F.max''
          rcases eq (F ∪ {n + 1}) with ⟨G, FsubG, le⟩
          use G
          constructor
          · use n + 1
            apply FsubG
            simp only [Finset.mem_union, Finset.mem_singleton, or_true]
          · constructor
            · rw [Finset.ssubset_iff_subset_ne]
              constructor
              · apply subset_trans _ FsubG
                exact Finset.subset_union_left
              · rw [ne_comm]
                have : n + 1 ∈ G := by
                  apply FsubG
                  simp only [Finset.mem_union, Finset.mem_singleton, or_true]
                apply ne_of_mem_of_not_mem' this
                intro inF
                have : n + 1 ≤ n := by
                  have := Finset.le_max'' F (n + 1) inF
                  dsimp [n] at *
                  exact this
                linarith
            · assumption
      let c : Finset ℕ → Finset ℕ := fun F ↦
        if h: ∃ G, G.Nonempty ∧ F ⊂ G ∧ ε₀ ≤ ‖∑ i ∈ G, f i - x‖
          then Classical.choose h else ∅
      have c_def : ∀ (F: Finset ℕ), (c F).Nonempty ∧ F ⊂ (c F) ∧
        ε₀ ≤ ‖∑ i ∈ (c F), f i - x‖ := by
          intro F
          unfold c
          rw [dif_pos (eq F)]
          exact Classical.choose_spec (eq F)
      let N := sInf_inc c (fun F ↦ (c_def F).1)
        (fun k ↦ ‖∑ i ∈ Finset.Iic k, f i - x‖ < ε₀/2)
      let F : ℕ → Finset ℕ := fun k ↦ Finset.Iic (N k)
      let C : ℕ → Finset ℕ := fun k ↦ c (F k)
      have Fznemp : F 0 ≠ ∅ := by
        unfold F
        exact Ne.symm (ne_of_beq_false rfl)
      have st1 : ∀ (n: ℕ), F n ⊂ C n := by
        intro n
        dsimp only [C]
        exact (c_def (F n)).2.1
      have st2 : ∀ (n: ℕ), C n ⊂ F (n + 1) := by
        intro n
        exact (sInf_inc_def c (fun F ↦ (c_def F).1) _ pevnt n).1
      have un : ∀ (m: ℕ), ∃ (n: ℕ), m ∈ F n := by
        intro m
        induction' m with m ih
        · use 0
          rw [Finset.mem_Iic]
          exact zero_le _
        · rcases ih with ⟨n, min⟩
          use n + 1
          simp only [F, Finset.mem_Iic] at *
          have := sInf_inc_StrictMono c (fun F ↦ (c_def F).1)
            (fun k ↦ ‖∑ i ∈ Finset.Iic k, f i - x‖ < ε₀/2) pevnt
          exact lt_of_le_of_lt min (this (lt_add_one n))
      rcases exists_bij_img_eq (sCF_not_empty st1 st2 Fznemp)
        (sCF_disjoint st1 st2) (sCF_cover un)
        with ⟨g, gbij, t, SMt, eq⟩
      have := CauchySerie_of_conv_serie (f ∘ g) (Rsf g gbij)
      rw [cauchyserie_iff_vanishing_norm'''] at this
      rcases this (ε₀/2) (by norm_num [ε₀pos]) with ⟨n₀, eq1⟩
      have le1 : n₀ ≤ t (2 * n₀ + 1) := by
        apply Nat.le_trans (StrictMono.le_apply SMt)
        exact StrictMono.monotone SMt
          (Nat.le_trans (Nat.le_mul_of_pos_left n₀ Nat.zero_lt_two)
           ((Nat.le_add_right _ 1)))
      have contr1 := eq1 (t (2 * n₀ + 1))
        (t (2 * n₀ + 1 + 1)) le1
        (StrictMono.monotone SMt (Nat.le_add_right _ 1))
      have contr2 : ε₀/2 < ‖∑ i ∈ Finset.Ico (t (2 * n₀ + 1))
        (t (2 * n₀ + 1 + 1)), (f ∘ g) i‖ := by
        calc
          ε₀/2 = ε₀ - ε₀/2 := by
            linarith
          _ ≤ ‖(∑ i ∈ C n₀, f i) - x‖ - ε₀/2 := by
            apply tsub_le_tsub_right _ (ε₀ / 2)
            unfold C
            exact (c_def (F n₀)).2.2
          _ < ‖(∑ i ∈ C n₀, f i) - x‖ - ‖(∑ i ∈ Finset.Iic (N n₀), f i) - x‖ := by
            apply sub_lt_sub_left _ ‖∑ i ∈ C n₀, f i - x‖
            exact (sInf_inc_def c (fun F ↦ (c_def F).1) _ pevnt n₀).2
          _ ≤ ‖((∑ i ∈ C n₀, f i) - x) - ((∑ i ∈ Finset.Iic (N n₀), f i) - x)‖ := by
            exact norm_sub_norm_le _ _
          _ = ‖∑ i ∈ (C n₀) \ (F n₀), f i‖ := by
            simp only [sub_sub_sub_cancel_right, F]
            apply congr_arg
            rw [← Finset.sum_sdiff_eq_sub (subset_of_ssubset (st1 n₀))]
          _ = ‖∑ i ∈ Finset.Ico (t (2 * n₀ + 1))
            (t (2 * n₀ + 1 + 1)), (f ∘ g) i‖ := by
              rw [← sCF_odd n₀ ,← eq (2 * n₀ + 1),
              Finset.sum_image (fun _ _ _ _ eq ↦ (gbij.1 eq))]
              simp only [@comp_apply _ _ _ f g]
      linarith
    · intro sumf
      intro g bijg
      exact conv_serie_comp_of_summable g bijg sumf

/- Sum of unconditional convergent series -/

theorem lim_of_comp_lim {Y: Type*} [NormedAddCommGroup Y]
  (f: ℕ → Y) (Rs: RSerie f) (x: Y) (g: ℕ → ℕ)
  (gbij: Bijective g) :
    (lim_serie (f ∘ g) x ↔ lim_serie f x) := by
      rw [RSerie_iff_Summable] at Rs
      rcases Rs with ⟨y, fhassumy⟩
      have fglimy := lim_serie_comp_of_hasnetsum g gbij y fhassumy
      have flimy := lim_serie_of_hasnetsum y fhassumy
      constructor
      · intro fglimx
        have : x = y := by
          unfold lim_serie at *
          exact net_unique_limit_of_T2' fglimx fglimy
        rwa [← this] at flimy
      · intro flimx
        have : x = y := by
          unfold lim_serie at *
          exact net_unique_limit_of_T2' flimx flimy
        rwa [← this] at fglimy

theorem unique_lim_RSerie {Y: Type*} [NormedAddCommGroup Y]
  (f: ℕ → Y) (Rs: RSerie f) (x: Y) :
    (∃ (g: ℕ → ℕ), Bijective g ∧ lim_serie (f ∘ g) x) →
    ∀ (g: ℕ → ℕ), Bijective g → lim_serie (f ∘ g) x := by
      intro cond
      rcases cond with ⟨g, bijg, fglimx⟩
      have limfx := (lim_of_comp_lim f Rs x g bijg).mp fglimx
      intro h bijh
      exact (lim_of_comp_lim f Rs x h bijh).mpr limfx

theorem Rserie_iff_bij_Rserie {Y: Type*} [NormedAddCommGroup Y]
  (f: ℕ → Y) (g: ℕ → ℕ) (gbij: Bijective g) :
    RSerie f ↔ RSerie (f ∘ g) := by
      constructor
      · intro Rsf
        intro h bijh
        rw [comp_assoc]
        exact Rsf (g ∘ h) (Function.Bijective.comp gbij bijh)
      · intro Rsfg
        intro h bijh
        have : Bijective (surjInv gbij.2) := by
          constructor
          · exact Function.injective_surjInv gbij.2
          · rw [Function.surjective_iff_hasRightInverse]
            use g
            exact Function.leftInverse_surjInv gbij
        have conv := Rsfg (surjInv gbij.2 ∘ h) (Function.Bijective.comp this bijh)
        have : g ∘ (surjInv gbij.2) = id := by
          ext n
          exact Function.surjInv_eq gbij.2 n
        rwa [← comp_assoc (f ∘ g), comp_assoc f, this, comp_id] at conv
