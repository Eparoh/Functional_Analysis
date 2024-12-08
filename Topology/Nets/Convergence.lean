import Topology.Nets.Theorems
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option trace.Meta.Tactic.simp false

noncomputable section

open Set Filter Topology Function DirectedSet

namespace Net

/- ### Archimedean property ### -/

theorem Real_archimedean (x y : ℝ) : (0 < x) → ∃ (n : ℕ), y < n * x := by
  intro x_pos
  have := exists_lt_nsmul x_pos y
  simp only [nsmul_eq_mul] at this
  assumption


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
        · exact norm_pos_iff.mpr h'

theorem limit_lessone_zero_inv {a: ℝ} (onelta: 1 < a): Limit (fun (n: ℕ) ↦ 1/(a^n)) 0 := by
  have: (fun (n: ℕ) ↦ 1/(a^n)) = (fun (n: ℕ) ↦ (1/a)^n) := by
    ext n
    norm_num
  rw [this]
  have: ‖1/a‖ < 1 := by
    rw [Real.norm_eq_abs]
    have : 1 < |a| := by
      exact lt_of_lt_of_le onelta (le_abs_self a)
    rw [← mul_lt_mul_right (lt_trans zero_lt_one this), abs_one_div, one_mul, one_div_mul_cancel]
    · assumption
    · linarith
  exact limit_lessone_zero this

lemma Finset.sum_Iic_zero {X: Type*} [AddCommMonoid X] (f: ℕ → X): ∑ n ≤ 0, f n = f 0 := by
  have : Finset.Iic 0 = {0} := by
    rfl
  rw [this]
  exact Finset.sum_singleton f 0



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
    · exact (shift_subsequence_conv g 1).mp limitg
    · exact limit_cte (g 0)

theorem telescopic_conv {X: Type*} [AddCommGroup X] [TopologicalSpace X] [TopologicalAddGroup X] {f g: ℕ → X}
  (tlsc: ∀ (n: ℕ), f n = g (n + 1) - g n) {x: X} (limitg: Limit g x): conv_serie f := by
    use x - g 0
    exact telescopic_conv_to tlsc limitg

theorem conv_telescopic_to {X: Type*} [AddCommGroup X] [TopologicalSpace X] [TopologicalAddGroup X] (f g: ℕ → X)
  (tlsc: ∀ (n: ℕ), f n = g (n + 1) - g n) {x: X} (fconvx: conv_serie_to f x): Limit g (x + g 0) := by
    unfold conv_serie_to at fconvx
    simp only [tlsc, Finset.sum_Iic_telescopic] at fconvx
    rw [shift_subsequence_conv g 1]
    have : (fun n ↦ g (n + 1)) = (fun N ↦ g (N + 1) - g 0) + ((fun N ↦ g 0)) := by
      ext n
      rw [Pi.add_apply, sub_add, sub_self, sub_zero]
    rw [this]
    apply sum_conv
    · exact fconvx
    · exact limit_cte (g 0)

theorem conv_telescopic {X: Type*} [AddCommGroup X] [TopologicalSpace X] [TopologicalAddGroup X] (f g: ℕ → X)
  (tlsc: ∀ (n: ℕ), f n = g (n + 1) - g n) (fconv: conv_serie f): ∃ (x: X), Limit g x := by
    rcases fconv with ⟨x, eq⟩
    use x + g 0
    exact conv_telescopic_to f g tlsc eq
