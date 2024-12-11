import FunctionalAnalysis.Convergence.Series
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option trace.Meta.Tactic.simp false

noncomputable section

open Set Filter Topology Function DirectedSet Net

variable {D: Type*} [DirectedSet D]

def InfLimit (s: D → ℝ) : Prop :=
  ∀ K > 0, ∃ (d₀: D), ∀ d ≥ d₀, s d > K

def mInfLimit (s: D → ℝ) : Prop :=
  ∀ K < 0, ∃ (d₀: D), ∀ d ≥ d₀, s d < K

theorem inflim_of_lim_zero (s: D → ℝ) (spos: ∃ (d₀: D), ∀ d ≥ d₀, s d > 0) :
  Limit s 0 ↔ InfLimit s⁻¹ := by
    constructor
    · intro limsz
      intro K Kpos
      rw [limit_metric_iff] at limsz
      rcases limsz K⁻¹ (inv_pos_of_pos Kpos) with ⟨d₁, eq⟩
      simp only [dist_eq_norm, sub_zero, Real.norm_eq_abs] at eq
      rcases spos with ⟨d₂, spos⟩
      rcases directed' d₁ d₂ with ⟨d₀, d₁led₀, d₂led₀⟩
      use d₀
      intro d d₀led
      simp only [Pi.inv_apply, lt_inv_comm₀ Kpos (spos d (le_trans d₂led₀ d₀led))]
      have := eq d (le_trans d₁led₀ d₀led)
      rw [abs_of_nonneg (le_of_lt (spos d (le_trans d₂led₀ d₀led)))] at this
      assumption
    · sorry

theorem Real_archimedean (x y : ℝ) : (0 < x) → ∃ (n : ℕ), y < n * x := by
  intro x_pos
  have := exists_lt_nsmul x_pos y
  simp only [nsmul_eq_mul] at this
  assumption

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


lemma finite_geo_sum {𝕂: Type*} [RCLike 𝕂] {r: 𝕂} (rneone: r ≠ 1): (fun N ↦ ∑ n ∈ Finset.Iic N, (fun n ↦ r ^ n) n) = (fun N ↦ (r^(N + 1) - 1)/(r - 1)) := by
  ext N
  induction' N with N ih
  · rw [Finset.sum_Iic_zero, pow_zero, zero_add, pow_one, div_self (sub_ne_zero_of_ne rneone)]
  · rw [Finset.sum_Iic_eq_sum_Ioc_add_Iic (Nat.le_add_right N 1), Nat.Ioc_succ_singleton, Finset.sum_singleton, ih]
    nth_rw 1 [← one_mul (r ^ (N + 1)), ← div_self (sub_ne_zero_of_ne rneone)]
    rw [← mul_div_right_comm, div_add_div_same, sub_mul, add_sub, sub_add, one_mul, sub_self, sub_zero, ← pow_succ']

theorem geo_sum {𝕂: Type} [RCLike 𝕂] {r: 𝕂} (rltone: ‖r‖ < 1): lim_serie (fun (n: ℕ) ↦ r^n) (1-r)⁻¹ := by
  unfold lim_serie
  have: r ≠ 1 := by
    by_contra reqone
    rw [reqone, norm_one] at rltone
    linarith
  rw [finite_geo_sum this]
  have := prod_num_conv (r/(r-1)) (limit_lessone_zero rltone)
  simp only [smul_eq_mul, div_mul_eq_mul_div, ← pow_succ', mul_zero] at this
  have sol := lim_of_sum_eq_sum_of_lim this (lim_of_cte (-1/(r-1)))
  simp only [div_add_div_same, zero_add, Mathlib.Tactic.RingNF.add_neg] at sol
  have : (-1/(r - 1)) = (1 - r)⁻¹ := by
    rw [inv_eq_one_div, neg_eq_neg_one_mul, mul_comm, ← div_mul_eq_mul_div, ← one_div_neg_one_eq_neg_one,
        div_mul_div_comm, mul_one, sub_mul, one_mul, mul_comm, ← neg_eq_neg_one_mul, neg_sub_neg]
  simp only [this] at sol
  exact sol

theorem geo_sum_inv {a: ℝ} (onelta: 1 < a): lim_serie (fun (n: ℕ) ↦ 1/(a^n)) (a/(a-1)) := by
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
