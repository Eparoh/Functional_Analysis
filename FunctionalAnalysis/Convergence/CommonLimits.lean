import FunctionalAnalysis.Convergence.Series
import Mathlib.Analysis.SpecialFunctions.Log.Basic

set_option trace.Meta.Tactic.simp false

noncomputable section

open Set Filter Topology Function DirectedSet Net

variable {D: Type*} [DirectedSet D]
variable {𝕂: Type*} [RCLike 𝕂]

/- ### Infinite limits ### -/

def InftLimit (s: D → ℝ) : Prop :=
  ∀ K > 0, ∃ (d₀: D), ∀ d ≥ d₀, s d > K

def mInftLimit (s: D → ℝ) : Prop :=
  ∀ K < 0, ∃ (d₀: D), ∀ d ≥ d₀, s d < K

lemma InftLimit_iff_mInftLimit_neg (s: D → ℝ) :
  InftLimit s ↔ mInftLimit (-s) := by
    unfold InftLimit mInftLimit
    simp only [Pi.neg_apply, neg_lt]
    constructor
    · intro cond K Kneg
      rcases cond (-K) (Left.neg_pos_iff.mpr Kneg) with ⟨d₀, eq⟩
      use d₀
    · intro cond K Kpos
      rcases cond (-K) (Left.neg_neg_iff.mpr Kpos) with ⟨d₀, eq⟩
      use d₀
      rwa [neg_neg] at eq

lemma mInftLimit_iff_InftLimit_neg (s: D → ℝ) :
  mInftLimit s ↔ InftLimit (-s) := by
    nth_rw 1 [← neg_neg s]
    exact (InftLimit_iff_mInftLimit_neg (-s)).symm

theorem inftlim_iff_lim_zero (s: D → ℝ) (spos: ∃ (d₀: D), ∀ d ≥ d₀, s d > 0) :
  Limit s 0 ↔ InftLimit s⁻¹ := by
    rw [limit_metric_iff]
    constructor
    · intro limsz
      intro K Kpos
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
    · intro liminft ε εpos
      simp only [dist_zero_right, Real.norm_eq_abs]
      rcases liminft ε⁻¹ (inv_pos_of_pos εpos) with ⟨d₁, eq⟩
      rcases spos with ⟨d₂, spos⟩
      rcases directed' d₁ d₂ with ⟨d₀, d₁led₀, d₂led₀⟩
      use d₀
      intro d d₀led
      rw [abs_of_nonneg (le_of_lt (spos d (le_trans d₂led₀ d₀led))),
          ← inv_lt_inv₀ εpos (spos d (le_trans d₂led₀ d₀led))]
      exact eq d (le_trans d₁led₀ d₀led)

/- ### Common limits ### -/

theorem limit_inv : ∀ (a: ℝ), Limit (fun (n: ℕ) ↦ (n + a)⁻¹) 0 := by
  intro a
  rw [inftlim_iff_lim_zero]
  · intro K Kpos
    use Nat.ceil (K + 1 - a)
    intro d dge
    rw [Pi.inv_apply, inv_inv, gt_iff_lt]
    rw [ge_iff_le, Nat.ceil_le, tsub_le_iff_right] at dge
    exact lt_of_lt_of_le (lt_add_one K) dge
  · simp only [ge_iff_le, gt_iff_lt, inv_pos]
    use Nat.ceil (1 - a)
    intro n len
    rw [Nat.ceil_le, tsub_le_iff_right] at len
    exact lt_of_lt_of_le (Real.zero_lt_one) len

theorem limit_pow_lt_one {r: 𝕂} (rltone: ‖r‖ < 1):
  Limit (fun (n: ℕ) ↦ r^n) 0 := by
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
      · rw [← Real.log_lt_log_iff (pow_pos (norm_pos_iff.mpr h') n) εpos,
            Real.log_pow, ← div_lt_iff_of_neg]
        · calc
            Real.log ε / Real.log ‖r‖ < ⌊Real.log ε / Real.log ‖r‖⌋₊ + 1 := by
              exact Nat.lt_floor_add_one (Real.log ε / Real.log ‖r‖)
            _ ≤ n := by
              norm_cast
        · rw [Real.log_neg_iff]
          · exact rltone
          · exact norm_pos_iff.mpr h'

theorem limit_pow_lt_one' {a: ℝ} (onelta: 1 < a):
  Limit (fun (n: ℕ) ↦ 1/(a^n)) 0 := by
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
    exact limit_pow_lt_one this

/- ### Common series ### -/

lemma finite_geo_sum {r: 𝕂} (rneone: r ≠ 1):
  (fun N ↦ ∑ n ∈ Finset.Iic N, (fun n ↦ r ^ n) n) =
  (fun N ↦ (r^(N + 1) - 1)/(r - 1)) := by
    ext N
    induction' N with N ih
    · rw [Finset.sum_Iic_zero, pow_zero, zero_add, pow_one,
          div_self (sub_ne_zero_of_ne rneone)]
    · rw [Finset.sum_Iic_eq_sum_Ioc_add_Iic (Nat.le_add_right N 1),
          Nat.Ioc_succ_singleton, Finset.sum_singleton, ih]
      nth_rw 1 [← one_mul (r ^ (N + 1)), ← div_self (sub_ne_zero_of_ne rneone)]
      rw [← mul_div_right_comm, div_add_div_same, sub_mul, add_sub, sub_add,
          one_mul, sub_self, sub_zero, ← pow_succ']

theorem geo_sum {r: 𝕂} (rltone: ‖r‖ < 1):
  lim_serie (fun (n: ℕ) ↦ r^n) (1-r)⁻¹ := by
    unfold lim_serie
    have: r ≠ 1 := by
      by_contra reqone
      rw [reqone, norm_one] at rltone
      linarith
    rw [finite_geo_sum this]
    have := prod_num_conv (r/(r-1)) (limit_pow_lt_one rltone)
    simp only [smul_eq_mul, div_mul_eq_mul_div, ← pow_succ', mul_zero] at this
    have sol := lim_of_sum_eq_sum_of_lim this (lim_of_cte (-1/(r-1)))
    simp only [div_add_div_same, zero_add, Mathlib.Tactic.RingNF.add_neg] at sol
    have : (-1/(r - 1)) = (1 - r)⁻¹ := by
      rw [inv_eq_one_div, neg_eq_neg_one_mul, mul_comm, ← div_mul_eq_mul_div,
          ← one_div_neg_one_eq_neg_one, div_mul_div_comm, mul_one, sub_mul,
          one_mul, mul_comm, ← neg_eq_neg_one_mul, neg_sub_neg]
    simp only [this] at sol
    exact sol

theorem geo_sum_inv {a: ℝ} (onelta: 1 < a):
  lim_serie (fun (n: ℕ) ↦ 1/(a^n)) (a/(a-1)) := by
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
