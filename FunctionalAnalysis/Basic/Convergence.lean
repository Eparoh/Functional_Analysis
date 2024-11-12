import Topology.Nets.Convergence

set_option trace.Meta.Tactic.simp false

noncomputable section

open Set Filter Topology Classical Function DirectedSet Net

/- ### Basic results ### -/

/- Characterization of convergence of a series in a normed space -/
theorem conv_serie_normed {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) (x: X):
  conv_serie_to f x ↔ ∀ ε, 0 < ε → (∃ (n₀: ℕ), ∀ (n: ℕ), (n₀ ≤ n → ‖(∑ i ≤ n, f i) - x‖ < ε)) := by
    unfold conv_serie_to Limit
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

lemma Finset.sum_Iic_sub_Iic_eq_sum_Ioc {M: Type*} [AddCommGroup M] {f : ℕ → M} {n m : ℕ}
  (h : n ≤ m) : ∑ i ∈ Finset.Iic m, f i - ∑ i ∈ Finset.Iic n, f i = ∑ i ∈ Finset.Ioc n m, f i := by
    rw [sub_eq_iff_eq_add]
    exact Finset.sum_Iic_eq_sum_Ioc_add_Iic h

theorem cauchy_serie_normed {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X):
  CauchySerie f ↔ ∀ ε, 0 < ε → (∃ (n₀: ℕ), ∀ (n m: ℕ), (n₀ ≤ n → n ≤ m → ‖(∑ i ∈ Finset.Ioc n m, f i)‖ < ε)) := by
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

/- Characterization of summability in a normed space -/
theorem hassum_normed {I X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: I → X) (x: X):
  HasSum f x ↔ ∀ ε, 0 < ε → (∃ (F₀: Finset I), ∀ (F: Finset I), (F₀ ⊆ F → ‖(∑ i ∈ F, f i) - x‖ < ε)) := by
    sorry

/- Characterization of Cauchy condition for arbitrary family in a normed space -/
theorem cauchysum_normed {I X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: I → X):
  CauchySumNet f ↔ ∀ ε, 0 < ε → (∃ (F₀: Finset I), ∀ (F: Finset I), (F₀ ∩ F = ∅ → ‖∑ i ∈ F, f i‖ < ε)) := by
    sorry

theorem abs_conv_implies_summable {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X): conv_abs_serie 𝕂 f → Summable f := by
    intro fconvabs
    rcases fconvabs with ⟨t, fconvabst⟩
    unfold conv_abs_serie_to at fconvabst
    simp only [conv_serie_normed ℝ, Real.norm_eq_abs] at fconvabst
    rw [summable_iff_summablenet]
    sorry

/- ### Constructions ### -/

/- ### Characterization of completeness in term of absolute convergence -/

def crec_recursive (s: ℕ → ℕ): ℕ → ℕ
  | 0 => s 0
  | n + 1 => max (s (n + 1)) ((crec_recursive s n) + 1)

lemma aux (s: ℕ → ℕ): ∀ (n: ℕ),  s n ≤ crec_recursive s n := by
  sorry

lemma aux' (s: ℕ → ℕ): ∀ (n: ℕ),  (crec_recursive s n) < crec_recursive s (n + 1) := by
  sorry

theorem complete_series_normed {X 𝕂: Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]:
  CompleteSpace X ↔ ∀ (f: ℕ → X), conv_abs_serie 𝕂 f → conv_serie f := by
    constructor
    · sorry
    · intro absimpconv
      rw [Metric.complete_iff]
      intro s scauchy
      have cauchycond : ∀ (k: ℕ), ∃ (n₀: ℕ), ∀ (n m : ℕ), (n₀ ≤ n → n₀ ≤ m → ‖s n - s m‖ < 1/(2^k)) := by
        intro k
        rw [Net.cauchy_metric_iff] at scauchy
        have := scauchy (1/(2^k)) (by norm_num)
        simp only [dist_eq_norm] at this
        exact this
      let F': ℕ → ℕ := fun k ↦ if h: ∃ (n₀: ℕ), ∀ (n m : ℕ), (n₀ ≤ n → n₀ ≤ m → ‖s n - s m‖ < 1/(2^k)) then Classical.choose h else 0
      let F: ℕ → ℕ := crec_recursive F'
      have : ∀ (k: ℕ), ‖s (F (k +1)) - s (F k)‖ < 1/(2^k) := by
        intro k
        have F'keqchoose : ∀ (k: ℕ), F' k = Classical.choose (cauchycond k) := by
          intro k
          dsimp only [F']
          rw [dif_pos (cauchycond k)]
        have := Classical.choose_spec (cauchycond k)
        rw [← F'keqchoose k] at this
        have leF : F' k ≤ F (k + 1) := by
          calc
            F' k ≤ F k := by
              exact aux F' k
            _ ≤ F (k + 1) := by
              have:= aux' F' k
              rw [lt_iff_le_and_ne] at this
              exact this.1
        exact this (F (k + 1)) (F k) leF (aux F' k)
      let y: ℕ → X := fun n ↦ s (F (n + 1)) - s (F n)
      have yconvabs : conv_abs_serie 𝕂 y := by
        sorry
      have yconv := absimpconv y yconvabs
      have yeqsubseq : (fun (N: ℕ) ↦ ∑ n ≤ N, y n) = s ∘ (F ∘ (fun (n : ℕ) ↦ n + 1)) := by
        sorry
      unfold conv_serie conv_serie_to at yconv
      simp only [yeqsubseq] at yconv
      have lemafuera : (∃ (f: ℕ → ℕ), StrictMono f ∧ ∃ (x: X), Limit (s ∘ f) x) → ∃ (x: X), Limit s x := by
        sorry
      have Fstricmono : StrictMono (F ∘ (fun (n : ℕ) ↦ n + 1)) := by
        sorry
      exact lemafuera (by use ((F ∘ fun n ↦ n + 1)))
