import Topology.Nets.Convergence

set_option trace.Meta.Tactic.simp false

noncomputable section

open Set Filter Topology Classical Function DirectedSet Net

/- ### Basic results ### -/

/- Characterization of summability in a normed space -/
theorem hassum_normed {I X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: I → X) (x: X):
  HasSum f x ↔ ∀ ε, 0 < ε → (∃ (F₀: Finset I), ∀ (F: Finset I), (F₀ ⊆ F → ‖(∑ i ∈ F, f i) - x‖ < ε)) := by
    rw [hassum_iff_hassumnet]
    unfold HasSumNet
    simp only [limit_metric_iff, dist_eq_norm, Finset.le_eq_subset]

/- Characterization of Cauchy condition for arbitrary family in a normed space -/
lemma Finset.inter_sdiff_subset {I: Type*} (A B C: Finset I) (h: C ⊆ B): C ∩ (A \ B) = ∅ := by
  have: C ∩ (A \ B) ⊆ B ∩ (A \ B) := by
    exact inter_subset_inter h (subset_refl (A \ B))
  rw [Finset.inter_sdiff_self, subset_empty] at this
  exact this

theorem cauchysum_normed {I X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: I → X):
  CauchySumNet f ↔ ∀ ε, 0 < ε → (∃ (F₀: Finset I), ∀ (F: Finset I), (F₀ ∩ F = ∅ → ‖∑ i ∈ F, f i‖ < ε)) := by
    unfold CauchySumNet
    simp only [cauchy_metric_iff, dist_eq_norm, Finset.le_eq_subset]
    constructor
    · intro h ε εpos
      rcases h ε εpos with ⟨F₀, eq⟩
      use F₀
      intro F FdisjF₀
      have := eq F₀ (F₀ ∪ F) (subset_refl F₀) Finset.subset_union_left
      rw [Finset.sum_union (Finset.disjoint_iff_inter_eq_empty.mpr FdisjF₀), sub_add_cancel_left, norm_neg] at this
      assumption
    · intro h ε εpos
      rcases h (ε/2) (half_pos εpos) with ⟨F₀, eq⟩
      use F₀
      intro F₁ F₂ F₀subF₁ F₀subF₂
      rw [← Finset.sdiff_union_inter F₂ F₁]
      nth_rw 1 [← Finset.sdiff_union_inter F₁ F₂]
      rw [Finset.sum_union (Finset.disjoint_sdiff_inter F₁ F₂), Finset.sum_union (Finset.disjoint_sdiff_inter F₂ F₁),
          add_comm (∑ x ∈ F₂ \ F₁, f x) _, ← sub_sub, ← add_sub, ← add_sub, Finset.inter_comm F₂ F₁, sub_self, zero_sub]
      calc
        ‖∑ x ∈ F₁ \ F₂, f x + -∑ x ∈ F₂ \ F₁, f x‖ ≤ ‖∑ x ∈ F₁ \ F₂, f x‖ + ‖-∑ x ∈ F₂ \ F₁, f x‖ := by
          exact norm_add_le (∑ x ∈ F₁ \ F₂, f x) (-∑ x ∈ F₂ \ F₁, f x)
        _ = ‖∑ x ∈ F₁ \ F₂, f x‖ + ‖∑ x ∈ F₂ \ F₁, f x‖ := by
          rw [norm_neg]
        _ < ε/2 + ‖∑ x ∈ F₂ \ F₁, f x‖ := by
          rw [add_lt_add_iff_right]
          exact eq (F₁ \ F₂) (Finset.inter_sdiff_subset F₁ F₂ F₀ F₀subF₂)
        _ < ε/2 + ε/2 := by
          rw [add_lt_add_iff_left]
          exact eq (F₂ \ F₁) (Finset.inter_sdiff_subset F₂ F₁ F₀ F₀subF₁)
        _ = ε := by
          norm_num

/- Characterization of absolute summability -/
theorem cauchysum_implies_bounded {I X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: I → X):
  CauchySumNet f → BddAbove {α: ℝ | ∃ (F: Finset I), α = ‖∑ (i ∈ F), f i‖} := by
    intro cauchyf
    rw [cauchysum_normed 𝕂] at cauchyf
    rcases cauchyf 1 zero_lt_one with ⟨F₀, eq⟩
    use 1 + ∑ i ∈ F₀, ‖f i‖
    rw [mem_upperBounds]
    intro α αin
    rw [Set.mem_setOf_eq] at αin
    rcases αin with ⟨F, αeq⟩
    rw [αeq]
    calc
      ‖∑ i ∈ F, f i‖ = ‖∑ i ∈ F \ F₀, f i + ∑ i ∈ F ∩ F₀, f i‖ := by
        apply congr_arg
        rw [← Finset.sum_union (Finset.disjoint_sdiff_inter F F₀), Finset.sdiff_union_inter]
      _ ≤ ‖∑ i ∈ F \ F₀, f i‖ + ‖∑ i ∈ F ∩ F₀, f i‖ := by
        exact norm_add_le (∑ i ∈ F \ F₀, f i) (∑ i ∈ F ∩ F₀, f i)
      _ ≤ 1 + ‖∑ i ∈ F ∩ F₀, f i‖ := by
        apply add_le_add_right
        apply le_of_lt
        exact eq (F \ F₀) (Finset.inter_sdiff_subset F F₀ F₀ subset_rfl)
      _ ≤ 1 + ∑ i ∈ F ∩ F₀, ‖f i‖ := by
        apply add_le_add_left
        exact norm_sum_le (F ∩ F₀) f
      _ ≤ 1 + ∑ i ∈ F₀, ‖f i‖ := by
        apply add_le_add_left
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro i iinF₀ inotininter
        exact norm_nonneg (f i)

lemma sum_of_norms_eq_abs_of_sum {I X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: I → X):
    {α | ∃ F, α = ∑ i ∈ F, ‖f i‖} = {α | ∃ F, α = |∑ i ∈ F, ‖f i‖|} := by
      ext α
      simp only [Set.mem_setOf_eq]
      constructor
      · intro eq
        rcases eq with ⟨F, αeq⟩
        use F
        rw [αeq]
        apply (abs_of_nonneg _).symm
        apply Finset.sum_nonneg
        intro i iinF
        exact norm_nonneg (f i)
      · intro eq
        rcases eq with ⟨F, αeq⟩
        use F
        rw [αeq]
        apply (abs_of_nonneg _)
        apply Finset.sum_nonneg
        intro i iinF
        exact norm_nonneg (f i)

theorem hasabssum_implies_bounded {I X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: I → X):
  AbsSummable 𝕂 f →  BddAbove {α: ℝ | ∃ (F: Finset I), α = ∑ (i ∈ F), ‖f i‖} := by
    intro fabssum
    have fcauchy : CauchyNet (fun (E: Finset I) ↦ ∑ e ∈ E, ‖f e‖):= by
      apply conv_implies_cauchy
      exact fabssum
    have h := cauchysum_implies_bounded ℝ (fun (i: I) ↦ ‖f i‖) fcauchy
    simp only [Real.norm_eq_abs] at h
    rw [sum_of_norms_eq_abs_of_sum 𝕂]
    assumption

theorem bddabv_impls_LUB_eq_sum {I X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: I → X):
  BddAbove {α: ℝ | ∃ (F: Finset I), α = ∑ (i ∈ F), ‖f i‖} → HasAbsSum 𝕂 f (sSup {α: ℝ | ∃ (F: Finset I), α = ∑ (i ∈ F), ‖f i‖}) := by
    intro bddab
    have : {α | ∃ F, α = ∑ i ∈ F, ‖f i‖}.Nonempty := by
      use 0
      rw [Set.mem_setOf_eq]
      use ∅
      rfl
    rcases Real.exists_isLUB this bddab with ⟨α, αLUB⟩
    have αeqssup : α = sSup {α: ℝ | ∃ (F: Finset I), α = ∑ (i ∈ F), ‖f i‖} := by
      exact (IsLUB.csSup_eq αLUB this).symm
    rw [← αeqssup]
    have αlimitf : HasAbsSum 𝕂 f α := by
      unfold HasAbsSum
      rw [← hassum_iff_hassumnet ,hassum_normed ℝ]
      intro ε εpos
      rcases exists_lt_LUB αLUB ε εpos with ⟨a, ain, αminusεlta⟩
      rw [Set.mem_setOf_eq] at ain
      rcases ain with ⟨F₀, aeq⟩
      use F₀
      intro F F₀subF
      rw [Real.norm_eq_abs, abs_sub_lt_iff]
      have sumleα : ∑ i ∈ F, ‖f i‖ ≤ α := by
        have := αLUB.1
        rw [mem_upperBounds] at this
        exact this (∑ i ∈ F, ‖f i‖) (by use F)
      constructor
      · rw [sub_lt_iff_lt_add]
        exact lt_of_le_of_lt sumleα (lt_add_of_pos_left α εpos)
      · rw [sub_lt_iff_lt_add', ← sub_lt_iff_lt_add]
        calc
          α - ε < ∑ i ∈ F₀, ‖f i‖ := by
            rw [← aeq]
            assumption
          _ ≤ ∑ i ∈ F, ‖f i‖ := by
            apply Finset.sum_le_sum_of_subset_of_nonneg F₀subF
            intro i iinF inotinF₀
            exact norm_nonneg (f i)
    assumption

theorem abssum_eq_LUB {I X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: I → X):
  AbsSummable 𝕂 f → HasAbsSum 𝕂 f (sSup {α: ℝ | ∃ (F: Finset I), α = ∑ (i ∈ F), ‖f i‖}) := by
    intro abssumf
    exact bddabv_impls_LUB_eq_sum 𝕂 f (hasabssum_implies_bounded 𝕂 f abssumf)

theorem hasabssum_normed {I X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: I → X):
  AbsSummable 𝕂 f ↔ BddAbove {α: ℝ | ∃ (F: Finset I), α = ∑ (i ∈ F), ‖f i‖} := by
    constructor
    · exact hasabssum_implies_bounded 𝕂 f
    · intro bddab
      use sSup {α: ℝ | ∃ (F: Finset I), α = ∑ (i ∈ F), ‖f i‖}
      exact bddabv_impls_LUB_eq_sum 𝕂 f bddab

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

lemma le_crec_recursive (s: ℕ → ℕ): ∀ (n: ℕ),  s n ≤ crec_recursive s n := by
  intro n
  induction' n with n ih
  · unfold crec_recursive
    rfl
  · unfold crec_recursive
    exact Nat.le_max_left (s (n + 1)) (crec_recursive s n + 1)

lemma crec_recursive_incr (s: ℕ → ℕ): ∀ (n: ℕ),  (crec_recursive s n) < crec_recursive s (n + 1) := by
  intro n
  dsimp only [crec_recursive]
  calc
    crec_recursive s n < (crec_recursive s n) + 1 := by
      exact lt_add_one (crec_recursive s n)
    _ ≤ s (n + 1) ⊔ (crec_recursive s n + 1) := by
      exact Nat.le_max_right (s (n + 1)) (crec_recursive s n + 1)

theorem complete_series_normed {X 𝕂: Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]:
  CompleteSpace X ↔ ∀ (f: ℕ → X), conv_abs_serie 𝕂 f → conv_serie f := by
    constructor
    · sorry
    · intro absimpconv
      rw [Metric.complete_iff]
      intro s scauchy
      let F: ℕ → ℕ := seqfromnet s (fun (k: ℕ) ↦ 1/(2^k))
      let y: ℕ → X := fun n ↦ s (F (n + 1)) - s (F n)
      have : ∀ (k: ℕ), ‖y k‖ < 1/(2^k) := by
        intro k
        rw [← dist_eq_norm, dist_comm]
        exact seqfromnet_cond s (fun (k: ℕ) ↦ 1/(2^k)) (by norm_num) scauchy k (F k) (F (k + 1)) (by rfl)
          (seqfromnet_incr s (fun (k: ℕ) ↦ 1/(2^k)) (by norm_num) scauchy (by linarith))
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
