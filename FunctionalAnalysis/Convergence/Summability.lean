import Topology.Nets.Summability
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Analysis.Normed.Module.FiniteDimension

set_option trace.Meta.Tactic.simp false

noncomputable section

open Set Filter Topology Function DirectedSet Net

variable {I X: Type*} [SeminormedAddCommGroup X]
variable {Y: Type*} [NormedAddCommGroup Y] [NormedSpace ℝ Y]
variable {Z: Type*} [NormedAddCommGroup Z]

/- ### Basic results about summability ### -/

/- Characterization of summability in a normed space -/
theorem hassumnet_eps (f: I → X) (x: X):
  HasSumNet f x ↔
  ∀ ε > 0, (∃ F₀, ∀ (F: Finset I),
  (F₀ ⊆ F → ‖(∑ i ∈ F, f i) - x‖ < ε)) := by
    unfold HasSumNet
    simp only [limit_metric_iff, dist_eq_norm, Finset.le_eq_subset]

theorem cauchynet_finset_iff_vanishing_norm (f: I → X):
  CauchySumNet f ↔ ∀ ε > 0, ∃ s, ∀ (t : Finset I),
  Disjoint t s → ‖∑ i ∈ t, f i‖ < ε := by
    unfold CauchySumNet
    rw [← cauchySeq_iff_cauchynet (fun E ↦ ∑ e ∈ E, f e)]
    rw [cauchySeq_finset_iff_vanishing_norm]

theorem netsummable_iff_cauchNet_finset [CompleteSpace X] {f: I → X}:
  SummableNet f ↔ CauchySumNet f := by
    unfold CauchySumNet
    rw [← cauchySeq_iff_cauchynet (fun E ↦ ∑ e ∈ E, f e),
        ← summable_iff_summablenet, summable_iff_cauchySeq_finset]

/- ### Definition of absolute summability ### -/

/- We say that a function f: I → X is summable if the net of sums over finite sets of I converges -/

def HasAbsSum (f: I → X) (t: ℝ): Prop :=
  HasSumNet (fun (i: I) ↦ ‖f i‖) t

def AbsSummable (f: I → X): Prop :=
  ∃ (t: ℝ), HasAbsSum f t

/- ### Characterization of absolute summability ### -/

/- Relation with HasSum and Summable -/
theorem hasabssum_iff_hassum_abs (f: I → X) (t: ℝ) :
  HasAbsSum f t ↔ HasSum (fun (i: I) ↦ ‖f i‖) t := by
    unfold HasAbsSum
    rw [hassum_iff_hassumnet]

theorem abssummable_iff_summable_abs (f: I → X) :
  AbsSummable f ↔ Summable (fun (i: I) ↦ ‖f i‖) := by
    unfold AbsSummable Summable HasAbsSum
    simp only [hassum_iff_hassumnet]

/- Characterization of absolute summability -/
theorem bounded_of_cauchyNet_finset
  (f: I → X):
  CauchySumNet f → BddAbove {α: ℝ | ∃ (F: Finset I), α = ‖∑ (i ∈ F), f i‖} := by
    classical
    intro cauchyf
    rw [cauchynet_finset_iff_vanishing_norm] at cauchyf
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
        rw [← Finset.sum_union (Finset.disjoint_sdiff_inter F F₀),
            Finset.sdiff_union_inter]
      _ ≤ ‖∑ i ∈ F \ F₀, f i‖ + ‖∑ i ∈ F ∩ F₀, f i‖ := by
        exact norm_add_le (∑ i ∈ F \ F₀, f i) (∑ i ∈ F ∩ F₀, f i)
      _ ≤ 1 + ‖∑ i ∈ F ∩ F₀, f i‖ := by
        apply add_le_add_right
        apply le_of_lt
        exact eq (F \ F₀) (Finset.sdiff_disjoint)
      _ ≤ 1 + ∑ i ∈ F ∩ F₀, ‖f i‖ := by
        apply add_le_add_left
        exact norm_sum_le (F ∩ F₀) f
      _ ≤ 1 + ∑ i ∈ F₀, ‖f i‖ := by
        apply add_le_add_left
        apply Finset.sum_le_sum_of_subset_of_nonneg Finset.inter_subset_right
        intro i iinF₀ inotininter
        exact norm_nonneg (f i)

lemma sum_of_norms_eq_abs_of_sum (f: I → X):
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

theorem bounded_of_abssummable (f: I → X):
  AbsSummable f →  BddAbove {α: ℝ | ∃ (F: Finset I), α = ∑ (i ∈ F), ‖f i‖} := by
    intro fabssum
    have fcauchy : CauchyNet (fun (E: Finset I) ↦ ∑ e ∈ E, ‖f e‖):= by
      apply cauchy_of_exists_lim
      exact fabssum
    have h := bounded_of_cauchyNet_finset (fun (i: I) ↦ ‖f i‖) fcauchy
    simp only [Real.norm_eq_abs] at h
    rw [sum_of_norms_eq_abs_of_sum]
    assumption

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

theorem hasabssum_eq_LUB_of_bounded
  (f: I → X):
  BddAbove {α: ℝ | ∃ (F: Finset I), α = ∑ (i ∈ F), ‖f i‖} →
  HasAbsSum f (sSup {α: ℝ | ∃ (F: Finset I), α = ∑ (i ∈ F), ‖f i‖}) := by
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
    have αlimitf : HasAbsSum f α := by
      unfold HasAbsSum
      rw [hassumnet_eps]
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

theorem hasabssum_eq_LUB_of_abssummable (f: I → X):
  AbsSummable f →
  HasAbsSum f (sSup {α: ℝ | ∃ (F: Finset I), α = ∑ (i ∈ F), ‖f i‖}) := by
    intro abssumf
    exact hasabssum_eq_LUB_of_bounded f (bounded_of_abssummable f abssumf)

theorem abssummable_iff_bounded (f: I → X):
  AbsSummable f ↔ BddAbove {α: ℝ | ∃ (F: Finset I), α = ∑ (i ∈ F), ‖f i‖} := by
    constructor
    · exact bounded_of_abssummable f
    · intro bddab
      use sSup {α: ℝ | ∃ (F: Finset I), α = ∑ (i ∈ F), ‖f i‖}
      exact hasabssum_eq_LUB_of_bounded f bddab

/- ### Relation between absolute summability and summability -/

theorem cauchyabssum_iff_abssummable (f: I → X) [CompleteSpace X]:
  AbsSummable f ↔ CauchySumNet (fun (i: I) ↦ ‖f i‖) := by
    unfold AbsSummable HasAbsSum
    exact netsummable_iff_cauchNet_finset

theorem summable_of_abssummable [CompleteSpace X] (f: I → X):
  AbsSummable f → SummableNet f := by
    rw [cauchyabssum_iff_abssummable, summable_iff_cauchysum,
        cauchynet_finset_iff_vanishing_norm,
        cauchynet_finset_iff_vanishing_norm]
    intro cauchysum ε εpos
    rcases cauchysum ε εpos with ⟨F₀, eq⟩
    simp only [Real.norm_of_nonneg
      (Finset.sum_nonneg (fun i x ↦ norm_nonneg (f i)))] at eq
    use F₀
    intro F interem
    calc
      ‖∑ i ∈ F, f i‖ ≤ ∑ i ∈ F, ‖f i‖ := by
        exact norm_sum_le F f
      _ < ε := by
        exact eq F interem

/- ### Comparation test for summability ### -/

theorem summablenet_of_norm_bounded [CompleteSpace X]
  {f : I → X} (g : I → ℝ) (hg : SummableNet g) (h : ∀ (i : I), ‖f i‖ ≤ g i) :
  SummableNet f := by
    simp only [← summable_iff_summablenet] at *
    exact Summable.of_norm_bounded g hg h

theorem abssummable_of_norm_bounded
  {f : I → X} (g : I → ℝ) (hg : SummableNet g) (h : ∀ (i : I), ‖f i‖ ≤ g i) :
  AbsSummable f := by
    rw [abssummable_iff_summable_abs, summable_iff_summablenet]
    have : ∀ (i : I), ‖‖f i‖‖ ≤ g i := by
      intro i
      rw [norm_norm]
      exact h i
    exact summablenet_of_norm_bounded g hg this

/- ### Equivalence of summable and absolute summable in finite dimensional spaces ### -/

theorem summablenet_iff_abssummable [FiniteDimensional ℝ Y] (f: I → Y) :
  SummableNet f ↔ AbsSummable f := by
    rw [← summable_iff_summablenet, abssummable_iff_summable_abs]
    exact summable_norm_iff.symm

/- ### Operations on absolute summable families ### -/

theorem abssum_sum {f : J → I → X} {s : Finset J} :
  (∀ j ∈ s, AbsSummable (f j)) →
  AbsSummable (fun (i : I) => ∑ j ∈ s, f j i) := by
    intro abssum
    have : SummableNet fun i ↦ ∑ j ∈ s, ‖f j i‖ := by
      simp only [abssummable_iff_summable_abs, summable_iff_summablenet] at abssum
      exact summablenet_sum abssum
    apply abssummable_of_norm_bounded _ this
    intro i
    exact norm_sum_le s (fun j ↦ f j i)

theorem abssum_add {f g: I → X} :
  AbsSummable f → AbsSummable g → AbsSummable (fun (i : I) => f i + g i) := by
    intro abssumf abssumg
    have : SummableNet fun i ↦ ‖f i‖ + ‖g i‖ := by
      simp only [abssummable_iff_summable_abs, summable_iff_summablenet] at *
      exact summablenet_add abssumf abssumg
    apply abssummable_of_norm_bounded _ this
    intro i
    exact norm_add_le (f i) (g i)

theorem hasabssum_const_smul (𝕜: Type*) [NontriviallyNormedField 𝕜]
 [NormedSpace 𝕜 X] {f : I → X} (r : 𝕜) (t: ℝ) :
  HasAbsSum f t → HasAbsSum (fun (i: I) ↦ r • (f i)) (‖r‖ * t) := by
    simp only [hasabssum_iff_hassum_abs, hassum_iff_hassumnet, norm_smul,
               ← smul_eq_mul]
    exact hassumnet_const_smul ‖r‖

theorem abssum_const_smul (𝕜: Type*) [NontriviallyNormedField 𝕜]
 [NormedSpace 𝕜 X] {f : I → X} (r : 𝕜) :
    AbsSummable f → AbsSummable (fun (i: I) ↦ r • (f i)) := by
      simp only [abssummable_iff_summable_abs, norm_smul, summable_iff_summablenet,
                 ← smul_eq_mul]
      exact summablenet_const_smul ‖r‖
