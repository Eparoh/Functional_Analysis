import Topology.Nets.Theorems
import Mathlib.Topology.Algebra.InfiniteSum.Group
import Mathlib.Topology.Algebra.InfiniteSum.Module

noncomputable section

set_option trace.Meta.Tactic.simp false

open Set Filter Topology Function DirectedSet

namespace Net

variable {I J X: Type*} [AddCommMonoid X] [TopologicalSpace X]
variable {Z: Type*} [AddCommMonoid Z] [UniformSpace Z]
variable {W: Type*} [AddCommGroup W] [UniformSpace W]
variable {U: Type*} [UniformSpace U]

/- ### Definitions ### -/

def HasSumNet (f: I → X) (x: X): Prop :=
   Limit (fun (E: Finset I) ↦ ∑ e ∈ E, f e) x

def SummableNet (f: I → X): Prop :=
   ∃ (x: X), HasSumNet f x

def CauchySumNet (f: I → Z): Prop :=
   CauchyNet (fun (E: Finset I) ↦ ∑ e ∈ E, f e)

/- ### Summable = NetSummable ### -/

/- A function is summable iff it is net summable -/
theorem hassum_iff_hassumnet (f: I → X) (x: X) :
  HasSum f x ↔ HasSumNet f x := by
    unfold HasSum HasSumNet Limit
    simp only [tendsto_nhds, Filter.mem_atTop_sets,
               Finset.le_eq_subset, Set.mem_preimage, ge_iff_le]
    constructor
    · intro fhsum
      intro U Unhds
      rw [mem_nhds_iff] at Unhds
      rcases Unhds with ⟨V, VsubU, Vopen, xinV⟩
      rcases fhsum V Vopen xinV with ⟨d₀, eq⟩
      use d₀
      intro d d₀subd
      apply VsubU
      exact eq d d₀subd
    · intro fhsumnet
      intro U Uopen xinU
      exact fhsumnet U (by rw [mem_nhds_iff]; use U)

theorem summable_iff_summablenet (f: I → X):
  Summable f ↔ SummableNet f := by
    unfold Summable SummableNet
    simp only [hassum_iff_hassumnet]

/- ### CauchySumable = CauchySeq ### -/

theorem cauchysum_iff_cauchySeqsum (f: I → Z):
  CauchySumNet f ↔ CauchySeq (fun (s: Finset I) ↦ ∑ i ∈ s, f i) := by
    rw [cauchySeq_iff_cauchynet]
    rfl

theorem cauchysum_of_summable {f: I → Z} (h: SummableNet f):
  CauchySumNet f := by
    exact cauchy_of_exists_lim h

theorem summable_iff_cauchysum [h: CompleteSpace W] {f: I → W} :
  SummableNet f ↔ CauchySumNet f := by
    rw [← summable_iff_summablenet, cauchysum_iff_cauchySeqsum,
        summable_iff_cauchySeq_finset]

/- ### Operations on summable famlies ### -/

theorem hassumnet_sum [ContinuousAdd X] {f : J → I → X} {a : J → X} {s : Finset J} :
  (∀ j ∈ s, HasSumNet (f j) (a j)) →
  HasSumNet (fun (i : I) => ∑ j ∈ s, f j i) (∑ j ∈ s, a j) := by
    simp only [← hassum_iff_hassumnet]
    exact hasSum_sum

theorem summablenet_sum [ContinuousAdd X] {f : J → I → X} {s : Finset J} :
  (∀ j ∈ s, SummableNet (f j)) →
  SummableNet (fun (i : I) => ∑ j ∈ s, f j i) := by
    simp only [← summable_iff_summablenet]
    exact summable_sum

theorem hassumnet_add [ContinuousAdd X] {f g: I → X} {x y: X} :
  HasSumNet f x → HasSumNet g y → HasSumNet (fun (i : I) => f i + g i) (x + y) := by
    simp only [← hassum_iff_hassumnet]
    exact HasSum.add

theorem summablenet_add [ContinuousAdd X] {f g: I → X} :
  SummableNet f → SummableNet g → SummableNet (fun (i : I) => f i + g i) := by
    simp only [← summable_iff_summablenet]
    exact Summable.add

theorem hassumnet_const_smul {R : Type*} [Monoid R] [TopologicalSpace R]
  [DistribMulAction R X] [ContinuousConstSMul R X] {f : I → X} {x : X} (r : R) :
    HasSumNet f x → HasSumNet (fun (i: I) ↦ r • (f i)) (r • x) := by
      simp only [← hassum_iff_hassumnet]
      exact HasSum.const_smul r

theorem summablenet_const_smul {R : Type*} [Monoid R] [TopologicalSpace R]
  [DistribMulAction R X] [ContinuousConstSMul R X] {f : I → X} (r : R) :
    SummableNet f → SummableNet (fun (i: I) ↦ r • (f i)) := by
      simp only [← summable_iff_summablenet]
      exact Summable.const_smul r

/- ### Operations on Cauchy summable families -/

theorem cauchysum_neg {f: I → U} [AddCommGroup U] [UniformAddGroup U] :
  CauchySumNet f → CauchySumNet (fun (i: I) ↦ - (f i)) := by
    unfold CauchySumNet
    have : (fun (E : Finset I) ↦ ∑ e ∈ E, - (f e)) =
       (fun (E : Finset I) ↦ - ∑ e ∈ E, f e) := by
        ext E
        rw [Finset.sum_neg_distrib]
    rw [this]
    exact cauchynet_neg

theorem cauchysum_add {f g: I → U} [AddCommGroup U] [UniformAddGroup U] :
  CauchySumNet f → CauchySumNet g → CauchySumNet (fun (i: I) ↦ (f i) + (g i)) := by
    unfold CauchySumNet
    have : (fun (E : Finset I) ↦ ∑ e ∈ E, ((f e) + (g e))) =
       (fun (E : Finset I) ↦ ∑ e ∈ E, f e + ∑ e ∈ E, g e) := by
        ext E
        rw [Finset.sum_add_distrib]
    rw [this]
    exact cauchynet_add
