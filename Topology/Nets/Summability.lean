import Topology.Nets.Theorems
import Mathlib.Topology.Algebra.InfiniteSum.Group

noncomputable section

set_option trace.Meta.Tactic.simp false

open Set Filter Topology Function DirectedSet

namespace Net

variable {I X: Type*} [AddCommMonoid X] [TopologicalSpace X]
variable {Z: Type*} [AddCommMonoid Z] [UniformSpace Z]
variable {W: Type*} [AddCommGroup W] [UniformSpace W]

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
