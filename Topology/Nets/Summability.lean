import Topology.Nets.Theorems

noncomputable section

set_option trace.Meta.Tactic.simp false

open Set Filter Topology Function DirectedSet

namespace Net

variable {I X Z: Type*} [AddCommMonoid X] [TopologicalSpace X] [AddCommMonoid Z] [UniformSpace Z]

/- ### Definitions ### -/

def HasSumNet (f: I → X) (x: X): Prop :=
   Limit (fun (E: Finset I) ↦ ∑ e ∈ E, f e) x

def SummableNet (f: I → X): Prop :=
   ∃ (x: X), HasSumNet f x

def CauchySumNet (f: I → Z): Prop :=
   CauchyNet (fun (E: Finset I) ↦ ∑ e ∈ E, f e)

/- ### Summable = NetSummable ### -/

/- A function is summable iff it is net summable -/
theorem hasSum_iff_hasSumnet (f: I → X) (x: X) :
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
    simp only [hasSum_iff_hasSumnet]

/- ### CauchySumable = CauchySeq ### -/

theorem cauchySeq_iff_cauchynet {X D: Type*} [UniformSpace X] [DirectedSet D]
  (f: D → X) : CauchySeq f ↔ CauchyNet f := by
    unfold CauchySeq CauchyNet
    rw [cauchy_iff']
    simp only [mem_map, mem_atTop_sets, ge_iff_le, mem_preimage]
    constructor
    · intro h U Uinunif
      rcases h.2 U Uinunif with ⟨A, eq⟩
      rcases eq.1 with ⟨d₀, inA⟩
      use d₀
      intro d e d₀led d₀lee
      exact eq.2 (f d) (inA d d₀led) (f e) (inA e d₀lee)
    · intro h
      constructor
      · exact map_neBot
      · intro U Uinunif
        rcases h U Uinunif with ⟨d₀, eq⟩
        use f '' {d: D | d₀ ≤ d}
        simp only [mem_image, Set.mem_setOf_eq]
        constructor
        · use d₀
          intro d d₀led
          use d
        · intro x condx y condy
          rcases condx with ⟨dx, d₀ledx, fdxeqx⟩
          rcases condy with ⟨dy, d₀ledy, fdyeqy⟩
          rw [← fdxeqx, ← fdyeqy]
          exact eq dx dy d₀ledx d₀ledy

theorem cauchysum_iff_cauchySeqsum (f: I → Z):
  CauchySumNet f ↔ CauchySeq (fun (s: Finset I) ↦ ∑ i ∈ s, f i) := by
    rw [cauchySeq_iff_cauchynet]
    rfl
