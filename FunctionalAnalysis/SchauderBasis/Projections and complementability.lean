import Mathlib.Topology.Instances.Real
import Mathlib.Analysis.RCLike.Basic
import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.Topology.Algebra.Module.FiniteDimension

noncomputable section

set_option trace.Meta.Tactic.simp false

open Set Topology Classical Function LinearMap

namespace Defs

/- Definition of projection -/
def IsProjection {X : Type*} (P: X → X): Prop := ∀ (x: X), P (P x) = P x

lemma range_of_projection_eq_ker {M R: Type*} [Semiring R] [AddCommGroup M] [Module R M] {P: M →ₗ[R] M} :
  IsProjection P → LinearMap.range P = LinearMap.ker (LinearMap.id  - P) := by
    intro Pproj
    ext m
    constructor
    · intro minrange
      rw [mem_ker, sub_apply, id_apply]
      rcases minrange with ⟨n, Pneqm⟩
      rw [← Pneqm, Pproj, sub_self]
    · intro minker
      rw [mem_ker, sub_apply, id_apply, sub_eq_zero] at minker
      use m
      exact minker.symm

/- Definition: Let X be a normed space and Y a subspace of X. We say that Y is complemented in X if there exists a bounded
               linear projection P of X onto Y. If λ is a real number such that ‖P‖ ≤ λ we say that Y is λ-complemented in X. -/
def IsComplemented (X 𝕂: Type*) [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X] (Y: Subspace 𝕂 X) : Prop :=
  ∃ (P: X →L[𝕂] X), IsProjection P ∧ LinearMap.range P = Y

lemma complemented_iff {X 𝕂: Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X] (Y: Subspace 𝕂 X) :
  IsComplemented X 𝕂 Y ↔ ∃ (P: X →L[𝕂] X), LinearMap.IsProj Y P := by
    constructor
    · intro Ycomp
      /- If Y is complemented in X, then there exists a linear bounded projection P from X onto Y. Then, if y ∈ Y we have that
         there exists some x ∈ X such that P x = y, so as P is a projection, P y = P (P x) = P x = y. -/
      rcases Ycomp with ⟨P, Pproj, ranPeqY⟩
      use P
      constructor
      · intro x
        rw [← ranPeqY, LinearMap.mem_range]
        use x
      · intro y yinY
        rw [← ranPeqY] at yinY
        rcases yinY with ⟨x, Pxeqy⟩
        rw [← Pxeqy, Pproj]
    · intro cond
      /- If there exists a linear bounded map P from X onto Y that fixes Y, then we can see that it is a projection and so
         Y is complemented in X. In fact, given any x in X we have that P x ∈ Y, so as P fixes Y, P (P x) = P x. -/
      rcases cond with ⟨P, PxinY, PfixY⟩
      use P
      constructor
      · intro x
        exact PfixY (P x) (PxinY x)
      · ext y
        constructor
        · intro yinrange
          rcases yinrange with ⟨x, Pxeqy⟩
          rw [← Pxeqy]
          exact PxinY x
        · intro yinY
          use y
          exact PfixY y yinY

theorem ker_closed {X Y 𝕂: Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X] [NormedAddCommGroup Y] [NormedSpace 𝕂 Y]
  (f: X →ₗ[𝕂] Y) : Continuous f → IsClosed {x: X | x ∈ ker f} := by
    intro fcont
    have : {x: X | x ∈ ker f} = f ⁻¹' {0} := by
      ext x
      constructor
      · intro xinker
        rw [Set.mem_setOf_eq, mem_ker] at xinker
        rw [mem_preimage, mem_singleton_iff]
        assumption
      · intro xinpre
        rw [mem_preimage, mem_singleton_iff] at xinpre
        rw [Set.mem_setOf_eq, mem_ker]
        assumption
    rw [this]
    rw [continuous_iff_isClosed] at fcont
    apply fcont
    exact isClosed_singleton

theorem complemented_closed (X 𝕂: Type*) [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X] (Y: Subspace 𝕂 X) :
  IsComplemented X 𝕂 Y → @IsClosed X _ Y := by
    intro Ycomp
    rcases Ycomp with ⟨P, Pproj, ranPeqY⟩
    have eqran : LinearMap.range P = LinearMap.range (P.toLinearMap) := by
      rfl
    rw [← ranPeqY, eqran, range_of_projection_eq_ker Pproj]
    apply ker_closed
    apply Continuous.sub
    · exact continuous_id
    · exact P.continuous

def IsDirectSum (M R: Type*) [Semiring R] [AddCommGroup M] [Module R M] (N₁ N₂: Submodule R M) : Prop := ∀ (m : M), ∃ m₁ ∈ N₁, ∃ m₂ ∈ N₂, m = m₁ + m₂

def TopologicalComplement (X 𝕂: Type*) [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X] (Y₂ Y₁: Subspace 𝕂 X) : Prop :=
  @IsClosed X _ Y₂ ∧ IsDirectSum X 𝕂 Y₁ Y₂

theorem complemented_iff_exists_topologicalcomplement (X 𝕂: Type*) [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X] [CompleteSpace X]
  (Y: Subspace 𝕂 X) (h: @IsClosed X _ Y)  : IsComplemented X 𝕂 Y ↔ ∃ (Z: Subspace 𝕂 X), TopologicalComplement X 𝕂 Y Z := by
    sorry

-- Equivalencia completitud con redes.
-- Equivalencia completitud en normados con sucesiones.
-- Equivalencia completitud en normados con serie abs. conv. implica conv.
-- Teoremas de la aplicación abierta y la gráfica cerrada.
