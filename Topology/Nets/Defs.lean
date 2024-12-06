import Topology.Nets.DirectedSet
import Mathlib.Analysis.RCLike.Basic

open Set Filter Topology Function DirectedSet

namespace Net

/- ### Definitions about nets ### -/

/- We say that a function f: I → X is summable if the net of sums over finite sets of I converges -/

def HasAbsSum {I X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
   (f: I → X) (t: ℝ): Prop := HasSumNet (fun (i: I) ↦ ‖f i‖) t

def AbsSummable {I X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
   (f: I → X): Prop := ∃ (t: ℝ), HasAbsSum 𝕂 f t

/- Convergence of series -/
def conv_serie_to {X: Type*} [AddCommMonoid X] [TopologicalSpace X] (f: ℕ → X) (x: X): Prop :=
   Limit (fun (N: ℕ) ↦ ∑ n ≤ N, f n) x

def conv_serie {X: Type*} [AddCommMonoid X] [TopologicalSpace X] (f: ℕ → X): Prop :=
   ∃ (x: X), conv_serie_to f x

def conv_abs_serie_to {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
   (f: ℕ → X) (t: ℝ) : Prop :=
      conv_serie_to (fun (n: ℕ) ↦ ‖f n‖) t

def conv_abs_serie {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : Prop :=
   ∃ (t: ℝ), conv_abs_serie_to 𝕂 f t

def CauchySerie {X: Type*} [AddCommMonoid X] [UniformSpace X] (f: ℕ → X): Prop :=
   CauchyNet (fun (N: ℕ) ↦ ∑ n ≤ N, f n)

/- Unconditional convergence -/

def RSerie {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : Prop :=
  ∀ (g: ℕ → ℕ), Bijective g → conv_serie (f ∘ g)

def SSerie {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : Prop :=
  ∀ (g: ℕ → ℕ), StrictMono g → conv_serie (f ∘ g)

def BMSerie {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : Prop :=
  ∀ (g: ℕ → 𝕂), Bornology.IsBounded (range g) → conv_serie (fun (n: ℕ) ↦ (g n) • (f n))

def ASerie {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : Prop :=
  ∀ (g: ℕ → 𝕂), range g ⊆ {1, -1} → conv_serie (fun (n: ℕ) ↦ (g n) • (f n))

def RCauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : Prop :=
  ∀ (g: ℕ → ℕ), Bijective g → CauchySerie (f ∘ g)

def SCauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : Prop :=
  ∀ (g: ℕ → ℕ), StrictMono g → CauchySerie (f ∘ g)

def BMCauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : Prop :=
  ∀ (g: ℕ → 𝕂), Bornology.IsBounded (range g) → CauchySerie (fun (n: ℕ) ↦ (g n) • (f n))

def ACauchy {X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
  (f: ℕ → X) : Prop :=
  ∀ (g: ℕ → 𝕂), range g ⊆ {1, -1} → CauchySerie (fun (n: ℕ) ↦ (g n) • (f n))
