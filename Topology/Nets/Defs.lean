import Topology.Nets.DirectedSet
import Mathlib.Analysis.RCLike.Basic

open Set Filter Topology Function DirectedSet

namespace Net

/- ### Definitions about nets ### -/


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
