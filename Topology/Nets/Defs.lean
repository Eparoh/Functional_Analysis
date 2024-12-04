import Topology.Nets.DirectedSets
import Mathlib.Analysis.RCLike.Basic

open Set Filter Topology Function DirectedSet

namespace Net

/- ### Definitions about nets ### -/

/- A net is simply a map s: D → X from a  directed set to  topological space X. -/

/- We say that a net s: D → X converges to a point x in X if for every neighborhood U of x there exists a d₀ in D such that
   for any d in D with d₀ ≤ d, we obtain that s d ∈ U. -/
def Limit {X D: Type*} [TopologicalSpace X] [DirectedSet D] (s : D → X) (x: X) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ (d₀ : D), ∀ (d : D), d₀ ≤ d → s d ∈ U

/- We say that a point x in X is a cluster point of a net s: D → X if for every d in D and every neighborhood U of x there exists
   an e in D such that d ≤ e and s e ∈ U. -/
def ClusterPoint {X D: Type*} [TopologicalSpace X] [DirectedSet D] (s: D → X) (x : X): Prop :=
  ∀ (d : D), ∀ U ∈ 𝓝 x, ∃ (e : D), (d ≤ e ∧ s e ∈ U)

/- We say that a net s': E → X is a subnet of a net s: D → X if there exists a cofinal map i : E → D such that s' = s ∘ i.
   With cofinal we mean that given any d in D, there exists an e₀ in E such that for any e in E, if e₀ ≤ e then d ≤ i e. -/
def Subnet {X D E: Type*} [DirectedSet D] [DirectedSet E] (s: D → X) (s': E → X) : Prop :=
  ∃ (i: E → D), (∀ (d : D), ∃ (e₀ : E), ∀ (e : E), (e₀ ≤ e →  d ≤ (i e))) ∧ s' = s ∘ i

/- We say that a net s: D → X on a uniform space X is Cauchy if for every U in the uniformity
   of X thre exists some d₀ in I such that (s d, s e) ∈ U for all d₀ ≤ d, e -/
def CauchyNet {X D: Type*} [DirectedSet D] [UniformSpace X] (s: D → X): Prop :=
   ∀ U ∈ uniformity X, ∃ (d₀: D), ∀ (d e: D), (d₀ ≤ d → d₀ ≤ e → (s d, s e) ∈ U)

/- We say that a uniform space X is complete if every cauchy net in it converges -/
def CompleteNet (X: Type*) [UniformSpace X]: Prop :=
   ∀ (D: Type u_1) (_: DirectedSet D) (s : D → X), (CauchyNet s → ∃ (x: X), Limit s x)

/- We say that a function f: I → X is summable if the net of sums over finite sets of I converges -/
def HasSumNet {I X: Type*} [AddCommMonoid X] [TopologicalSpace X] (f: I → X) (x: X): Prop :=
   Limit (fun (E: Finset I) ↦ ∑ e ∈ E, f e) x

def SummableNet {I X: Type*}  [AddCommMonoid X] [TopologicalSpace X] (f: I → X): Prop :=
   ∃ (x: X), HasSumNet f x

def HasAbsSum {I X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
   (f: I → X) (t: ℝ): Prop := HasSumNet (fun (i: I) ↦ ‖f i‖) t

def AbsSummable {I X: Type*} [SeminormedAddCommGroup X] (𝕂: Type*) [RCLike 𝕂] [NormedSpace 𝕂 X]
   (f: I → X): Prop := ∃ (t: ℝ), HasAbsSum 𝕂 f t

def CauchySumNet {I X: Type*} [AddCommMonoid X] [UniformSpace X] (f: I → X): Prop :=
   CauchyNet (fun (E: Finset I) ↦ ∑ e ∈ E, f e)

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
