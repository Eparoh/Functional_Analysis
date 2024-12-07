import Mathlib.Topology.Instances.Real

noncomputable section

open Set Filter Topology Function

/- ### Class ### -/

class DirectedSet (D: Type*) extends Preorder D, Inhabited D, IsDirected D (fun d d' ↦ d ≤ d')

/- ### Basic ### -/

def DirectedSet.default' (D: Type*) [DirectedSet D] := @Inhabited.default D toInhabited

theorem DirectedSet.directed' {D: Type*} [DirectedSet D] (d d': D) :
  ∃ (f: D), d ≤ f ∧ d' ≤ f := DirectedSet.toIsDirected.directed d d'

/- ### Theorems ### -/

/- Any finite set on a directed set has a supremum -/
theorem DirectedSet.sup_finite_set {D : Type*} [DirectedSet D] (I : Finset D): ∃ (d: D), ∀ c ∈ I, c ≤ d := by
  classical
  induction' I using Finset.induction_on with d I _ ih
  · simp only [Finset.not_mem_empty, false_implies, implies_true, exists_const]
  · simp only [Finset.mem_insert, forall_eq_or_imp]
    rcases ih with ⟨d₀, leI⟩
    rcases DirectedSet.directed' d d₀ with ⟨d₁, ledd₀⟩
    use d₁
    apply And.intro (ledd₀.1) _
    intro a ainI
    exact le_trans (leI a ainI) ledd₀.2

/- ### Instances ### -/

/- # Linear order # -/

/- Every linear order is a directed set -/

instance LinearOrder.instDirectedSet {X : Type*} [LinearOrder X] [Inhabited X] : DirectedSet X where
  directed := by
    intro d e
    use max d e
    exact And.intro (le_max_left d e) (le_max_right d e)

/- The set of natural numbers is a directed set with its usual order -/

instance : DirectedSet ℕ := LinearOrder.instDirectedSet

/- # Family of sets with inclusion (⊇) # -/

/- The set of neighbourhoods of a point x (ordered by ⊇) is a directed set -/

def Preorder.SetSubLeft (X : Type*) : Preorder (Set X) where
  toLE := {le := fun U ↦ (fun V ↦ V ⊆ U)}
  toLT := {lt := fun U ↦ (fun V ↦ V ⊆ U ∧ ¬ U ⊆ V)}
  le_refl := by
    intro U
    exact le_refl U
  le_trans := by
    intro U V W UleV VleW
    exact subset_trans VleW UleV
  lt_iff_le_not_le := by
    intro U V
    constructor
    repeat
      intro h
      exact h

def DirectedSet.instNeighbourhoodLeft {X: Type*} [TopologicalSpace X] (x : X) : DirectedSet {U | U ∈ 𝓝 x} where
  toPreorder := @Subtype.preorder (Set X) (Preorder.SetSubLeft X) (fun U => U ∈ 𝓝 x)
  default := ⟨univ, univ_mem⟩
  directed := by
    intro d e
    use ⟨d.1 ∩ e.1, inter_mem d.2 e.2⟩
    constructor
    · apply inter_subset_left
    · apply inter_subset_right

/- # Family of sets with inclusion (⊆) # -/

/- -- The set of neighbourhoods of a point x (ordered by ⊆) is a directed set -/

lemma union_mem {X: Type*} [TopologicalSpace X] (A B : Set X) (x : X) :
  A ∈ 𝓝 x → B ∈ 𝓝 x → A ∪ B ∈ 𝓝 x := by
  intro A_nhds B_nhds
  rw [mem_nhds_iff] at *
  rcases A_nhds with ⟨tA, tAsubA, tA_open, xintA⟩
  rcases B_nhds with ⟨tB, tBsubB, tB_open, _⟩
  use tA ∪ tB
  exact And.intro (union_subset_union tAsubA tBsubB)
    (And.intro (IsOpen.union tA_open tB_open) (Or.inl xintA))

def DirectedSet.instNeighbourhoodRight {X: Type*} [TopologicalSpace X] (x : X) : DirectedSet {U | U ∈ 𝓝 x} where
  default := ⟨univ, univ_mem⟩
  directed := by
    intro d e
    use ⟨d.1 ∪ e.1, union_mem d.1 e.1 x d.2 e.2⟩
    constructor
    · apply subset_union_left
    · apply subset_union_right

/- # Product of directed sets  # -/

/- The product of directed sets is a directed set with the order relation defined pointwise -/

instance DirectedSet.instProduct {D E : Type*} [DirectedSet D] [DirectedSet E] : DirectedSet (D × E) where
  default := (default' D, default' E)
  directed := by
    intro u v
    rcases DirectedSet.directed' u.1 v.1 with ⟨f1, f1le⟩
    rcases DirectedSet.directed' u.2 v.2 with ⟨f2, f2le⟩
    use (f1, f2)
    exact And.intro (And.intro f1le.1 f2le.1) (And.intro f1le.2 f2le.2)

/- # Family of finite intersections of a set # -/

/- Set of finite intersections of sets is directed by ⊇

   We include an optional argument "K" that by default will be univ, and so the set will be equal to
   the set of finite intersections as stated -/

def Preorder.instFiniteInterLeft {X F: Type*} {A: F → Set X} (K := univ) : Preorder {U | ∃ (u: Finset F), U = K ∩ ⋂ i ∈ u, A i} where
toLE := {le := fun U ↦ (fun V ↦ V.1 ⊆ U.1)}
toLT := {lt := fun U ↦ (fun V ↦ V.1 ⊆ U.1 ∧ ¬ U.1 ⊆ V.1)}
le_refl := by
  intro a
  exact le_refl a
le_trans := by
  intro a b c aleb blec
  exact subset_trans blec aleb
lt_iff_le_not_le := by
  intro a b
  constructor
  repeat
    intro h
    exact h

def DirectedSet.instFiniteInterLeft {X F: Type*} {A: F → Set X} (K := univ) : DirectedSet {U | ∃ (u: Finset F), U = K ∩ ⋂ i ∈ u, A i} where
  toPreorder := Preorder.instFiniteInterLeft K
  default := by
    have : K ∈ {U | ∃ (u: Finset F), U = K ∩ ⋂ i ∈ u, A i} := by
      dsimp
      use ∅
      simp
    exact ⟨K, this⟩
  directed := by
      dsimp
      intro d e
      have : ∃ (u : Finset F),  d.1 ∩ e.1 = K ∩ ⋂ i ∈ u, A i := by
        classical
        rcases d.2 with ⟨u, d_eq_int⟩
        rcases e.2 with ⟨v, e_eq_int⟩
        use u ∪ v
        ext x
        constructor
        · intro ⟨xind, xine⟩
          simp
          rw [d_eq_int] at xind
          rw [e_eq_int] at xine
          constructor
          · exact xind.1
          · intro i iinuv
            rcases iinuv with iinu | iinv
            · simp at xind
              exact xind.2 i iinu
            · simp at xine
              exact xine.2 i iinv
        · intro h
          simp at h
          constructor
          · rw [d_eq_int]
            simp
            constructor
            · exact h.1
            · intro i iinu
              exact h.2 i (Or.inl iinu)
          · rw [e_eq_int]
            simp
            constructor
            · exact h.1
            · intro i iinv
              exact h.2 i (Or.inr iinv)
      use ⟨d.1 ∩ e.1, this⟩
      constructor
      · apply inter_subset_left
      · apply inter_subset_right

/- # Finset # -/

/- Family of finite subsets of a type is directed by inclusion -/

instance DirectedSet.instFinset {X: Type*}: DirectedSet (Finset X) where
  default := ∅
  directed := by
    classical
    intro E F
    use E ∪ F
    constructor
    · exact Finset.subset_union_left
    · exact Finset.subset_union_right
