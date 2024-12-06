import Topology.Nets.Basic
import Mathlib.Topology.UniformSpace.Cauchy

noncomputable section

open Set Filter Topology Function DirectedSet Net

/-
###### ########### ######
###### DEFINITIONS ######
###### ########### ######
-/

namespace Net

section Definitions

variable {X D: Type*} [DirectedSet D]

/- ### Filter associated to a net ### -/

/- Given any net s: D → X we can associate to it a filter in X, namely the filter of tails of s.
   The important property about this filter is that it has the same limit and accumulation points as the net. -/

def filter_of_net (s : D → X) : Filter X :=
{
  sets := {A : Set X | ∃ d : D, ∀ d' : D, (d ≤ d' → s d' ∈ A)}
  univ_sets := by
    simp only [Set.mem_setOf_eq, mem_univ, implies_true, exists_const]
  sets_of_superset := by
    intro A B Ain AsubB
    rcases Ain with ⟨d, sinA⟩
    rw [Set.mem_setOf_eq]
    use d
    intro d' dled'
    exact AsubB (sinA d' dled')
  inter_sets := by
    intro A B Ain Bin
    rcases Ain with ⟨d, sdin⟩
    rcases Bin with ⟨e, sein⟩
    rcases directed' d e with ⟨f, dlef, elef⟩
    rw [Set.mem_setOf_eq]
    use f
    intro d' fled'
    constructor
    · exact sdin d' (le_trans dlef fled')
    · exact sein d' (le_trans elef fled')
}

/- Furthermore, the filter is Nebot -/
instance filter_of_net.instNeBot (s : D → X) : Filter.NeBot (filter_of_net s) where
  ne' := by
    intro emptyinF
    simp only [← empty_mem_iff_bot, filter_of_net, Filter.mem_mk, Set.mem_setOf_eq, mem_empty_iff_false] at emptyinF
    rcases emptyinF with ⟨d, eq⟩
    exact eq d (le_refl d)

/- Furthermore, observe that if the net s: D → X is contained in a set A, that is for any d in D we have that s d ∈ A, then this
   set A belongs to the associated filter. -/
lemma set_in_filter_of_net_in_set (A: Set X) (s: D → X):
  (∀ (d: D), s d ∈ A) → A ∈ filter_of_net s := by
    intro sinA
    /- Observe that s'' {d: D | (default' D) ≤ d} is in filter_of_net s by definition, so as filter_of_net s is a filter and the image of s is
       contained in A, we conclude that A ∈ filter_of_net s. -/
    have : s '' {d: D | (default' D) ≤ d} ∈ filter_of_net s := by
      simp only [filter_of_net, Filter.mem_mk, Set.mem_setOf_eq]
      use default' D
      intro d' defled'
      use d'
      constructor
      · rw [Set.mem_setOf_eq]
        assumption
      · rfl
    apply Filter.sets_of_superset (filter_of_net s) this
    intro x xin
    rcases xin with ⟨d, _, sdeqx⟩
    rw [← sdeqx]
    exact sinA d

/- ### Net associated to a filter ### -/

/- Given any filter F in a set X we can construct a directed set associated to it as
    D := {(x, E): X × Set X | x ∈ E ∈ F},
   where the order relation is given by
    (x, E) ≤ (y, E') ↔ E' ⊆ E
   We can then associate a net to F by defining s: D → X such that s (x, E) = x.

   Again, the important property about this net is that it has the same limit and cluster points as F. -/

def directedset_of_filter (F: Filter X) := {P : X × Set X | P.1 ∈ P.2 ∧ P.2 ∈ F}

def net_of_filter (F: Filter X): directedset_of_filter F → X :=
  fun (P: directedset_of_filter F) ↦ P.1.1

/- If F is NeBot, then the directedset_of_filter is indeed a directed set and so net_of_filter is indeed a net. -/
instance directedset_of_filter.isntDirectedSet (F: Filter X) [Filter.NeBot F] :
  DirectedSet (directedset_of_filter F) where
    le := fun P Q ↦ Q.1.2 ⊆ P.1.2
    le_refl := by
      intro P x xin
      exact xin
    le_trans := by
      intro P Q R PleQ QleR
      apply subset_trans QleR PleQ
    default := by
      /- Observe that X is Inhabited because as univ ∈ F and F is NeBot, we have that univ ≠ ∅. -/
      have : Inhabited X := by
        have : @univ X ≠ ∅ := by
          intro univempty
          have := empty_not_mem F
          rw [← univempty] at this
          have := Filter.univ_sets F
          contradiction
        rw [← nonempty_iff_ne_empty, nonempty_def] at this
        exact Classical.inhabited_of_exists this
      let x := @Inhabited.default X _
      have : (x, univ) ∈ directedset_of_filter F := by
        simp only [directedset_of_filter, Set.mem_setOf_eq]
        exact And.intro (mem_univ x) univ_mem
      exact ⟨(x, univ), this⟩
    directed := by
      /- Given any (z, P), (y, Q) in directedset_of_filter F, we have that P, Q ∈ F so P ∩ Q ∈ F. Then, as F is NeBot we have that P ∩ Q ≠ ∅,
        so there exists some x ∈ P ∩ Q, and so (x, P ∩ Q) is an element of directedset_of_filter F and (z, P) ≤ (x, P ∩ Q), (y, Q) ≤ (x, P ∩ Q). -/
      intro P Q
      have : P.1.2 ∩ Q.1.2 ∈ F := by
        exact inter_mem (P.2.2) (Q.2.2)
      have : ∃ (x: X), x ∈ P.1.2 ∩ Q.1.2 := by
        exact Eventually.exists this
      rcases this with ⟨x, xininter⟩
      have : (x, P.1.2 ∩ Q.1.2) ∈ directedset_of_filter F := by
        simp only [directedset_of_filter, Set.mem_setOf_eq]
        constructor
        · assumption
        · assumption
      use ⟨(x, P.1.2 ∩ Q.1.2), this⟩
      constructor
      · exact Set.inter_subset_left
      · exact Set.inter_subset_right

/- Definition of the order relation -/
@[simp]
theorem directedset_of_filter_le_iff (F: Filter X) [Filter.NeBot F] :
  ∀ (P Q : directedset_of_filter F), P ≤ Q ↔ Q.1.2 ⊆ P.1.2 := by
    intro P Q
    rfl

/- ### Net associated to a filter (with a distinguished element) ### -/

/- Furthermore, if A ∈ F, we can define a new directed set
    D' := {(x, E): X × Set X | x ∈ E ∈ F ∧ E ⊆ A},
   where the order relation is the same
    (x, E) ≤ (y, E') ↔ E' ⊆ E
   Then, we have an inclusion from D' into D which allows as to define a subnet of NetF which will be contained in A.
   Furthermore, if x is a limit point of F, then it will be a limit point of this subnet, and if x is a cluster point of the
   subnet, then it is a cluster point of F. -/

def directedset_of_filter' (F: Filter X) (A: Set X) (_: A ∈ F) :=
  {P : X × Set X | P.1 ∈ P.2 ∧ P.2 ∈ F ∧ P.2 ⊆ A}

instance directedset_of_filter'.isntDirectedSet (F: Filter X) [Filter.NeBot F] (A: Set X) (h: A ∈ F) :
  DirectedSet (directedset_of_filter' F A h) where
    le := fun P Q ↦ Q.1.2 ⊆ P.1.2
    le_refl := by
      intro P x xin
      exact xin
    le_trans := by
      intro P Q R PleQ QleR
      apply subset_trans QleR PleQ
    default := by
      /- As A ∈ F and F is NeBot, we have that A ≠ ∅ and so taking any a ∈ A we have that (a, A) ∈ directedset_of_filter' F A. -/
      have : A ≠ ∅ := by
        intro Aempty
        have := empty_not_mem F
        rw [← Aempty] at this
        contradiction
      rw [← nonempty_iff_ne_empty, nonempty_def] at this
      let a := Classical.choose this
      exact ⟨(a, A), And.intro (Classical.choose_spec this) (And.intro h subset_rfl)⟩
    directed := by
      intro P Q
      have : P.1.2 ∩ Q.1.2 ∈ F := by
        exact inter_mem (P.2.2.1) (Q.2.2.1)
      have : ∃ (x: X), x ∈ P.1.2 ∩ Q.1.2 := by
        exact Eventually.exists this
      rcases this with ⟨x, xininter⟩
      have : (x, P.1.2 ∩ Q.1.2) ∈ directedset_of_filter' F A h := by
        simp only [directedset_of_filter', Set.mem_setOf_eq]
        constructor
        · assumption
        · constructor
          · assumption
          · intro x xininter
            apply P.2.2.2
            exact xininter.1
      use ⟨(x, P.1.2 ∩ Q.1.2), this⟩
      constructor
      · exact Set.inter_subset_left
      · exact Set.inter_subset_right

/- Definition of the order relation -/
@[simp]
theorem directedset_of_filter'_le_iff {F: Filter X} [Filter.NeBot F] {A: Set X} {h: A ∈ F}:
  ∀ (P Q : directedset_of_filter' F A h), P ≤ Q ↔ Q.1.2 ⊆ P.1.2 := by
    intro P Q
    rfl

/- Here we define the stated inclusion and the related subnet -/
def dsof_of_dsof' (F: Filter X) [Filter.NeBot F] (A: Set X) (h: A ∈ F):
  directedset_of_filter' F A h → directedset_of_filter F :=
    fun P ↦ ⟨P, And.intro P.2.1 P.2.2.1⟩

def net_of_filter' (F: Filter X) [Filter.NeBot F] (A: Set X) (h: A ∈ F):
  directedset_of_filter' F A h → X :=
    fun P ↦ (net_of_filter F ∘ dsof_of_dsof' F A h) P

/- As stated, NetFA is indeed a subnet of NetF -/
theorem net_of_filter'_subnet (F: Filter X) [NeBot F] (A: Set X) (h: A ∈ F) :
  Subnet (net_of_filter F) (net_of_filter' F A h) := by
    use dsof_of_dsof' F A h
    constructor
    · /- Given (x, P) in directedset_of_filter we have that P ∈ F and, as A ∈ F, we obtain that A ∩ P ∈ F. As F is NeBot, there exists
         some y ∈ A ∩ P. It is then clear that (y, A ∩ P) is in directedset_of_filter' and observe that given any (z, Q) in directedset_of_filter
         such that (y, A ∩ P) ≤ (z, Q) we have that Q ⊆ A ∩ P and so Q ⊆ P which implies that (x, P) ≤ (z, Q) = net_of_filter' (z, Q). -/
      intro d
      have : ∃ (y: X), y ∈ A ∩ d.1.2 := by
        rw [← nonempty_def, nonempty_iff_ne_empty]
        intro empty
        have : A ∩ d.1.2 ∈ F := by
          exact inter_mem h d.2.2
        rw [empty] at this
        have := empty_not_mem F
        contradiction
      rcases this with ⟨y, yininter⟩
      have : (y, A ∩ d.1.2) ∈ directedset_of_filter' F A h := by
        simp only [directedset_of_filter', Set.mem_setOf_eq]
        constructor
        · exact yininter
        · constructor
          · exact inter_mem h d.2.2
          · intro a aininter
            exact aininter.1
      use ⟨(y, A ∩ d.1.2), this⟩
      intro e lee
      simp only [directedset_of_filter_le_iff]
      simp only [directedset_of_filter'_le_iff] at lee
      apply subset_trans lee
      intro x xininter
      exact xininter.2
    · rfl

/- As stated, net_of_filter' is contained in A. -/
theorem net_of_filter'_subset (F: Filter X) [NeBot F] (A: Set X) (h: A ∈ F) :
  ∀ (d: directedset_of_filter' F A h), (net_of_filter' F A h) d ∈ A := by
    /- Indeed, given any (x, P) in directedset_of_filter' we have that directedset_of_filter' (x, P) = NetF (net_of_filter' (x, P)) = NetF (x, P) = x and, as
       (x, P) is in directedset_of_filter', we have that x ∈ P ⊆ A, so x ∈ A. -/
    intro d
    simp only [comp_apply, net_of_filter']
    exact d.2.2.2 d.2.1

/- ### Relation between both definitions ### -/

theorem filter_of_net_of_filter (F: Filter X) [NeBot F] :
  F = filter_of_net (net_of_filter F) := by
    ext A
    constructor
    · intro AinF
      have : ∃ (x: X), x ∈ A := by
        exact Eventually.exists AinF
      rcases this with ⟨x, xinA⟩
      unfold filter_of_net net_of_filter
      rw [Filter.mem_mk, Set.mem_setOf_eq]
      have : (x, A) ∈ directedset_of_filter F := by
        unfold directedset_of_filter
        simp only [Set.mem_setOf_eq]
        exact And.intro xinA AinF
      use ⟨(x,A), this⟩
      intro P xAleP
      simp only [directedset_of_filter_le_iff] at xAleP
      exact xAleP P.2.1
    · intro Ain
      unfold filter_of_net net_of_filter at Ain
      rw [Filter.mem_mk, Set.mem_setOf_eq] at Ain
      rcases Ain with ⟨P, eq⟩
      simp only [directedset_of_filter_le_iff, Subtype.forall, Prod.forall] at eq
      have : P.1.2 ⊆ A := by
        intro x xinP2
        exact eq x P.1.2 (And.intro xinP2 P.2.2) (le_refl P.1.2)
      exact mem_of_superset P.2.2 this

end Definitions
end Net

/-
###### ####### ######
###### RESULTS ######
###### ####### ######
-/

section Results

variable {X D: Type*} [TopologicalSpace X] [DirectedSet D]

/- ### Limits ### -/

/- As announced, given a net s and a point x in X, x is a limit of s iff it is a limit of its associated filter, that is
   filter_of_net s ≤ 𝓝 x. -/
theorem limnet_iff_limfilter (s: D → X) (x: X) :
  Limit s x ↔  filter_of_net s ≤ 𝓝 x := by
    constructor
    · intro limitsx
      intro U Unhds
      rcases limitsx U Unhds with ⟨d, eq⟩
      simp only [filter_of_net, Filter.mem_mk, Set.mem_setOf_eq]
      use d
    · intro limitFx U Unhds
      have UinF := limitFx Unhds
      simp only [filter_of_net, Filter.mem_mk, Set.mem_setOf_eq] at UinF
      assumption

/- As stated, a point x in X will be a limit point of F iff it is a limit point of net_of_filter F. -/
theorem limfilter_iff_limnet (F: Filter X) [Filter.NeBot F] (x: X) :
  F ≤ 𝓝 x ↔ Limit (net_of_filter F) x := by
    constructor
    · intro limitFx
      intro U Unhds
      have : (x, U) ∈ directedset_of_filter F := by
        simp only [directedset_of_filter, Set.mem_setOf_eq]
        constructor
        · exact mem_of_mem_nhds Unhds
        · exact limitFx Unhds
      use ⟨(x, U), this⟩
      intro e dlee
      simp only [net_of_filter]
      simp only [directedset_of_filter_le_iff] at dlee
      exact dlee e.2.1
    · intro limitsx U Unhds
      rcases limitsx U Unhds with ⟨d, eq⟩
      apply Filter.sets_of_superset F d.2.2
      intro y yind2
      have : (y, d.1.2) ∈ directedset_of_filter F := by
        simp only [directedset_of_filter, Set.mem_setOf_eq]
        exact And.intro yind2 d.2.2
      have := eq ⟨(y, d.1.2), this⟩ (by simp only [directedset_of_filter_le_iff]; exact subset_rfl)
      simp only [net_of_filter] at this
      assumption

/- As stated, if x is a limit point of F, then it is a limit point of directedset_of_filter'. -/
theorem limfilter'_implies_limnet (F: Filter X) [NeBot F] (A: Set X) (h: A ∈ F) (x: X) :
  F ≤ 𝓝 x → Limit (net_of_filter' F A h) x := by
    /- If x is a limit point of F, then we know it is a limit point of NetF and as directedset_of_filter' is a subnet the result is obvious. -/
    intro limitFx
    rw [limfilter_iff_limnet] at limitFx
    exact subnet_same_limit (net_of_filter'_subnet F A h) limitFx

theorem limnet_of_filter_nhds (x: X): Limit (net_of_filter (𝓝 x)) x := by
  rw [limnet_iff_limfilter, ← filter_of_net_of_filter]

/- ### Cluster points ### -/

/- As announced, given a net s and a point x in X, x is a cluster point of s iff it is a cluster point of its associated filter. -/
theorem clpointnet_iff_clpointfilter (s : D → X) (x: X) :
  ClusterPt s x ↔ ClusterPt x (filter_of_net s) := by
    constructor
    · intro clpointsx
      rw [clusterPt_iff]
      intro U Unhds V VinF
      rw [nonempty_def]
      simp only [filter_of_net, Filter.mem_mk, Set.mem_setOf_eq] at VinF
      rcases VinF with ⟨d, eq⟩
      rcases clpointsx d U Unhds with ⟨e, dlee, seinU⟩
      use s e
      constructor
      · assumption
      · exact eq e dlee
    · intro clpointFx
      intro d U Unhds
      rw [clusterPt_iff] at clpointFx
      have : s '' {e: D | d ≤ e} ∈ filter_of_net s := by
        simp only [filter_of_net, Filter.mem_mk, Set.mem_setOf_eq]
        use d
        intro d' dled'
        rw [mem_image]
        use d'
        constructor
        · assumption
        · rfl
      have := clpointFx Unhds this
      rcases this with ⟨z, zinU, zinV⟩
      rcases zinV with ⟨f, dlef, sfeqz⟩
      rw [Set.mem_setOf_eq] at dlef
      use f
      constructor
      · assumption
      · rw [sfeqz]
        assumption

/- As stated, a point x in X will be a cluster point of F iff it is a cluster point of net_of_filter F. -/
theorem clpointfilter_iff_clpointnet (F: Filter X) [h: Filter.NeBot F] (x: X) :
  ClusterPt x F ↔ ClusterPt (net_of_filter F) x := by
    constructor
    · intro clpointFx
      intro d U Unhds
      rw [clusterPt_iff] at clpointFx
      rcases clpointFx Unhds d.2.2 with ⟨y, yinU, yind⟩
      use ⟨(y, d.1.2), And.intro yind d.2.2⟩
      constructor
      · simp only [directedset_of_filter_le_iff]
        exact subset_rfl
      · simp only [net_of_filter]
        assumption
    · intro clpoinsx
      rw [clusterPt_iff]
      intro U Unhds V VinF
      rcases NeBot.nonempty_of_mem h VinF with ⟨v, vinV⟩
      rcases clpoinsx ⟨(v, V), And.intro vinV VinF⟩ U Unhds with ⟨e, vVlee, seinU⟩
      use e.1.1
      constructor
      · exact seinU
      · exact vVlee e.2.1

/- As stated, if x is a cluster point of net_of_filter', then it is a cluster point of F. -/
theorem clupointnet'_implies_clpointfilter (F: Filter X) [NeBot F] (A: Set X) (h: A ∈ F) (x: X):
  ClusterPt (net_of_filter' F A h) x → ClusterPt x F := by
    /- If x is a cluster point of directedset_of_filter', then it will be a clusert point of NetF, and so of F. -/
    intro clpointsx
    have := subnet_clusterpoint_implies_net (net_of_filter'_subnet F A h) clpointsx
    rw [← clpointfilter_iff_clpointnet] at this
    assumption

/- ### Cauchy ### -/

/- We also have that given a net s: D → X with X a uniform space, it is satisfied that s is Cauchy if, and only
   if, the associated filter is Cauchy. -/
lemma cauchynet_iff_cauchyfilter {X: Type*} [UniformSpace X] (s : D → X):
  CauchyNet s ↔ Cauchy (filter_of_net s) := by
    constructor
    · intro cauchys
      rw [cauchy_iff']
      unfold CauchyNet at cauchys
      constructor
      · exact filter_of_net.instNeBot s
      · intro U Uinunif
        rcases cauchys U Uinunif with ⟨d₀, eq⟩
        use s '' {d: D | d₀ ≤ d}
        constructor
        · simp only [filter_of_net, Filter.mem_mk, Set.mem_setOf_eq]
          use d₀
          intro d d₀led
          rw [mem_image]
          use d
          simp only [Set.mem_setOf_eq]
          apply And.intro d₀led trivial
        · intro sd sdin se sein
          rcases sdin with ⟨d, d₀led, sdeq⟩
          rcases sein with ⟨e, d₀lee, seeq⟩
          rw [← sdeq, ← seeq]
          rw [Set.mem_setOf_eq] at *
          exact eq d e d₀led d₀lee
    · intro cauchyf
      rw [cauchy_iff'] at cauchyf
      unfold CauchyNet
      intro U Uinunif
      rcases cauchyf.2 U Uinunif with ⟨A, AinF, eq⟩
      simp only [filter_of_net, Filter.mem_mk, Set.mem_setOf_eq] at AinF
      rcases AinF with ⟨d₀, eqd⟩
      use d₀
      intro d e d₀led d₀lee
      exact eq (s d) (eqd d d₀led) (s e) (eqd e d₀lee)

/- We also have that given a filter in X a uniform space, it is satisfied that it is Cauchy if, and only
   if, the associated net is Cauchy. -/
lemma cauchyfilter_iff_cauchynet {X: Type*} [UniformSpace X] (F: Filter X) [h: Filter.NeBot F]:
  Cauchy F ↔ CauchyNet (net_of_filter F) := by
    constructor
    · intro cauchyf
      rw [cauchy_iff'] at cauchyf
      unfold CauchyNet
      intro U Uinunif
      rcases cauchyf.2 U Uinunif with ⟨A, AinF, eq⟩
      have: ∃ (a: X), a ∈ A := by
        have: A ≠ ∅ := by
          intro Aempty
          rw [Aempty] at AinF
          have := empty_not_mem F
          exact this AinF
        rw [← nonempty_iff_ne_empty, nonempty_def] at this
        assumption
      rcases this with ⟨a, ainA⟩
      use ⟨(a, A), And.intro ainA AinF⟩
      intro d e aAled aAlee
      unfold net_of_filter
      simp only [directedset_of_filter_le_iff] at *
      exact eq d.1.1 (aAled d.2.1) e.1.1 (aAlee e.2.1)
    · intro cauchys
      unfold CauchyNet at cauchys
      rw [cauchy_iff']
      constructor
      · exact h
      · intro U Uinunif
        rcases cauchys U Uinunif with ⟨d₀, eq⟩
        use d₀.1.2
        constructor
        · exact d₀.2.2
        · intro x xind₀ y yind₀
          exact eq ⟨(x, d₀.1.2), And.intro xind₀ d₀.2.2⟩ ⟨(y, d₀.1.2), And.intro yind₀ d₀.2.2⟩
            (by rw[directedset_of_filter_le_iff]) (by rw[directedset_of_filter_le_iff])
