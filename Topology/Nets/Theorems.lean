import Topology.Nets.Filter
import Mathlib.Topology.UniformSpace.Cauchy
import Mathlib.Topology.Algebra.InfiniteSum.Defs

set_option trace.Meta.Tactic.simp false

noncomputable section

open Set Filter Topology Classical Function DirectedSet

namespace Net

/- ### Classic characterizations ### -/

/- In this file we stated the characterizations of closure, closed set, compact set, continuous function at a point and Hausdorff set
   in terms of nets.

   To do so, we use the equivalent results for filters and the relations between nets and filter. -/

/- ### Missing results for filters ### -/

/- Here we stablish a couple of results about filters. Mainly a characterization for the closure and for a Hausdorff space. -/

/- An element x of X is in the closure of A iff there exists a filter F in X such that it is NeBot, A ∈ F and x is a limit
   point of F. -/
theorem mem_closure_iff_exists_filter {X: Type*} [TopologicalSpace X] (A: Set X) (x : X) :
  x ∈ closure A ↔ ∃ (F: Filter X), F.NeBot ∧  A ∈ F ∧ F ≤ 𝓝 x := by
    constructor
    · intro xinclos
      let G:= Filter.generate ({U | U ∈ 𝓝 x} ∪ {A})
      use G
      constructor
      · rw [Filter.generate_neBot_iff]
        intro Y Ysub Yfin
        by_cases AinY : A ∈ Y
        · have : ⋂₀ (Y \ {A}) ∈ 𝓝 x := by
            rw [Filter.sInter_mem]
            · intro U UinY
              simp only [Set.mem_diff, Set.mem_singleton_iff] at UinY
              rcases Ysub UinY.1 with h | h
              · assumption
              · rw [mem_singleton_iff] at h
                have := UinY.2
                contradiction
            · exact Finite.diff Yfin {A}
          rw [mem_closure_iff_nhds] at xinclos
          have:= xinclos (⋂₀ (Y \ {A})) this
          have : ⋂₀ (Y \ {A}) ∩ A = ⋂₀ Y := by
            ext y
            constructor
            · intro yin
              simp only [Set.union_singleton, Set.mem_inter_iff, Set.mem_sInter, Set.mem_diff, Set.mem_singleton_iff, and_imp]  at *
              intro t tinY
              by_cases teqA : t = A
              · rw [teqA]
                exact yin.2
              · exact yin.1 t tinY teqA
            · intro yin
              simp only [Set.union_singleton, Set.mem_inter_iff, Set.mem_sInter, Set.mem_diff, Set.mem_singleton_iff, and_imp]  at *
              constructor
              · intro t tinY _
                exact yin t tinY
              · exact yin A AinY
          rw [← this]
          assumption
        · have : ⋂₀ Y ∈ 𝓝 x := by
            rw [Filter.sInter_mem]
            · intro U UinY
              rcases Ysub UinY with h | h
              · exact h
              · rw [mem_singleton_iff] at h
                rw [h] at UinY
                contradiction
            · assumption
          use x
          exact mem_of_mem_nhds this
      · constructor
        · apply mem_generate_of_mem
          simp only [Set.union_singleton, Set.mem_insert_iff, eq_self, Set.mem_setOf_eq, true_or]
        · intro U Unhds
          apply mem_generate_of_mem
          simp only [Set.union_singleton, Set.mem_insert_iff, Set.mem_setOf_eq]
          right
          assumption
    · intro h
      rcases h with ⟨F, Fnebot, AinF, limitFx⟩
      rw [mem_closure_iff_nhds]
      intro U Unhds
      have : U ∩ A ∈ F := by
        exact inter_mem (limitFx Unhds) AinF
      exact NeBot.nonempty_of_mem Fnebot this

/- A topological space X is T2 iff every NeBot filter F in X has at most one limit point. -/
theorem t2_iff_net_unique_limit_filter {X : Type*} [TopologicalSpace X] :
  T2Space X ↔ ∀ (F: Filter X) (_: Filter.NeBot F) (x y : X), F ≤ 𝓝 x → F ≤ 𝓝 y → x = y := by
    constructor
    · intro t2
      intro F h x y limitFx limitFy
      by_contra! xneqy
      rw [← disjoint_nhds_nhds] at xneqy
      unfold Disjoint at xneqy
      have := xneqy limitFx limitFy
      simp only [le_bot_iff] at this
      rw [Filter.neBot_iff] at h
      contradiction
    · intro cond
      rw [t2Space_iff_disjoint_nhds]
      by_contra not_haus
      unfold Pairwise at not_haus
      push_neg at not_haus
      rcases not_haus with ⟨x, y, xneqy, disjnhds⟩
      unfold Disjoint at disjnhds
      push_neg at disjnhds
      rcases disjnhds with ⟨F, limitFx, limitFy, nebotF⟩
      simp only [le_bot_iff] at nebotF
      rw [← Ne, ← Filter.neBot_iff] at nebotF
      exact xneqy (cond F nebotF x y limitFx limitFy)

/- ### Characterizations in terms of nets ### -/

/- A net in a product space converges iff every coordinate converges -/
theorem prod_limit  {X ι D: Type*} {π : ι → Type*} [DirectedSet D] [TopologicalSpace X] [T : (i : ι) → TopologicalSpace (π i)]
  (s: D → (i : ι) → π i) (x: (i : ι) → π i) : Limit s x ↔ ∀ (i: ι), Limit (fun (d: D) ↦ s d i) (x i) := by
    simp only [limit_net_iff_filter, ← tendsto_id']
    exact tendsto_pi_nhds

theorem prod_limit'  {X Y D: Type u_1} [h: DirectedSet D] [TopologicalSpace X] [TopologicalSpace Y]
  (s: D → X × Y) (x: X × Y) : Limit s x ↔ Limit (fun (d: D) ↦ (s d).1) x.1 ∧ Limit (fun (d: D) ↦ (s d).2) x.2 := by
    rw [limit_net_iff_filter, limit_net_iff_filter, limit_net_iff_filter, ← tendsto_id', ← tendsto_id', ← tendsto_id']
    exact Prod.tendsto_iff id x


/- An element x of X is in the closure of A iff there exists a net s: D → X such that it is contained in A and
   converges to x. -/
theorem mem_closure_iff_exists_net {X: Type*} [TopologicalSpace X] (A: Set X) (x : X):
  x ∈ closure A ↔ ∃ (D: Type u_1) (_: DirectedSet D) (s: D → X), (∀ (d: D), s d ∈ A) ∧ Limit s x := by
    have : Inhabited X := by
      exact { default := x }
    rw [mem_closure_iff_exists_filter]
    constructor
    · intro cond
      rcases cond with ⟨F, Fnebot, AinF, limitFx⟩
      use DirectedSetFA F A AinF, DirectedSetFA.isntDirectedSet F A AinF , NetFA F A AinF
      exact And.intro (NetFA_subset F A AinF) (limit_filter_implies_net F A AinF x limitFx)
    · intro cond
      rcases cond with ⟨D, h, s, sinA, limitsx⟩
      use FNet s
      exact And.intro (FNet.instNeBot s) (And.intro (net_in_set_implies_set_in_filter A D h s sinA)
        ((limit_net_iff_filter s x).mp limitsx))

/- A set C of X is closed iff for every x in X and every net s: D → X contained in C that converges to x we have that x ∈ C. -/
theorem isClosed_iff_limit_self {X: Type*} [TopologicalSpace X] (C: Set X) :
  IsClosed C ↔ ∀ (x : X), ∀ (D: Type u_1) (_: DirectedSet D) (s : D → X), (∀ (d: D), s d ∈ C) → Limit s x → x ∈ C := by
    rw [isClosed_iff_forall_filter]
    constructor
    · intro cond
      intro x D h s sinC limitsx
      have : FNet s ≤ 𝓟 C := by
        rw [le_principal_iff]
        exact net_in_set_implies_set_in_filter C D h s sinC
      exact cond x (FNet s) (FNet.instNeBot s) this ((limit_net_iff_filter s x).mpr limitsx)
    · intro cond
      intro x F Fnebot CinF limitFx
      rw [le_principal_iff] at CinF
      exact cond x (DirectedSetFA F C CinF) (DirectedSetFA.isntDirectedSet F C CinF) (NetFA F C CinF)
        (NetFA_subset F C CinF) (limit_filter_implies_net F C CinF x limitFx)

/- A set K of X is compact iff (K is empty or) any net s: D → X contained in K has a cluster point x such that x ∈ K. -/
theorem compact_iff_net_has_accumulationpoint {X : Type*} [TopologicalSpace X] (K: Set X) : IsCompact K ↔
  K = ∅ ∨ ∀ (D: Type u_1) (_: DirectedSet D) (s : D → X), (∀ (d : D), s d ∈ K) → (∃ x ∈ K, ClusterPoint s x) := by
    constructor
    · intro Kcomp
      by_cases Kem : K = ∅
      · left
        assumption
      · right
        intro D h s sinK
        simp only [IsCompact] at Kcomp
        rcases Kcomp ((le_principal_iff).mpr (net_in_set_implies_set_in_filter K D h s sinK)) with ⟨x, xinK, clpointFx⟩
        use x
        exact And.intro xinK ((clpoint_net_iff_filter s x).mpr clpointFx)
    · intro cond
      rcases cond with cond | cond
      · rw [cond]
        exact isCompact_empty
      · simp only [IsCompact]
        intro F Fnebot KinF
        rw [le_principal_iff] at KinF
        rcases cond (DirectedSetFA F K KinF) (DirectedSetFA.isntDirectedSet F K KinF) (NetFA F K KinF)
          (NetFA_subset F K KinF) with ⟨x, xinK, clpoint⟩
        use x
        exact And.intro xinK (clupoint_NetF_inclusion_implies_clpoint F K KinF x clpoint)

/- A set K of X is compact iff (K is empty or) any net s: D → X contained in K has a subnet that converges to a point of K. -/
theorem compact_iff_net_has_convergent_subnet {X : Type*} [TopologicalSpace X] (K: Set X) : IsCompact K ↔
  K = ∅ ∨ ∀ (D: Type u_1) (_: DirectedSet D) (s : D → X), (∀ (d : D), s d ∈ K) →
  (∃ (E: Type u_1) (_: DirectedSet E) (s': E → X), ∃ x ∈ K, Subnet s s' ∧ Limit s' x) := by
    have : (∀ (D: Type u_1) (h: DirectedSet D) (s : D → X), (∀ (d : D), s d ∈ K) → ∃ (E: Type u_1) (h': DirectedSet E) (s': E → X), ∃ x ∈ K, Subnet s s' ∧ Limit s' x) ↔
             (∀ (D: Type u_1) (h: DirectedSet D) (s : D → X), (∀ (d : D), s d ∈ K) → ∃ x ∈ K, ClusterPoint s x) := by
              constructor
              · intro t D h s dinK
                rcases t D h s dinK with ⟨E, h', s', x, xinK, eq⟩
                use x, xinK
                rw [clpoint_iff_exists_subnet]
                use E, h', s'
              · intro t D h s dinK
                rcases t D h s dinK with ⟨x, xinK, eq⟩
                rw [clpoint_iff_exists_subnet] at eq
                rcases eq with ⟨E, h', s', eq⟩
                use E, h', s', x
    rw [compact_iff_net_has_accumulationpoint, this]

/- A function f: X → Y is continuous at x iff for every net s: D → X we have that the net f ∘ s: D → Y converges to f x. -/
theorem continuous_iff_image_of_net_converges {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y] (f: X → Y) (x : X):
  ContinuousAt f x ↔ ∀ (D: Type u_1) (_: DirectedSet D) (s : D → X), Limit s x → Limit (f ∘ s) (f x) := by
    constructor
    · intro fcontatx D h s limitsx
      unfold ContinuousAt at fcontatx
      rw [Filter.tendsto_def] at fcontatx
      rw [limit_net_iff_filter]
      intro V Vnhds
      simp only [FNet, Filter.mem_mk, Set.mem_setOf_eq]
      have := limitsx (f ⁻¹' V) (fcontatx V Vnhds)
      simp only [mem_preimage] at this
      simp only [comp_apply]
      assumption
    · intro cond
      unfold ContinuousAt
      rw [Filter.tendsto_def]
      intro V Vnhds
      have : Limit (NetF (𝓝 x)) x := by
        intro U Unhds
        use ⟨(x, U), And.intro (mem_of_mem_nhds Unhds) Unhds⟩
        intro d xUled
        simp only [NetF]
        simp only [DirectedSetF_le_iff] at xUled
        exact xUled d.2.1
      rcases cond (DirectedSetF (𝓝 x)) (DirectedSetF.isntDirectedSet (𝓝 x)) (NetF (𝓝 x)) this V Vnhds with ⟨d, eq⟩
      have : d.1.2 ⊆ f ⁻¹' V := by
        intro z zind2
        rw [mem_preimage]
        have : d ≤ ⟨(z, d.1.2), And.intro zind2 d.2.2⟩ := by
          rw [DirectedSetF_le_iff]
        have := eq ⟨(z, d.1.2), And.intro zind2 d.2.2⟩ this
        simp only [NetF, comp_apply] at this
        assumption
      exact mem_of_superset d.2.2 this

/- A topological space X is T2 iff every net in X has at most one limit point. -/
theorem t2_iff_net_unique_limit {X : Type*} [TopologicalSpace X] :
  T2Space X ↔ ∀ (D: Type u_1) (_: DirectedSet D) (s : D → X) (x y : X), Limit s x → Limit s y → x = y := by
    rw [t2_iff_net_unique_limit_filter]
    constructor
    · intro cond
      intro D h s x y limitsx limitsy
      rw [limit_net_iff_filter] at *
      exact cond (FNet s) (FNet.instNeBot s) x y limitsx limitsy
    · intro cond F Fnebot x y limitFx limitFy
      rw [limit_filter_iff_net] at *
      exact cond (DirectedSetF F) (DirectedSetF.isntDirectedSet F) (NetF F) x y limitFx limitFy

theorem unique_limit {X D: Type*} [h: DirectedSet D] [TopologicalSpace X] [T: T2Space X] {s: D → X} {x y: X}:
  Limit s y → Limit s x → x = y := by
    rw [t2_iff_net_unique_limit_filter] at T
    intro slimity slimitx
    rw [limit_net_iff_filter] at *
    exact T (FNet s) (FNet.instNeBot s) x y slimitx slimity

/- A uniform space is complete iff is CompleteNet -/
theorem complete_iff_netcomplete {X: Type*} [UniformSpace X]:
  CompleteSpace X ↔ CompleteNet X := by
    constructor
    · intro completeX
      unfold CompleteNet
      intro D h s cauchys
      rcases completeX.complete ((cauchy_net_iff_filter s).mp cauchys) with ⟨x, limitFx⟩
      use x
      rw [limit_net_iff_filter]
      assumption
    · intro completeX
      unfold CompleteNet at completeX
      apply completeSpace_of_isComplete_univ
      unfold IsComplete
      intro F cauchyF _
      rcases completeX (DirectedSetF F) (@DirectedSetF.isntDirectedSet X F cauchyF.1) (NetF F)
        ((@cauchy_filter_iff_net X _ F cauchyF.1).mp cauchyF) with ⟨x, limitsx⟩
      use x
      constructor
      · exact mem_univ x
      · rw [@limit_filter_iff_net X _ F cauchyF.1 x]
        assumption
