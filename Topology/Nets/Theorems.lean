import Topology.Nets.Filter
import Mathlib.Topology.Algebra.InfiniteSum.Defs
import Mathlib.Topology.Constructions
import Mathlib.Analysis.Normed.Group.Basic

set_option trace.Meta.Tactic.simp false

noncomputable section

open Set Filter Topology Function DirectedSet Net

variable {X Y Z D: Type*} [TopologicalSpace X] [TopologicalSpace Y] [UniformSpace Z] [DirectedSet D]

/- ### Missing results for filters ### -/

/- Here we stablish a couple of results about filters. Mainly a characterization for the closure and for a Hausdorff space. -/

/- An element x of X is in the closure of A iff there exists a filter F in X such that it is NeBot, A ∈ F and x is a limit
   point of F. -/
theorem mem_closure_iff_exists_filter (A: Set X) (x : X) :
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
theorem t2_iff_filter:
  T2Space X ↔ ∀ (F: Filter X) (_: Filter.NeBot F) (x y : X),
    F ≤ 𝓝 x → F ≤ 𝓝 y → x = y := by
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

/- ### Limit of products ### -/

/- A net in a product space converges iff every coordinate converges -/
theorem prod_limit  {ι: Type*} {π : ι → Type*}
  [T : (i : ι) → TopologicalSpace (π i)]
  (s: D → (i : ι) → π i) (x: (i : ι) → π i) :
    Limit s x ↔ ∀ (i: ι), Limit (fun (d: D) ↦ s d i) (x i) := by
      simp only [limnet_iff_limfilter, ← tendsto_id']
      exact tendsto_pi_nhds

theorem prod_limit' (s: D → X × Y) (x: X × Y) :
  Limit s x ↔ Limit (fun (d: D) ↦ (s d).1) x.1 ∧ Limit (fun (d: D) ↦ (s d).2) x.2 := by
    rw [limnet_iff_limfilter, limnet_iff_limfilter, limnet_iff_limfilter,
        ← tendsto_id', ← tendsto_id', ← tendsto_id']
    exact Prod.tendsto_iff id x

/- ### Closure ### -/

/- An element x of X is in the closure of A iff there exists a net s: D → X such that it is contained in A and
   converges to x. -/

theorem mem_closure_of_exists_net (A: Set X) (x : X):
  (∃ (D: Type*) (_: DirectedSet D) (s: D → X),
    (∀ (d: D), s d ∈ A) ∧ Limit s x) → x ∈ closure A:= by
    rw [mem_closure_iff_exists_filter]
    intro cond
    rcases cond with ⟨D, h, s, sinA, limitsx⟩
    use filter_of_net s
    exact And.intro (filter_of_net.instNeBot s)
      (And.intro (set_in_filter_of_net_in_set A s sinA)
      ((limnet_iff_limfilter s x).mp limitsx))

theorem mem_closure_iff_exists_net (A: Set X) (x : X):
  x ∈ closure A ↔ ∃ (D: Type u_1) (_: DirectedSet D) (s: D → X),
    (∀ (d: D), s d ∈ A) ∧ Limit s x := by
    constructor
    · rw [mem_closure_iff_exists_filter]
      intro cond
      rcases cond with ⟨F, Fnebot, AinF, limitFx⟩
      use directedset_of_filter' F A AinF,
        directedset_of_filter'.isntDirectedSet F A AinF, net_of_filter' F A AinF
      exact And.intro (net_of_filter'_subset F A AinF) (limfilter'_implies_limnet F A AinF x limitFx)
    · exact mem_closure_of_exists_net A x

/- A set C of X is closed iff for every x in X and every net s: D → X contained in C that converges to x we have that x ∈ C. -/
theorem limit_self_of_isClosed (C: Set X) :
  IsClosed C → ∀ (x : X), ∀ (D: Type*) (_: DirectedSet D) (s : D → X),
    (∀ (d: D), s d ∈ C) → Limit s x → x ∈ C := by
      rw [isClosed_iff_forall_filter]
      intro cond
      intro x D h s sinC limitsx
      have : filter_of_net s ≤ 𝓟 C := by
        rw [le_principal_iff]
        exact set_in_filter_of_net_in_set C s sinC
      exact cond x (filter_of_net s) (filter_of_net.instNeBot s) this
        ((limnet_iff_limfilter s x).mpr limitsx)

theorem isClosed_iff_limit_self (C: Set X) :
  IsClosed C ↔ ∀ (x : X), ∀ (D: Type u_1) (_: DirectedSet D) (s : D → X),
    (∀ (d: D), s d ∈ C) → Limit s x → x ∈ C := by
    constructor
    · exact limit_self_of_isClosed C
    · rw [isClosed_iff_forall_filter]
      intro cond
      intro x F Fnebot CinF limitFx
      rw [le_principal_iff] at CinF
      exact cond x (directedset_of_filter' F C CinF)
        (directedset_of_filter'.isntDirectedSet F C CinF) (net_of_filter' F C CinF)
        (net_of_filter'_subset F C CinF) (limfilter'_implies_limnet F C CinF x limitFx)

/- ### Compactness ### -/

/- A set K of X is compact iff (K is empty or) any net s: D → X contained in K has a cluster point x such that x ∈ K. -/
theorem net_has_accumulationpoint_of_compact (K: Set X) : IsCompact K →
  K = ∅ ∨ ∀ (D: Type*) (_: DirectedSet D) (s : D → X),
    (∀ (d : D), s d ∈ K) → (∃ x ∈ K, ClusterPt s x) := by
      intro Kcomp
      by_cases Kem : K = ∅
      · left
        assumption
      · right
        intro D h s sinK
        simp only [IsCompact] at Kcomp
        rcases Kcomp ((le_principal_iff).mpr (set_in_filter_of_net_in_set K s sinK)) with
          ⟨x, xinK, clpointFx⟩
        use x
        exact And.intro xinK ((clpointnet_iff_clpointfilter s x).mpr clpointFx)

theorem net_has_accumulationpoint_of_compact' {K: Set X} (Knempty: K ≠ ∅) :
  IsCompact K → ∀ (D: Type*) (_: DirectedSet D) (s : D → X),
    (∀ (d : D), s d ∈ K) → (∃ x ∈ K, ClusterPt s x) := by
      intro Kcomp
      rcases net_has_accumulationpoint_of_compact K Kcomp with h | h
      · contradiction
      · assumption

theorem compact_iff_net_has_accumulationpoint (K: Set X) : IsCompact K ↔
  K = ∅ ∨ ∀ (D: Type u_1) (_: DirectedSet D) (s : D → X),
    (∀ (d : D), s d ∈ K) → (∃ x ∈ K, ClusterPt s x) := by
      constructor
      · exact net_has_accumulationpoint_of_compact K
      · intro cond
        rcases cond with cond | cond
        · rw [cond]
          exact isCompact_empty
        · simp only [IsCompact]
          intro F Fnebot KinF
          rw [le_principal_iff] at KinF
          rcases cond (directedset_of_filter' F K KinF)
            (directedset_of_filter'.isntDirectedSet F K KinF) (net_of_filter' F K KinF)
            (net_of_filter'_subset F K KinF) with ⟨x, xinK, clpoint⟩
          use x
          exact And.intro xinK (clupointnet'_implies_clpointfilter F K KinF x clpoint)

theorem compact_iff_net_has_accumulationpoint' {K: Set X} (Knempty: K ≠ ∅) :
  IsCompact K ↔ ∀ (D: Type u_1) (_: DirectedSet D) (s : D → X),
    (∀ (d : D), s d ∈ K) → (∃ x ∈ K, ClusterPt s x) := by
      constructor
      · exact net_has_accumulationpoint_of_compact' Knempty
      · intro cond
        exact (compact_iff_net_has_accumulationpoint K).mpr (@Or.inr (K = ∅) _ cond)

/- A set K of X is compact iff (K is empty or) any net s: D → X contained in K has a subnet that converges to a point of K. -/
theorem has_convergent_subnet_of_compact (K: Set X) : IsCompact K →
  K = ∅ ∨ ∀ (D: Type*) (_: DirectedSet D) (s : D → X), (∀ (d : D), s d ∈ K) →
  (∃ x ∈ K, ∃ (E: Type (max u_1 u_5)) (_: DirectedSet E) (s': E → X),
  Subnet s s' ∧ Limit s' x) := by
      intro Kcomp
      rcases (net_has_accumulationpoint_of_compact K Kcomp) with h | h
      · left
        assumption
      · right
        intro D Ddir s sinK
        rcases h D Ddir s sinK with ⟨x, xinK, xclpt⟩
        rw [clpoint_iff_exists_subnet] at xclpt
        use x

theorem has_convergent_subnet_of_compact' {K: Set X} (Knempty: K ≠ ∅) : IsCompact K →
  ∀ (D: Type*) (_: DirectedSet D) (s : D → X), (∀ (d : D), s d ∈ K) →
  (∃ x ∈ K, ∃ (E: Type (max u_1 u_5)) (_: DirectedSet E) (s': E → X),
  Subnet s s' ∧ Limit s' x) := by
      intro Kcomp
      rcases has_convergent_subnet_of_compact K Kcomp with h | h
      · contradiction
      · assumption

theorem compact_iff_net_has_convergent_subnet (K: Set X) : IsCompact K ↔
  K = ∅ ∨ ∀ (D: Type u_1) (_: DirectedSet D) (s : D → X), (∀ (d : D), s d ∈ K) →
  (∃ x ∈ K, ∃ (E: Type u_1) (_: DirectedSet E) (s': E → X), Subnet s s' ∧ Limit s' x) := by
    simp only [compact_iff_net_has_accumulationpoint, clpoint_iff_exists_subnet]

theorem compact_iff_net_has_convergent_subnet' {K: Set X} (Knempty: K ≠ ∅) :
  IsCompact K ↔
  ∀ (D: Type u_1) (_: DirectedSet D) (s : D → X), (∀ (d : D), s d ∈ K) →
  (∃ x ∈ K, ∃ (E: Type u_1) (_: DirectedSet E) (s': E → X), Subnet s s' ∧ Limit s' x) := by
    constructor
    · exact has_convergent_subnet_of_compact' Knempty
    · intro cond
      exact (compact_iff_net_has_convergent_subnet K).mpr (@Or.inr (K = ∅) _ cond)

/- ### Continuity ### -/

/- A function f: X → Y is continuous at x iff for every net s: D → X we have that the net f ∘ s: D → Y converges to f x. -/
theorem limfunnet_of_continuousAt (f: X → Y) (x : X) {s: D → X}:
  ContinuousAt f x → Limit s x → Limit (f ∘ s) (f x) := by
    intro fcontatx limitsx
    unfold ContinuousAt at fcontatx
    rw [Filter.tendsto_def] at fcontatx
    rw [limnet_iff_limfilter]
    intro V Vnhds
    simp only [filter_of_net, Filter.mem_mk, Set.mem_setOf_eq]
    have := limitsx (f ⁻¹' V) (fcontatx V Vnhds)
    simp only [mem_preimage] at this
    simp only [comp_apply]
    assumption

theorem limfunnet_of_continuousAt' {Z: Type*} [TopologicalSpace Z]
  {s: D → X} {t: D → Y} {x: X} {y: Y} {f: X × Y → Z} :
  ContinuousAt f (x,y) → Limit s x → Limit t y →
  Limit (fun (d: D) ↦ f ((s d), (t d))) (f (x, y)) := by
    intro contf slimitx tlimity
    let S: D → X × Y := fun (d: D) ↦ (s d, t d)
    have Slimitxy: Limit S (x,y) := by
      rw [prod_limit']
      exact And.intro slimitx tlimity
    exact limfunnet_of_continuousAt f (x,y) contf Slimitxy

theorem continuous_iff_image_of_net_converges (f: X → Y) (x : X):
  ContinuousAt f x ↔ ∀ (D: Type u_1) (_: DirectedSet D) (s : D → X),
    Limit s x → Limit (f ∘ s) (f x) := by
    constructor
    · intro fcontatx D Ddirected s slimitx
      exact limfunnet_of_continuousAt f x fcontatx slimitx
    · intro cond
      unfold ContinuousAt
      rw [Filter.tendsto_def]
      intro V Vnhds
      rcases cond (directedset_of_filter (𝓝 x))
        (directedset_of_filter.isntDirectedSet (𝓝 x))
        (net_of_filter (𝓝 x)) (limnet_of_filter_nhds x) V Vnhds with ⟨d, eq⟩
      have : d.1.2 ⊆ f ⁻¹' V := by
        intro z zind2
        rw [mem_preimage]
        have : d ≤ ⟨(z, d.1.2), And.intro zind2 d.2.2⟩ := by
          rw [directedset_of_filter_le_iff]
        have := eq ⟨(z, d.1.2), And.intro zind2 d.2.2⟩ this
        simp only [net_of_filter, comp_apply] at this
        assumption
      exact mem_of_superset d.2.2 this

/- ### Characterization of topologies in term of nets ### -/

theorem same_topology_iff_same_convergent_nets {X: Type*} [T₁: TopologicalSpace X]
  [T₂: TopologicalSpace X] :
    T₁ = T₂ ↔ ∀ (D: Type u_5) (_: DirectedSet D) (s: D → X) (x: X),
    (@Limit X D T₁ _ s x ↔ @Limit X D T₂ _ s x) := by
      constructor
      · intro eqtop
        intro D Ddir s x
        rw [eqtop]
      · intro cond
        rw [TopologicalSpace.ext_iff_isClosed]
        intro C
        rw [@isClosed_iff_limit_self X T₁ C, @isClosed_iff_limit_self X T₂ C]
        simp only [cond]

theorem IsPiTopology_iff_pointwise_convergence {ι: Type*} {π : ι → Type*}
  [T : (i : ι) → TopologicalSpace (π i)] [t: TopologicalSpace ((i : ι) → π i)] :
  t = Pi.topologicalSpace ↔ ∀ (D: Type (max u_5 u_6)) (_: DirectedSet D)
  (s: D → ((i : ι) → π i)) (x: ((i : ι) → π i)),
  (Limit s x ↔ ∀ (i: ι), Limit (fun (d: D) ↦ s d i) (x i)) := by
    constructor
    · intro Pitop D Ddir s x
      have := prod_limit s x
      rw [← Pitop] at this
      exact this
    · intro cond
      rw [@same_topology_iff_same_convergent_nets _ t Pi.topologicalSpace]
      intro D Ddir s x
      rw [cond D Ddir s x, prod_limit]

theorem induced_limit {X Y: Type*} (f: X → Y) [tY: TopologicalSpace Y]
  (s: D → X) (x: X) :
    @Limit X D (TopologicalSpace.induced f tY) _ s x ↔
    Limit (f ∘ s) (f x) := by
      constructor
      · intro slimitx
        have: @Continuous X Y (TopologicalSpace.induced f tY) tY f := by
          exact continuous_iff_le_induced.mpr
            (le_refl (TopologicalSpace.induced f tY))
        rw [@continuous_iff_continuousAt X Y (TopologicalSpace.induced f tY) tY] at this
        exact @limfunnet_of_continuousAt X Y D (TopologicalSpace.induced f tY)
          tY _ f x s (this x) slimitx
      · intro fslimitfx
        intro U Unhds
        rw [mem_nhds_induced] at Unhds
        rcases Unhds with ⟨V, Vnhds, prefVsubU⟩
        rcases fslimitfx V Vnhds with ⟨d₀, eq⟩
        use d₀
        intro d d₀led
        apply prefVsubU
        rw [mem_preimage]
        exact eq d d₀led

theorem IsinducedTopology_iff {X Y: Type*} (f: X → Y) [tX: TopologicalSpace X]
  [tY: TopologicalSpace Y] :
  tX = TopologicalSpace.induced f tY ↔ ∀ (D: Type u_5) (_: DirectedSet D)
  (s: D → X) (x: X), (Limit s x ↔ Limit (f ∘ s) (f x)) := by
    constructor
    · intro indudtop D Ddir s x
      rw [indudtop]
      exact induced_limit f s x
    · intro cond
      rw [@same_topology_iff_same_convergent_nets _ tX (TopologicalSpace.induced f tY)]
      intro D Ddir s x
      rw [cond D Ddir s x, induced_limit]

/- ### Operations on limits ### -/

/- Limit of constant net -/
theorem lim_of_cte (x: X): Limit (fun (_: D) ↦ x) x := by
  intro U Unhds
  use default
  intro d defled
  exact mem_of_mem_nhds Unhds

/- Sum of convergent nets is convergent -/
theorem lim_of_sum_eq_sum_of_lim [Add X] [h: ContinuousAdd X]
  {s t: D → X} {x y: X}:
  Limit s x → Limit t y → Limit (fun (d: D) ↦ (s d) + (t d)) (x + y) := by
    exact limfunnet_of_continuousAt'
      (continuous_iff_continuousAt.mp h.continuous_add (x, y))

/- Difference of convergent nets is convergent -/
theorem lim_of_sub_eq_sub_of_lim [Sub X] [h: ContinuousSub X]
  {s t: D → X} {x y: X} :
  Limit s x → Limit t y → Limit (fun (d: D) ↦ (s d) - (t d)) (x - y) := by
    exact limfunnet_of_continuousAt'
      (continuous_iff_continuousAt.mp h.continuous_sub (x, y))

/- Product of scalar and convergent nets is convergent -/
theorem prod_num_conv {R: Type*} [TopologicalSpace R] [SMul R X]
  [h: ContinuousSMul R X] {x: X} {s: D → X} (r: R):
  Limit s x → Limit (fun (d: D) ↦ r • (s d)) (r • x) := by
    intro slimitx
    exact limfunnet_of_continuousAt'
      (continuous_iff_continuousAt.mp h.continuous_smul (r, x))
        (lim_of_cte r) slimitx

/- ### T2 Spaces ### -/

/- A topological space X is T2 iff every net in X has at most one limit point. -/
theorem net_unique_limit_of_T2 :
  T2Space X → ∀ (D: Type*) (_: DirectedSet D) (s : D → X) (x y : X),
     Limit s x → Limit s y → x = y := by
      rw [t2_iff_filter]
      intro cond
      intro D h s x y limitsx limitsy
      rw [limnet_iff_limfilter] at *
      exact cond (filter_of_net s) (filter_of_net.instNeBot s) x y limitsx limitsy

theorem net_unique_limit_of_T2' {D: Type*} [h: DirectedSet D] [T: T2Space X]
  {s: D → X} {x y: X}:
    Limit s x → Limit s y → x = y := by
      exact net_unique_limit_of_T2 T D h s x y

theorem T2_iff_net_unique_limit :
  T2Space X ↔ ∀ (D: Type u_1) (_: DirectedSet D) (s : D → X) (x y : X),
    Limit s x → Limit s y → x = y := by
    constructor
    · exact net_unique_limit_of_T2
    · rw [t2_iff_filter]
      intro cond F Fnebot x y limitFx limitFy
      rw [limfilter_iff_limnet] at *
      exact cond (directedset_of_filter F) (directedset_of_filter.isntDirectedSet F)
        (net_of_filter F) x y limitFx limitFy

/- ### Completeness ### -/

/- A uniform space is complete iff is CompleteNet -/
theorem complete_iff_netcomplete:
  CompleteSpace Z ↔ CompleteNet Z := by
    constructor
    · intro completeZ
      unfold CompleteNet
      intro D h s cauchys
      rcases completeZ.complete ((cauchynet_iff_cauchyfilter s).mp cauchys) with ⟨x, limitFx⟩
      use x
      rw [limnet_iff_limfilter]
      assumption
    · intro completeZ
      unfold CompleteNet at completeZ
      apply completeSpace_of_isComplete_univ
      unfold IsComplete
      intro F cauchyF _
      rcases completeZ (directedset_of_filter F)
        (@directedset_of_filter.isntDirectedSet Z F cauchyF.1) (net_of_filter F)
        ((@cauchyfilter_iff_cauchynet Z _ F cauchyF.1).mp cauchyF) with ⟨x, limitsx⟩
      use x
      constructor
      · exact mem_univ x
      · rw [@limfilter_iff_limnet Z _ F cauchyF.1 x]
        assumption

/- Completeness in metric spaces is equivalent to the statement that every Cauchy sequence is convergent -/

variable {M: Type*} [PseudoMetricSpace M]

theorem complete_iff_seqcomplete :
  CompleteSpace M ↔ ∀ (s: ℕ → M), CauchyNet s → ∃ (x: M), Limit s x := by
    constructor
    · intro completeX s cauchys
      rw [cauchynet_iff_cauchyfilter] at cauchys
      rcases completeX.complete cauchys with ⟨x, limitFx⟩
      use x
      rw [limnet_iff_limfilter]
      assumption
    · intro cauchyconv
      apply Metric.complete_of_cauchySeq_tendsto
      simp only [cauchySeq_iff_cauchynet, ← limit_iff_tendsto]
      assumption

/- ### Construction of a sequence from a net ### -/

/- Given a Cauchy net t: D → X in a metric space X and a positive sequence s: ℕ → ℝ, we can extract
   an (strictly) increasing sequence r : ℕ → D, such that for any d, e in D with r n ≤ d, e, we have that
   dist (t d) (t e) < s n. -/

def seq_of_net (t: D → M) (s: ℕ → ℝ): ℕ → D := fun k ↦ by
  classical
  exact match k with
  | 0 => if h: ∃ d₀, (∀ (d e : D), d₀ ≤ d → d₀ ≤ e → dist (t d) (t e) < s 0) then
     Classical.choose h else default
  | n + 1 => if h: ∃ (d₀: D), ((seq_of_net t s n) ≤ d₀ ∧
    ((∀ (d e : D), d₀ ≤ d → d₀ ≤ e → dist (t d) (t e) < s (n + 1)))) then
     Classical.choose h else default

/- If the net t: D → X is Cauchy, then seqfromnet satisfies what we want -/
lemma seq_of_net_def (t: D → M) (s: ℕ → ℝ) (spos: ∀ (n: ℕ), 0 < s n)
  (h: CauchyNet t):
    ∀ (n: ℕ), (∀ (d e : D), seq_of_net t s n ≤ d →
    seq_of_net t s n ≤ e → dist (t d) (t e) < s n) := by
      intro n d e led lee
      rw [cauchy_metric_iff] at h
      by_cases nz: n = 0
      · have cond := h (s 0) (spos 0)
        rw [nz] at led lee
        dsimp only [seq_of_net] at *
        rw [dif_pos cond] at *
        rw [nz]
        exact Classical.choose_spec cond d e led lee
      · rcases Nat.exists_eq_succ_of_ne_zero nz with ⟨m, neqm1⟩
        rw [Nat.succ_eq_add_one] at neqm1
        rw [neqm1] at led lee
        have cond : ∃ (d₀: D), ((seq_of_net t s m) ≤ d₀ ∧
          ((∀ (d e : D), d₀ ≤ d → d₀ ≤ e → dist (t d) (t e) < s (m + 1)))) := by
            rcases h (s (m + 1)) (spos (m + 1)) with ⟨d₁, eq⟩
            rcases directed' d₁ (seq_of_net t s m) with ⟨d₀, d₁led₀, led₀⟩
            use d₀
            constructor
            · assumption
            · intro d e d₀led d₀lee
              exact eq d e (le_trans d₁led₀ d₀led) (le_trans d₁led₀ d₀lee)
        dsimp only [seq_of_net] at *
        rw [dif_pos cond] at *
        rw [neqm1]
        exact (Classical.choose_spec cond).2 d e led lee

/- The defined sequence is increasing -/
lemma seq_of_net_le_succ (t: D → M) (s: ℕ → ℝ) (spos: ∀ (n: ℕ), 0 < s n)
  (h: CauchyNet t):
    ∀ (n: ℕ), seq_of_net t s n ≤ seq_of_net t s (n + 1) := by
      intro n
      rw [cauchy_metric_iff] at h
      have cond : ∃ d₀, seq_of_net t s n ≤ d₀ ∧
        ∀ (d e : D),  d₀ ≤ d → d₀ ≤ e → dist (t d) (t e) < s (n + 1) := by
          rcases h (s (n + 1)) (spos (n + 1)) with ⟨d₁, eq⟩
          rcases directed' (seq_of_net t s n) d₁ with ⟨d₀, seqmled₀, d₁led₀⟩
          use d₀
          constructor
          · assumption
          · intro d e d₀led d₀lee
            exact eq d e (le_trans d₁led₀ d₀led) (le_trans d₁led₀ d₀lee)
      dsimp only [seq_of_net]
      rw [dif_pos cond]
      exact (Classical.choose_spec cond).1

lemma seq_of_net_monotone (t: D → M) (s: ℕ → ℝ) (spos: ∀ (n: ℕ), 0 < s n)
  (h: CauchyNet t):
    Monotone (seq_of_net t s) := by
      intro n m nlem
      induction' m with m ih
      · rw [Nat.le_zero] at nlem
        rw [nlem]
      · rw [Nat.le_succ_iff_eq_or_le] at nlem
        rcases nlem with neqm1 | nlem
        · rw [Nat.succ_eq_add_one] at neqm1
          rw [← neqm1]
        · exact le_trans (ih nlem) (seq_of_net_le_succ t s spos h m)

/- If if s has limit 0 , then the sequence t ∘ (seqfromnet t s) is a Cauchy sequence with the porperty that if
   it converges, then so does t and to the same point -/

lemma seq_of_net_cauchy (t: D → M) (s: ℕ → ℝ) (spos: ∀ (n: ℕ), 0 < s n)
  (h: CauchyNet t) (slimitz: Limit s 0):
    CauchyNet (t ∘ seq_of_net t s) := by
      rw [cauchy_metric_iff]
      intro ε εpos
      rw [limit_metric_iff] at slimitz
      rcases slimitz ε εpos with ⟨n₀, eq⟩
      have sn₀leε : s n₀ < ε := by
        have := eq n₀ (le_refl n₀)
        rw [dist_zero_right, Real.norm_eq_abs] at this
        exact lt_of_abs_lt this
      use n₀
      intro n m n₀len n₀lem
      have := seq_of_net_def t s spos h n₀ (seq_of_net t s n) (seq_of_net t s m)
        (seq_of_net_monotone t s spos h n₀len) (seq_of_net_monotone t s spos h n₀lem)
      exact lt_trans this sn₀leε

lemma limnet_of_seq_of_net (t: D → M) (s: ℕ → ℝ) (spos: ∀ (n: ℕ), 0 < s n)
  (h: CauchyNet t) (slimitz: Limit s 0) (x: M):
    Limit (t ∘ seq_of_net t s) x → Limit t x := by
      intro tseqlimitx
      rw [limit_metric_iff] at *
      intro ε εpos
      rcases tseqlimitx (ε/2) (by linarith) with ⟨n₀, eq⟩
      rcases slimitz (ε/2) (by linarith) with ⟨n₁, eq'⟩
      have sleε2 : s (max n₀ n₁) < ε/2 := by
        have := eq' (max n₀ n₁) (le_max_right n₀ n₁)
        rw [dist_zero_right, Real.norm_eq_abs] at this
        exact lt_of_abs_lt this
      use seq_of_net t s (max n₀ n₁)
      intro d seqfled
      calc
        dist (t d) x ≤ dist (t d) (t (seq_of_net t s (max n₀ n₁))) +
        dist (t (seq_of_net t s (max n₀ n₁))) x := by
          exact dist_triangle (t d) (t (seq_of_net t s (max n₀ n₁))) x
        _ < ε/2 + dist (t (seq_of_net t s (max n₀ n₁))) x := by
          rw [add_lt_add_iff_right]
          have := seq_of_net_def t s spos h (max n₀ n₁) d
             (seq_of_net t s (max n₀ n₁)) seqfled
             (le_refl (seq_of_net t s (max n₀ n₁)))
          exact lt_trans this sleε2
        _ < ε/2 + ε/2 := by
          rw [add_lt_add_iff_left]
          exact eq (max n₀ n₁) (le_max_left n₀ n₁)
        _ = ε := by
          linarith
