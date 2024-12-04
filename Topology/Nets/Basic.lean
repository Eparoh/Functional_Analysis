import Topology.Nets.Defs

open Set Filter Topology Function DirectedSet

set_option trace.Meta.Tactic.simp false

namespace Net

/- ### Basic results ### -/

/- Subsequences are subnets -/
theorem subsequence_is_subnet {X: Type*} (s s' : ℕ → X) :
  (∃ (i: ℕ → ℕ), StrictMono i ∧ s' = s ∘ i) → Subnet s s' := by
  intro h
  unfold Subnet
  rcases h with ⟨i, stricmono_i, s'eqscompi⟩
  use i
  constructor
  · intro d
    use d
    intro e dlee
    exact le_trans dlee (StrictMono.id_le stricmono_i e)
  · assumption

theorem shift_subsequence {X: Type*} (s : ℕ → X) (k: ℕ): Subnet s (fun (n: ℕ) ↦ s (n + k)) := by
  apply subsequence_is_subnet
  use fun (n: ℕ) ↦ n + k
  constructor
  · intro n m nltm
    exact Nat.add_lt_add_right nltm k
  · rfl

/- If a net s converges to a point x in X, then every subnet of s converges to x. -/
theorem subnet_same_limit {X D E: Type*} [TopologicalSpace X] [DirectedSet D] [DirectedSet E]
  {s : D → X} {s' : E → X} {x : X} : Subnet s s' → Limit s x → Limit s' x := by
    intro subnet slimitx
    unfold Limit at *
    intro U U_nhds
    unfold Subnet at subnet
    rcases subnet with ⟨i, crec, comp⟩
    rw [comp]
    rcases slimitx U U_nhds with ⟨d, eq_d⟩ -- We take d so that if d ≤ d' then s(d') ∈ U
    rcases crec d with ⟨e, eq_e⟩ -- We take e so that if e ≤ e' then d ≤ i(e')
    /- Then, if e ≤ e', we have that d ≤ i(e') and so s(i(e')) ∈ U as wanted -/
    use e
    intro e' elee'
    have := eq_e e' elee'
    have := eq_d (i e') this
    exact this

theorem shift_subsequence_conv {X: Type*} [TopologicalSpace X] (s : ℕ → X) (k: ℕ) {x: X}:
  Limit s x ↔ Limit (fun (n: ℕ) ↦ s (n + k)) x := by
    constructor
    · intro slimitx
      exact subnet_same_limit (shift_subsequence s k) slimitx
    · intro slimitx
      intro U Unhds
      rcases slimitx U Unhds with ⟨d₀, eq⟩
      use d₀ + k
      intro d d₀kled
      have:= eq (d - k) (Nat.le_sub_of_add_le d₀kled)
      dsimp at this
      rw [← tsub_tsub_assoc (le_of_add_le_right d₀kled) (le_refl k), Nat.sub_self, Nat.sub_zero] at this
      assumption

/- If a point x in X is a cluster point of a net s' and s' is a subnet of another net s, then x is also a cluster point of s. -/
theorem subnet_clusterpoint_implies_net {X D E: Type*} [TopologicalSpace X] [DirectedSet D] [DirectedSet E]
  {s : D → X} {s' : E → X} {x : X} : Subnet s s' → ClusterPoint s' x → ClusterPoint s x := by
    intro subnet clpoints'x
    unfold ClusterPoint at *
    intro d U Unhds
    unfold Subnet at subnet
    rcases subnet with ⟨i, crec, comp⟩
    /- Take some e₀ in E such that for any e in E we have that if e₀ ≤ e, then d ≤ i e (by "crec"). Then, as x is a cluster point
       of s', we have that there exists some e in E such that e₀ ≤ e and s' e ∈ U.
       Then, the looked point in D is i e. In fact, by "crec" we have that d ≤ i e, and we also have that s (i e) = s' e ∈ U. -/
    rcases crec d with ⟨e₀, eq⟩
    rcases clpoints'x e₀ U Unhds with ⟨e, e₀lee, s'einU⟩
    use i e
    constructor
    · exact eq e e₀lee
    · rw [← @comp_apply D X E s i e, ← comp]
      assumption

/- A point x is an accumulation point of a net s iff there exists a subnet that converges to x -/
theorem clpoint_iff_exists_subnet {X D: Type*} [TopologicalSpace X] [h: DirectedSet D] (s: D → X) (x : X) :
  ClusterPoint s x ↔ ∃ (E: Type (max u_1 u_2)) (_: DirectedSet E) (s': E → X), (Subnet s s' ∧ Limit s' x) := by
    classical
    constructor
    · intro t
      unfold ClusterPoint at t
      have existence : ∀ V ∈ 𝓝 x, ∀ (d: D), ∃ (e: D), (d ≤ e ∧ s e ∈ V) := by
        intro V V_nhds d
        exact t d V V_nhds
      /- Since given any neighbourhood V of x and any d of D there exists an element e of D such that
         d ≤ e and s(e) ∈ V, we'll define i(V, d) = e and the subnet s' = s ∘ i (with 𝓝 x
         ordered by ⊇), so s'(V,d) ∈ V -/
      let i : {V | V ∈ 𝓝 x} × D → D := fun (⟨V, _⟩, d) ↦ if h: ∃ (e: D), (d ≤ e ∧ s e ∈ V) then Classical.choose h else d
      let s' : {V | V ∈ 𝓝 x} × D → X := s ∘ i
      use ({V | V ∈ 𝓝 x} × D), (@instProduct {V | V ∈ 𝓝 x} D (instNeighbourhoodLeft x) h), s'
      constructor
      · unfold Subnet
        use i
        constructor
        · intro d
          /- Using (X, d), we have that if (X, d) ≤ e = (e₁, e₂), then d ≤ e₂ and, As e₂ ≤ i(e), we
             obtain that d ≤ i(e) -/
          use (⟨univ, univ_mem⟩ , d)
          intro e t'
          simp only [Prod.le_def] at t'
          dsimp only [i]
          rw [dif_pos (existence e.1 e.1.2 e.2)] -- choose = i(e)
          have := Classical.choose_spec (existence e.1 e.1.2 e.2)
          apply le_trans t'.2 this.1
        · rfl
      · unfold Limit
        intro U U_nhds
        /- Given any d in D, we can use (U, d). In fact, if (U, d) ≤ e = (e₁, e₂), then e₁ ⊆ U
           and s(i(e)) ∈ e₁, so s(i(e)) ∈ U -/
        let d := DirectedSet.default' D
        use (⟨U, U_nhds⟩ , d)
        intro e le_e
        simp only [Prod.le_def] at le_e
        simp only [s', i, Set.coe_setOf, comp_apply]
        rw [dif_pos (existence e.1.1 e.1.2 e.2)] -- choose = i(e)
        have := (Classical.choose_spec (existence e.1.1 e.1.2 e.2)).right
        exact le_e.1 this
    · intro t
      rcases t with ⟨E, h', s', subnet_s', limit_s'⟩
      unfold ClusterPoint
      intro d U U_nhds
      /- As s' is a subnet of s, there exists an i: s'.D → s.D such that there exists an e₀ with the
         property that if e₀ ≤ e, then d ≤ i(e). Furthermore, as s' converges to x there exists an e₁
         in s'.D such that if e₁ ≤ e, then s'(e) = s(i(e)) ∈ U. So, it suffices to use an e in s.D with
         e₀, e₁ ≤ e. -/
      unfold Subnet at subnet_s'
      rcases subnet_s' with ⟨i, i_crec, s'eqscompi⟩
      rcases i_crec d with ⟨e₀, e₀_eq⟩
      unfold Limit at limit_s'
      rcases limit_s' U U_nhds with ⟨e₁, e₁_eq⟩
      rcases DirectedSet.directed' e₀ e₁ with ⟨e, e₀lee, e₁lee⟩
      use i e
      constructor
      · exact e₀_eq e e₀lee
      · have : s (i e) = (s ∘ i) e := by
          rfl
        rw [this, ← s'eqscompi]
        apply e₁_eq e e₁lee
