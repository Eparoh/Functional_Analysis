import Topology.Nets.DirectedSet

open Set Filter Topology Function DirectedSet

set_option trace.Meta.Tactic.simp false

namespace Net

variable {X D E F: Type*} [TopologicalSpace X] [DirectedSet D] [DirectedSet E]

/- ### Definitions ### -/

/- A net is simply a map s: D → X from a  directed set to  topological space X. -/

/- We say that a net s: D → X converges to a point x in X if for every neighborhood U of x there exists a d₀ in D such that
   for any d in D with d₀ ≤ d, we obtain that s d ∈ U. -/
def Limit (s : D → X) (x: X) : Prop :=
  ∀ U ∈ 𝓝 x, ∃ (d₀ : D), ∀ (d : D), d₀ ≤ d → s d ∈ U

/- We say that a point x in X is a cluster point of a net s: D → X if for every d in D and every neighborhood U of x there exists
   an e in D such that d ≤ e and s e ∈ U. -/
def ClusterPt (s: D → X) (x : X): Prop :=
  ∀ (d : D), ∀ U ∈ 𝓝 x, ∃ (e : D), (d ≤ e ∧ s e ∈ U)

/- We say that a net s': E → X is a subnet of a net s: D → X if there exists a cofinal map i : E → D such that s' = s ∘ i.
   With cofinal we mean that given any d in D, there exists an e₀ in E such that for any e in E, if e₀ ≤ e then d ≤ i e. -/
def Subnet {X: Type*} (s: D → X) (s': E → X) : Prop :=
  ∃ (i: E → D), (∀ (d : D), ∃ (e₀ : E), ∀ (e : E), (e₀ ≤ e →  d ≤ (i e))) ∧ s' = s ∘ i

/- We say that a net s: D → X on a uniform space X is Cauchy if for every U in the uniformity
   of X thre exists some d₀ in I such that (s d, s e) ∈ U for all d₀ ≤ d, e -/
def CauchyNet {X: Type*} [UniformSpace X] (s: D → X): Prop :=
   ∀ U ∈ uniformity X, ∃ (d₀: D), ∀ (d e: D), (d₀ ≤ d → d₀ ≤ e → (s d, s e) ∈ U)

def CompleteNet (X: Type*) [UniformSpace X]: Prop :=
   ∀ (D: Type u_5) (_: DirectedSet D) (s : D → X), (CauchyNet s → ∃ (x: X), Limit s x)

/- ### Basic results about subnets ### -/

/- If a net s converges to a point x in X, then every subnet of s converges to x. -/
theorem subnet_same_limit {s : D → X} {s' : E → X} {x : X} :
  Subnet s s' → Limit s x → Limit s' x := by
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

theorem shift_subsequence {X: Type*} (s : ℕ → X) (k: ℕ):
  Subnet s (fun (n: ℕ) ↦ s (n + k)) := by
    apply subsequence_is_subnet
    use fun (n: ℕ) ↦ n + k
    constructor
    · intro n m nltm
      exact Nat.add_lt_add_right nltm k
    · rfl

theorem shift_subsequence_conv (s : ℕ → X) (k: ℕ) {x: X}:
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

/- ### Basic results about cluster points ### -/

/- If a point x in X is a cluster point of a net s' and s' is a subnet of another net s, then x is also a cluster point of s. -/
theorem subnet_clusterpoint_implies_net {s : D → X} {s' : E → X} {x : X} :
  Subnet s s' → ClusterPt s' x → ClusterPt s x := by
    intro subnet clpoints'x
    unfold ClusterPt at *
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
theorem clpoint_iff_exists_subnet {D: Type*} [h: DirectedSet D] (s: D → X) (x : X) :
  ClusterPt s x ↔ ∃ (E: Type (max u_1 u_5)) (_: DirectedSet E) (s': E → X), (Subnet s s' ∧ Limit s' x) := by
    classical
    constructor
    · intro t
      unfold ClusterPt at t
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
      unfold ClusterPt
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
