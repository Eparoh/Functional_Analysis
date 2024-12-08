import Topology.Nets.DirectedSet
import Mathlib.Data.Fintype.Lattice
import Mathlib.Analysis.Normed.Group.Basic

noncomputable section

open Set Filter Topology Function DirectedSet

set_option trace.Meta.Tactic.simp false

namespace Net

variable {X D E F Z: Type*} [TopologicalSpace X] [DirectedSet D] [DirectedSet E] [UniformSpace Z]

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
def CauchyNet (s: D → Z): Prop :=
   ∀ U ∈ uniformity Z, ∃ (d₀: D), ∀ (d e: D), (d₀ ≤ d → d₀ ≤ e → (s d, s e) ∈ U)

def CompleteNet (X: Type*) [UniformSpace X] : Prop :=
   ∀ (D: Type u_6) (_: DirectedSet D) (s : D → X), (CauchyNet s → ∃ (x: X), Limit s x)

/- ### Equivalence with TendsTo and CauchySeq ### -/

theorem limit_iff_tendsto (s: D → X) (x: X) : Limit s x ↔ Tendsto s Filter.atTop (𝓝 x) := by
  simp only [tendsto_nhds, mem_atTop_sets, ge_iff_le, mem_preimage]
  unfold Limit
  constructor
  · intro h U Uopen xinU
    rcases h U (IsOpen.mem_nhds Uopen xinU) with ⟨d₀, eq⟩
    use d₀
  · intro h U Unhds
    rw [mem_nhds_iff] at Unhds
    rcases Unhds with ⟨V, VsubU, Vopen, xinV⟩
    rcases h V Vopen xinV with ⟨d₀, eq⟩
    use d₀
    intro d d₀led
    apply VsubU
    exact eq d d₀led

theorem cauchySeq_iff_cauchynet
  (f: D → Z) : CauchySeq f ↔ CauchyNet f := by
    unfold CauchySeq CauchyNet
    rw [cauchy_iff']
    simp only [mem_map, mem_atTop_sets, ge_iff_le, mem_preimage]
    constructor
    · intro h U Uinunif
      rcases h.2 U Uinunif with ⟨A, eq⟩
      rcases eq.1 with ⟨d₀, inA⟩
      use d₀
      intro d e d₀led d₀lee
      exact eq.2 (f d) (inA d d₀led) (f e) (inA e d₀lee)
    · intro h
      constructor
      · exact map_neBot
      · intro U Uinunif
        rcases h U Uinunif with ⟨d₀, eq⟩
        use f '' {d: D | d₀ ≤ d}
        simp only [mem_image, Set.mem_setOf_eq]
        constructor
        · use d₀
          intro d d₀led
          use d
        · intro x condx y condy
          rcases condx with ⟨dx, d₀ledx, fdxeqx⟩
          rcases condy with ⟨dy, d₀ledy, fdyeqy⟩
          rw [← fdxeqx, ← fdyeqy]
          exact eq dx dy d₀ledx d₀ledy

/- ### Basic results about subnets ### -/

/- If a net s converges to a point x in X, then every subnet of s converges to x. -/
theorem limsubnet_of_limnet {s : D → X} {s' : E → X} {x : X} :
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

theorem cauchysubnet_of_cauchynet {s : D → Z} {s' : E → Z} :
  Subnet s s' → CauchyNet s → CauchyNet s' := by
    intro subnetss' cauchys
    unfold CauchyNet at *
    rcases subnetss' with ⟨i, iincr, s'eqsi⟩
    simp only [s'eqsi, comp_apply]
    intro U Uinunif
    rcases cauchys U Uinunif with ⟨d₀, eq⟩
    rcases iincr d₀ with ⟨e₀, eq'⟩
    use e₀
    intro e e' e₀lee e₀lee'
    exact eq (i e) (i e') (eq' e e₀lee) (eq' e' e₀lee')

theorem lim_of_subnet_of_subnet {D: Type u_1} [DirectedSet D]
  (s: D → X) (x: X) :
    (∀ (E: Type u_1) (_: DirectedSet E) (s': E → X),
    Subnet s s' →  ∃ (F: Type u_1) (_: DirectedSet F) (s'': F → X),
    (Subnet s' s'' ∧ Limit s'' x)) →
    Limit s x := by
      classical
      intro cond
      unfold Limit
      by_contra! xnolimits
      rcases xnolimits with ⟨U, Unhds, eq⟩
      let i: D → D := fun (d: D) ↦
        if h: ∃ e, (d ≤ e ∧ s e ∉ U) then Classical.choose h else default
      have iincr: ∀ (d : D), ∃ e₀, ∀ (e : D), e₀ ≤ e → d ≤ i e := by
        intro d
        use d
        intro d' dled'
        unfold i
        rw [dif_pos (eq d')]
        exact le_trans dled' (Classical.choose_spec (eq d')).1
      let s': D → X := s ∘ i
      have subnetss' : Subnet s s' := by
        use i
      rcases cond D _ s' subnetss' with ⟨F, _, ⟨s'', subnets'', s''limitx⟩⟩
      rcases subnets'' with ⟨i', i'incr, s''eq⟩
      rcases s''limitx U Unhds with ⟨d₀, s''cond⟩
      simp only [s''eq, s', comp_apply] at s''cond
      have sii'd₀inU := s''cond d₀ (le_refl d₀)
      have sii'd₀ninU := (Classical.choose_spec (eq (i' d₀))).2
      have : i (i' d₀) = Classical.choose (eq (i' d₀)) := by
        unfold i
        rw [dif_pos (eq ((i' d₀)))]
      rw [← this] at sii'd₀ninU
      contradiction

/- Subsequences are subnets -/
theorem subnet_of_subsequence {X: Type*} (s s' : ℕ → X) :
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
    apply subnet_of_subsequence
    use fun (n: ℕ) ↦ n + k
    constructor
    · intro n m nltm
      exact Nat.add_lt_add_right nltm k
    · rfl

theorem netlim_iff_shift_subsequence_lim (s : ℕ → X) (k: ℕ) {x: X}:
  Limit s x ↔ Limit (fun (n: ℕ) ↦ s (n + k)) x := by
    constructor
    · intro slimitx
      exact limsubnet_of_limnet (shift_subsequence s k) slimitx
    · intro slimitx
      intro U Unhds
      rcases slimitx U Unhds with ⟨d₀, eq⟩
      use d₀ + k
      intro d d₀kled
      have:= eq (d - k) (Nat.le_sub_of_add_le d₀kled)
      dsimp at this
      rw [← tsub_tsub_assoc (le_of_add_le_right d₀kled) (le_refl k),
          Nat.sub_self, Nat.sub_zero] at this
      assumption

theorem cauchynet_iff_shift_subsequence_cauchy (s : ℕ → Z) (k: ℕ):
  CauchyNet s ↔ CauchyNet (fun (n: ℕ) ↦ s (n + k)) := by
    constructor
    · exact cauchysubnet_of_cauchynet (shift_subsequence s k)
    · intro cauchyshift
      unfold CauchyNet at *
      dsimp at cauchyshift
      intro U Uinunif
      rcases cauchyshift U Uinunif with ⟨n₀, eq⟩
      use n₀ + k
      intro n m n₀len n₀lem
      have := eq (n - k) (m - k) (Nat.le_sub_of_add_le n₀len)
        (Nat.le_sub_of_add_le n₀lem)
      rw [← tsub_tsub_assoc (le_of_add_le_right n₀len) (le_refl k),
          Nat.sub_self, Nat.sub_zero, ← tsub_tsub_assoc
          (le_of_add_le_right n₀lem) (le_refl k),
          Nat.sub_self, Nat.sub_zero] at this
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
  ClusterPt s x ↔ ∃ (E: Type (max u_1 u_6)) (_: DirectedSet E) (s': E → X), (Subnet s s' ∧ Limit s' x) := by
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

/- ### Characterization of convergence and Cauchy in metric spaces ### -/

variable {M: Type*} [PseudoMetricSpace M]

/- Characterization of convergence in a metric space -/
lemma limit_metric_iff (s: D → M) (x: M):
  Limit s x ↔
  ∀ ε > 0, ∃ (d₀: D), (∀ (d: D), d₀ ≤ d → dist (s d) x < ε) := by
    simp only [limit_iff_tendsto, Metric.tendsto_nhds, Filter.eventually_atTop]

/- Characterization of a Cauchy net in a metric space -/
lemma cauchy_metric_iff (s: D → M):
  CauchyNet s ↔
  ∀ ε > 0, ∃ (d₀: D), (∀ (d e: D), d₀ ≤ d → d₀ ≤ e → dist (s d) (s e) < ε) := by
    constructor
    · intro sCauchy
      intro ε εpos
      have := sCauchy {p | dist p.1 p.2 < ε} (Metric.dist_mem_uniformity εpos)
      simp only [Set.mem_setOf_eq] at this
      assumption
    · intro cond
      intro U Uunif
      rw [Metric.mem_uniformity_dist] at Uunif
      rcases Uunif with ⟨ε, εpos, eq⟩
      rcases cond ε εpos with ⟨d₀, eq'⟩
      use d₀
      intro d e d₀led d₀lee
      exact eq (eq' d e d₀led d₀lee)

lemma Nat_cauchy_metric_iff (s: ℕ → M):
  CauchyNet s ↔
  ∀ (ε: ℝ), (0 < ε →
    ∃ (n₀: ℕ), (∀ (n m: ℕ), n₀ ≤ n → n ≤ m → dist (s n) (s m) < ε)) := by
    rw [cauchy_metric_iff]
    constructor
    · intro cond ε εpos
      rcases cond ε εpos with ⟨n₀, eq⟩
      use n₀
      intro n m n₀len nlem
      exact eq n m n₀len (le_trans n₀len nlem)
    · intro cond ε εpos
      rcases cond ε εpos with ⟨n₀, eq⟩
      use n₀
      intro n m n₀len n₀lem
      by_cases h: n ≤ m
      · exact eq n m n₀len h
      · rw [Nat.not_le] at h
        rw [dist_comm]
        exact eq m n n₀lem (le_of_lt h)

/- ### Some results about Cauchy nets ### -/

/- Any convergent net in a uniform space is Cauchy -/
theorem cauchy_of_exists_lim {s: D → Z} (h: ∃ (x: Z), Limit s x):
  CauchyNet s := by
    intro U Uunif
    rcases comp_mem_uniformity_sets Uunif with ⟨V, Vunif, VoVsubU⟩
    rcases h with ⟨x, slimitx⟩
    rcases slimitx {y: Z | (x, y) ∈ V} (by exact mem_nhds_left x Vunif) with ⟨d₁, eq1⟩
    rcases slimitx {y: Z | (y, x) ∈ V} (by exact mem_nhds_right x Vunif) with ⟨d₂, eq2⟩
    rcases directed' d₁ d₂ with ⟨d₀, d₁led₀, d₂led₀⟩
    use d₀
    intro d e d₀led d₀lee
    apply VoVsubU
    rw [mem_compRel]
    use x
    constructor
    · have:= eq2 d (le_trans d₂led₀ d₀led)
      rw [Set.mem_setOf_eq] at this
      assumption
    · have:= eq1 e (le_trans d₁led₀ d₀lee)
      rw [Set.mem_setOf_eq] at this
      assumption

theorem lim_of_clpoint_of_cauchynet {s: D → Z} (scauchy: CauchyNet s) (x: Z) :
  ClusterPt s x → Limit s x := by
    intro cond
    unfold ClusterPt at cond
    intro U Unhds
    rw [mem_nhds_uniformity_iff_right] at Unhds
    rcases comp_mem_uniformity_sets Unhds with ⟨W, Winunif, WWsub⟩
    rcases scauchy W Winunif with ⟨d₀, eq⟩
    use d₀
    intro d d₀led
    rcases cond d (UniformSpace.ball x W)
      (UniformSpace.ball_mem_nhds x Winunif) with ⟨e, dlee, seinWball⟩
    unfold UniformSpace.ball at seinWball
    rw [mem_preimage] at seinWball
    have : (x, s d) ∈ compRel W W := by
      rw [mem_compRel]
      use s e
      exact And.intro seinWball (eq e d (le_trans d₀led dlee) d₀led)
    have := WWsub this
    rw [Set.mem_setOf_eq] at this
    exact this (rfl)

theorem lim_of_subnet_of_cauchynet {s: D → Z} (scauchy: CauchyNet s) (x: Z) :
  (∃ (E: Type (max u_2 u_5)) (_: DirectedSet E) (s': E → Z),
  Subnet s s' ∧ Limit s' x) → Limit s x := by
    intro cond
    rw [← clpoint_iff_exists_subnet s x] at cond
    exact lim_of_clpoint_of_cauchynet scauchy x cond

/- Any Cauchy sequence in a metric space is bounded -/
theorem cauchyNet_bdd {s: ℕ → M}:
  CauchyNet s → ∃ R > 0, ∀ (m n : ℕ), dist (s m) (s n) < R := by
    intro cauchys
    rw [← cauchySeq_iff_cauchynet] at cauchys
    exact cauchySeq_bdd cauchys

/- ### Construction of a representative sequence from a Cauchy net ### -/

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
