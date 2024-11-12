import Mathlib.Analysis.Normed.Module.Dual
import Mathlib.Analysis.Normed.Module.WeakDual
import Mathlib.Analysis.NormedSpace.HahnBanach.Separation
import FunctionalAnalysis.MazurTheorem.Lemmas



noncomputable section

open Set Filter Topology Classical Function NormedSpace TopologicalSpace Defs Lemmas

set_option linter.unusedVariables false
set_option trace.Meta.Tactic.simp false

universe u

/- ### Instances for substraction on weak topologies ### -/

/- Instance for substraction in X for the weak topology -/
instance WeakSpace.instHSub {X 𝕂 : Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]:
  HSub (WeakSpace 𝕂 X) (WeakSpace 𝕂 X) (WeakSpace 𝕂 X) where
    hSub := by
      dsimp only [WeakSpace, WeakBilin]
      exact fun x y ↦ x - y

/- Instance for substraction in X* for the weak* topology -/
instance WeakDual.instHSub {X 𝕂 : Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]:
  HSub (WeakDual 𝕂 X) (WeakDual 𝕂 X) (WeakDual 𝕂 X) where
    hSub := by
      dsimp only [WeakDual, WeakBilin]
      exact fun x y ↦ x - y

/- ### Weak topologies are coarser than any compatible topology ### -/

/- Theorem: Let E and F be vector spaces over 𝕂 (with 𝕂 being ℝ or ℂ), B: E × F → 𝕂 a bilinear form and t a compatible
            topology with B. Then, the weak topology induced by B is coarser than t. -/
theorem weak_open_implies_open {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  {B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂} (t: TopologicalSpace E) (h: CompatibleTopology B t) (s: Set E) :
  @IsOpen E (WeakBilin.instTopologicalSpace B) s → @IsOpen E t s := by
    intro s_wopen
    /- As the weak topology induced by B is the topology on E induced by the map B: E → (F → 𝕂), by the
       lemma "induced_coarsest" it is enough to prove that B is continuous when we consider in E the topology t.
       Now, as the topology in F → 𝕂 is the product topology, it is enough to prove that πᵢ ∘ B : E → 𝕂 (where πᵢ are the
       projections of F → 𝕂) for every i ∈ F.
       Fixed an f ∈ F, we must then prove that the map B': E → 𝕂 given by B' e = B e f is continuous. Observe that B' = B.flip f.
       Then, B' is a linear map and as t is compatible with B (that is, (E, t)* = B.flip [F]) it will be enough to see that
       B' = B.flip f ∈ range B.flip which is clear. -/
    apply induced_coarsest (fun x y => B x y)
    · rw [continuous_pi_iff]
      intro f
      have : (fun e ↦ (B e) f) = B.flip f := by
        rfl
      rw [this]
      dsimp [CompatibleTopology] at h
      rw [h (B.flip f), mem_range]
      use f
    · assumption

/- Theorem: Let E and F be vector spaces over 𝕂 (with 𝕂 being ℝ or ℂ), B: E × F → 𝕂 a bilinear form and t a compatible
            topology with B. Then, any closed set with the weak topology will be closed in t. -/
theorem weak_closed_implies_closed {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  {B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂} (t: TopologicalSpace E) (h: CompatibleTopology B t) (s: Set E) :
  @IsClosed E (WeakBilin.instTopologicalSpace B) s → @IsClosed E t s := by
    intro s_wclosed
    /- If s is closed in the weak topology induced by B, then sᶜ is open for this topology and by the theorem "weak_open_implies_open"
       it will be open in t. This implies then that s is closed in t as wanted. -/
    rw [← @isOpen_compl_iff] at *
    exact weak_open_implies_open t h sᶜ s_wclosed

/- ### Basis for weak topologies ### -/

/- Theorem: Let E and F be vector spaces over 𝕂 (with 𝕂 being ℝ or ℂ), B: E × F → 𝕂 a bilinear form. Then, a basis for the
            weak topology induced by B is the family formed by the sets of the form
            U[e₀; f₁, ⋯, fₙ; ε] = {e ∈ E | ‖ B (e - e₀) fᵢ ‖ < ε, i = 1, ⋯, n}
            with e₀ ∈ E, f₁, ⋯, fₙ ∈ F and ε > 0. -/
theorem weak_basis_general {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂): IsTopologicalBasis
  {U : Set (WeakBilin B) | ∃ (e₀ : WeakBilin B), ∃ (I : Finset F), ∃ (ε : ℝ), (0 < ε ∧
   U = {e : WeakBilin B | ∀ i ∈ I, ‖(B (e - e₀) i)‖ < ε})} := by
    /- To see that this family forms a basis it is enough to see that every set is open and that given any e ∈ E and any open set
       U with e ∈ U, there exists an element v of the family such that e ∈ v ⊆ U. -/
    apply isTopologicalBasis_of_isOpen_of_nhds
    · intro U Uin
      rcases Uin with ⟨e₀, I, ε, εpos, Ubasopen⟩
      /- Observe that U[e₀; f₁, ⋯, fₙ; ε] = B ⁻¹' V where V = {x : F → 𝕂 | ∀ i ∈ I, x i ∈ Metric.ball (B e₀ i) ε}.
         Indeed, observe that:
           - e ∈ U[e₀; f₁, ⋯, fₙ; ε] ↔ ∀ i ∈ I, ‖(B (e - e₀)) i‖ < ε ↔ ∀ i ∈ I, ‖B e i - B e₀ i‖ < ε ↔ ∀ i ∈ I, B e i ∈ Metric.ball (B e₀ i) ε
           - e ∈ B ⁻¹' V ↔ B e ∈ V ↔ ∀ i ∈ I, B e i ∈ Metric.ball (B e₀ i) ε ↔ ∀ i ∈ I, B e i ∈ Metric.ball (B e₀ i) ε
         So the equivalence is clear. -/
      let V : Set (F → 𝕂) := {x : F → 𝕂 | ∀ i ∈ I, x i ∈ Metric.ball (B e₀ i) ε}
      have : U = (fun x y ↦ (B x) y) ⁻¹' V := by
        ext e
        simp only [Ubasopen, map_sub, LinearMap.sub_apply, ← mem_ball_iff_norm, mem_preimage, V, Set.mem_setOf_eq]
      rw [this]
      /- So, if we see that V is open, as B is continuous by the definition of the weak topology, we can conclude the proof. -/
      have Vopen : IsOpen V := by
        /- Observe that V = Π i ∈ F, T i where T i = Metric.ball (B e₀ i) ε if i ∈ I and T i = 𝕂 if i ≠ i, so as I is finite
           it will be open.
           With more detail, because the topology on F → 𝕂 is the product topology, to see that V is open it is enough to see that
           for every x ∈ V there exists a finite set J ⊆ F and a function u: F → Set 𝕂 such that u j is open for every j ∈ J,
           x j ∈ u j for every j ∈ J and Π i ∈ F, Tᵢ ⊆ V where Tᵢ = u i if i ∈ J and Tᵢ = 𝕂 if i ∉ J. -/
        rw [isOpen_pi_iff]
        intro x xinV
        /- It is then clear that by choosing J = I and defining u: F → Set 𝕂 as u f = Metric.ball (B e₀ f) ε, all the previous
           conditions are satisfied. -/
        use I, fun (f: F) ↦ Metric.ball ((B e₀) f) ε
        constructor
        · intro i iinI
          constructor
          · exact Metric.isOpen_ball
          · exact xinV i iinI
        · intro y yin -- "((↑I).pi fun f ↦ Metric.ball ((B e₀) f) ε)" is the set Π i ∈ F, Tᵢ ⊆ V where Tᵢ = u i if i ∈ I and Tᵢ = 𝕂 if i ∉ I
          rw [Set.mem_pi] at yin
          exact yin
      /- As said, because B is continuous and V is open we conclude that U[e₀; f₁, ⋯, fₙ; ε] = B ⁻¹' V is open as wanted. -/
      exact IsOpen.preimage (WeakBilin.coeFn_continuous B) Vopen
    · intro e U einU Uopen
      /- As U is open in the weak topology induced by B, there exists an open set V in F → 𝕂 such that U = B ⁻¹' V. -/
      rw [isOpen_induced_iff] at Uopen
      rcases Uopen with ⟨V, Vopen, UeqpreV⟩
      /- On the other hand, as V is open in the product topology and B e ∈ V (because e ∈ U), we know that there exists a
         finite set I ⊆ F and a function u: F → Set 𝕂 such that u i is open for every i ∈ I, (B e) i ∈ u i for every i ∈ I
         and Π i ∈ F, Tᵢ ⊆ V where Tᵢ = u i if i ∈ J and Tᵢ = 𝕂 if i ∉ J. -/
      rw [isOpen_pi_iff] at Vopen
      rw [← UeqpreV, mem_preimage] at einU -- B e ∈ V
      rcases Vopen ((fun y ↦ (B e) y)) einU with ⟨I, u, uopen, piusubV⟩
      /- Now, for every i ∈ I, as (B e) i ∈ u i and u i is open in 𝕂, we now that there exists some εᵢ > 0 such that
         Metric.ball (B e i) εᵢ ⊆ u i. Taking then ε as the minimum of the εᵢ over i ∈ I, we have that for every i ∈ I,
         Metric.ball (B e i) ε ⊆ u i.
         Let's see how to implement this reasoning. -/
      have : ∃ (ε : ℝ), (0 < ε ∧ ∀ i ∈ I, Metric.ball (B e i) ε ⊆ u i) := by
        have existence : ∀ i ∈ I, ∃ (t : ℝ), (0 < t ∧ Metric.ball (B e i) t ⊆ u i) := by
          intro i iinI
          have Beiinui := (uopen i iinI).2
          have uiopen := (uopen i iinI).1
          rw [Metric.isOpen_iff] at uiopen
          exact uiopen (B e i) Beiinui
        /- We can then define the following selection function: -/
        let I' := Finset.attach I -- The set version of I is also finite
        let ε': I → ℝ := fun i ↦ if h: ∃ (t : ℝ), (0 < t ∧ Metric.ball (B e i) t ⊆ u i.1) then Classical.choose h else 0
        /- Observe that by "existence" we have that for any i ∈ I, ε' satisfies:
           - 0 < ε' i
           - Metric.ball (B e i) (ε' i) ⊆ u i) -/
        /- We will distinguish two cases depending on whether I is or not empty. -/
        by_cases hI : Finset.Nonempty I'
        · /- If I is nonempty, as it is finite, we have that ε' must have a minimum in some point i₀ and we can define ε = ε' i₀.
             In fact, by the previous argument it is clear that ε' i₀ > 0 and, given any i ∈ I, we have that ε' i₀ ≤ ε' i, so
             Metric.ball (B e i) (ε' i₀) ⊆ Metric.ball (B e i) (ε' i) ⊆ u i, as wanted to prove. -/
          rcases Finset.exists_min_image I' ε' hI with ⟨i₀, iinI', i₀minε'⟩
          use ε' i₀
          constructor
          · dsimp [ε']
            rw [dif_pos (existence i₀ i₀.2)] -- choose (existence i₀ i₀.2) = ε' i₀
            exact (Classical.choose_spec (existence i₀ i₀.2)).1
          · intro i iinI
            have ballsubball : Metric.ball (B e i) (ε' i₀) ⊆ Metric.ball (B e i) (ε' ⟨i, iinI⟩) := by
              exact Metric.ball_subset_ball (i₀minε' ⟨i, iinI⟩ (Finset.mem_attach I ⟨i, iinI⟩))
            have ballsubε' : Metric.ball (B e i) (ε' ⟨i, iinI⟩) ⊆ u i := by
              dsimp [ε']
              rw [dif_pos (existence i iinI)] -- choose (existence i iinI) = ε' i
              exact (Classical.choose_spec (existence i iinI)).2
            exact subset_trans ballsubball ballsubε'
        · /- On the other hand, if I is empty it is clear that we can take any positive real number as ε -/
          rw [Finset.nonempty_iff_ne_empty, Ne, not_not] at hI
          use 1
          constructor
          · linarith
          · intro i iinI
            have : ⟨i, iinI⟩ ∈ I' := by
              exact Finset.mem_attach I ⟨i, iinI⟩
            rw [hI] at this
            contradiction
      rcases this with ⟨ε, εpos, eq⟩
      /- Definining then v = {e' : WeakBilin B | ∀ i ∈ I, ‖(B (e' - e)) i‖ < ε} it is clear that it belongs to the family
         of sets we are trying to prove it is a basis and e ∈ v. -/
      let v := {e' : WeakBilin B | ∀ i ∈ I, ‖(B (e' - e)) i‖ < ε}
      use v
      constructor
      · simp only [Set.mem_setOf_eq, map_sub]
        use e, I, ε, εpos
        simp only [v, map_sub]
      · constructor
        · simp only [Set.mem_setOf_eq, v, sub_self, map_zero, LinearMap.zero_apply, norm_zero, εpos, implies_true]
        · /- Furthermore, v ⊆ B ⁻¹' V = U because given any e' ∈ v, we have that B e' ∈ Π i ∈ F, u i ⊆ V as for any i ∈ I
             B e' i ∈ Metric.ball (B e i) ε ⊆ u i. -/
          intro e' e'inv
          rw [← UeqpreV, mem_preimage]
          apply piusubV
          rw [Set.mem_pi]
          intro i iinI
          apply eq i iinI
          simp only [v, Set.mem_setOf_eq, map_sub, LinearMap.sub_apply, ← mem_ball_iff_norm] at e'inv
          exact e'inv i iinI

/- Corollary: Let X be a normed space over 𝕂 (with 𝕂 being ℝ or ℂ). Then, a basis for the weak topology is the family formed
              by the sets of the form
              U[x₀; f₁, ⋯, fₙ; ε] = {x ∈ X | ‖ fᵢ (x - x₀) ‖ < ε, i = 1, ⋯, n}
            with x₀ ∈ X, f₁, ⋯, fₙ ∈ X* and ε > 0. -/
theorem weak_basis {X 𝕂 : Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]:
  IsTopologicalBasis
  {U : Set (WeakSpace 𝕂 X) | ∃ (x₀ : WeakSpace 𝕂 X), ∃ (I : Finset (Dual 𝕂 X)), ∃ (ε : ℝ), (0 < ε ∧
  U = {x : WeakSpace 𝕂 X | ∀ f ∈ I, ‖f (x - x₀)‖ < ε})} := by
    apply weak_basis_general ((topDualPairing 𝕂 X).flip)

/- Corollary: Let X be a normed space over 𝕂 (with 𝕂 being ℝ or ℂ). Then, a basis for the weak* topology is the family formed
              by the sets of the form
              U[f₀; x₁, ⋯, xₙ; ε] = {f ∈ X* | ‖ f xᵢ - f₀ xᵢ) ‖ < ε, i = 1, ⋯, n}
            with f₀ ∈ X*, x₁, ⋯, xₙ ∈ X and ε > 0. -/
theorem weak_star_basis {X 𝕂 : Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]:
  IsTopologicalBasis
  {U : Set (WeakDual 𝕂 X) | ∃ (f₀ : WeakDual 𝕂 X), ∃ (I : Finset X), ∃ (ε : ℝ), (0 < ε ∧
  U = {f : WeakDual 𝕂 X | ∀ i ∈ I, ‖(f - f₀) i‖ < ε})} := by
    apply weak_basis_general ((topDualPairing 𝕂 X))

/- ### Weak topologies are compatible ### -/

/- Theorem: Let X be a normed space over 𝕂 (with 𝕂 being ℝ or ℂ). Then, the weak topology is compatible with the normed
            topology, i.e., X* = (X, ω)*. -/
theorem weak_compatible_normed (𝕂 X : Type*) [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X] :
  CompatibleTopology ((topDualPairing 𝕂 X).flip) (@UniformSpace.toTopologicalSpace X _) := by
    dsimp [CompatibleTopology]
    intro g
    rw [LinearMap.flip_flip]
    /- Let's rename φ = topDualPairing 𝕂 X : X* → (X → 𝕂). Then, to conclude the proof it is enough to show that range φ = X*. -/
    have : range (topDualPairing 𝕂 X) = {f: (X →ₗ[𝕂] 𝕂) | Continuous f} := by
      ext f
      constructor
      · intro finrange
        /- If f ∈ range φ, then there exists some h ∈ X* such that f = φ h, but for any x ∈ X, (φ h) x = h x, so f = φ h = h
           and it is clear that f is continuous. -/
        rw [mem_range] at finrange
        rcases finrange with ⟨h, feqh⟩
        simp only [topDualPairing, ContinuousLinearMap.coeLM, LinearMap.coe_mk, AddHom.coe_mk] at feqh
        rw [← feqh, Set.mem_setOf_eq]
        exact h.cont
      · intro fcont
        rw [Set.mem_setOf_eq] at fcont
        /- If f is continuous, then f ∈ range φ because f= φ f. -/
        rw [mem_range]
        use ⟨f, fcont⟩
        simp only [topDualPairing, ContinuousLinearMap.coeLM, LinearMap.coe_mk, AddHom.coe_mk]
    rw [this]
    rfl

/- FALTA COMENTAR -/
theorem weak_compatible {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂) : CompatibleTopology B (WeakBilin.instTopologicalSpace B) := by
    dsimp [CompatibleTopology]
    intro g
    constructor
    · intro gcont
      rw [mem_range]
      have : ∃ (H: Finset F), g ∈ Submodule.span 𝕂 (Finset.image (fun (f: F) ↦ B.flip f) H) := by
        rw [@continuous_iff_continuousAt] at gcont
        have contzero := gcont 0
        rw [@continuousAt_def] at contzero
        simp at contzero
        have := contzero (Metric.ball (0 : 𝕂) 1) (Metric.ball_mem_nhds (0 : 𝕂) (by linarith))
        rw [@mem_nhds_iff] at this
        rcases this with ⟨V, Vsubpre, Vopen, zinV⟩
        have gVsubball : g '' V ⊆ Metric.ball (0 : 𝕂) 1 := by
          intro c cinimg
          rw [mem_image] at cinimg
          rcases cinimg with ⟨v, vinV, gvc⟩
          have := Vsubpre vinV
          rw [mem_preimage] at this
          rw [← gvc]
          assumption
        rw [IsTopologicalBasis.isOpen_iff (weak_basis_general B)] at Vopen
        rcases Vopen (0 : E) zinV with ⟨U, Uin, zinU, UsubV⟩
        rcases Uin with ⟨e₀, I, ε, εpos, Ueq⟩
        use I
        rw [mem_submodule_iff_inter_of_ker_sub_ker]
        intro e eininter
        simp only [mem_iInter] at eininter
        have : ∀ (m : 𝕂), m • e ∈ U := by
          intro m
          rw [Ueq]
          dsimp [WeakBilin]
          intro i iinI
          have : (fun f ↦ B.flip f) i ∈ Finset.image (fun f ↦ B.flip f) I := by
            rw [Finset.mem_image]
            use i
          have:= eininter _ this
          simp at this
          have : B (m • e) i = 0 := by
            rw [map_smul]
            have eq : (m • B e) i = m * (B e i) := by
              rfl
            rw [eq, this]
            simp
          rw [LinearMap.map_sub₂, this, zero_sub, norm_neg]
          rw [Ueq] at zinU
          dsimp at zinU
          have := zinU i iinI
          rw [zero_sub, LinearMap.map_neg₂, norm_neg] at this
          assumption
        have : ∀ (m : ℕ), (0 < m) → ‖g e‖ < 1/m := by
          intro m mpos
          have := UsubV (this m)
          have gin : g ((@Nat.cast 𝕂 Semiring.toNatCast m) • e) ∈ g '' V := by
            rw [mem_image]
            use (@Nat.cast 𝕂 Semiring.toNatCast m) • e
          have normltone := gVsubball gin
          rw [mem_ball_iff_norm, sub_zero, map_smul, norm_smul, RCLike.norm_natCast] at normltone
          rw [lt_div_iff₀ (by norm_num [mpos]), mul_comm]
          assumption
        simp
        rw [← norm_eq_zero]
        apply Real_archimedean'' ‖g e‖ (norm_nonneg (g e)) this
      rcases this with ⟨H, gin⟩
      have : ∃ (I: Finset F), (∀ f ∈ I, ∀ f' ∈ I, B.flip f = B.flip f' → f = f') ∧
         Finset.image (fun f ↦ B.flip f) H = Finset.image (fun f ↦ B.flip f) I := by
          have : ∀ y ∈ Finset.image (fun f ↦ B.flip f) H, ∃ f ∈ H, B.flip f = y := by
            intro i iin
            rw [Finset.mem_image] at iin
            assumption
          let t : Finset.image (fun f ↦ B.flip f) H → F := fun i ↦ if h: ∃ f ∈ H, B.flip f = i then Classical.choose h else 0
          use Finset.image t Finset.univ
          constructor
          · intro f fin f' fin' eqim
            rw [Finset.mem_image] at *
            rcases fin with ⟨x, xinuniv, txf⟩
            rcases fin' with ⟨x', x'inuniv, tx'f⟩
            have condf := x.2
            have condf' := x'.2
            rw [Finset.mem_image] at *
            have : x = x' := by
              dsimp [t] at *
              rw [dif_pos condf] at txf
              rw [dif_pos condf'] at tx'f
              have c1 := (Classical.choose_spec condf).2
              have c2 := (Classical.choose_spec condf').2
              apply SetCoe.ext
              rw [← c1, ← c2, txf, tx'f]
              assumption
            rw [← txf, ← tx'f, this]
          · ext i
            constructor
            · intro iin
              rw [Finset.mem_image]
              use t ⟨i, iin⟩
              constructor
              · rw [Finset.mem_image]
                use ⟨i, iin⟩
                exact And.intro (Finset.mem_univ ⟨i, iin⟩) (by rfl)
              · rw [Finset.mem_image] at iin
                dsimp [t]
                rw [dif_pos iin]
                exact (Classical.choose_spec iin).2
            · intro iin
              rw [Finset.mem_image] at *
              rcases iin with ⟨f, fin, ieqBf⟩
              use f
              constructor
              · rw [Finset.mem_image] at fin
                rcases fin with ⟨x, xinuniv, txf⟩
                rw [← txf]
                dsimp only [t]
                have := x.2
                rw [Finset.mem_image] at this
                rw [dif_pos this]
                exact (Classical.choose_spec this).1
              · assumption
      rcases this with ⟨I, injinI, eq⟩
      rw [mem_span_finset, eq] at gin
      rcases gin with ⟨c, geq⟩
      have : ∑ i ∈ Finset.image (fun f ↦ B.flip f) I, c i • i = ∑ f ∈ I, c (B.flip f) • (B.flip f) := by
        rw [Finset.sum_image]
        assumption
      use (∑ i ∈ I, c (B.flip i) • i)
      rw [← geq, this]
      rw [map_sum]
      congr
      ext f e
      have := (B.flip).map_smul' (c (B.flip f)) f
      dsimp at this
      rw [this]
    · intro h
      rw [mem_range] at h
      rcases h with ⟨f, geqBf⟩
      rw [← geqBf]
      apply WeakBilin.eval_continuous

theorem locallyconvex_dual_pair (X: Type*) [AddCommGroup X] [Module ℝ X] [TopologicalSpace X]
  [TopologicalAddGroup X] [ContinuousSMul ℝ X] [LocallyConvexSpace ℝ X] [T1Space X] :
  DualPair ((topDualPairing ℝ X).flip) := by
    dsimp [DualPair, SepPoints]
    constructor
    · intro x fxzero
      by_contra!
      rcases geometric_hahn_banach_point_point this with ⟨f, fxltzero⟩
      rw [map_zero] at fxltzero
      have := fxzero f (mem_univ f)
      dsimp [topDualPairing] at this
      linarith
    · intro f fxzero
      ext x
      exact fxzero x (mem_univ x)

/- Convergence on weak topologies -/

theorem weak_conv_nets {E F 𝕂: Type*} [RCLike 𝕂] [AddCommGroup E] [Module 𝕂 E] [AddCommGroup F] [Module 𝕂 F]
  (B: E →ₗ[𝕂] F →ₗ[𝕂] 𝕂) (D: Type u_1) (h: DirectedSet D) (s: D → WeakBilin B) (e : WeakBilin B) :
  Net.Limit s e ↔ ∀ (f : F), Net.Limit ((fun (d : WeakBilin B) ↦ B d f) ∘ s) (B e f) := by
    constructor
    · intro slimite f
      exact (Net.continuous_iff_image_of_net_converges (fun (d : WeakBilin B) ↦ B d f) e).mp
             (continuous_iff_continuousAt.mp (WeakBilin.eval_continuous B f) e) D h s slimite
    · intro hyp
      dsimp [Net.Limit]
      intro U Unhdse
      rw [IsTopologicalBasis.mem_nhds_iff (weak_basis_general B)] at Unhdse
      rcases Unhdse with ⟨V, Vbasic, einV, VsubU⟩
      dsimp at Vbasic
      rcases Vbasic with ⟨e₀, I, ε, εpos, Vbasic⟩
      have : ∃ (d₀ : D), ∀ i ∈ I, ∀ (d : D), d₀ ≤ d → (‖(B ((s d) - e₀) i)‖ < ε) := by
        · apply aux_sup I (fun (f : F) (d : D) ↦ (∀ (d' : D), d ≤ d' → (‖(B ((s d') - e₀) f)‖ < ε)))
          intro i iinI
          have limit := hyp i
          rw [Net.Limit] at limit
          have : Metric.ball (B e i) (ε - ‖B (e - e₀) ↑i‖) ∈ 𝓝 (B e i) := by
            apply Metric.ball_mem_nhds
            rw [sub_pos]
            rw [Vbasic] at einV
            dsimp at einV
            exact einV i iinI
          rcases limit (Metric.ball (B e i) (ε - ‖B (e - e₀) ↑i‖)) this with ⟨d₀, cond⟩
          dsimp at cond
          use d₀
          intro d d₀led
          have := cond d d₀led
          rw [Metric.mem_ball] at this
          rw [LinearMap.map_sub₂, ← dist_eq_norm]
          calc
            dist (B (s d) i) (B e₀ i) ≤ dist (B (s d) i) (B e i) + dist (B e i) (B e₀ i) := by
              exact dist_triangle (B (s d) i) (B e i) (B e₀ i)
            _ < (ε - ‖B (e - e₀) i‖) + dist (B e i) (B e₀ i) := by
              apply add_lt_add_right
              assumption
            _ = ε := by
              rw [LinearMap.map_sub₂ ,← dist_eq_norm]
              simp
          · intro i iinI t s' tles' h' d' s'led'
            exact h' d' (le_trans tles' s'led')
      rcases this with ⟨d₀, eq⟩
      use d₀
      intro d d₀led
      apply VsubU
      rw [Vbasic]
      dsimp
      intro i iinI
      exact eq i iinI d d₀led

theorem weak_conv {X 𝕂 : Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]
  (D: Type u_1) (h: DirectedSet D) (x: WeakSpace 𝕂 X) (s: D → WeakSpace 𝕂 X):
  Net.Limit s x ↔ ∀ (f : WeakDual 𝕂 X), Net.Limit (f ∘ s) (f x) := by
    exact weak_conv_nets ((topDualPairing 𝕂 X).flip) D h s x

theorem weak_star_conv {X 𝕂 : Type*} [RCLike 𝕂] [NormedAddCommGroup X] [NormedSpace 𝕂 X]
  (D: Type (max u_1 u_2)) (h: DirectedSet D) (f: WeakDual 𝕂 X) (s: D → WeakDual 𝕂 X):
  Net.Limit s f ↔ ∀ (x : WeakSpace 𝕂 X), Net.Limit (((topDualPairing 𝕂 X).flip x) ∘ s) (f x) := by
    exact weak_conv_nets (topDualPairing 𝕂 X) D h s f
