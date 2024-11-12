import FunctionalAnalysis.MazurTheorem.WeakTopology

noncomputable section

open Set Topology Classical Function NormedSpace Defs Lemmas

set_option linter.unusedVariables false
set_option trace.Meta.Tactic.simp true


/- Theorem (Mazur): Let E be a locally convex space and F a vector space over ℝ, B: E × F → ℝ a bilinear form, t a compatible
            topology with B and s a convex subset of E. Then, E is closed with respect to t if, and only if, it is weakly
            closed (with respect to B). -/
theorem closed_convex_iff_weak_closed {E F: Type*} [AddCommGroup E] [Module ℝ E] [AddCommGroup F] [Module ℝ F]
  {B: E →ₗ[ℝ] F →ₗ[ℝ] ℝ} (t: TopologicalSpace E)  [TopologicalAddGroup E] [ContinuousSMul ℝ E]
  [LocallyConvexSpace ℝ E] (h: CompatibleTopology B t) (s: Set E): Convex ℝ s →
  (@IsClosed E t s ↔ @IsClosed E (WeakBilin.instTopologicalSpace B) s) := by
    intro sconvex
    /- By the theorem "weak_closed_implies_closed" we know that any weak closed set is closed in any compatible topology, so
       we only need to worry about the other implication. -/
    constructor
    · intro s_tclosed
      /- To prove that s is weakly closed we will prove that sᶜ is weakly open and, to do so, we will prove that given any point
         e ∈ sᶜ we have that sᶜ is a neighbourhood of e, that is, we will prove that there exists a weakly open set U such that
         e ∈ U ⊆ sᶜ. -/
      rw [← @isOpen_compl_iff, @isOpen_iff_mem_nhds]
      intro e enins
      rw [@mem_nhds_iff]
      /- As e ∉ s and s is convex and closed for t, by the geometric version of Hahn-Banach theorem we have that there exists
         a g ∈ E* and some a ∈ ℝ such that sup {g e': e' ∈ s} < a < g e.-/
      rw [mem_compl_iff] at enins
      rcases geometric_hahn_banach_closed_point sconvex s_tclosed enins with ⟨g, a ,asupboundgs, altge⟩
      /- On the other hand, as t is compatible with B, we have that there exists some f ∈ F such that g = B.flip f -/
      rcases (h g).mp g.cont with ⟨f, Bfeqg⟩
      /- We will take U = U[e; f; g e - a] -/
      let I : Finset F := {f}
      use {e' : E | ∀ i ∈ I, ‖(B (e' - e) i)‖ < g e - a}
      constructor
      · /- U ⊆ sᶜ because given any e' ∈ U, we have that |B e' f - B e f| < g e - a, so
           g e' = B.flip f e' = B e' f > B e f - (g e - a) = a (because g e = B.flip f e = B e f) and by "asupboundgs" we conclude
           that e' ∉ s. -/
        intro e' ein'
        rw [mem_compl_iff]
        /- Let's suppose that e' ∈ s. Then, as B.flip f = g, we have that for any e ∈ E, B e f = g e, and as e' ∈ U we obtain
           that |g e' - g e| < g e - a.
           Then, we have that -(g e' - g e) < g e - a, so a < g e', but that contradicts "asupboundgs" as we are assuming that e' ∈ s. -/
        intro e'ins
        have Befeqge : ∀ (e: E), B e f = g e := by
          intro e
          apply congr_arg (fun (x: E →ₗ[ℝ] ℝ) ↦ x e) Bfeqg
        rw [Set.mem_setOf_eq] at ein'
        have := ein' f (Finset.mem_singleton.mpr (by rfl))
        rw [LinearMap.map_sub₂, Befeqge, Befeqge, Real.norm_eq_abs] at this
        rw [abs_lt] at this
        have : a < g e' := by
          have := this.1
          rw [neg_sub, sub_lt_sub_iff_right] at this
          assumption
        have : g e' < a := by
          exact asupboundgs e' e'ins
        linarith
      · constructor
        · /- To see that U is open it is enough to see that it is one of the basis sets given by the theorem "weak_basis_general" -/
          apply TopologicalSpace.IsTopologicalBasis.isOpen (weak_basis_general B)
          rw [Set.mem_setOf_eq]
          use e, I, (g e - a)
          constructor
          · linarith
          · rfl
        · /- Lastly, it is clear that e ∈ U because ‖B(e - e) i‖ = 0 < g e - a by "altge" -/
          rw [Set.mem_setOf_eq]
          intro i iinI
          rw [sub_self, map_zero, LinearMap.zero_apply, norm_zero]
          linarith
    · intro s_wclosed
      exact weak_closed_implies_closed t h s s_wclosed

/- Corollary: Let X be a normed space over ℝ and s a convex subset of X. Then, s is closed if, and only if, it is weakly closed. -/
theorem closed_convex_iff_weak_closed_normed {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] (s: Set X):
  Convex ℝ s → (IsClosed s ↔ IsClosed {x : WeakSpace ℝ X | x ∈ s}) := by
    exact closed_convex_iff_weak_closed (@UniformSpace.toTopologicalSpace X _) (weak_compatible_normed ℝ X) s
