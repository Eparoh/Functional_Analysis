import Mathlib.Algebra.Module.Submodule.Basic
import Mathlib.LinearAlgebra.Basis.VectorSpace
import FunctionalAnalysis.MazurTheorem.Defs
import Topology.Nets.Theorems

noncomputable section

set_option linter.unusedVariables false
set_option trace.Meta.Tactic.simp false

open Set Topology Function LinearMap Defs

namespace Lemmas

/- ### Lemas for evaluation of partial functions ### -/

/- Evaluation of a partial function if the condition is satisfied. -/
lemma eval_pos (p : α → Prop) (f g : α → β) {a : α} (h: p a) : partial_fun p f g a = f a := by
  classical
  rw [partial_fun, ite_eq_left_iff]
  intro npn
  contradiction

/- Evaluation of a partial function if the condition is not satisfied. -/
lemma eval_neg (p : α → Prop) (f g : α → β) {a : α} (h: ¬p a) : partial_fun p f g a = g a := by
  classical
  rw [partial_fun, ite_eq_right_iff]
  intro npn
  contradiction

/- ### Lemas from linear algebra ### -/

/- Lemma: Let E, F, G be vector spaces over a field 𝕜 and f: E → G, g: E → F linear maps. Then, it exists a linear map h: F → G
          such that f = h ∘ g if, and only if, Ker g ⊆ Ker f -/
lemma exist_comp_iff_ker_sub {E F G 𝕜: Type*} [Field 𝕜] [AddCommGroup E] [AddCommGroup F] [AddCommGroup G] [Module 𝕜 E] [Module 𝕜 F] [Module 𝕜 G]
  (f: E →ₗ[𝕜] G) (g: E →ₗ[𝕜] F) : (∃ (h: F →ₗ[𝕜] G), f = h ∘ₗ g) ↔ {e | e ∈ ker g} ⊆ {e | e ∈ ker f} := by
    classical
    constructor
    · intro existence
      rcases existence with ⟨h, feqhg⟩
      intro e einkerg
      /- If e ∈ Ker g, then g e = 0, so f e = h (g e) = h 0 = 0 as h is a linear map. -/
      simp at *
      rw [feqhg]
      dsimp [LinearMap.comp]
      rw [einkerg, map_zero]
    · intro kergsubkerf
      /- If we define h': g[E] → G as h' (g e) = f e, we have that it is well defined because given x ∈ g[E], if there exists
         two different elements e₁, e₂ ∈ E with x = g e₁ and x = g e₂, then g (e₁ - e₂) = 0, so e₁ - e₂ ∈ Ker g ⊆ Ker f and we
         obtain that f e₁ = f e₂. To conclude the proof we just have to extend h' to some linear map h: F → G.  -/
      let s: (LinearMap.range g) → E := fun (x : LinearMap.range g) ↦ if h: ∃ (e: E), g e = x then Classical.choose h else 0 -- For every x ∈ g[E] we select an e ∈ E such that x = g e
      let h': (LinearMap.range g) →ₗ[𝕜] G := {
        toFun := f ∘ s
        map_add' := by
          intro x x'
          simp
          have xinrangeg := x.2
          have x'inrangeg := x'.2
          /- As the range of a linear map is a submodule we have that x+x' ∈ g[E] -/
          have xx'inrangeg : (x.1 + x'.1) ∈ LinearMap.range g := by
            rw [Submodule.add_mem_iff_right _ x.2]
            exact x'.2
          rw [LinearMap.mem_range] at *
          dsimp [s]
          rw [dif_pos xinrangeg, dif_pos x'inrangeg, dif_pos xx'inrangeg] -- g (choose xinrangeg) = x, g (choose x'inrangeg) = x', g (choose xx'inrangeg) = x + x'
          /- We have that g (choose xx'inrangeg - (choose xinrangeg + choose x'inrangeg)) = 0 by the selection of these elements and
             the linearity of g, so  choose xx'inrangeg - (choose xinrangeg + choose x'inrangeg) ∈ Ker g and, by assumption,
             choose xx'inrangeg - (choose xinrangeg + choose x'inrangeg) ∈ Ker f.
             By the linearity of f we conclude as wanted. -/
          have : Classical.choose xx'inrangeg - (Classical.choose xinrangeg + Classical.choose x'inrangeg) ∈ ker f := by
            apply kergsubkerf
            simp [Classical.choose_spec xinrangeg, Classical.choose_spec x'inrangeg, Classical.choose_spec xx'inrangeg]
          rw [mem_ker, map_sub, map_add, sub_eq_zero] at this
          assumption
        map_smul' := by
          intro c x
          simp
          have xinrangeg := x.2
          /- As the range of a linear map is a submodule we have that c • x ∈ g[E] -/
          have cxinrangeg : c • x.1 ∈ LinearMap.range g := by
            exact Submodule.smul_mem _ c x.2
          rw [LinearMap.mem_range] at *
          dsimp [s]
          rw [dif_pos xinrangeg, dif_pos cxinrangeg] -- g (choose xinrangeg) = x, g (choose cxinrangeg) = c • x
          /- We have that g (choose cxinrangeg - (c • choose xinrangeg)) = 0 by the selection of these elements and
             the linearity of g, so choose cxinrangeg - (c • choose xinrangeg) ∈ Ker g and, by assumption,
             choose cxinrangeg - (c • choose xinrangeg) ∈ Ker f.
             By the linearity of f we conclude as wanted. -/
          have : Classical.choose cxinrangeg - (c • Classical.choose xinrangeg) ∈ ker f := by
            apply kergsubkerf
            simp [Classical.choose_spec xinrangeg, Classical.choose_spec cxinrangeg]
          rw [mem_ker, map_sub, map_smul, sub_eq_zero] at this
          assumption
      }
      /- We have that h' (g e) = f (s (g e)) = f e -/
      have eqcomp : ∀ (e: E), f e = h' (⟨g e, by rw [LinearMap.mem_range]; use e⟩) := by
        intro e
        dsimp [h', s]
        have cond : ∃ e', g e' = g e := by
          use e
        rw [dif_pos cond] -- g (choose cond) = g e
        /- To obtain the desired result it is enough to prove that e - (choose cond) ∈ Ker f and, by assumption, it is enough
           to prove that e - (choose cond) ∈ Ker g, which is true by the selection done. -/
        have : Classical.choose cond - e ∈ ker f := by
          apply kergsubkerf
          simp [Classical.choose_spec cond]
        rw [mem_ker, map_sub, sub_eq_zero] at this
        exact this.symm
      /- We define the linear extension of h' -/
      have extension : ∃ (h: F →ₗ[𝕜] G), ∀ (x : LinearMap.range g), h x.1 = h' x := by
        rcases exists_extend h' with ⟨h, hcircinceqh'⟩
        use h
        intro x
        rw [← hcircinceqh']
        rfl
      rcases extension with ⟨h, hexth'⟩
      use h
      ext e
      simp
      rw [hexth' ⟨g e, by rw [LinearMap.mem_range]; use e⟩]
      exact eqcomp e

/- Lemma: Let E be a vector space over a field 𝕜, f: E → 𝕜 a linear functional and F a finite set of lineal functionals over E.
          Then, f is a linear combination of the elements of F if, and only if, the intersection of the kernel of the elements of F
          is contained in the kernel of f. -/
lemma mem_submodule_iff_inter_of_ker_sub_ker {E 𝕜: Type*} [Field 𝕜] [AddCommGroup E] [Module 𝕜 E] (f: E →ₗ[𝕜] 𝕜) (F: Finset (E →ₗ[𝕜] 𝕜)):
  f ∈ Submodule.span 𝕜 F ↔ ⋂ g ∈ F, {e | e ∈ ker g} ⊆ {e | e ∈ ker f} := by
    constructor
    · intro finspan
      /- If f ∈ span F, then there exists some u: (E →ₗ[𝕜] 𝕜) → 𝕜 such that f = ∑ g ∈ F, (u g) • g.
         Then, if e ∈ ⋂ g ∈ F, Ker g, we obtain that g e = 0 for every g ∈ F and so f e = ∑ g ∈ F, (u g) • (g e) = 0, from where
         we conclude that e ∈ Ker f. -/
      rw [mem_span_finset] at finspan
      rcases finspan with ⟨u, feqsum⟩
      intro e eininter
      simp at eininter
      simp
      have : ∀ i ∈ F, (u i) * (i e) = 0 := by
        intro i iinF
        rw [eininter i iinF, mul_zero]
      rw [← feqsum]
      simp
      exact Finset.sum_eq_zero this
    · intro intersubkerf
      /- We can apply the lemma "exist_comp_iff_ker_sub" to E, 𝕜ⁿ, 𝕜, f and t = (F₁, ⋯, Fₙ) (where F₁, ⋯, Fₙ are the elements
         of F) to obtain a linear map h: 𝕜ⁿ → 𝕜 such that f = h ∘ₗ t. In fact, if e ∈ Ker t, then e ∈ ⋂ g ∈ F, Ker g and so by
         assumption, e ∈ Ker f. Then, we can write h (y₁, ..., yₙ) = ∑ yᵢ * (h (yᵢ • eᵢ)) (with eᵢ the canonical basis) for some
         and then we obtain that for every e ∈ E,
         f e = h (t e) = h (F₁ e, ⋯, Fₙ e) = ∑ h ((Fᵢ e) • eᵢ) * (Fᵢ e), so we obtain that f ∈ span F. -/
      let F' := Finset.toSet F -- We coerce F to be a set
      /- F' is finite and so we can obtain a bijection b: Fin n → F' for some natural number n -/
      have F'fin:= @Set.Finite.ofFinset _ F' F (by intro x; rfl)
      rw [← Set.finite_coe_iff, finite_iff_exists_equiv_fin] at F'fin
      rcases F'fin with ⟨n, eq⟩
      rcases eq with ⟨b⟩
      have b := b.symm -- It is more convenient to have Fin n as the domain
      let asdf := Subtype.val ∘ b.toFun
      /- We will now define t: E →ₗ[𝕜] (Fin n → 𝕜) -/
      let t: E →ₗ[𝕜] (Fin n → 𝕜) := {
        toFun := fun e ↦ (fun i ↦ (Subtype.val ∘ b) i e)
        map_add' := by
          intro e e'
          simp only [map_add]
          ext i
          rfl
        map_smul' := by
          intro c e
          simp only [map_smul, RingHom.id_apply]
          ext i
          rfl
      }
      /- We'll show that Ker t ⊆ Ker f to apply "exist_comp_iff_ker_sub" and obtain a linear map h: 𝕜ⁿ → 𝕜 such that f = h ∘ₗ t. -/
      have kertsubkerf : {e | e ∈ ker t} ⊆ {e | e ∈ ker f} := by
        intro e einkert
        apply intersubkerf
        simp at *
        intro g ginF
        have : t e (b.invFun ⟨g, ginF⟩) = g e := by
          dsimp [t]
          rw [Equiv.apply_symm_apply]
        rw [← this, einkert]
        rfl
      rcases (exist_comp_iff_ker_sub f t).mpr kertsubkerf with ⟨h, feqht⟩
      /- We define the canonical basis of 𝕜ⁿ and show that for any r ∈ 𝕜ⁿ we have that r = ∑ i: Fin n, r i * canbasis i -/
      let canbasis : Fin n → (Fin n → 𝕜) := fun i ↦ partial_fun (fun (j: Fin n) ↦ i = j) (fun (j: Fin n) ↦ (1: 𝕜)) (fun (j: Fin n) ↦ (0 : 𝕜))
      have basisdec : ∀ (r: Fin n → 𝕜), r = ∑ i: Fin n, r i • canbasis i := by
        intro r
        ext i
        simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
        rw [← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
        have : ∀ x ∈ (Finset.univ.erase i), r x * canbasis x i = 0 := by
          intro x xinerasei
          rw [Finset.mem_erase] at xinerasei
          dsimp [canbasis]
          rw [eval_neg, mul_zero]
          exact xinerasei.1
        rw [Finset.sum_eq_zero this, zero_add]
        dsimp [canbasis]
        rw [eval_pos, mul_one]
        rfl
      rw [mem_span_set', feqht]
      /- We have that given any e ∈ E,
         h (t e) = h (∑ i: Fin n, ((t e) i) • canbasis i) = ∑ i: Fin n, (t e i) * h (canbasis i) =
         = ∑ i: Fin n, (h ∘ canbasis) i * (t e i) = ∑ i: Fin n, (h ∘ canbasis) i * ((b i).1 e) =
         = ∑ i: Fin n, (h ∘ canbasis) i * ((Subtype.val ∘ b) i e) = (∑ i: Fin n, (h ∘ canbasis) i • (Subtype.val ∘ b) i) e. -/
      use n, h ∘ canbasis, b.toFun
      ext e
      simp
      rw [basisdec (t e)]
      simp only [map_sum, map_smul, smul_eq_mul]
      dsimp [t]
      simp only [mul_comm]

/- ### Lemas from topology ### -/

/- Theorem: Let Y be a topological space and f: X → Y a map. The topology in X induced by f is the coarsest topology on f
            that makes f continuous. -/
theorem induced_coarsest {X Y: Type*} (f: X → Y) [tY: TopologicalSpace Y] (tX: TopologicalSpace X):
  @Continuous X Y tX tY f → ∀ (s: Set X), @IsOpen X (TopologicalSpace.induced f tY) s → @IsOpen X tX s := by
    intro f_tcont s s_iopen
    /- As s is open in the induced topology by f, we have that there exists an open set V in Y such that s = f ⁻¹' V.
       On the other hand, as f is continuous when we consider the topology tX in X, we have that f ⁻¹' V is an open set in for
       the topology tX, but then so is s. -/
    rw [isOpen_induced_iff] at s_iopen
    rcases s_iopen with ⟨V, Vopen, seqpreV⟩
    rw [continuous_def] at f_tcont
    rw [← seqpreV]
    exact f_tcont V Vopen

/- FALTA COMENTAR -/

theorem exists_ball_subset_family {ι : Type*} (X: Type*) [MetricSpace X] (I : Finset ι) (f : ι → X) (u : ι → Set X)
    (h: ∀ i ∈ I, ∃ (t : ℝ), (0 < t ∧ Metric.ball (f i) t ⊆ u i)):
    ∃ (ε : ℝ), (0 < ε ∧ ∀ i ∈ I, Metric.ball (f i) ε ⊆ u i) := by
  choose t ht using h
  by_cases hI : Finset.Nonempty I
  · rcases Finset.exists_min_image Finset.univ (fun i : I ↦ t i.1 i.2) (by simp [hI]) with ⟨j, jinuniv, jmin⟩
    use t j.1 j.2
    constructor
    · exact (ht j j.2).1
    · intro i iinI
      have : Metric.ball (f i) (t j.1 j.2) ⊆ Metric.ball (f i) (t i iinI) := by
        exact Metric.ball_subset_ball (jmin ⟨i, iinI⟩ (@Finset.mem_univ { x // x ∈ I } _ ⟨i, iinI⟩))
      exact subset_trans this (ht i iinI).2
  · rw [Finset.nonempty_iff_ne_empty, Ne, not_not] at hI
    use 1
    constructor
    · linarith
    · rw [hI]
      intro i iinI
      contradiction

theorem aux_sup {ι α : Type*} [DirectedSet α] (I: Finset ι) (p: ι → α → Prop) (h: ∀ i ∈ I, ∃ (t : α), p i t)
  (h' : ∀ i ∈ I, ∀ (t s : α), t ≤ s → p i t → p i s) : ∃ (t : α), ∀ i ∈ I, p i t := by
    classical
    let F : ι → α := fun i ↦ if q: ∃ (t : α), p i t then Classical.choose q else DirectedSet.default' α
    let T := Finset.image F I
    rcases DirectedSet.sup_finite_set T with ⟨t, tsubT⟩
    use t
    intro i iinI
    have FiinT : F i ∈ T := by
      dsimp [T]
      rw [Finset.mem_image]
      use i
    have : p i (F i) := by
      dsimp [F]
      rw [dif_pos (h i iinI)]
      exact Classical.choose_spec (h i iinI)
    exact h' i iinI (F i) t (tsubT (F i) FiinT) this

theorem Real_archimedean' (x y : ℝ) : (0 < x) → ∃ (n : ℕ), y < n * x := by
  intro x_pos
  simpa using exists_lt_nsmul x_pos y

theorem Real_archimedean'' (x: ℝ) (h₁: 0 ≤ x) (h₂: ∀ (m : ℕ), (0 < m) → x < 1/m) : x = 0 := by
  by_contra! xnz
  have xpos: 0 < x := by
    exact lt_of_le_of_ne h₁ (Ne.symm xnz)
  rcases Real_archimedean' x 1 xpos with ⟨n, oneltnx⟩
  have : 0 < n := by
    by_contra! neqz
    rw [Nat.le_zero] at neqz
    rw [neqz] at oneltnx
    norm_cast at oneltnx
    rw [zero_mul] at oneltnx
    linarith
  rw [mul_comm, ← div_lt_iff₀] at oneltnx
  · have := h₂ n this
    linarith
  · norm_cast
