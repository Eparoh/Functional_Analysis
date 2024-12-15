import Mathlib.Analysis.RCLike.Basic

set_option trace.Meta.Tactic.simp false

open Set Filter Topology Function

variable {M: Type*} [AddCommGroup M]

/- ### Results about intervals ### -/

lemma Finset.Icc_union {m n k: ℕ} (mlek: m ≤ k) (klen: k ≤ n) :
  Finset.Icc m n = Finset.Icc m k ∪ Finset.Icc (k + 1) n := by
    ext x
    rw [Finset.mem_union, Finset.mem_Icc, Finset.mem_Icc, Finset.mem_Icc]
    by_cases xlek: x ≤ k
    · constructor
      · intro xin
        left
        exact And.intro xin.1 xlek
      · intro xin
        rcases xin with h | h
        · exact And.intro h.1 (le_trans h.2 klen)
        · exact And.intro (le_trans (le_trans mlek (Nat.le_succ k)) h.1) h.2
    · push_neg at xlek
      constructor
      · intro xin
        right
        exact And.intro xlek xin.2
      · intro xin
        rcases xin with h | h
        · linarith
        · exact And.intro (le_trans (le_trans mlek (Nat.le_succ k)) h.1) h.2

lemma Finset.Icc_disjoint {m n p q: ℕ} (nltp: n < p):
  Disjoint (Finset.Icc m n) (Finset.Icc p q) := by
    rw [Finset.disjoint_left]
    intro x xinmn
    rw [Finset.mem_Icc] at *
    push_neg
    intro plex
    linarith

/- ### Results about finite sums ### -/

lemma Finset.sum_Iic_eq_sum_Ioc_add_Iic {f : ℕ → M} {n m : ℕ} (h : n ≤ m) :
  ∑ i ∈ Finset.Iic m, f i =
  ∑ i ∈ Finset.Ioc n m, f i + ∑ i ∈ Finset.Iic n, f i := by
    have inter: ∀ (m: ℕ), Finset.Iic m = Finset.Icc 0 m := by
      intro m
      exact rfl
    simp only [inter]
    induction' n with n ih
    · simp only [Finset.Icc_self, Finset.sum_singleton]
      rw [Finset.sum_Ioc_add_eq_sum_Icc h]
    · rw [Finset.sum_Icc_succ_top (Nat.le_add_left 0 (n + 1)),
          add_comm _ (f (n + 1)), ← add_assoc,
          Finset.sum_Ioc_add_eq_sum_Icc h]
      simp only [Nat.Icc_succ_left]
      exact ih (Nat.le_of_succ_le h)

lemma Finset.sum_Iic_sub_Iic_eq_sum_Ioc {f : ℕ → M} {n m : ℕ} (h : n ≤ m) :
    ∑ i ∈ Finset.Iic m, f i - ∑ i ∈ Finset.Iic n, f i =
    ∑ i ∈ Finset.Ioc n m, f i := by
    rw [sub_eq_iff_eq_add]
    exact Finset.sum_Iic_eq_sum_Ioc_add_Iic h

lemma Finset.sum_Iic_zero {X: Type*} [AddCommMonoid X] (f: ℕ → X): ∑ n ≤ 0, f n = f 0 := by
  have : Finset.Iic 0 = {0} := by
    rfl
  rw [this]
  exact Finset.sum_singleton f 0

lemma Finset.sum_succ {f : ℕ → M} {N : ℕ} (m: ℕ):
  ∑ x ∈ Finset.Iic N, f (x + m) = ∑ x ∈ Finset.Icc m (N + m), f (x) := by
    induction' N with N ih
    · rw [Finset.sum_Iic_zero, zero_add, Finset.Icc_self, Finset.sum_singleton]
    · rw [Finset.sum_Iic_eq_sum_Ioc_add_Iic (Nat.le_add_right N 1), Nat.Ioc_succ_singleton, Finset.sum_singleton, ih]
      have union: Finset.Icc m (N + 1 + m) = Finset.Icc (N + 1 + m) (N + 1 + m) ∪ Finset.Icc m (N + m) := by
        rw [add_comm, ← add_assoc, add_comm m N, Finset.union_comm]
        exact Finset.Icc_union (Nat.le_add_left m N) (Nat.le_succ (N + m))
      have disj: Disjoint (Finset.Icc (N + 1 + m) (N + 1 + m)) (Finset.Icc m (N + m)) := by
        rw [disjoint_comm]
        apply Finset.Icc_disjoint
        linarith
      rw [union, Finset.sum_union disj, add_right_cancel_iff, Finset.Icc_self, Finset.sum_singleton]

lemma Finset.sum_Icc_sub_Icc {f : ℕ → M} {m n k : ℕ} (mlek: m ≤ k)
  (klen : k ≤ n) : ∑ i ∈ Finset.Icc m n, f i - ∑ i ∈ Finset.Icc m k, f i = ∑ i ∈ Finset.Ioc k n, f i := by
  rw [Finset.Icc_union mlek klen, Finset.sum_union (Finset.Icc_disjoint (lt_add_one k)),
      add_comm, ← add_sub, sub_self, add_zero]
  have : Finset.Icc (k + 1) n = Finset.Ioc k n := by
    exact Nat.Icc_succ_left k n
  rw [this]

lemma Finset.sum_Iic_telescopic {f : ℕ → M} {N : ℕ}:
  ∑ x ∈ Finset.Iic N, (f (x + 1) - f x) = f (N + 1) - f 0 := by
    by_cases h: 1 ≤ N
    · rw [Finset.sum_sub_distrib, Finset.sum_succ, Finset.sum_Iic_eq_sum_Ioc_add_Iic (Nat.zero_le N),Finset.sum_Iic_zero,
        sub_add_eq_sub_sub, ← Nat.Icc_succ_left, Finset.sum_Icc_sub_Icc h (Nat.le_succ N), Nat.Ioc_succ_singleton,
        Finset.sum_singleton]
    · push_neg at h
      rw [Nat.lt_one_iff] at h
      rw [h, Finset.sum_Iic_zero]

lemma Finset.Icc_eq_Iic (n: ℕ) : Finset.Iic n = Finset.Icc 0 n := by
  rfl

/- ### Sums with zeros ### -/

variable {f f': ℕ → M} {g: ℕ → ℕ}

/- In this section we treat sums which have zeros. That is, given
   a function `f: ℕ → M` (with infinite non-null values) we can "delete"
   its zeros by definining an strictily increasing function `g: ℕ → ℕ`
   such that `g n` is the nth natural number where `f` is non zero.

   The sums of `f` and `f ∘ g` must be related as `f` is null outside
   the range of `g` and that relation is what we formalize here.-/

/- In more generality, we will consider a pair of functions `f f': ℕ → M`
   and an strictily increasing function `g: ℕ → ℕ` in such a way that:
   - `f ∘ g = f' ∘ g`
   - `f` is null outside the range of `g`
   And we will study the relation between the sums of `f` and `f' ∘ g`.
   Observe that taking `f' = f` we recover the original case. -/

/- The main results are `sum_of_comp_eq` and `sum_eq_sum_with_no_extra_zeros` -/

/- `sum_of_comp_eq` asserts that, under the mentioned conditions, we have
   `∑ k ∈ Finset.Icc n m, f' (g k) = ∑ k ∈ Finset.Icc (g n) (g m), f k` -/

/- `sum_eq_sum_with_no_extra_zeros` asserts that, under the mentioned conditions
   (and some more to be sure that `f` is not null in the given interval), we have
   `∑ k ∈ Finset.Icc n m, f k = ∑ k ∈ Finset.Icc a b, f' (g k)`
   where:
   `a = (invFun g (sInf {k: ℕ | n ≤ k ∧ f k ≠ 0}))`
   `b = (invFun g (sSup {k: ℕ | k ≤ m ∧ f k ≠ 0}))` -/

/- `sum_of_comp_eq` -/

lemma mem_range_of_fnez (fz: ∀ (n: ℕ), n ∉ range g → f n = 0) :
  ∀ (k: ℕ), f k ≠ 0 → ∃ (p: ℕ), k = g p := by
    intro k fknez
    by_contra! h
    have : k ∉ range g := by
      intro kin
      rw [mem_range] at kin
      rcases kin with ⟨p, gpeqk⟩
      have := (h p).symm
      contradiction
    have := fz k this
    contradiction

lemma Icc_image_sub_image_Icc (n m: ℕ) (incr: StrictMono g)
  (fz: ∀ (n: ℕ), n ∉ range g → f n = 0) :
    ∀ a ∈ Finset.Icc (g n) (g m), f a ≠ 0 →
    a ∈ Finset.image g (Finset.Icc n m) := by
      intro k kin fknez
      rcases (mem_range_of_fnez fz) k fknez with ⟨p, keqgp⟩
      rw [Finset.mem_image]
      use p
      constructor
      · rw [Finset.mem_Icc] at *
        rw [keqgp, StrictMono.le_iff_le incr, StrictMono.le_iff_le incr] at kin
        assumption
      · exact keqgp.symm

lemma mem_Icc_image_and_nzero_of_mem_image_Icc_and_nzero (n m: ℕ) (incr: StrictMono g)
  (eqcomp: f ∘ g = f' ∘ g) :
  ∀ b ∈ Finset.image g (Finset.Icc n m), f' b ≠ 0 →
    b ∈ Finset.Icc (g n) (g m) ∧ f b ≠ 0 := by
      intro b bin f'bnez
      rw [Finset.mem_image] at bin
      rcases bin with ⟨a, ain, gaeqb⟩
      rw [← gaeqb]
      constructor
      · rw [Finset.mem_Icc, StrictMono.le_iff_le incr, StrictMono.le_iff_le incr, ← Finset.mem_Icc]
        assumption
      · rw [← @comp_apply _ _ _ f, eqcomp, comp_apply, gaeqb]
        assumption

theorem sum_of_comp_eq (n m: ℕ) (incr: StrictMono g) (eqcomp: f ∘ g = f' ∘ g)
  (fz: ∀ (n: ℕ), n ∉ range g → f n = 0) :
    ∑ k ∈ Finset.Icc n m, f' (g k) = ∑ k ∈ Finset.Icc (g n) (g m), f k := by
    have : ∑ k ∈ Finset.Icc n m, f' (g k) =
      ∑ k ∈ Finset.image g (Finset.Icc n m), f' k := by
        rw [eq_comm]
        apply Finset.sum_image
        intro k _ p _ gkeqgp
        exact StrictMono.injective incr gkeqgp
    rw [this, eq_comm]
    apply Finset.sum_bij_ne_zero (fun (a: ℕ) (h: a ∈ Finset.Icc (g n) (g m))
      (h': f a ≠ 0) ↦ a) (Icc_image_sub_image_Icc n m incr fz)
    · intros
      assumption
    · simp only [exists_prop, exists_eq_right_right]
      exact mem_Icc_image_and_nzero_of_mem_image_Icc_and_nzero n m incr eqcomp
    · intro k _ fknez
      rcases mem_range_of_fnez fz k fknez with ⟨p, keqgp⟩
      rw [keqgp, ← @comp_apply _ _ _ f, ← @comp_apply _ _ _ f', eqcomp]

/- `sum_eq_sum_with_no_extra_zeros` -/

-- We include a lemma about Nat.sSup that is not in mathlib for natural numbers:
lemma Nat.le_sSup {s: Set ℕ} (sbdd: BddAbove s) {k: ℕ} :
  k ∈ s → k ≤ sSup s := by
    classical
    intro kins
    have := Nat.find_spec (sbdd)
    rw [mem_upperBounds] at this
    rw [sSup_def sbdd]
    exact this k kins

lemma nezero_ge_nonempty (n: ℕ) (fnez: ∃ k ≥ n, f k ≠ 0) :
  {k | n ≤ k ∧ f k ≠ 0}.Nonempty := by
    rcases fnez with ⟨k, kin, fknez⟩
    use k
    exact And.intro kin fknez

lemma sInf_in_range (n: ℕ) (fz: ∀ (n: ℕ), n ∉ range g → f n = 0)
  (fnez: ∃ k ≥ n, f k ≠ 0) :
  ∃ (k: ℕ), g k = (sInf {k | n ≤ k ∧ f k ≠ 0}) := by
    rw [← mem_range]
    by_contra! h
    have feqz := fz _ h
    have := (Nat.sInf_mem (nezero_ge_nonempty n fnez)).2
    contradiction

lemma nezero_le_nonempty (m: ℕ) (fnez: ∃ k ≤ m, f k ≠ 0) :
  {k | k ≤ m ∧ f k ≠ 0}.Nonempty := by
    rcases fnez with ⟨k, kin, fknez⟩
    use k
    exact And.intro kin fknez

lemma bddabove_le_nonempty {m: ℕ} :
  BddAbove {k | k ≤ m ∧ f k ≠ 0} := by
    use m
    rw [mem_upperBounds]
    intro k kin
    exact kin.1

lemma sSup_in_range (m: ℕ) (fz: ∀ (n: ℕ), n ∉ range g → f n = 0)
  (fnez: ∃ k ≤ m, f k ≠ 0) :
  ∃ (k: ℕ), g k = (sSup {k | k ≤ m ∧ f k ≠ 0}) := by
    rw [← mem_range]
    by_contra! h
    have feqz := fz _ h
    have := (Nat.sSup_mem (nezero_le_nonempty m fnez) bddabove_le_nonempty).2
    contradiction

lemma exists_le_and_ge_of_exists_Icc {n m: ℕ} (fnez: ∃ k ∈ Finset.Icc n m, f k ≠ 0) :
  (∃ k ≥ n, f k ≠ 0) ∧ (∃ k ≤ m, f k ≠ 0) := by
    rcases fnez with ⟨k, kin, fknez⟩
    rw [Finset.mem_Icc] at kin
    constructor
    · use k
      exact And.intro kin.1 fknez
    · use k
      exact And.intro kin.2 fknez

theorem sum_eq_sum_with_no_extra_zeros (n m: ℕ) (incr: StrictMono g)
  (eqcomp: f ∘ g = f' ∘ g) (fz: ∀ (n: ℕ), n ∉ range g → f n = 0)
  (fnez: ∃ k ∈ Finset.Icc n m, f k ≠ 0) :
    ∑ k ∈ Finset.Icc n m, f k =
    ∑ k ∈ Finset.Icc (invFun g (sInf {k: ℕ | n ≤ k ∧ f k ≠ 0}))
      (invFun g (sSup {k: ℕ | k ≤ m ∧ f k ≠ 0})), f' (g k) := by
        have fnez1 := (exists_le_and_ge_of_exists_Icc fnez).1
        have fnez2 := (exists_le_and_ge_of_exists_Icc fnez).2
        rw [sum_of_comp_eq (invFun g (sInf {k | n ≤ k ∧ f k ≠ 0}))
            (invFun g (sSup {k | k ≤ m ∧ f k ≠ 0})) incr eqcomp fz]
        rw [Function.invFun_eq (sInf_in_range n fz fnez1),
            Function.invFun_eq (sSup_in_range m fz fnez2)]
        rw [eq_comm]
        apply Finset.sum_subset
        · apply Finset.Icc_subset_Icc
          · exact (Nat.sInf_mem (nezero_ge_nonempty n fnez1)).1
          · exact (Nat.sSup_mem (nezero_le_nonempty m fnez2)
              bddabove_le_nonempty).1
        · intro k kinnm knin
          rw [Finset.mem_Icc] at *
          by_contra! h
          have : k ∈ {k | n ≤ k ∧ f k ≠ 0} := by
            exact And.intro kinnm.1 h
          have infle := Nat.sInf_le this
          have : k ∈ {k | k ≤ m ∧ f k ≠ 0} := by
            exact And.intro kinnm.2 h
          have lesup := Nat.le_sSup (@bddabove_le_nonempty _ _ f m) this
          have := And.intro infle lesup
          contradiction

/- We study now some properties and relations of
   `invFun g (sInf {k: ℕ | n ≤ k ∧ f k ≠ 0})`
   and
   `invFun g (sSup {k: ℕ | k ≤ m ∧ f k ≠ 0})` -/

lemma StrictMono.pos (incr: StrictMono g) (npos: 0 < n) :
  0 < g n := by
    exact lt_of_le_of_lt (StrictMono.le_apply incr) (incr npos)

lemma StrictMono.pos_add_one (incr: StrictMono g) (n: ℕ) :
  0 < g (n + 1) := by
    exact StrictMono.pos incr (Nat.zero_lt_succ n)

lemma sInfge_le_sSuple (n m: ℕ)
  (fnez: ∃ k ∈ Finset.Icc n m, f k ≠ 0) :
    sInf {k | n ≤ k ∧ f k ≠ 0} ≤ sSup {k | k ≤ m ∧ f k ≠ 0} := by
      rcases fnez with ⟨k, kin, fknez⟩
      rw [Finset.mem_Icc] at kin
      have kinge : k ∈ {k | n ≤ k ∧ f k ≠ 0} := by
        exact And.intro kin.1 fknez
      have kinle : k ∈ {k | k ≤ m ∧ f k ≠ 0} := by
        exact And.intro kin.2 fknez
      exact Nat.le_trans (Nat.sInf_le kinge)
        (Nat.le_sSup bddabove_le_nonempty kinle)

lemma lt_invFun_sInf (n p : ℕ) (h: g p < n) (incr: StrictMono g)
  (fz: ∀ (n: ℕ), n ∉ range g → f n = 0)
  (fnez: ∃ k ≥ n, f k ≠ 0) :
    p  < invFun g (sInf {k | n ≤ k ∧ f k ≠ 0}) := by
      rw [← StrictMono.lt_iff_lt incr, Function.invFun_eq
          (sInf_in_range n fz fnez)]
      by_contra! h
      have := Nat.le_trans (Nat.sInf_mem (nezero_ge_nonempty n fnez)).1 h
      linarith

lemma invFun_sInf_pos (incr: StrictMono g) (gzltn: g 0 < n)
  (fz: ∀ (n: ℕ), n ∉ range g → f n = 0)
  (fnez: ∃ k ≥ n, f k ≠ 0) :
  0 < invFun g (sInf {k | n ≤ k ∧ f k ≠ 0}) := by
    exact lt_invFun_sInf n 0 gzltn incr fz fnez

lemma le_invFun_sSup (m p : ℕ) (h: g p ≤ m) (incr: StrictMono g)
  (fz: ∀ (n: ℕ), n ∉ range g → f n = 0) (fgpneqz: f (g p) ≠ 0)
  (fnez: ∃ k ≤ m, f k ≠ 0) :
    p ≤ invFun g (sSup {k | k ≤ m ∧ f k ≠ 0}) := by
      rw [← StrictMono.le_iff_le incr, Function.invFun_eq
          (sSup_in_range m fz fnez)]
      exact Nat.le_sSup bddabove_le_nonempty (And.intro h fgpneqz)

/- Finally we have a couple more equalities for the sums where the interval
   has lower bound zero. -/

lemma sum_gz_eq_sum_zero (incr: StrictMono g)
  (fz: ∀ (n: ℕ), n ∉ range g → f n = 0) :
    ∑ k ∈ Finset.Icc (g 0) (g n), f k =
    ∑ k ∈ Finset.Icc 0 (g n), f k := by
      apply Finset.sum_subset
      · apply Finset.Icc_subset_Icc
        · exact StrictMono.le_apply incr
        · rfl
      · intro k kin knin
        have : k ∉ range g := by
          by_contra inran
          rcases inran with ⟨p, gpeqk⟩
          simp only [← gpeqk, Finset.mem_Icc, not_and, not_le,
                    StrictMono.lt_iff_lt incr, StrictMono.le_iff_le incr,
                    zero_le, forall_const, true_and] at *
          linarith
        exact fz k this

lemma sum_invFun_eq_sum_zero (m: ℕ) (incr: StrictMono g)
  (fz: ∀ (n: ℕ), n ∉ range g → f n = 0)
  (fnez: ∃ k ≥ 0, f k ≠ 0):
    ∑ k ∈ Finset.Icc (invFun g (sInf {k | 0 ≤ k ∧ f k ≠ 0})) m, f (g k) =
    ∑ k ∈ Finset.Icc 0 m, f (g k) := by
      apply Finset.sum_subset
      · apply Finset.Icc_subset_Icc (zero_le _) (le_refl m)
      · intro k kin knin
        simp only [Finset.mem_Icc, Decidable.not_and_iff_or_not, not_le] at kin knin
        rcases knin with h | h
        · rw [← StrictMono.lt_iff_lt incr,
              Function.invFun_eq (sInf_in_range 0 fz fnez)] at h
          have : g k ∉ {k | 0 ≤ k ∧ f k ≠ 0} := by
            by_contra!
            have := Nat.sInf_le this
            linarith
          simp only [zero_le, ne_eq, true_and, mem_setOf_eq, not_not] at this
          assumption
        · linarith

/- ### Sums of bijection composition ### -/

lemma Finset.sum_image_inj (injg: Injective g) (n m: ℕ) :
  ∑ i ∈ Finset.Icc n m , f (g i) = ∑ i ∈ Finset.image g (Finset.Icc n m), f i := by
    rw [eq_comm]
    apply Finset.sum_image
    intro i _ j _ eq
    exact injg eq
