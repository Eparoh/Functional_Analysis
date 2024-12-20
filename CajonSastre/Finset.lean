import CajonSastre.Nat

set_option trace.Meta.Tactic.simp false

open Set Filter Topology Function

variable {M: Type*} [AddCommMonoid M]
variable {Y: Type*} [AddCommGroup Y]
variable {α: Type*} [Inhabited α] [LinearOrder α]
variable {β: Type*} {C F : ℕ → Finset β}

/- ### Miscellanea ### -/

lemma Finset.union_deleted_mem {ι: Type*} [DecidableEq ι] (J: Finset ι) :
  ∀ j ∈ J, J = (J \ {j}) ∪ {j} := by
    intro j jinJ
    rw [eq_comm, Finset.sdiff_union_self_eq_union, eq_comm,
        Finset.left_eq_union, Finset.singleton_subset_iff]
    exact jinJ

lemma Finset.sdiff_nempty_of_ssub {α: Type*} [DecidableEq α] {s t: Finset α} :
  s ⊂ t → t \ s ≠ ∅ := by
    intro ssubt eqemp
    simp only [sdiff_eq_empty_iff_subset] at eqemp
    have := ssubset_of_ssubset_of_subset ssubt eqemp
    have := not_ssubset_of_subset (subset_refl s)
    contradiction

lemma Finset.disjoint_sdiff_of_sub {α: Type*} [DecidableEq α]
(s t u v: Finset α) :
  s ⊆ v → Disjoint (s \ t) (u \ v) := by
    intro ssubv
    rw [Finset.disjoint_iff_ne]
    intro a ain b bin
    by_contra!
    rw [← this] at bin
    rw [mem_sdiff] at *
    have := ssubv ain.1
    have := bin.2
    contradiction

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

lemma Finset.Ioc_eq_Ico {n m: ℕ} (ngtz: 0 < n) (mgtz: 0 < m) :
  Finset.Ioc (n - 1) (m - 1) = Finset.Ico n m := by
    ext k
    rw [Finset.mem_Ioc, Finset.mem_Ico]
    constructor
    · intro h
      exact And.intro (Nat.le_of_pred_lt h.1)
        (Nat.lt_of_le_pred mgtz h.2)
    · intro h
      exact And.intro (Nat.sub_one_lt_of_le ngtz h.1)
        ((Nat.le_sub_one_iff_lt mgtz).mpr h.2)

lemma Finset.Ico_eq_Ioc {n m: ℕ} :
  Finset.Ico (n + 1) (m + 1) = Finset.Ioc n m := by
    rw [← Finset.Ioc_eq_Ico (Nat.zero_lt_succ n)
        (Nat.zero_lt_succ m), Nat.succ_eq_add_one,
        Nat.add_sub_cancel, Nat.succ_eq_add_one,
        Nat.add_sub_cancel]

lemma Finset.sub_Iic_of_lt {s: Finset ℕ} (k: ℕ) :
  (∀ n ∈ s, n < k) → s ⊂ Finset.Iic k := by
    intro h
    rw [Finset.ssubset_iff_of_subset]
    · use k
      constructor
      · rw [Finset.mem_Iic]
      · by_contra!
        have := h k this
        linarith
    · intro m mins
      rw [Finset.mem_Iic]
      exact le_of_lt (h m mins)

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

lemma Finset.sum_Iic_sub_Iic_eq_sum_Ioc {f : ℕ → Y} {n m : ℕ} (h : n ≤ m) :
    ∑ i ∈ Finset.Iic m, f i - ∑ i ∈ Finset.Iic n, f i =
    ∑ i ∈ Finset.Ioc n m, f i := by
    rw [sub_eq_iff_eq_add]
    exact Finset.sum_Iic_eq_sum_Ioc_add_Iic h

lemma Finset.sum_Iic_zero {X: Type*} [AddCommMonoid X] (f: ℕ → X): ∑ n ≤ 0, f n = f 0 := by
  have : Finset.Iic 0 = {0} := by
    rfl
  rw [this]
  exact Finset.sum_singleton f 0

lemma Finset.sum_succ {f : ℕ → Y} {N : ℕ} (m: ℕ):
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

lemma Finset.sum_Icc_sub_Icc {f : ℕ → Y} {m n k : ℕ} (mlek: m ≤ k)
  (klen : k ≤ n) : ∑ i ∈ Finset.Icc m n, f i - ∑ i ∈ Finset.Icc m k, f i = ∑ i ∈ Finset.Ioc k n, f i := by
  rw [Finset.Icc_union mlek klen, Finset.sum_union (Finset.Icc_disjoint (lt_add_one k)),
      add_comm, ← add_sub, sub_self, add_zero]
  have : Finset.Icc (k + 1) n = Finset.Ioc k n := by
    exact Nat.Icc_succ_left k n
  rw [this]

lemma Finset.sum_Iic_telescopic {f : ℕ → Y} {N : ℕ}:
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

lemma Finset.sum_Iic_succ_top {f: ℕ → M} (n: ℕ) :
  ∑ i ∈ Finset.Iic (n + 1), f i =
  ∑ i ∈ Finset.Iic n, f i + f (n + 1) := by
    simp only [Finset.Icc_eq_Iic,
    Finset.sum_Icc_succ_top (Nat.zero_le (n + 1))]

lemma Finset.sum_image_inj {f: ℕ → M} {g: ℕ → ℕ} (injg: Injective g) (n m: ℕ) :
  ∑ i ∈ Finset.Icc n m , f (g i) = ∑ i ∈ Finset.image g (Finset.Icc n m), f i := by
    rw [eq_comm]
    apply Finset.sum_image
    intro i _ j _ eq
    exact injg eq

theorem Finset.sum_decomp {ι: Type*} (J: Finset ι)
  [Nonempty J] (f: ℕ → M) (g: ι → ℕ → ℕ) (gSM: ∀ j ∈ J, StrictMono (g j))
  (disj: ∀ j ∈ J, ∀ i ∈ J, i ≠ j →
   Disjoint (Set.range (g j)) (Set.range (g i)))
  (un: ∀ (m: ℕ), ∃ j ∈ J, ∃ (n: ℕ), m = (g j) n)
  (n: ℕ) :
    ∑ i ∈ Finset.Iic n, f i =
    ∑ j ∈ J, (∑ i ∈ {i ∈ Finset.Iic n | g j i ≤ n}, f ((g j) i)) := by
      classical
      induction' n with n ih
      · have : ∃ j ∈ J, g j 0 = 0 := by
          rcases un 0 with ⟨j, jinJ, n₀, zeq⟩
          use j, jinJ
          have : g j n₀ ≤ g j 0 := by
            rw [← zeq]
            exact zero_le _
          rw [StrictMono.le_iff_le (gSM j jinJ)] at this
          have : n₀ = 0 := by
            exact Nat.eq_zero_of_le_zero this
          nth_rw 1 [← this]
          exact zeq.symm
        rcases this with ⟨j₀, j₀inJ, gj₀eqz⟩
        have eqz : {i ∈ Finset.Iic 0 | g j₀ i ≤ 0} = {0} := by
          ext k
          constructor
          · intro kin
            simp only [Finset.mem_singleton]
            simp only [nonpos_iff_eq_zero, Finset.mem_filter,
              Finset.mem_Iic] at kin
            exact kin.1
          · intro kin
            simp only [nonpos_iff_eq_zero, Finset.mem_filter,
              Finset.mem_Iic]
            simp only [Finset.mem_singleton] at kin
            constructor
            · assumption
            · rw [kin]
              assumption
        have eqemp : ∑ j ∈ J \ {j₀}, ∑ i ∈
          {i ∈ Finset.Iic 0 | g j i ≤ 0}, f ((g j) i) = 0 := by
            apply Finset.sum_eq_zero
            intro j jinJm
            have : Finset.filter (fun i ↦ g j i ≤ 0) (Finset.Iic 0) = ∅ := by
              rw [Finset.filter_eq_empty_iff]
              intro k kin
              simp only [Finset.mem_sdiff, Finset.mem_singleton,
                ← ne_eq] at jinJm
              simp only [Finset.mem_Iic, nonpos_iff_eq_zero] at kin
              rw [kin]
              simp only [nonpos_iff_eq_zero, ← ne_eq]
              intro gjzeqz
              have r1 : 0 ∈ Set.range (g j) := by
                use 0
              have r2 : 0 ∈ Set.range (g j₀) := by
                use 0
              have := disj j₀ j₀inJ j jinJm.1 jinJm.2
              rw [disjoint_iff_forall_ne] at this
              have := this r2 r1
              contradiction
            rw [this, Finset.sum_empty]
        rw [Finset.union_deleted_mem J j₀ j₀inJ,
            Finset.sum_union (Finset.sdiff_disjoint), eqemp, zero_add,
            Finset.sum_singleton, eqz, Finset.sum_singleton, gj₀eqz,
            Finset.sum_Iic_zero]
      · rcases un (n + 1) with ⟨j₀, j₀inJ, n₀, gn₀eqnp1⟩
        rw [eq_comm] at gn₀eqnp1
        have eq1 : ∑ x ∈ J \ {j₀}, ∑ i ∈
          {i ∈ Finset.Iic (n + 1) | g x i ≤ n + 1}, f (g x i) =
          ∑ x ∈ J \ {j₀}, ∑ i ∈
          {i ∈ Finset.Iic n | g x i ≤ n}, f (g x i) := by
            apply Finset.sum_congr rfl
            intro j jinJm
            simp only [Finset.mem_sdiff, Finset.mem_singleton] at jinJm
            apply Finset.sum_congr
            · ext k
              simp only [Finset.mem_filter, Finset.mem_Iic] at *
              constructor
              · intro kin
                have : g j k ≠ n + 1 := by
                  by_contra!
                  have r1 : n + 1 ∈ Set.range (g j) := by
                    use k
                  have r2 : n + 1 ∈ Set.range (g j₀) := by
                    use n₀
                  have := disj j₀ j₀inJ j jinJm.1 jinJm.2
                  rw [disjoint_iff_forall_ne] at this
                  have := this r2 r1
                  contradiction
                constructor
                · by_contra!
                  have := Nat.le_antisymm kin.1 this
                  have : n + 1 ≤ g j k := by
                    rw [this]
                    exact StrictMono.le_apply (gSM j jinJm.1)
                  have := Nat.le_antisymm kin.2 this
                  contradiction
                · by_contra!
                  have := Nat.le_antisymm kin.2 this
                  contradiction
              · intro kin
                constructor
                · exact Nat.le_trans kin.1 (Nat.le_add_right n 1)
                · exact Nat.le_trans kin.2 (Nat.le_add_right n 1)
            · intros
              rfl
        have eq2 : {i ∈ Finset.Iic (n + 1) | g j₀ i ≤ n + 1} =
          {i ∈ Finset.Iic n | g j₀ i ≤ n} ∪ {n₀} := by
            ext k
            simp only [Finset.mem_filter, Finset.mem_Iic,
              Finset.mem_union, Finset.mem_singleton]
            constructor
            · intro kin
              by_cases h: g j₀ k = n + 1
              · rw [← gn₀eqnp1] at h
                right
                exact StrictMono.injective (gSM j₀ j₀inJ) h
              · have := Nat.le_of_lt_succ (Nat.lt_of_le_of_ne kin.2 h)
                left
                constructor
                · by_contra! h'
                  rw [← StrictMono.lt_iff_lt (gSM j₀ j₀inJ)] at h'
                  have := lt_of_lt_of_le (lt_of_le_of_lt
                    (StrictMono.le_apply (gSM j₀ j₀inJ)) h') this
                  linarith
                · assumption
            · intro kin
              rcases kin with h | h
              · constructor
                · exact Nat.le_trans h.1 (Nat.le_add_right n 1)
                · exact Nat.le_trans h.2 (Nat.le_add_right n 1)
              · rw [h]
                constructor
                · rw [← StrictMono.le_iff_le (gSM j₀ j₀inJ), gn₀eqnp1]
                  exact StrictMono.le_apply (gSM j₀ j₀inJ)
                · rw [gn₀eqnp1]
        have eq3: Disjoint {i ∈ Finset.Iic n | g j₀ i ≤ n} {n₀} := by
          rw [Finset.disjoint_iff_ne]
          simp only [Finset.mem_filter, Finset.mem_Iic, Finset.mem_singleton,
                     ne_eq, forall_eq, and_imp]
          intro k klen gjklen
          by_contra!
          rw [this, gn₀eqnp1] at gjklen
          linarith
        rw [Finset.sum_Iic_succ_top, Finset.union_deleted_mem J j₀ j₀inJ,
            Finset.sum_union (Finset.sdiff_disjoint), Finset.sum_singleton,
            eq2, Finset.sum_union eq3, Finset.sum_singleton, gn₀eqnp1,
            ← Finset.sum_singleton
            (fun x ↦ ∑ i ∈ {i ∈ Finset.Iic n | g x i ≤ n},
            f (g x i)) j₀, eq1, ← add_assoc,
            ← Finset.sum_union (Finset.sdiff_disjoint),
            ← Finset.union_deleted_mem J j₀ j₀inJ, ih]

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

/- ### Inclusion in families of finite sets ### -/

lemma Fsub {β: Type*} (C F : ℕ → Finset β)
(st1: ∀ (n: ℕ), F n ⊂ C n)
(st2: ∀ (n: ℕ), C n ⊂ F (n + 1)) :
  ∀ {n m: ℕ}, n ≤ m → F n ⊆ F m := by
    have st1 : ∀ (n: ℕ), F n ⊆ C n := by
      intro n
      exact subset_of_ssubset (st1 n)
    have st2 : ∀ (n: ℕ), C n ⊆ F (n + 1) := by
      intro n
      exact subset_of_ssubset (st2 n)
    intro n m nlem
    induction' m with m ih
    · rw [nonpos_iff_eq_zero] at nlem
      rw [nlem]
    · rw [Nat.le_succ_iff, Nat.succ_eq_add_one] at nlem
      rcases nlem with h | h
      · exact subset_trans
          (subset_trans (ih h) (st1 m)) (st2 m)
      · rw [h]

lemma Csub {β: Type*} (C F : ℕ → Finset β)
(st1: ∀ (n: ℕ), F n ⊂ C n)
(st2: ∀ (n: ℕ), C n ⊂ F (n + 1)) :
  ∀ {n m: ℕ}, n ≤ m → C n ⊆ C m := by
    have st1 : ∀ (n: ℕ), F n ⊆ C n := by
      intro n
      exact subset_of_ssubset (st1 n)
    have st2 : ∀ (n: ℕ), C n ⊆ F (n + 1) := by
      intro n
      exact subset_of_ssubset (st2 n)
    intro n m nlem
    induction' m with m ih
    · rw [nonpos_iff_eq_zero] at nlem
      rw [nlem]
    · rw [Nat.le_succ_iff, Nat.succ_eq_add_one] at nlem
      rcases nlem with h | h
      · exact subset_trans
          (subset_trans (ih h) (st2 m)) (st1 (m + 1))
      · rw [h]

lemma FCsub {β: Type*} (C F : ℕ → Finset β)
(st1: ∀ (n: ℕ), F n ⊂ C n)
(st2: ∀ (n: ℕ), C n ⊂ F (n + 1)) :
  ∀ {n m: ℕ}, n ≤ m → F n ⊆ C m := by
    have st1 : ∀ (n: ℕ), F n ⊆ C n := by
      intro n
      exact subset_of_ssubset (st1 n)
    have st2 : ∀ (n: ℕ), C n ⊆ F (n + 1) := by
      intro n
      exact subset_of_ssubset (st2 n)
    intro n m nlem
    induction' m with m ih
    · rw [nonpos_iff_eq_zero] at nlem
      rw [nlem]
      exact st1 0
    · rw [Nat.le_succ_iff, Nat.succ_eq_add_one] at nlem
      rcases nlem with h | h
      · exact subset_trans
          (subset_trans (ih h) (st2 m)) (st1 (m + 1))
      · rw [h]
        exact st1 (m + 1)

lemma CFsub {β: Type*} (C F : ℕ → Finset β)
(st1: ∀ (n: ℕ), F n ⊂ C n)
(st2: ∀ (n: ℕ), C n ⊂ F (n + 1)) :
  ∀ {n m: ℕ}, n < m → C n ⊆ F m := by
    have st1 : ∀ (n: ℕ), F n ⊆ C n := by
      intro n
      exact subset_of_ssubset (st1 n)
    have st2 : ∀ (n: ℕ), C n ⊆ F (n + 1) := by
      intro n
      exact subset_of_ssubset (st2 n)
    intro n m nlem
    induction' m with m ih
    · contradiction
    · rw [Nat.lt_succ_iff_lt_or_eq] at nlem
      rcases nlem with h | h
      · exact subset_trans
          (subset_trans (ih h) (st1 m)) (st2 m)
      · rw [h]
        exact st2 m

/- ### Minimum and maximum of finite set in non empty type -/

def Finset.min'' (s: Finset α) := if h: s.Nonempty then
   Finset.min' s h else default

lemma Finset.min''_def (s : Finset α) (H : s.Nonempty) :
  Finset.min'' s = Finset.min' s H := by
    unfold Finset.min''
    rw [dif_pos H]

theorem Finset.min''_mem (s : Finset α) (H : s.Nonempty) :
  Finset.min'' s ∈ s := by
    rw [Finset.min''_def s H]
    exact Finset.min'_mem s H

theorem Finset.min''_le (s : Finset α) (x : α) (H2 : x ∈ s) :
  Finset.min'' s ≤ x := by
    rw [Finset.min''_def s ⟨x, H2⟩]
    exact Finset.min'_le s x H2

theorem Finset.le_min'' (s : Finset α) (H : s.Nonempty) (x : α)
  (H2 : ∀ y ∈ s, x ≤ y) :
    x ≤ Finset.min'' s := by
    rw [Finset.min''_def s H]
    exact Finset.le_min' s H x H2

@[simp]
theorem Finset.le_min''_iff (s : Finset α) (H : s.Nonempty) {x : α} :
  x ≤ Finset.min'' s ↔ ∀ y ∈ s, x ≤ y := by
    rw [Finset.min''_def s H]
    exact Finset.le_min'_iff s H

@[simp]
theorem Finset.min''_singleton (a : α) :
  Finset.min'' {a} = a := by
    rw [Finset.min''_def {a} (singleton_nonempty _)]
    exact Finset.min'_singleton a

@[simp]
theorem Finset.lt_min''_iff (s : Finset α) (H : s.Nonempty) {x : α} :
  x < Finset.min'' s ↔ ∀ y ∈ s, x < y := by
    rw [Finset.min''_def s H]
    exact Finset.lt_min'_iff s H

def Finset.max'' (s: Finset α) := if h: s.Nonempty then
   Finset.max' s h else default

lemma Finset.max''_def (s : Finset α) (H : s.Nonempty) :
  Finset.max'' s = Finset.max' s H := by
    unfold Finset.max''
    rw [dif_pos H]

theorem Finset.max''_mem (s : Finset α) (H : s.Nonempty) :
  Finset.max'' s ∈ s := by
    rw [Finset.max''_def s H]
    exact Finset.max'_mem s H

theorem Finset.le_max'' (s : Finset α) (x : α) (H2 : x ∈ s) :
  x ≤ Finset.max'' s := by
    rw [Finset.max''_def s ⟨x, H2⟩]
    exact Finset.le_max' s x H2

theorem Finset.max''_le (s : Finset α) (H : s.Nonempty) (x : α)
  (H2 : ∀ y ∈ s, y ≤ x) :
    Finset.max'' s ≤ x := by
    rw [Finset.max''_def s H]
    exact Finset.max'_le s H x H2

@[simp]
theorem Finset.max''_le_iff (s : Finset α) (H : s.Nonempty) {x : α} :
  Finset.max'' s ≤ x ↔ ∀ y ∈ s, y ≤ x := by
    rw [Finset.max''_def s H]
    exact Finset.max'_le_iff s H

@[simp]
theorem Finset.max''_singleton (a : α) :
  Finset.max'' {a} = a := by
    rw [Finset.max''_def {a} (singleton_nonempty _)]
    exact Finset.max'_singleton a

@[simp]
theorem Finset.max''_lt_iff (s : Finset α) (H : s.Nonempty) {x : α} :
  Finset.max'' s < x ↔ ∀ y ∈ s, y < x := by
    rw [Finset.max''_def s H]
    exact Finset.max'_lt_iff s H

/- ### Bijection beetween finite sets and its cardinal ### -/

/- Every finite set `F` has a bijection with the interval `[0, #F)` -/

lemma Finset.bij_with_card (α: Type*) [Inhabited α] :
  ∀ (F: Finset α), ∃ (g: ℕ → α), Set.BijOn g (Set.Iio F.card) F := by
    intro F
    have equiv := Fintype.equivFin F
    rw [Fintype.card_coe] at equiv
    let g : ℕ → α := fun n ↦ if h: n < F.card then (equiv.invFun ⟨n, h⟩).1 else default
    use g
    constructor
    · intro n nin
      rw [Set.mem_Iio] at nin
      unfold g
      rw [dif_pos nin]
      simp only [Equiv.invFun_as_coe, Subtype.coe_prop]
    · constructor
      · intro n nin m min gneqgm
        rw [Set.mem_Iio] at *
        unfold g  at gneqgm
        rw [dif_pos nin, dif_pos min] at gneqgm
        simp only [Equiv.invFun_as_coe] at gneqgm
        exact Fin.mk.inj_iff.mp
          (Equiv.injective equiv.symm (Subtype.eq gneqgm))
      · intro n ninF
        simp only [Set.mem_image, Set.mem_Iio]
        rcases Equiv.surjective equiv.symm ⟨n, ninF⟩ with ⟨k, gkeq⟩
        use k.1, k.2
        unfold g
        rw [dif_pos k.2]
        simp only [Fin.eta, Equiv.invFun_as_coe, gkeq]

/- Furthermore, if `α` is a linear order,
   we can impose that the bijection is in fact strictly increasing -/

def Finset.SMC (F: Finset α) (n: ℕ) : α :=
  match n with
  | 0 => Finset.min'' F
  | m + 1 =>
      let image := (Multiset.map (fun ⟨x, _h⟩ => Finset.SMC F x)
      (Finset.Iic m).attach.1).toFinset
      Finset.min'' (F \ image)
termination_by n
decreasing_by
  simp only [mem_Iic] at _h
  exact Nat.lt_add_one_of_le _h

@[simp]
lemma SMC_simp_def (F: Finset α) (m: ℕ) :
  (Multiset.map (fun ⟨x, _⟩ ↦ Finset.SMC F x)
    (Finset.Iic m).attach.val).toFinset =
  Finset.image (Finset.SMC F) (Finset.Iic m) := by
    ext a
    simp only [Finset.attach_val, Multiset.mem_toFinset,
               Multiset.mem_map, Finset.mem_Iic,
               Finset.mem_image]
    constructor
    · intro ain
      rcases ain with ⟨n, nin, SMCneqa⟩
      use n.1
      constructor
      · have := n.2
        rw [Finset.mem_Iic] at this
        assumption
      · assumption
    · intro ain
      rcases ain with ⟨n, nlem, SMCneqa⟩
      rw [← Finset.mem_Iic] at nlem
      use ⟨n, nlem⟩
      constructor
      · exact Multiset.mem_attach ((Finset.Iic m).val) ⟨n, nlem⟩
      · assumption

lemma Finset.SMC_not_empty (F: Finset α) (m: ℕ) (mltcard: m + 1 < F.card) :
  (F \ Finset.image (Finset.SMC F) (Finset.Iic m)).Nonempty := by
    have cardim : (Finset.image F.SMC (Finset.Iic m)).card ≤
      (Finset.Iic m).card := by
        exact Finset.card_image_le
    rw [Nat.card_Iic m] at cardim
    by_cases h: image F.SMC (Iic m) ⊆ F
    · rw [← Finset.card_pos, Finset.card_sdiff h, Nat.sub_pos_iff_lt]
      exact lt_of_le_of_lt cardim mltcard
    · rw [nonempty_iff_ne_empty, ne_eq, Finset.sdiff_eq_empty_iff_subset]
      by_contra!
      have := Nat.le_trans (card_le_card this) cardim
      linarith

theorem Finset.SMC_StrictMonoOn (F: Finset α) :
  StrictMonoOn F.SMC (Set.Iio F.card) := by
    intro n nin m min nltm
    have lt_succ : ∀ (n: ℕ), n + 1 ∈ Set.Iio F.card →
      Finset.SMC F n < Finset.SMC F (n + 1) := by
        intro n np1in
        induction' n with n ih
        · unfold Finset.SMC
          simp only [SMC_simp_def]
          rw [Finset.lt_min''_iff]
          · intro a ain
            simp only [mem_sdiff, mem_image, mem_Iic,
                       nonpos_iff_eq_zero, exists_eq_left, SMC] at ain
            rw [lt_iff_le_and_ne]
            constructor
            · apply Finset.min''_le F a ain.1
            · exact ain.2
          · exact SMC_not_empty F 0 np1in
        · rw [Set.mem_Iio] at *
          unfold SMC
          simp only [SMC_simp_def]
          rw [Finset.lt_min''_iff]
          · intro a ain
            simp only [mem_sdiff, mem_image, mem_Iic,
                       not_exists, not_and] at ain
            rw [lt_iff_le_and_ne]
            constructor
            · apply Finset.min''_le
              simp only [mem_sdiff, mem_image, mem_Iic,
                         not_exists, not_and]
              constructor
              · exact ain.1
              · intro m mlen
                exact ain.2 m (Nat.le_trans mlen (Nat.le_add_right n 1))
            · by_contra! eq
              have : a = F.SMC (n + 1) := by
                unfold SMC
                simp only [SMC_simp_def]
                exact eq.symm
              have := Ne.symm (ain.2 (n + 1) (le_refl _))
              contradiction
          · exact SMC_not_empty F (n + 1) np1in
    induction' m with m ih
    · contradiction
    · rw [Set.mem_Iio] at *
      rw [Nat.lt_succ_iff_lt_or_eq] at nltm
      rcases nltm with h | h
      · exact lt_trans (ih (lt_trans (lt_add_one m) min) h)
          (lt_succ m min)
      · rw [h]
        exact lt_succ m min

theorem Finset.SMC_maps_to (F: Finset α) :
  MapsTo (Finset.SMC F) (Set.Iio F.card) F := by
    intro n nin
    by_cases h: F.Nonempty
    · by_cases neqz: n = 0
      · rw [neqz]
        unfold SMC
        exact min''_mem F h
      · rcases Nat.exists_eq_succ_of_ne_zero neqz with ⟨m, neq⟩
        rw [neq]
        unfold SMC
        simp only [SMC_simp_def]
        rw [neq, Nat.succ_eq_add_one, Set.mem_Iio] at nin
        have := min''_mem (F \ image F.SMC (Iic m))
          (Finset.SMC_not_empty F m nin)
        rw [mem_sdiff] at this
        exact this.1
    · rw [not_nonempty_iff_eq_empty] at h
      rw [h] at nin
      rw [card_empty, Set.mem_Iio] at nin
      contradiction

lemma Finset.SMC_empty (F: Finset α) :
  (F \ Finset.image (Finset.SMC F) (Finset.Iio F.card)) = ∅ := by
    rw [← Finset.card_eq_zero, Finset.card_sdiff,
        Finset.card_image_of_injOn, Nat.card_Iio, Nat.sub_self]
    · simp only [coe_Iio]
      exact StrictMonoOn.injOn (SMC_StrictMonoOn F)
    · have := Finset.SMC_maps_to F
      intro a ain
      rw [mem_image] at ain
      rcases ain with ⟨n, nin, FSMCneqa⟩
      have nin : n ∈ Set.Iio (F.card) := by
        simp only [Set.mem_Iio, mem_Iio] at *
        assumption
      rw [← FSMCneqa]
      exact this nin

theorem Finset.SMC_SurjOn (F: Finset α) :
  SurjOn (Finset.SMC F) (Set.Iio F.card) F := by
    intro a ainF
    by_contra!
    have ain : a ∈ F \ Finset.image F.SMC (Finset.Iio F.card) := by
      simp only [mem_sdiff, mem_image, mem_Iio, not_exists, not_and]
      simp only [Set.mem_image, Set.mem_Iio, not_exists, not_and] at this
      exact And.intro ainF this
    rw [SMC_empty F] at ain
    contradiction

lemma Finset.bij_StrictMono_with_card (α: Type*) [Inhabited α] [LinearOrder α] :
  ∀ (F: Finset α), ∃ (g: ℕ → α), StrictMonoOn g (Set.Iio F.card) ∧
    Set.BijOn g (Set.Iio F.card) F := by
      intro F
      use Finset.SMC F
      constructor
      · exact SMC_StrictMonoOn F
      · constructor
        · exact Finset.SMC_maps_to F
        · constructor
          · exact StrictMonoOn.injOn (SMC_StrictMonoOn F)
          · exact Finset.SMC_SurjOn F

/- ### Some useful recursive constructions ### -/

noncomputable section

/- Given any sequence of finite sets `s: ℕ → Finset β` and any function
   `h: Finset β → ℕ → ℕ` such that for any `F: Finset β`, `h F` is a
    bijection of `[0, #F)` to `F`, we can construct a new sequence
    `g: ℕ → β` that goes like:
    `h (s 0) 0, h (s 0) 1, ..., h (s 0) (#F - 1), h (s 1) 0, h (s 1) 1, ...`

    We can achieve this by defining a couple of functions `Ts` and `ps`
    that tell us "when to start with a new `s i`"-/

def Ts (s: ℕ → Finset β) : ℕ → ℕ
  | 0 => 0
  | n + 1 => ∑ i ∈ Finset.Iic n, (s i).card

def ps (s: ℕ → Finset β) : ℕ → ℕ := fun n ↦ sInf {k: ℕ | n < Ts s (k + 1)}

lemma Ts_zero {β: Type*} {s: ℕ → Finset β} :
  Ts s 0 = 0 := by
    dsimp only [Ts]

lemma Ts_pos {β: Type*} {s: ℕ → Finset β} :
  ∀ (n: ℕ), Ts s (n + 1) = ∑ i ∈ Finset.Iic n, (s i).card := by
    intro n
    dsimp only [Ts]

/- `Ts` is an strict monotone sequence for any `s: ℕ → Finset β` such
   that `∀ (n: ℕ), s n ≠ ∅` -/

lemma Ts_StrictMono {β: Type*} {s: ℕ → Finset β}
  (snemp: ∀ (n: ℕ), s n ≠ ∅) :
    StrictMono (Ts s) := by
      have : ∀ (n: ℕ), Ts s n < Ts s (n + 1) := by
        intro n
        by_cases h: n = 0
        · rw [h, Ts_zero, Ts_pos, Finset.sum_Iic_zero,
              Finset.card_pos, Finset.nonempty_iff_ne_empty]
          exact snemp 0
        · rw [← Ne, Nat.ne_zero_iff_zero_lt] at h
          rcases Nat.exists_eq_add_one.mpr h with ⟨m, meq⟩
          rw [meq, Ts_pos, Ts_pos, Finset.sum_Iic_succ_top]
          apply Nat.lt_add_of_pos_right
          rw [Finset.card_pos, Finset.nonempty_iff_ne_empty]
          exact snemp (m + 1)
      exact strictMono_nat_of_lt_succ this

lemma Ts_lt_apply {β: Type*} {s: ℕ → Finset β}
  (snemp: ∀ (n: ℕ), s n ≠ ∅) :
 ∀ (n: ℕ), n < Ts s (n + 1) := by
  intro n
  exact lt_of_lt_of_le (lt_add_one n)
    (StrictMono.le_apply (Ts_StrictMono snemp))

/- The set defining `ps` is not empty, so for any `n: ℕ` we have:
   - `n < Ts s ((ps s n) + 1)` (`lt_ps`)
   - `Ts s (ps s n) ≤ n` (`ps_le`) -/

lemma ps_not_empty {β: Type*} {s: ℕ → Finset β}
  (snemp: ∀ (n: ℕ), s n ≠ ∅) :
  ∀ (n: ℕ), {k: ℕ | n < Ts s (k + 1)}.Nonempty := by
    intro n
    use n
    simp only [mem_setOf_eq]
    exact Ts_lt_apply snemp n

lemma lt_ps {β: Type*} {s: ℕ → Finset β}
  (snemp: ∀ (n: ℕ), s n ≠ ∅) :
  ∀ (n: ℕ), n < Ts s ((ps s n) + 1) := by
    intro n
    unfold ps
    have := Nat.sInf_mem (ps_not_empty snemp n)
    exact this

lemma ps_le {β: Type*} {s: ℕ → Finset β} :
  ∀ (n: ℕ), Ts s (ps s n) ≤ n := by
    intro n
    by_cases pnz: ps s n = 0
    · rw [pnz]
      rw [Ts_zero]
      exact zero_le _
    · have := Nat.not_mem_of_lt_sInf (Nat.sub_one_lt pnz)
      unfold ps at *
      rw [← Ne, ← Nat.one_le_iff_ne_zero] at pnz
      simp only [mem_setOf_eq, not_lt,
                 Nat.sub_add_cancel pnz] at this
      assumption

/- We have then that for any `n: ℕ`
   `(n - Ts s (ps s n)) ∈ Iio #(s (ps s n))` (`correct_domain`)

   So, the desired function will be:
   `g n := h (s (ps s n)) (n - Ts s (ps s n)))`-/

lemma correct_domain {β: Type*} {s: ℕ → Finset β}
  (snemp: ∀ (n: ℕ), s n ≠ ∅) :
  ∀ (n: ℕ), (n - Ts s (ps s n)) ∈
    Iio (s (ps s n)).card := by
      intro n
      rw [mem_Iio]
      by_cases h: ps s n = 0
      · rw [h, Ts_zero, Nat.sub_zero]
        have := lt_ps snemp n
        rw [h, Ts_pos 0, Finset.sum_Iic_zero] at this
        assumption
      · apply Nat.sub_lt_left_of_lt_add (ps_le n)
        have pmone : ps s n = (ps s n - 1) + 1 := by
          exact (Nat.succ_pred_eq_of_ne_zero h).symm
        rw [pmone, Ts_pos, ← Finset.sum_Iic_succ_top (ps s n - 1),
            ← pmone, ← Ts_pos]
        exact lt_ps snemp n

lemma mem_Ts_Ico_iff_ps_eq {β: Type*} {s: ℕ → Finset β}
  (snemp: ∀ (n: ℕ), s n ≠ ∅) :
  ∀ (n m: ℕ), m ∈ Finset.Ico (Ts s n) (Ts s (n + 1)) ↔ ps s m = n := by
    intro n m
    rw [Finset.mem_Ico]
    constructor
    · intro min
      unfold ps
      rw [Nat.sInf_eq (ps_not_empty snemp m)]
      constructor
      · rw [mem_setOf_eq]
        exact min.2
      · intro k kin
        rw [mem_setOf_eq] at kin
        rw [← StrictMono.le_iff_le (Ts_StrictMono snemp)]
        by_contra! klt
        have ltk := lt_of_le_of_lt min.1 kin
        rw [StrictMono.lt_iff_lt (Ts_StrictMono snemp)] at *
        linarith
    · intro eq
      rw [← eq]
      exact And.intro (ps_le m) (lt_ps snemp m)

lemma cover_gTs {β: Type*} [DecidableEq β] {s: ℕ → Finset β}
  (snemp: ∀ (n: ℕ), s n ≠ ∅) {h: Finset β → ℕ → β}
  (hdef: ∀ (F : Finset β), BijOn (h F) (Iio F.card) F) :
    ∀ (m: ℕ) (b: β), b ∈ s m →
    ∃ n ∈ Finset.Ico (Ts s m) (Ts s (m + 1)),
    h (s (ps s n)) (n - Ts s (ps s n)) = b := by
      intro m b binsm
      rcases (hdef (s m)).2.2 binsm with ⟨n, nin, hsmneqb⟩
      use n + Ts s m
      have : ps s (n + Ts s m) = m := by
        rw [← mem_Ts_Ico_iff_ps_eq snemp, Finset.mem_Ico]
        constructor
        · exact Nat.le_add_left (Ts s m) n
        · by_cases h: m = 0
          · rw [h, Ts_zero, add_zero, Ts_pos, Finset.sum_Iic_zero]
            rw [mem_Iio, h] at nin
            assumption
          · rcases Nat.exists_eq_succ_of_ne_zero h with ⟨k, neqkp1⟩
            rw [neqkp1, Nat.succ_eq_add_one, Ts_pos, Ts_pos,
                Finset.sum_Iic_succ_top, add_comm]
            apply Nat.add_lt_add_left
            rw [mem_Iio, neqkp1] at nin
            assumption
      constructor
      · rw [mem_Ts_Ico_iff_ps_eq snemp]
        assumption
      · rw [this, add_tsub_cancel_right]
        assumption

lemma image_Ts {β: Type*} [DecidableEq β] {s: ℕ → Finset β}
  (snemp: ∀ (n: ℕ), s n ≠ ∅)
  {h: Finset β → ℕ → β}
  (hdef: ∀ (F : Finset β), BijOn (h F) (Iio F.card) F) :
    ∀ (n: ℕ), Finset.image
      (fun (n: ℕ) ↦ h (s (ps s n)) (n - Ts s (ps s n)))
    (Finset.Ico (Ts s n) (Ts s (n + 1))) = s n := by
      intro n
      ext k
      rw [Finset.mem_image]
      constructor
      · intro kin
        rcases kin with ⟨m, min, gmeqk⟩
        rw [← (mem_Ts_Ico_iff_ps_eq snemp n m).mp min, ← gmeqk]
        exact (hdef (s (ps s m))).1 (correct_domain snemp m)
      · intro kin
        rcases cover_gTs snemp hdef n k kin with ⟨m, min, gmeqk⟩
        use m

/- From this, we can now proof that given any `s: ℕ → Finset ℕ`
   there exists of a bijective function `g: ℕ → ℕ` and an strictly
   increasing sequence `t: ℕ → ℕ` such that for any `n: ℕ`
   `g '' [t n, t (n + 1)] = s n` -/

lemma exists_bij_img_eq {s: ℕ → Finset ℕ}
  (snemp: ∀ (n: ℕ), s n ≠ ∅)
  (disj: ∀ (n m: ℕ), n ≠ m → Disjoint (s n) (s m))
  (un: ∀ (m: ℕ), ∃ (n: ℕ), m ∈ s n):
  ∃ (g: ℕ → ℕ), Bijective g ∧ ∃ (t: ℕ → ℕ), StrictMono t ∧ ∀ (n: ℕ),
  Finset.image g (Finset.Ico (t n) (t (n + 1))) = s n := by
    classical
    rcases Classical.axiom_of_choice (Finset.bij_with_card ℕ) with ⟨h, hdef⟩
    let g : ℕ → ℕ := fun n ↦ h (s (ps s n)) (n - Ts s (ps s n))
    have eqg : ∀ (n m: ℕ), (g n = g m → ps s n = ps s m) := by
      intro n m gneqgm
      unfold g at gneqgm
      have inspn := (hdef (s (ps s n))).1 (correct_domain snemp n)
      have inspm := (hdef (s (ps s m))).1 (correct_domain snemp m)
      rw [gneqgm] at inspn
      have : ¬ Disjoint (s (ps s n)) (s (ps s m)) := by
        rw [Finset.not_disjoint_iff]
        use h (s (ps s m)) (m - Ts s (ps s m))
        exact And.intro inspn inspm
      have := (Decidable.not_imp_not).mpr (disj (ps s n) (ps s m)) this
      simp only [ne_eq, Decidable.not_not] at this
      assumption
    have gsurj : Surjective g := by
      unfold g
      intro m
      dsimp only
      rcases un m with ⟨n, minsn⟩
      rcases cover_gTs snemp hdef n m minsn with ⟨a, ain, eq⟩
      use a
    use g
    constructor
    · constructor
      · intro n m gneqgm
        have := eqg n m gneqgm
        unfold g at gneqgm
        rw [this] at gneqgm
        have nin := correct_domain snemp n
        have min := correct_domain snemp m
        rw [this] at nin
        have sol := (hdef (s (ps s m))).2.1 nin min gneqgm
        apply Nat.sub_sub_cancel _ (ps_le m) sol
        rw [← this]
        exact ps_le n
      · exact gsurj
    · use (Ts s)
      constructor
      · exact Ts_StrictMono snemp
      · exact image_Ts snemp hdef

/- We can also obtain the same result but changing the "bijectivity" by
   "strictly increasing" -/

lemma exists_StrictMono_img_eq {s: ℕ → Finset ℕ} (snemp: ∀ (n: ℕ), s n ≠ ∅)
  (incr: ∀ (n: ℕ), sSup (s n).toSet < sInf (s (n + 1))):
  ∃ (g: ℕ → ℕ), StrictMono g ∧ ∃ (t: ℕ → ℕ), StrictMono t ∧ ∀ (n: ℕ),
  Finset.image g (Finset.Ico (t n) (t (n + 1))) = s n := by
    classical
    rcases Classical.axiom_of_choice
      (Finset.bij_StrictMono_with_card ℕ) with ⟨h, hdef⟩
    let g : ℕ → ℕ := fun n ↦ h (s (ps s n)) (n - Ts s (ps s n))
    use g
    constructor
    · sorry
    · use (Ts s)
      constructor
      · exact Ts_StrictMono snemp
      · have : ∀ (x : Finset ℕ), BijOn (h x) (Iio x.card) x := by
          intro F
          exact (hdef F).2
        exact image_Ts snemp this

/- Given two sequences `C F : ℕ → Finset β` of finite subsets, we can construct
   a sequence `sCF C F` given by:
   `F 0, C 0 \ F 0, F 1 \ C 0, C 1 \ F 1, F 2 \ C 1, ...` -/

def sCF [DecidableEq β] (C F : ℕ → Finset β) : ℕ → Finset β := fun n ↦ by
  classical
  exact
  if n = 0 then F 0 else
  (if h: ∃ (k: ℕ), n = 2 * (k + 1) then
  (F (Classical.choose h + 1)) \ (C (Classical.choose h)) else
  (if h: ∃ (k: ℕ), n = 2 * k + 1 then
  (C (Classical.choose h)) \ (F (Classical.choose h)) else ∅))

lemma sCF_zero [DecidableEq β] : sCF C F 0 = F 0 := by
  unfold sCF
  rw [if_pos rfl]

lemma sCF_even [DecidableEq β] :
  ∀ (k: ℕ), sCF C F (2 * (k + 1)) = F (k + 1) \ C k := by
    intro k
    unfold sCF
    have : ∃ (m: ℕ), 2 * (k + 1) = 2 * (m + 1) := by
      use k
    have eqk : Classical.choose this = k := by
      have : 2 * (Classical.choose this + 1) = 2 * (k + 1) := by
        exact (Classical.choose_spec this).symm
      linarith
    rw [if_neg (by linarith), dif_pos this]
    rw [eqk]

lemma sCF_odd [DecidableEq β] :
  ∀ (k: ℕ), sCF C F (2 * k + 1) = C k \ F k := by
    intro k
    unfold sCF
    have : ∃ (m: ℕ), 2 * k + 1 = 2 * m + 1:= by
      use k
    have neg : ¬ ∃ (m: ℕ), 2 * k + 1 = 2 * (m + 1) := by
      push_neg
      intro m
      exact Ne.symm Nat.two_mul_ne_two_mul_add_one
    have eqk : Classical.choose this = k := by
      have : 2 * (Classical.choose this) + 1 = 2 * k + 1 := by
        exact (Classical.choose_spec this).symm
      linarith
    rw [if_neg (by linarith), dif_neg neg, dif_pos this]
    rw [eqk]

/- If furthermore we have that `∀ (n: ℕ), F n ⊂ C n`,
   `∀ (n: ℕ), C n ⊂ F (n + 1)` and `F 0 ≠ ∅` we can ensure that:
   - Every set of the sequence is nonempty (`sCF_not_empty`)
   - Every pair of distinct sets in the sequence are
     disjoint (`sCF_disjoint`) -/

lemma sCF_not_empty [DecidableEq β] (st1: ∀ (n: ℕ), F n ⊂ C n)
(st2: ∀ (n: ℕ), C n ⊂ F (n + 1)) (nemp: F 0 ≠ ∅) :
  ∀ (n: ℕ), sCF C F n ≠ ∅ := by
    intro n
    by_cases h: n = 0
    · rw [h, sCF_zero]
      assumption
    · rcases Nat.exists_eq_succ_of_ne_zero h with ⟨m, neqmp1⟩
      rw [neqmp1, Nat.succ_eq_add_one]
      by_cases h: Odd m
      · rcases h with ⟨k, neq⟩
        rw [neq, add_assoc, one_add_one_eq_two]
        nth_rw 2 [← mul_one 2]
        rw [← Nat.mul_add, sCF_even k]
        exact Finset.sdiff_nempty_of_ssub (st2 k)
      · rw [Nat.not_odd_iff_even] at h
        rcases h with ⟨k, neq⟩
        rw [neq, ← Nat.two_mul k, sCF_odd k]
        exact Finset.sdiff_nempty_of_ssub (st1 k)

lemma sCF_disjoint' [DecidableEq β] (st1: ∀ (n: ℕ), F n ⊂ C n)
(st2: ∀ (n: ℕ), C n ⊂ F (n + 1)) :
  ∀ (n m: ℕ), n < m → Disjoint (sCF C F n) (sCF C F m) := by
    intro n m nltm
    by_cases neqz : n = 0
    · rw [neqz, sCF_zero]
      by_cases h : Odd m
      · rcases h with ⟨k, meq⟩
        rw [meq, sCF_odd k, ← @Finset.sdiff_empty _ _ (F 0)]
        exact Finset.disjoint_sdiff_of_sub (F 0) ∅ (C k) (F k)
          (Fsub C F st1 st2 (zero_le k))
      · simp only [Nat.not_odd_iff_even] at h
        rcases h with ⟨k, meq⟩
        rw [← Nat.two_mul k] at meq
        have : k ≥ 1 := by
          by_contra!
          rw [Nat.lt_one_iff] at this
          rw [neqz, meq, this, mul_zero] at nltm
          contradiction
        rcases Nat.exists_eq_add_one.mpr this with ⟨q, keq⟩
        rw [meq, keq, sCF_even q, ← @Finset.sdiff_empty _ _ (F 0)]
        exact Finset.disjoint_sdiff_of_sub (F 0) ∅ (F (q + 1)) (C q)
          (FCsub C F st1 st2 (zero_le _))
    · rw [← Ne, ← Nat.pos_iff_ne_zero] at neqz
      by_cases hn : Odd n
      · rcases hn with ⟨k, neq⟩
        rw [neq, sCF_odd k]
        · by_cases hm : Odd m
          · rcases hm with ⟨q, meq⟩
            rw [meq, sCF_odd q]
            have : k < q := by
              rw [neq, meq] at nltm
              linarith
            exact Finset.disjoint_sdiff_of_sub
              (C k) (F k) (C q) (F q)
              (CFsub C F st1 st2 this)
          · simp only [Nat.not_odd_iff_even] at hm
            rcases hm with ⟨q, meq⟩
            rw [← Nat.two_mul q] at meq
            have : q ≥ 1 := by
              by_contra!
              rw [Nat.lt_one_iff] at this
              rw [meq, this, mul_zero] at nltm
              contradiction
            rcases Nat.exists_eq_add_one.mpr this with ⟨a, aeq⟩
            rw [meq, aeq, sCF_even a]
            have : k ≤ a := by
              rw [neq, meq, aeq] at nltm
              linarith
            exact Finset.disjoint_sdiff_of_sub
              (C k) (F k) (F (a + 1)) (C a)
              (Csub C F st1 st2 this)
      · simp only [Nat.not_odd_iff_even] at hn
        rcases hn with ⟨k, neq⟩
        rw [← Nat.two_mul k] at neq
        have : k ≥ 1 := by
          by_contra!
          rw [Nat.lt_one_iff] at this
          rw [neq, this, mul_zero] at neqz
          contradiction
        rcases Nat.exists_eq_add_one.mpr this with ⟨a, aeq⟩
        rw [neq, aeq, sCF_even a]
        · by_cases hm : Odd m
          · rcases hm with ⟨q, meq⟩
            rw [meq, sCF_odd q]
            have : a + 1 ≤ q := by
              rw [neq, meq, aeq] at nltm
              linarith
            exact Finset.disjoint_sdiff_of_sub
              (F (a + 1)) (C a) (C q) (F q)
              (Fsub C F st1 st2 this)
          · simp only [Nat.not_odd_iff_even] at hm
            rcases hm with ⟨q, meq⟩
            rw [← Nat.two_mul q] at meq
            have : q ≥ 1 := by
              by_contra!
              rw [Nat.lt_one_iff] at this
              rw [meq, this, mul_zero] at nltm
              contradiction
            rcases Nat.exists_eq_add_one.mpr this with ⟨b, beq⟩
            rw [meq, beq, sCF_even b]
            have : a + 1 ≤ b := by
              rw [neq, meq, aeq, beq] at nltm
              linarith
            exact Finset.disjoint_sdiff_of_sub
              (F (a + 1)) (C a) (F (b + 1)) (C b)
              (FCsub C F st1 st2 this)

lemma sCF_disjoint [DecidableEq β] (st1: ∀ (n: ℕ), F n ⊂ C n)
(st2: ∀ (n: ℕ), C n ⊂ F (n + 1)) :
  ∀ (n m: ℕ), n ≠ m → Disjoint (sCF C F n) (sCF C F m) := by
  intro n m nneqm
  by_cases h: n < m
  · exact sCF_disjoint' st1 st2 n m h
  · simp only [not_lt] at h
    exact Disjoint.symm
      (sCF_disjoint' st1 st2 m n
      (Nat.lt_of_le_of_ne h (Ne.symm nneqm)))

/- Lastly, if we also have that `∀ (m: β), ∃ (n: ℕ), m ∈ F n` we get
   that sCF also covers `β` -/

lemma sCF_cover [DecidableEq β] (un: ∀ (m: β), ∃ (n: ℕ), m ∈ F n) :
∀ (m: β), ∃ (n: ℕ), m ∈ sCF C F n := by
  intro m
  let n := sInf {k: ℕ | m ∈ F k}
  have notemp : {k: ℕ | m ∈ F k}.Nonempty := by
    rcases un m with ⟨n, minFn⟩
    use n
    assumption
  have minFn : m ∈ F n := Nat.sInf_mem notemp
  by_cases nz : n = 0
  · rw [nz] at minFn
    use 0
    rw [sCF_zero]
    assumption
  · rcases Nat.exists_eq_succ_of_ne_zero nz with ⟨N, neqNp1⟩
    rw [Nat.succ_eq_add_one] at neqNp1
    rw [neqNp1] at minFn
    have mninFN : m ∉ F N := by
      by_contra!
      have : N ∈ {k | m ∈ F k} := by
        exact this
      have := Nat.sInf_le this
      linarith
    by_cases minCN : m ∈ C N
    · have : m ∈ C N \ F N := by
        rw [Finset.mem_sdiff]
        exact And.intro minCN mninFN
      rw [← sCF_odd N] at this
      use (2 * N + 1)
    · have min : m ∈ F (N + 1) \ C N := by
        rw [Finset.mem_sdiff]
        exact And.intro minFn minCN
      rw [← @sCF_even _ C F _ N, Nat.mul_add, mul_one] at min
      use 2 * N + 2

/- Given a function `c: Finset ℕ → Finset ℕ` such that any `c F` is
   nonempty and some `p: ℕ → Prop` we can construct an strictly increasing
  sequence `sInf_inc` such that for all `n: ℕ`:
  - `c ([0, sInf_inc n]) ⊂ Finset.Iic ([0, sInf_inc (n + 1)])`
  - `p (sInf_inc n)` -/

def sInf_inc (c: Finset ℕ → Finset ℕ)
  (cnemp: ∀ (F: Finset ℕ), (c F).Nonempty) (p: ℕ → Prop) : ℕ → ℕ
  | 0 => sInf {k: ℕ | p k}
  | n + 1 => sInf {k: ℕ | p k ∧
    Finset.max'' (c (Finset.Iic (sInf_inc c cnemp p n))) < k ∧
    sInf_inc c cnemp p n < k}

lemma sInf_not_empty (c: Finset ℕ → Finset ℕ)
  (cnemp: ∀ (F: Finset ℕ), (c F).Nonempty) (p: ℕ → Prop)
  (pevnt: ∀ (n: ℕ), ∃ k > n, p k) :
    ∀ (n: ℕ), {k: ℕ | p k ∧ Finset.max''
    (c (Finset.Iic (sInf_inc c cnemp p n))) < k ∧
    sInf_inc c cnemp p n < k}.Nonempty := by
      intro n
      rcases pevnt (Nat.max (Finset.max''
      (c (Finset.Iic (sInf_inc c cnemp p n))))
      (sInf_inc c cnemp p n)) with ⟨k, kgt, pk⟩
      use k
      rw [mem_setOf_eq, Finset.max''_lt_iff]
      · constructor
        · assumption
        · constructor
          · intro m min
            exact lt_of_le_of_lt (Finset.le_max''
              (c ((Finset.Iic (sInf_inc c cnemp p n)))) m min)
              (lt_of_le_of_lt (Nat.le_max_left
              (c (Finset.Iic (sInf_inc c cnemp p n))).max''
              (sInf_inc c cnemp p n)) kgt)
          · exact lt_of_le_of_lt (Nat.le_max_right
              (c (Finset.Iic (sInf_inc c cnemp p n))).max''
              (sInf_inc c cnemp p n)) kgt
      · exact cnemp (Finset.Iic (sInf_inc c cnemp p n))

lemma sInf_inc_def (c: Finset ℕ → Finset ℕ)
  (cnemp: ∀ (F: Finset ℕ), (c F).Nonempty) (p: ℕ → Prop)
  (pevnt: ∀ (n: ℕ), ∃ k > n, p k) :
    ∀ (n: ℕ), c (Finset.Iic (sInf_inc c cnemp p n)) ⊂
    Finset.Iic (sInf_inc c cnemp p (n + 1)) ∧
    p (sInf_inc c cnemp p n) := by
      classical
      intro n
      constructor
      · apply Finset.sub_Iic_of_lt
        intro k kin
        unfold sInf_inc
        apply Nat.le_sInf (sInf_not_empty c cnemp p pevnt n)
        intro m min
        rw [mem_setOf_eq, Finset.max''_lt_iff] at min
        · exact min.2.1 k kin
        · exact cnemp (Finset.Iic (sInf_inc c cnemp p n))
      · by_cases h: n = 0
        · rw [h]
          unfold sInf_inc
          have : {k: ℕ | p k}.Nonempty := by
            rcases pevnt 0 with ⟨k, kgt, pk⟩
            use k
            simpa only [mem_setOf_eq]
          rw [Nat.sInf_def this]
          exact Nat.find_spec this
        · rcases Nat.exists_eq_succ_of_ne_zero h with ⟨m, neq⟩
          rw [neq]
          unfold sInf_inc
          exact (Nat.sInf_mem (sInf_not_empty c cnemp p pevnt m)).1

lemma sInf_inc_StrictMono (c: Finset ℕ → Finset ℕ)
  (cnemp: ∀ (F: Finset ℕ), (c F).Nonempty) (p: ℕ → Prop)
  (pevnt: ∀ (n: ℕ), ∃ k > n, p k) :
    StrictMono (sInf_inc c cnemp p) := by
      have : ∀ (n: ℕ), sInf_inc c cnemp p n <
        sInf_inc c cnemp p (n + 1) := by
          intro n
          rw [sInf_inc]
          exact (Nat.sInf_mem
            (sInf_not_empty c cnemp p pevnt n)).2.2
      exact strictMono_nat_of_lt_succ this
