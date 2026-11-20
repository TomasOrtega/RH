import Mathlib

open Filter PeriodPair Bornology
open scoped Topology

noncomputable section

namespace GlobalTheory

variable (L : PeriodPair)

/- English proof (translation)
The claim follows from `countable_of_Lindelof_of_discrete (X := L.lattice)`.
-/
lemma countable_periodLattice : (L.lattice : Set ℂ).Countable :=
  countable_of_Lindelof_of_discrete (X := L.lattice)

/- English proof (translation)
The claim follows from `hf.eqOn_of_preconnected_of_eventuallyEq hg (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) hS).2 hz h`.
-/
lemma eqOn_compl_of_countable {f g : ℂ → ℂ} {S : Set ℂ} (hS : S.Countable)
    (hf : AnalyticOnNhd ℂ f Sᶜ) (hg : AnalyticOnNhd ℂ g Sᶜ) {z : ℂ} (hz : z ∉ S)
    (h : f =ᶠ[𝓝 z] g) : Set.EqOn f g Sᶜ :=
  hf.eqOn_of_preconnected_of_eventuallyEq hg
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) hS).2 hz h

/- English proof (translation)
The claim follows from `L.isClosed_lattice.isOpen_compl.mem_nhds hz`.
-/
lemma eventually_notMem_periodLattice {z : ℂ} (hz : z ∉ L.lattice) :
    ∀ᶠ w in 𝓝 z, w ∉ L.lattice :=
  L.isClosed_lattice.isOpen_compl.mem_nhds hz

/- English proof (translation)
Use `filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds (L.compl_lattice_sdiff_singleton_mem_nhds z)] with w hw hw'`. Simplify the hypotheses and the goal together.
-/
lemma eventually_ne_notMem_periodLattice (z : ℂ) : ∀ᶠ w in 𝓝[≠] z, w ∉ L.lattice := by
  filter_upwards [self_mem_nhdsWithin, mem_nhdsWithin_of_mem_nhds
    (L.compl_lattice_sdiff_singleton_mem_nhds z)] with w hw hw'
  simp_all

/- English proof (translation)
Rewrite using `[tendsto_cobounded_iff_meromorphicOrderAt_neg (L.meromorphic_weierstrassP l), L.order_weierstrassP l hl]`. Evaluate the decidable proposition.
-/
lemma tendsto_weierstrassP_cobounded {l : ℂ} (hl : l ∈ L.lattice) :
    Tendsto ℘[L] (𝓝[≠] l) (cobounded ℂ) := by
  rw [tendsto_cobounded_iff_meromorphicOrderAt_neg (L.meromorphic_weierstrassP l),
    L.order_weierstrassP l hl]
  decide

/- English proof (translation)
The claim follows from `fun h ↦ ((tendsto_weierstrassP_cobounded L hl).congr' h).not_tendsto (Metric.disjoint_cobounded_nhds (g l)) (hg.tendsto.mono_left nhdsWithin_le_nhds)`.
-/
lemma not_eventually_weierstrassP_eq {l : ℂ} (hl : l ∈ L.lattice) {g : ℂ → ℂ}
    (hg : ContinuousAt g l) : ¬ ∀ᶠ z in 𝓝[≠] l, ℘[L] z = g z := fun h ↦
  ((tendsto_weierstrassP_cobounded L hl).congr' h).not_tendsto
    (Metric.disjoint_cobounded_nhds (g l)) (hg.tendsto.mono_left nhdsWithin_le_nhds)

/- English proof (translation)
Simplify using `using (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt`.
-/
lemma hasDerivAt_weierstrassP {z : ℂ} (hz : z ∉ L.lattice) : HasDerivAt ℘[L] (℘'[L] z) z := by
  simpa using (L.analyticOnNhd_weierstrassP z hz).differentiableAt.hasDerivAt

/- English proof (translation)
Establish `hd : ∀ z ∉ L.lattice, HasDerivAt ℘'[L] (deriv ℘'[L] z) z` using `fun z hz ↦ (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt`. Establish `h1 : ∀ z ∈ (L.lattice : Set ℂ)ᶜ, ℘'[L] z * (deriv ℘'[L] z - (6 * ℘[L] z ^ 2 - L.g₂ / 2)) = 0` using `fun z hz ↦ by`. Establish `h2` using `(hd z hz).pow 2`. Establish `h3` using `((((hasDerivAt_weierstrassP L hz).pow 3).const_mul 4).sub ((hasDerivAt_weierstrassP L hz).const_mul L.g₂)).sub_const L.g₃`. Establish `h4` using `h2.unique (h3.congr_of_eventuallyEq (by filter_upwards [eventually_notMem_periodLattice L hz] with w hw`.

Simplify using `using L.derivWeierstrassP_sq w hw))`. Simplify using `only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at h4`. Take the linear combination `h4 / 2`. Establish `hP` using `L.analyticOnNhd_weierstrassP`. Establish `hP'` using `L.analyticOnNhd_derivWeierstrassP`.

Establish `h5` using `AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero hP' (g := fun z ↦ deriv ℘'[L] z - (6 * ℘[L] z ^ 2 - L.g₂ / 2)) (fun z hz ↦ by have := hP z hz; have := (hP' z hz).deriv; fun_prop) h1 (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) (countable_periodLattice L)).2`. Break down `h5 with h5 | h5` into its components or cases. It suffices to derive a contradiction. Establish `h6 : Set.EqOn ℘[L] (fun _ ↦ ℘[L] z) (L.lattice : Set ℂ)ᶜ` using `IsOpen.eqOn_of_deriv_eq (𝕜 := ℂ) L.isClosed_lattice.isOpen_compl (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) (countable_periodLattice L)).2 L.differentiableOn_weierstrassP (by fun_prop) (fun w hw ↦ by simpa using h5 w hw) hz rfl`. Use `not_eventually_weierstrassP_eq L (zero_mem _) (g := fun _ ↦ ℘[L] z) (by fun_prop) ?_` and prove the remaining obligations.

Use `filter_upwards [eventually_ne_notMem_periodLattice L 0] with w hw using h6 hw`. Rewrite using `[← sub_eq_zero.mp (h5 z hz)]`. Conclude with `hd z hz`.
-/
theorem hasDerivAt_derivWeierstrassP {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt ℘'[L] (6 * ℘[L] z ^ 2 - L.g₂ / 2) z := by
  have hd : ∀ z ∉ L.lattice, HasDerivAt ℘'[L] (deriv ℘'[L] z) z := fun z hz ↦
    (L.analyticOnNhd_derivWeierstrassP z hz).differentiableAt.hasDerivAt
  have h1 : ∀ z ∈ (L.lattice : Set ℂ)ᶜ,
      ℘'[L] z * (deriv ℘'[L] z - (6 * ℘[L] z ^ 2 - L.g₂ / 2)) = 0 := fun z hz ↦ by
    have h2 := (hd z hz).pow 2
    have h3 := ((((hasDerivAt_weierstrassP L hz).pow 3).const_mul 4).sub
      ((hasDerivAt_weierstrassP L hz).const_mul L.g₂)).sub_const L.g₃
    have h4 := h2.unique (h3.congr_of_eventuallyEq (by
      filter_upwards [eventually_notMem_periodLattice L hz] with w hw
      simpa using L.derivWeierstrassP_sq w hw))
    simp only [Nat.cast_ofNat, Nat.add_one_sub_one, pow_one] at h4
    linear_combination h4 / 2
  have hP := L.analyticOnNhd_weierstrassP
  have hP' := L.analyticOnNhd_derivWeierstrassP
  have h5 := AnalyticOnNhd.eq_zero_or_eq_zero_of_mul_eq_zero hP'
    (g := fun z ↦ deriv ℘'[L] z - (6 * ℘[L] z ^ 2 - L.g₂ / 2))
    (fun z hz ↦ by have := hP z hz; have := (hP' z hz).deriv; fun_prop) h1
    (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) (countable_periodLattice L)).2
  rcases h5 with h5 | h5
  · exfalso
    have h6 : Set.EqOn ℘[L] (fun _ ↦ ℘[L] z) (L.lattice : Set ℂ)ᶜ :=
      IsOpen.eqOn_of_deriv_eq (𝕜 := ℂ) L.isClosed_lattice.isOpen_compl
        (Set.Countable.isConnected_compl_of_one_lt_rank (by simp) (countable_periodLattice L)).2
        L.differentiableOn_weierstrassP (by fun_prop) (fun w hw ↦ by simpa using h5 w hw) hz rfl
    refine not_eventually_weierstrassP_eq L (zero_mem _) (g := fun _ ↦ ℘[L] z) (by fun_prop) ?_
    filter_upwards [eventually_ne_notMem_periodLattice L 0] with w hw using h6 hw
  · rw [← sub_eq_zero.mp (h5 z hz)]
    exact hd z hz

/- English proof (translation)
Establish `an : ∀ {f g : ℂ → ℂ}, (∀ᶠ w in 𝓝 z, HasDerivAt f (g w) w) → AnalyticAt ℂ f z` using `fun h ↦ Complex.analyticAt_iff_eventually_differentiableAt.mpr (h.mono fun w hw ↦ hw.differentiableAt)`. Establish `a₁` using `an (h₁.mono fun _ h ↦ h.1)`. Establish `a₂` using `an (h₂.mono fun _ h ↦ h.1)`. Establish `b₁` using `an (h₁.mono fun _ h ↦ h.2)`. Establish `b₂` using `an (h₂.mono fun _ h ↦ h.2)`.

Establish `d₁ : deriv (f₁ - f₂) =ᶠ[𝓝 z] g₁ - g₂` using `by filter_upwards [h₁, h₂] with w p q using (p.1.sub q.1).deriv`. Establish `d₂ : deriv (g₁ - g₂) =ᶠ[𝓝 z] (fun w ↦ 6 * (f₁ w + f₂ w)) * (f₁ - f₂)` using `by filter_upwards [h₁, h₂] with w p q`. Rewrite using `[(p.2.sub q.2).deriv]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.

Establish `key : ∀ n : ℕ, n ≤ analyticOrderAt (f₁ - f₂) z ∧ n ≤ analyticOrderAt (g₁ - g₂) z`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp`. Consider the case `succ n ih`.

Use `push_cast`. Rewrite using `[← analyticOrderAt_deriv_ge_iff (a₁.sub a₂) (by simp [hf]), ← analyticOrderAt_deriv_ge_iff (b₁.sub b₂) (by simp [hg]), analyticOrderAt_congr d₁, analyticOrderAt_congr d₂, analyticOrderAt_mul (by fun_prop) (a₁.sub a₂)]`. Conclude with `⟨ih.2, ih.1.trans le_add_self⟩`. Use `analyticOrderAt_eq_top.mp (ENat.eq_top_iff_forall_ge.mpr fun n ↦ (key n).1)` as an intermediate fact. Use `filter_upwards [this] with w hw`.

Simplify `hw` using `[sub_eq_zero]`.
-/
theorem eventuallyEq_of_weierstrass_system {f₁ g₁ f₂ g₂ : ℂ → ℂ} {k z : ℂ}
    (h₁ : ∀ᶠ w in 𝓝 z, HasDerivAt f₁ (g₁ w) w ∧ HasDerivAt g₁ (6 * f₁ w ^ 2 - k) w)
    (h₂ : ∀ᶠ w in 𝓝 z, HasDerivAt f₂ (g₂ w) w ∧ HasDerivAt g₂ (6 * f₂ w ^ 2 - k) w)
    (hf : f₁ z = f₂ z) (hg : g₁ z = g₂ z) : f₁ =ᶠ[𝓝 z] f₂ := by
  have an : ∀ {f g : ℂ → ℂ}, (∀ᶠ w in 𝓝 z, HasDerivAt f (g w) w) → AnalyticAt ℂ f z :=
    fun h ↦ Complex.analyticAt_iff_eventually_differentiableAt.mpr
      (h.mono fun w hw ↦ hw.differentiableAt)
  have a₁ := an (h₁.mono fun _ h ↦ h.1)
  have a₂ := an (h₂.mono fun _ h ↦ h.1)
  have b₁ := an (h₁.mono fun _ h ↦ h.2)
  have b₂ := an (h₂.mono fun _ h ↦ h.2)
  have d₁ : deriv (f₁ - f₂) =ᶠ[𝓝 z] g₁ - g₂ := by
    filter_upwards [h₁, h₂] with w p q using (p.1.sub q.1).deriv
  have d₂ : deriv (g₁ - g₂) =ᶠ[𝓝 z] (fun w ↦ 6 * (f₁ w + f₂ w)) * (f₁ - f₂) := by
    filter_upwards [h₁, h₂] with w p q
    rw [(p.2.sub q.2).deriv]
    simp
    ring
  have key : ∀ n : ℕ, n ≤ analyticOrderAt (f₁ - f₂) z ∧ n ≤ analyticOrderAt (g₁ - g₂) z := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      push_cast
      rw [← analyticOrderAt_deriv_ge_iff (a₁.sub a₂) (by simp [hf]),
        ← analyticOrderAt_deriv_ge_iff (b₁.sub b₂) (by simp [hg]),
        analyticOrderAt_congr d₁, analyticOrderAt_congr d₂,
        analyticOrderAt_mul (by fun_prop) (a₁.sub a₂)]
      exact ⟨ih.2, ih.1.trans le_add_self⟩
  have := analyticOrderAt_eq_top.mp (ENat.eq_top_iff_forall_ge.mpr fun n ↦ (key n).1)
  filter_upwards [this] with w hw
  simpa [sub_eq_zero] using hw

/- English proof (translation)
Use `filter_upwards [(continuous_add_const c).continuousAt.eventually (eventually_notMem_periodLattice L hz)] with w hw`. Conclude with `⟨(hasDerivAt_weierstrassP L hw).comp_add_const w c, (hasDerivAt_derivWeierstrassP L hw).comp_add_const w c⟩`.
-/
lemma weierstrass_system_add_const (c : ℂ) {z : ℂ} (hz : z + c ∉ L.lattice) :
    ∀ᶠ w in 𝓝 z, HasDerivAt (fun t ↦ ℘[L] (t + c)) (℘'[L] (w + c)) w ∧
      HasDerivAt (fun t ↦ ℘'[L] (t + c)) (6 * ℘[L] (w + c) ^ 2 - L.g₂ / 2) w := by
  filter_upwards [(continuous_add_const c).continuousAt.eventually
    (eventually_notMem_periodLattice L hz)] with w hw
  exact ⟨(hasDerivAt_weierstrassP L hw).comp_add_const w c,
    (hasDerivAt_derivWeierstrassP L hw).comp_add_const w c⟩

/- English proof (translation)
The claim follows from `(countable_periodLattice L).preimage_of_injOn (f := (· + c)) (add_left_injective c).injOn`.
-/
lemma countable_add_mem_periodLattice (c : ℂ) : {z : ℂ | z + c ∈ L.lattice}.Countable :=
  (countable_periodLattice L).preimage_of_injOn (f := (· + c)) (add_left_injective c).injOn

/- English proof (translation)
The claim follows from `(L.analyticOnNhd_weierstrassP _ hz).comp (f := (· + c)) (by fun_prop)`.
-/
lemma analyticAt_weierstrassP_add (c : ℂ) {z : ℂ} (hz : z + c ∉ L.lattice) :
    AnalyticAt ℂ (fun t ↦ ℘[L] (t + c)) z :=
  (L.analyticOnNhd_weierstrassP _ hz).comp (f := (· + c)) (by fun_prop)

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Establish `hw' : w + (z - w) ∉ L.lattice` using `by simpa using hz`. Establish `h1` using `eventuallyEq_of_weierstrass_system (weierstrass_system_add_const L 0 (z := w) (by simpa using hw)) (weierstrass_system_add_const L (z - w) hw') (by simp [h]) (by simp [h'])`. Establish `h2` using `eqOn_compl_of_countable ((countable_add_mem_periodLattice L 0).union (countable_add_mem_periodLattice L (z - w))) (fun t ht ↦ analyticAt_weierstrassP_add L 0 fun h ↦ ht (.inl h)) (fun t ht ↦ analyticAt_weierstrassP_add L (z - w) fun h ↦ ht (.inr h)) (z := w) (by rintro (h | h); e …`. Establish `h0 : 0 + (z - w) ∉ L.lattice` using `by simpa using hc`.

Use `not_eventually_weierstrassP_eq L (zero_mem _) (analyticAt_weierstrassP_add L (z - w) h0).continuousAt ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ne_notMem_periodLattice L 0, mem_nhdsWithin_of_mem_nhds ((continuous_add_const (z - w)).continuousAt.eventually (eventually_notMem_periodLattice L h0))] with t h3 h4`. Simplify `h), h4 h])` using `using h2 (x := t) (by rintro (h | h); exacts [h3 (by simpa`.
-/
theorem sub_mem_lattice_of_weierstrassP_eq {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (h : ℘[L] z = ℘[L] w) (h' : ℘'[L] z = ℘'[L] w) : z - w ∈ L.lattice := by
  by_contra hc
  have hw' : w + (z - w) ∉ L.lattice := by simpa using hz
  have h1 := eventuallyEq_of_weierstrass_system
    (weierstrass_system_add_const L 0 (z := w) (by simpa using hw))
    (weierstrass_system_add_const L (z - w) hw') (by simp [h]) (by simp [h'])
  have h2 := eqOn_compl_of_countable
    ((countable_add_mem_periodLattice L 0).union (countable_add_mem_periodLattice L (z - w)))
    (fun t ht ↦ analyticAt_weierstrassP_add L 0 fun h ↦ ht (.inl h))
    (fun t ht ↦ analyticAt_weierstrassP_add L (z - w) fun h ↦ ht (.inr h))
    (z := w) (by rintro (h | h); exacts [hw (by simpa using h), hw' h]) h1
  have h0 : 0 + (z - w) ∉ L.lattice := by simpa using hc
  refine not_eventually_weierstrassP_eq L (zero_mem _)
    (analyticAt_weierstrassP_add L (z - w) h0).continuousAt ?_
  filter_upwards [eventually_ne_notMem_periodLattice L 0, mem_nhdsWithin_of_mem_nhds
    ((continuous_add_const (z - w)).continuousAt.eventually
      (eventually_notMem_periodLattice L h0))] with t h3 h4
  simpa using h2 (x := t) (by rintro (h | h); exacts [h3 (by simpa using h), h4 h])

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : ℘'[L] z ^ 2 = ℘'[L] w ^ 2`. Rewrite using `[L.derivWeierstrassP_sq z hz, L.derivWeierstrassP_sq w hw, h]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h2 | h2` into its components or cases.

Conclude with `.inl (sub_mem_lattice_of_weierstrassP_eq L hz hw h h2)`. Conclude with `.inr (by`. Simplify `hw) (by simpa using h) (by simpa using h2))` using `using sub_mem_lattice_of_weierstrassP_eq L (w := -w) hz (by simpa`. Introduce and unpack `(h | h)`. Rewrite using `[← L.weierstrassP_add_coe w ⟨_, h⟩]`.

Simplify using the standard rewrite rules. Rewrite using `[← L.weierstrassP_neg w, ← L.weierstrassP_add_coe (-w) ⟨_, h⟩]`. Simplify using the standard rewrite rules.
-/
theorem weierstrassP_eq_iff {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice) :
    ℘[L] z = ℘[L] w ↔ z - w ∈ L.lattice ∨ z + w ∈ L.lattice := by
  constructor
  · intro h
    have h1 : ℘'[L] z ^ 2 = ℘'[L] w ^ 2 := by
      rw [L.derivWeierstrassP_sq z hz, L.derivWeierstrassP_sq w hw, h]
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp h1 with h2 | h2
    · exact .inl (sub_mem_lattice_of_weierstrassP_eq L hz hw h h2)
    · exact .inr (by
        simpa using sub_mem_lattice_of_weierstrassP_eq L (w := -w) hz (by simpa using hw)
          (by simpa using h) (by simpa using h2))
  · rintro (h | h)
    · rw [← L.weierstrassP_add_coe w ⟨_, h⟩]; simp
    · rw [← L.weierstrassP_neg w, ← L.weierstrassP_add_coe (-w) ⟨_, h⟩]; simp

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Simplify `hz) (by simp) (by simp [h])` using `using sub_mem_lattice_of_weierstrassP_eq L (w := -z) hz (by simpa`. Introduce `h`. Use `L.derivWeierstrassP_add_coe (-z) ⟨_, h⟩` as an intermediate fact.

Simplify `this` using `[CharZero.eq_neg_self_iff]`.
-/
theorem derivWeierstrassP_eq_zero_iff {z : ℂ} (hz : z ∉ L.lattice) :
    ℘'[L] z = 0 ↔ z + z ∈ L.lattice := by
  constructor
  · intro h
    simpa using sub_mem_lattice_of_weierstrassP_eq L (w := -z) hz (by simpa using hz)
      (by simp) (by simp [h])
  · intro h
    have := L.derivWeierstrassP_add_coe (-z) ⟨_, h⟩
    simpa [CharZero.eq_neg_self_iff] using this

/- English proof (translation)
The claim follows from `hf.apply_eq_apply_of_bounded (IsZLattice.isCompact_range_of_periodic L.lattice _ hf.continuous hp).isBounded z w`.
-/
theorem eq_of_differentiable_of_periodic {f : ℂ → ℂ} (hf : Differentiable ℂ f)
    (hp : ∀ z, ∀ l ∈ L.lattice, f (z + l) = f z) (z w : ℂ) : f z = f w :=
  hf.apply_eq_apply_of_bounded
    (IsZLattice.isCompact_range_of_periodic L.lattice _ hf.continuous hp).isBounded z w

/- English proof (translation)
Use `by_contra! hc`. Set `f : ℂ → ℂ` to `fun z ↦ if z ∈ L.lattice then 0 else (℘[L] z - c)⁻¹`. Establish `hf1 : ∀ z ∉ L.lattice, DifferentiableAt ℂ f z` using `fun z hz ↦ by`. Use `(((hasDerivAt_weierstrassP L hz).differentiableAt.sub_const c).inv (sub_ne_zero.mpr (hc z hz))).congr_of_eventuallyEq ?_` and prove the remaining obligations. Use `filter_upwards [eventually_notMem_periodLattice L hz] with w hw`.

Simplify using `[f, hw]`. Establish `hf : Differentiable ℂ f` using `fun z ↦ by`. Distinguish the cases in `hz : z ∈ L.lattice`. Use `(Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt ((eventually_ne_notMem_periodLattice L z).mono hf1) ?_).differentiableAt` and prove the remaining obligations. Rewrite using `[continuousAt_iff_punctured_nhds, show f z = 0 by simp [f, hz]]`.

Use `(tendsto_inv₀_cobounded.comp ((tendsto_sub_const_cobounded c).comp (tendsto_weierstrassP_cobounded L hz))).congr' ?_` and prove the remaining obligations. Use `filter_upwards [eventually_ne_notMem_periodLattice L z] with w hw`. Simplify using `[f, hw]`. Conclude with `hf1 z hz`. Use `eq_of_differentiable_of_periodic L hf (fun z l hl ↦ by` as an intermediate fact.

Simplify using `only [f, L.weierstrassP_add_coe z ⟨l, hl⟩, (L.lattice.add_mem_iff_left hl)])`. Use the proof step `(L.ω₁ / 2) 0`. Simplify using `[f, L.ω₁_div_two_notMem_lattice, sub_ne_zero.mpr (hc _ L.ω₁_div_two_notMem_lattice)] at this`.
-/
theorem exists_weierstrassP_eq (c : ℂ) : ∃ z ∉ L.lattice, ℘[L] z = c := by
  classical
  by_contra! hc
  let f : ℂ → ℂ := fun z ↦ if z ∈ L.lattice then 0 else (℘[L] z - c)⁻¹
  have hf1 : ∀ z ∉ L.lattice, DifferentiableAt ℂ f z := fun z hz ↦ by
    refine (((hasDerivAt_weierstrassP L hz).differentiableAt.sub_const c).inv
      (sub_ne_zero.mpr (hc z hz))).congr_of_eventuallyEq ?_
    filter_upwards [eventually_notMem_periodLattice L hz] with w hw
    simp [f, hw]
  have hf : Differentiable ℂ f := fun z ↦ by
    by_cases hz : z ∈ L.lattice
    · refine (Complex.analyticAt_of_differentiable_on_punctured_nhds_of_continuousAt
        ((eventually_ne_notMem_periodLattice L z).mono hf1) ?_).differentiableAt
      rw [continuousAt_iff_punctured_nhds, show f z = 0 by simp [f, hz]]
      refine (tendsto_inv₀_cobounded.comp ((tendsto_sub_const_cobounded c).comp
        (tendsto_weierstrassP_cobounded L hz))).congr' ?_
      filter_upwards [eventually_ne_notMem_periodLattice L z] with w hw
      simp [f, hw]
    · exact hf1 z hz
  have := eq_of_differentiable_of_periodic L hf (fun z l hl ↦ by
    simp only [f, L.weierstrassP_add_coe z ⟨l, hl⟩, (L.lattice.add_mem_iff_left hl)])
    (L.ω₁ / 2) 0
  simp [f, L.ω₁_div_two_notMem_lattice, sub_ne_zero.mpr (hc _ L.ω₁_div_two_notMem_lattice)] at this

/- English proof (translation)
Take `⟨z, hz, rfl⟩` from `exists_weierstrassP_eq L x`. Rewrite `h` using `[← L.derivWeierstrassP_sq z hz]`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h` into its components or cases. Conclude with `⟨z, hz, rfl, h.symm⟩`. Conclude with `⟨-z, by simpa using hz, by simp, by simp [h]⟩`.
-/
theorem exists_weierstrassP_eq_and_derivWeierstrassP_eq {x y : ℂ} (h : y ^ 2 = 4 * x ^ 3 - L.g₂ * x - L.g₃) :
    ∃ z ∉ L.lattice, ℘[L] z = x ∧ ℘'[L] z = y := by
  obtain ⟨z, hz, rfl⟩ := exists_weierstrassP_eq L x
  rw [← L.derivWeierstrassP_sq z hz] at h
  rcases sq_eq_sq_iff_eq_or_eq_neg.mp h with h | h
  · exact ⟨z, hz, rfl, h.symm⟩
  · exact ⟨-z, by simpa using hz, by simp, by simp [h]⟩

/- English proof (translation)
Establish `hq : q = y - s * (x - p)` using `by rw [hs]; field_simp; ring`. Use `⟨hq, mul_left_cancel₀ hxp ?_, by linear_combination h⟩` and prove the remaining obligations. Rewrite `h'` using `[hq]`. Take the linear combination `h - h'`.
-/
lemma chord_algebra {x y p q g₂ g₃ s : ℂ} (hxp : x - p ≠ 0) (hs : s = (y - q) / (x - p))
    (h : y ^ 2 = 4 * x ^ 3 - g₂ * x - g₃) (h' : q ^ 2 = 4 * p ^ 3 - g₂ * p - g₃) :
    q = y - s * (x - p) ∧ g₂ = 4 * (x ^ 2 + x * p + p ^ 2) - s * (2 * y - s * (x - p)) ∧
      g₃ = 4 * x ^ 3 - g₂ * x - y ^ 2 := by
  have hq : q = y - s * (x - p) := by rw [hs]; field_simp; ring
  refine ⟨hq, mul_left_cancel₀ hxp ?_, by linear_combination h⟩
  rw [hq] at h'
  linear_combination h - h'

/- English proof (translation)
Use `set p := ℘[L] w with hp`. Use `set q := ℘'[L] w with hq'`. Set `s : ℂ → ℂ` to `fun t ↦ (℘'[L] t - q) / (℘[L] t - p)`. Set `F : ℂ → ℂ` to `fun t ↦ s t ^ 2 / 4 - ℘[L] t - p`. Set `G : ℂ → ℂ` to `fun t ↦ -(s t * (F t - ℘[L] t) + ℘'[L] t)`.

Establish `alg : ∀ t ∉ L.lattice, ℘[L] t - p ≠ 0 → _` using `fun t ht ht' ↦ chord_algebra (s := s t) ht' rfl (L.derivWeierstrassP_sq t ht) (L.derivWeierstrassP_sq w hw)`. Establish `hev : ∀ᶠ t in 𝓝 z, t ∉ L.lattice ∧ ℘[L] t - p ≠ 0` using `(eventually_notMem_periodLattice L hz).and (((hasDerivAt_weierstrassP L hz).continuousAt.sub continuousAt_const).eventually_ne (sub_ne_zero.mpr hne))`. Establish `sys : ∀ᶠ t in 𝓝 z, HasDerivAt F (G t) t ∧ HasDerivAt G (6 * F t ^ 2 - L.g₂ / 2) t` using `by filter_upwards [hev] with t ⟨ht, ht'⟩`. Take `⟨e1, e2, -⟩` from `alg t ht ht'`. Establish `d1` using `hasDerivAt_weierstrassP L ht`.

Establish `d2` using `hasDerivAt_derivWeierstrassP L ht`. Establish `ds : HasDerivAt s (2 * (℘[L] t - F t)) t`. Use `((d2.sub_const q).div (d1.sub_const p) ht').congr_deriv ?_` and prove the remaining obligations. Rewrite using `[div_eq_iff (pow_ne_zero 2 ht'), e2]`. Simplify using `only [F]`.

Take the linear combination `℘'[L] t * e1`. Establish `dF : HasDerivAt F (G t) t`. Use `((((ds.pow 2).div_const 4).sub d1).sub_const p).congr_deriv ?_` and prove the remaining obligations. Simplify using `only [G]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨dF, ?_⟩` and prove the remaining obligations. Use `((ds.mul (dF.sub d1)).add d2).neg.congr_deriv ?_` and prove the remaining obligations. Simplify using `only [G, F, e2, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨u, hu, hu1, hu2⟩` from `exists_weierstrassP_eq_and_derivWeierstrassP_eq L (x := F z) (y := G z) (by`.

Take `⟨-, e2, e3⟩` from `alg z hz (sub_ne_zero.mpr hne)`. Rewrite using `[e3, e2]`. Simplify using `only [G, F]`. Use the proof step `ring)`. Take `⟨c, rfl⟩ : ∃ c, u = z + c` from `⟨u - z, by ring⟩`.

Establish `loc` using `eventuallyEq_of_weierstrass_system (weierstrass_system_add_const L c hu) sys hu1 hu2`. Establish `glob : Set.EqOn (fun t ↦ 4 * (℘[L] (t + c) + ℘[L] t + p) * (℘[L] t - p) ^ 2) (fun t ↦ (℘'[L] t - q) ^ 2) ((L.lattice : Set ℂ) ∪ {t | t + c ∈ L.lattice})ᶜ`. Use `eqOn_compl_of_countable ((countable_periodLattice L).union (countable_add_mem_periodLattice L c)) (fun t ht ↦ ?_) (fun t ht ↦ ?_) (z := z) (by rintro (h | h); exacts [hz h, hu h]) ?_` and prove the remaining obligations. Use `analyticAt_weierstrassP_add L c (z := t) fun h ↦ ht (.inr h)` as an intermediate fact. Use `L.analyticOnNhd_weierstrassP t fun h ↦ ht (.inl h)` as an intermediate fact.

Use `fun_prop`. Use `L.analyticOnNhd_derivWeierstrassP t fun h ↦ ht (.inl h) fun_prop` as an intermediate fact. Use `filter_upwards [loc, hev] with t ht ⟨_, ht'⟩`. Rewrite using `[ht]`. Simplify using `only [F, s]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Establish `hc : -w + c ∈ L.lattice`. Assume the negation of the conclusion as `hc`. Use `glob (x := -w) (by rintro (h | h); exacts [hw (by simpa using h), hc h])` as an intermediate fact.

Simplify using `only [weierstrassP_neg, derivWeierstrassP_neg, ← hp, ← hq'] at this`. Conclude with `hq (pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination -this / 4))`. Establish `e : z + c = z + w + (⟨_, hc⟩ : L.lattice)` using `by simp`. Rewrite `hu1` using `[e, weierstrassP_add_coe]`. Rewrite `hu2` using `[e, derivWeierstrassP_add_coe]`.

Conclude with `⟨hu1, by rw [hu2, hu1]⟩`.
-/
lemma weierstrassP_add_of_ne_of_deriv_ne_zero {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hne : ℘[L] z ≠ ℘[L] w) (hq : ℘'[L] w ≠ 0) :
    ℘[L] (z + w) = ((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w)) ^ 2 / 4 - ℘[L] z - ℘[L] w ∧
    ℘'[L] (z + w) = -((℘'[L] z - ℘'[L] w) / (℘[L] z - ℘[L] w) * (℘[L] (z + w) - ℘[L] z) +
      ℘'[L] z) := by
  set p := ℘[L] w with hp
  set q := ℘'[L] w with hq'
  let s : ℂ → ℂ := fun t ↦ (℘'[L] t - q) / (℘[L] t - p)
  let F : ℂ → ℂ := fun t ↦ s t ^ 2 / 4 - ℘[L] t - p
  let G : ℂ → ℂ := fun t ↦ -(s t * (F t - ℘[L] t) + ℘'[L] t)
  have alg : ∀ t ∉ L.lattice, ℘[L] t - p ≠ 0 → _ := fun t ht ht' ↦
    chord_algebra (s := s t) ht' rfl (L.derivWeierstrassP_sq t ht) (L.derivWeierstrassP_sq w hw)
  have hev : ∀ᶠ t in 𝓝 z, t ∉ L.lattice ∧ ℘[L] t - p ≠ 0 :=
    (eventually_notMem_periodLattice L hz).and
      (((hasDerivAt_weierstrassP L hz).continuousAt.sub continuousAt_const).eventually_ne
        (sub_ne_zero.mpr hne))
  have sys : ∀ᶠ t in 𝓝 z, HasDerivAt F (G t) t ∧ HasDerivAt G (6 * F t ^ 2 - L.g₂ / 2) t := by
    filter_upwards [hev] with t ⟨ht, ht'⟩
    obtain ⟨e1, e2, -⟩ := alg t ht ht'
    have d1 := hasDerivAt_weierstrassP L ht
    have d2 := hasDerivAt_derivWeierstrassP L ht
    have ds : HasDerivAt s (2 * (℘[L] t - F t)) t := by
      refine ((d2.sub_const q).div (d1.sub_const p) ht').congr_deriv ?_
      rw [div_eq_iff (pow_ne_zero 2 ht'), e2]
      simp only [F]
      linear_combination ℘'[L] t * e1
    have dF : HasDerivAt F (G t) t := by
      refine ((((ds.pow 2).div_const 4).sub d1).sub_const p).congr_deriv ?_
      simp only [G]
      ring
    refine ⟨dF, ?_⟩
    refine ((ds.mul (dF.sub d1)).add d2).neg.congr_deriv ?_
    simp only [G, F, e2, Pi.sub_apply]
    ring
  obtain ⟨u, hu, hu1, hu2⟩ := exists_weierstrassP_eq_and_derivWeierstrassP_eq L (x := F z) (y := G z) (by
    obtain ⟨-, e2, e3⟩ := alg z hz (sub_ne_zero.mpr hne)
    rw [e3, e2]
    simp only [G, F]
    ring)
  obtain ⟨c, rfl⟩ : ∃ c, u = z + c := ⟨u - z, by ring⟩
  have loc := eventuallyEq_of_weierstrass_system (weierstrass_system_add_const L c hu) sys hu1 hu2
  have glob : Set.EqOn (fun t ↦ 4 * (℘[L] (t + c) + ℘[L] t + p) * (℘[L] t - p) ^ 2)
      (fun t ↦ (℘'[L] t - q) ^ 2) ((L.lattice : Set ℂ) ∪ {t | t + c ∈ L.lattice})ᶜ := by
    refine eqOn_compl_of_countable
      ((countable_periodLattice L).union (countable_add_mem_periodLattice L c))
      (fun t ht ↦ ?_) (fun t ht ↦ ?_) (z := z) (by rintro (h | h); exacts [hz h, hu h]) ?_
    · have := analyticAt_weierstrassP_add L c (z := t) fun h ↦ ht (.inr h)
      have := L.analyticOnNhd_weierstrassP t fun h ↦ ht (.inl h)
      fun_prop
    · have := L.analyticOnNhd_derivWeierstrassP t fun h ↦ ht (.inl h)
      fun_prop
    · filter_upwards [loc, hev] with t ht ⟨_, ht'⟩
      rw [ht]
      simp only [F, s]
      field_simp
      ring
  have hc : -w + c ∈ L.lattice := by
    by_contra hc
    have := glob (x := -w) (by rintro (h | h); exacts [hw (by simpa using h), hc h])
    simp only [weierstrassP_neg, derivWeierstrassP_neg, ← hp, ← hq'] at this
    exact hq (pow_eq_zero_iff two_ne_zero |>.mp (by linear_combination -this / 4))
  have e : z + c = z + w + (⟨_, hc⟩ : L.lattice) := by simp
  rw [e, weierstrassP_add_coe] at hu1
  rw [e, derivWeierstrassP_add_coe] at hu2
  exact ⟨hu1, by rw [hu2, hu1]⟩

end GlobalTheory
