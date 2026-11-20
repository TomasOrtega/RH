import Mathlib
import Development.AutomorphicSpectrum.Statements.GeometryStatements.IsPolLatticePlane
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.HopfOrderContainsCharacters

open GlobalTheory.CompanionTheory.Ar.BT GlobalTheory.CompanionTheory.Ar.HT

noncomputable section

namespace PositivityTheory.HtPt.Twpair

section Ind

variable {R : Type} [CommRing R] {T : Type} [CommGroup T]

/- English proof (translation)
Establish `key : ∀ g ∈ prodSpan A, (fun h => g (t, h)) ∈ A`. Introduce `g hg`. Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨a, -, b, hb, rfl⟩` from `h`.

Conclude with `A.smul_mem hb (a t)`. Consider the case `zero => exact A.zero_mem`. Consider the case `add x y _ _ hx hy => exact A.add_mem hx hy`. Consider the case `smul r x _ hx => exact A.smul_mem hx r`. Conclude with `key _ (hA.comul f hf)`.
-/
theorem translate_mem {A : Subalgebra R (T → R)} (hA : IsHopfOrder A) {f : T → R} (hf : f ∈ A) (t : T) :
    (fun h => f (t * h)) ∈ A := by
  have key : ∀ g ∈ prodSpan A, (fun h => g (t, h)) ∈ A := by
    intro g hg
    induction hg using Submodule.span_induction with
    | mem x h =>
      obtain ⟨a, -, b, hb, rfl⟩ := h
      exact A.smul_mem hb (a t)
    | zero => exact A.zero_mem
    | add x y _ _ hx hy => exact A.add_mem hx hy
    | smul r x _ hx => exact A.smul_mem hx r
  exact key _ (hA.comul f hf)

omit [CommGroup T] in

/- English proof (translation)
Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨a', ha', b', hb', rfl⟩` from `h`. Use `Submodule.subset_span ⟨a * a', A.mul_mem ha ha', b * b', A.mul_mem hb hb', ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`.

Simplify using `only [Pi.mul_apply]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero`. Use `(prodSpan A).zero_mem` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `z`. Simplify using the standard rewrite rules. Consider the case `add x y _ _ hx hy`. Use `(prodSpan A).add_mem hx hy` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `z`. Simplify using `[mul_add]`. Consider the case `smul r x _ hx`. Use `(prodSpan A).smul_mem r hx` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `z`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mul_mem_prodSpan {A : Subalgebra R (T → R)} {a b : T → R} (ha : a ∈ A) (hb : b ∈ A)
    {g : T × T → R} (hg : g ∈ prodSpan A) : (fun z => a z.1 * b z.2 * g z) ∈ prodSpan A := by
  induction hg using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a', ha', b', hb', rfl⟩ := h
    refine Submodule.subset_span ⟨a * a', A.mul_mem ha ha', b * b', A.mul_mem hb hb', ?_⟩
    funext z
    simp only [Pi.mul_apply]
    ring
  | zero =>
    have := (prodSpan A).zero_mem
    convert this using 1
    funext z
    simp
  | add x y _ _ hx hy =>
    have := (prodSpan A).add_mem hx hy
    convert this using 1
    funext z
    simp [mul_add]
  | smul r x _ hx =>
    have := (prodSpan A).smul_mem r hx
    convert this using 1
    funext z
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

open Classical in

def extZero (H : Subgroup T) (t : T) (a : H → R) : T → R :=
  fun x => if h : t⁻¹ * x ∈ H then a ⟨_, h⟩ else 0

open Classical in

def extZero₂ (H : Subgroup T) (t s : T) (g : H × H → R) : T × T → R :=
  fun z => if h : t⁻¹ * z.1 ∈ H ∧ s⁻¹ * z.2 ∈ H then g (⟨_, h.1⟩, ⟨_, h.2⟩) else 0

/- English proof (translation)
Introduce `u`. Distinguish the cases in `hu : t⁻¹ * u ∈ H`. Use `translate_mem hA ha ⟨_, hu⟩` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `h`.

Establish `h1 : t⁻¹ * (u * H.subtype h) ∈ H`. Rewrite using `[← mul_assoc]`. Conclude with `H.mul_mem hu h.2`. Simplify using `only [extZero]`. Rewrite using `[dif_pos h1]`.

Use `congr 1`. Conclude with `Subtype.ext (mul_assoc _ _ _).symm`. Establish `: (fun h : H => extZero H t a (u * H.subtype h)) = 0`. Use function extensionality and compare the values at `h`. Establish `h1 : ¬ t⁻¹ * (u * H.subtype h) ∈ H`.

Rewrite using `[← mul_assoc]`. Conclude with `fun h1 => hu ((H.mul_mem_cancel_right h.2).1 h1)`. Simplify using `only [extZero]`. Rewrite using `[dif_neg h1]`. Both sides reduce to the same expression.

Rewrite using `[this]`. Conclude with `A.zero_mem`.
-/
theorem extZero_mem {H : Subgroup T} {A : Subalgebra R (H → R)} (hA : IsHopfOrder A) (t : T) {a : H → R}
    (ha : a ∈ A) : extZero H t a ∈ indOrder H.subtype A := by
  intro u
  by_cases hu : t⁻¹ * u ∈ H
  · have := translate_mem hA ha ⟨_, hu⟩
    convert this using 1
    funext h
    have h1 : t⁻¹ * (u * H.subtype h) ∈ H := by
      rw [← mul_assoc]; exact H.mul_mem hu h.2
    simp only [extZero]
    rw [dif_pos h1]
    congr 1
    exact Subtype.ext (mul_assoc _ _ _).symm
  · have : (fun h : H => extZero H t a (u * H.subtype h)) = 0 := by
      funext h
      have h1 : ¬ t⁻¹ * (u * H.subtype h) ∈ H := by
        rw [← mul_assoc]
        exact fun h1 => hu ((H.mul_mem_cancel_right h.2).1 h1)
      simp only [extZero]
      rw [dif_neg h1]
      rfl
    rw [this]
    exact A.zero_mem

/- English proof (translation)
Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem x h`. Take `⟨a, ha, b, hb, rfl⟩` from `h`. Use `Submodule.subset_span ⟨_, extZero_mem hA t ha, _, extZero_mem hA s hb, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `z`.

Apply the tactic sequence `by_cases h1 : t⁻¹ * z.1 ∈ H <;> by_cases h2 : s⁻¹ * z.2 ∈ H <;> simp [extZero, extZero₂, h1, h2]`. Consider the case `zero`. Establish `: extZero₂ H t s (0 : H × H → R) = 0`. Use function extensionality and compare the values at `z`. Simplify using `[extZero₂]`.

Rewrite using `[this]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy`. Use `Submodule.add_mem _ hx hy` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `z`. Simplify using `only [extZero₂, Pi.add_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Consider the case `smul r x _ hx`. Use `Submodule.smul_mem _ r hx` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`. Simplify using `only [extZero₂, Pi.smul_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem extZero₂_mem {H : Subgroup T} {A : Subalgebra R (H → R)} (hA : IsHopfOrder A) (t s : T)
    {g : H × H → R} (hg : g ∈ prodSpan A) : extZero₂ H t s g ∈ prodSpan (indOrder H.subtype A) := by
  induction hg using Submodule.span_induction with
  | mem x h =>
    obtain ⟨a, ha, b, hb, rfl⟩ := h
    refine Submodule.subset_span ⟨_, extZero_mem hA t ha, _, extZero_mem hA s hb, ?_⟩
    funext z
    by_cases h1 : t⁻¹ * z.1 ∈ H <;> by_cases h2 : s⁻¹ * z.2 ∈ H <;> simp [extZero, extZero₂, h1, h2]
  | zero =>
    have : extZero₂ H t s (0 : H × H → R) = 0 := by
      funext z
      simp [extZero₂]
    rw [this]
    exact Submodule.zero_mem _
  | add x y _ _ hx hy =>
    have := Submodule.add_mem _ hx hy
    convert this using 1
    funext z
    simp only [extZero₂, Pi.add_apply]
    split_ifs <;> simp
  | smul r x _ hx =>
    have := Submodule.smul_mem _ r hx
    convert this using 1
    funext z
    simp only [extZero₂, Pi.smul_apply]
    split_ifs <;> simp

/- English proof (translation)
Introduce `R _ _ _ T _ _ H A β hA hβ`. Use `Fintype.ofFinite (T ⧸ H)` as an intermediate fact. Establish `h1 : ∀ t s : T, (fun w : H × H => ((β (t * w.1) (s * w.2) : Rˣ) : R)) ∈ prodSpan A`. Introduce `t s`. Establish `ha` using `char_mem_hopfOrder R H A hA ((β.flip s).comp H.subtype)`.

Establish `hb` using `char_mem_hopfOrder R H A hA ((β t).comp H.subtype)`. Use `Submodule.smul_mem _ ((β t s : Rˣ) : R) (mul_mem_prodSpan ha hb hβ)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `w`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Establish `key : ∀ (c : T ⧸ H) (x : T), c.out⁻¹ * x ∈ H ↔ c = (x : T ⧸ H)`. Introduce `c x`. Rewrite using `[← QuotientGroup.eq, QuotientGroup.out_eq']`. Establish `e : (fun z : T × T => ((β z.1 z.2 : Rˣ) : R)) = ∑ c : (T ⧸ H) × (T ⧸ H), extZero₂ H c.1.out c.2.out (fun w : H × H => ((β (c.1.out * w.1) (c.2.out * w.2) : Rˣ) : R))`.

Use function extensionality and compare the values at `z`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single ((z.1 : T ⧸ H), (z.2 : T ⧸ H))]`. Simplify using `only [extZero₂]`. Rewrite using `[dif_pos ⟨(key _ _).2 rfl, (key _ _).2 rfl⟩]`. Simplify using `only [mul_inv_cancel_left]`.

Introduce `c _ hc`. Simplify using `only [extZero₂]`. Rewrite using `[dif_neg]`. Introduce and unpack `⟨a, b⟩`. Conclude with `hc (Prod.ext ((key _ _).1 a) ((key _ _).1 b))`.

Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `Submodule.sum_mem _ fun c _ => extZero₂_mem hA _ _ (h1 _ _)`.
-/
theorem pair_ind : ∀ (R : Type) [CommRing R] [IsDomain R] [IsIntegrallyClosed R] (T : Type) [CommGroup T] [Finite T] (H : Subgroup T) (A : Subalgebra R (H → R)) (β : T →* T →* Rˣ), IsHopfOrder A → (fun z : H × H => ((β z.1 z.2 : Rˣ) : R)) ∈ prodSpan A → (fun z : T × T => ((β z.1 z.2 : Rˣ) : R)) ∈ prodSpan (indOrder H.subtype A) := by
  intro R _ _ _ T _ _ H A β hA hβ
  classical
  have := Fintype.ofFinite (T ⧸ H)
  have h1 : ∀ t s : T, (fun w : H × H => ((β (t * w.1) (s * w.2) : Rˣ) : R)) ∈ prodSpan A := by
    intro t s
    have ha := char_mem_hopfOrder R H A hA ((β.flip s).comp H.subtype)
    have hb := char_mem_hopfOrder R H A hA ((β t).comp H.subtype)
    have := Submodule.smul_mem _ ((β t s : Rˣ) : R) (mul_mem_prodSpan ha hb hβ)
    convert this using 1
    funext w
    simp
    ring
  have key : ∀ (c : T ⧸ H) (x : T), c.out⁻¹ * x ∈ H ↔ c = (x : T ⧸ H) := by
    intro c x
    rw [← QuotientGroup.eq, QuotientGroup.out_eq']
  have e : (fun z : T × T => ((β z.1 z.2 : Rˣ) : R)) = ∑ c : (T ⧸ H) × (T ⧸ H),
      extZero₂ H c.1.out c.2.out (fun w : H × H => ((β (c.1.out * w.1) (c.2.out * w.2) : Rˣ) : R)) := by
    funext z
    rw [Finset.sum_apply, Finset.sum_eq_single ((z.1 : T ⧸ H), (z.2 : T ⧸ H))]
    · simp only [extZero₂]
      rw [dif_pos ⟨(key _ _).2 rfl, (key _ _).2 rfl⟩]
      simp only [mul_inv_cancel_left]
    · intro c _ hc
      simp only [extZero₂]
      rw [dif_neg]
      rintro ⟨a, b⟩
      exact hc (Prod.ext ((key _ _).1 a) ((key _ _).1 b))
    · simp
  rw [e]
  exact Submodule.sum_mem _ fun c _ => extZero₂_mem hA _ _ (h1 _ _)

end Ind

section Val

variable {C : Type} [Field C] {v : Valuation C NNReal} {O : Type} [CommRing O] [Algebra O C]

/- English proof (translation)
Rewrite using `[IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]`. Conclude with `⟨fun h => lt_of_le_of_ne (hv.map_le_one x) h, fun h => h.ne⟩`.
-/
theorem mem_maximalIdeal_iff [IsLocalRing O] (hv : v.Integers O) (x : O) :
    x ∈ IsLocalRing.maximalIdeal O ↔ v (algebraMap O C x) < 1 := by
  rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, hv.isUnit_iff_valuation_eq_one]
  exact ⟨fun h => lt_of_le_of_ne (hv.map_le_one x) h, fun h => h.ne⟩

/- English proof (translation)
Distinguish the cases in `h : P = ⊥`. Conclude with `Or.inl h`. Use `right`. Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot h`. Use `le_antisymm (IsLocalRing.le_maximalIdeal hP.ne_top) fun y hy => ?_` and prove the remaining obligations.

Rewrite `hy` using `[mem_maximalIdeal_iff hv]`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one (hv.valuation_pos_iff_ne_zero.2 hx0) hy`. Establish `: x ∣ y ^ n` using `hv.dvd_of_le (by rw [map_pow, map_pow]; exact hn.le)`. Conclude with `hP.mem_of_pow_mem n (Ideal.mem_of_dvd P this hx)`.
-/
theorem prime_eq_bot_or_maximal [IsLocalRing O] (hv : v.Integers O) (P : Ideal O) [hP : P.IsPrime] :
    P = ⊥ ∨ P = IsLocalRing.maximalIdeal O := by
  by_cases h : P = ⊥
  · exact Or.inl h
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot h
  refine le_antisymm (IsLocalRing.le_maximalIdeal hP.ne_top) fun y hy => ?_
  rw [mem_maximalIdeal_iff hv] at hy
  obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (hv.valuation_pos_iff_ne_zero.2 hx0) hy
  have : x ∣ y ^ n := hv.dvd_of_le (by rw [map_pow, map_pow]; exact hn.le)
  exact hP.mem_of_pow_mem n (Ideal.mem_of_dvd P this hx)

/- English proof (translation)
Rewrite `h₀` using `[mem_maximalIdeal_iff hv]`. Establish `hm : (f.map (algebraMap O C)).Monic` using `hf.map _`. Establish `e` using `(IsAlgClosed.splits (f.map (algebraMap O C))).eval_eq_prod_roots_of_monic hm (algebraMap O C a₀)`. Rewrite `e` using `[Polynomial.eval_map_algebraMap, Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval]`. Establish `: ∃ r ∈ (f.map (algebraMap O C)).roots, v (algebraMap O C a₀ - r) < 1`.

Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Rewrite `h₀` using `[e, map_multiset_prod]`. Use `absurd h₀ (not_lt.2 (Multiset.one_le_prod_of_one_le fun x hx => ?_))` and prove the remaining obligations. Simplify using `only [Multiset.map_map, Multiset.mem_map] at hx`.

Take `⟨r, hr, rfl⟩` from `hx`. Conclude with `hne r hr`. Take `⟨r, hr, hlt⟩` from `this`. Establish `hr1 : v r ≤ 1`. Establish `: r = algebraMap O C a₀ - (algebraMap O C a₀ - r)` using `by ring`.

Rewrite using `[this]`. Conclude with `v.map_sub_le (hv.map_le_one _) hlt.le`. Take `⟨a, rfl⟩` from `hv.exists_of_le_one hr1`. Use `⟨a, ?_, ?_⟩` and prove the remaining obligations. Use `(Polynomial.mem_roots hm.ne_zero).1 hr` as an intermediate fact.

Conclude with `(Polynomial.isRoot_map_iff hv.hom_inj).1 this`. Rewrite using `[mem_maximalIdeal_iff hv, map_sub, Valuation.map_sub_swap]`. Conclude with `hlt`.
-/
theorem henselian [IsAlgClosed C] [IsLocalRing O] (hv : v.Integers O) : HenselianLocalRing O where
  is_henselian f hf a₀ h₀ _ := by
    rw [mem_maximalIdeal_iff hv] at h₀
    have hm : (f.map (algebraMap O C)).Monic := hf.map _
    have e := (IsAlgClosed.splits (f.map (algebraMap O C))).eval_eq_prod_roots_of_monic hm (algebraMap O C a₀)
    rw [Polynomial.eval_map_algebraMap, Polynomial.aeval_algebraMap_apply, Polynomial.coe_aeval_eq_eval] at e
    have : ∃ r ∈ (f.map (algebraMap O C)).roots, v (algebraMap O C a₀ - r) < 1 := by
      by_contra hne
      push Not at hne
      rw [e, map_multiset_prod] at h₀
      refine absurd h₀ (not_lt.2 (Multiset.one_le_prod_of_one_le fun x hx => ?_))
      simp only [Multiset.map_map, Multiset.mem_map] at hx
      obtain ⟨r, hr, rfl⟩ := hx
      exact hne r hr
    obtain ⟨r, hr, hlt⟩ := this
    have hr1 : v r ≤ 1 := by
      have : r = algebraMap O C a₀ - (algebraMap O C a₀ - r) := by ring
      rw [this]
      exact v.map_sub_le (hv.map_le_one _) hlt.le
    obtain ⟨a, rfl⟩ := hv.exists_of_le_one hr1
    refine ⟨a, ?_, ?_⟩
    · have := (Polynomial.mem_roots hm.ne_zero).1 hr
      exact (Polynomial.isRoot_map_iff hv.hom_inj).1 this
    · rw [mem_maximalIdeal_iff hv, map_sub, Valuation.map_sub_swap]
      exact hlt

end Val

section Lev

variable {La : Type} [AddCommGroup La]

/- English proof (translation)
Introduce `t` and use `by obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ t.toAdd exact ⟨a, congrArg Multiplicative.ofAdd ha⟩`.
-/
theorem lev_surjective (p n : ℕ) : Function.Surjective (lev p n : La → LevGrp La p n) := fun t => by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ t.toAdd
  exact ⟨a, congrArg Multiplicative.ofAdd ha⟩

/- English proof (translation)
Establish `: Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La)))`. Use `Module.finite_of_fg_torsion _ fun x => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Use `⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Submodule.Quotient.mk (((p ^ n : ℕ) : ℤ) • a) = 0`.

Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨a, by simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]⟩`. Use `infer_instance`.
-/
theorem finite_levGrp [Module.Finite ℤ La] {p : ℕ} (hp : p ≠ 0) (n : ℕ) : Finite (LevGrp La p n) := by
  have : Finite (La ⧸ LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))) := by
    refine Module.finite_of_fg_torsion _ fun x => ?_
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    refine ⟨⟨((p ^ n : ℕ) : ℤ), mem_nonZeroDivisors_of_ne_zero (by positivity)⟩, ?_⟩
    change Submodule.Quotient.mk (((p ^ n : ℕ) : ℤ) • a) = 0
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨a, by simp only [LinearMap.smul_apply, LinearMap.id_apply, natCast_zsmul]⟩
  infer_instance

/- English proof (translation)
Set `N` to `LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))`. Set `z : ℤ →ₗ[ℤ] Additive Oˣ` to `LinearMap.toSpanSingleton ℤ _ (Additive.ofMul ζ)`. Establish `hz : ∀ k : ℤ, z ((p ^ n) • k) = 0`. Introduce `k`. Rewrite using `[map_nsmul, LinearMap.toSpanSingleton_apply, smul_comm, ← ofMul_pow, hζ]`.

Simplify using the standard rewrite rules. Set `B' : La →ₗ[ℤ] La →ₗ[ℤ] Additive Oˣ` to `B.compr₂ z`. Set `B'' : (La ⧸ N) →ₗ[ℤ] (La ⧸ N) →ₗ[ℤ] Additive Oˣ` to `B'.liftQ₂ N N (by`. Introduce and unpack `_ ⟨a, rfl⟩`. Rewrite using `[LinearMap.mem_ker]`.

Use extensionality with `b`. Simplify using `only [B', LinearMap.smul_apply, LinearMap.id_apply, LinearMap.compr₂_apply, map_nsmul, LinearMap.zero_apply]`. Rewrite using `[← map_nsmul, hz])`. Use the proof step `(by`. Introduce and unpack `_ ⟨a, rfl⟩`.

Rewrite using `[LinearMap.mem_ker]`. Use extensionality with `b`. Simplify using `only [B', LinearMap.smul_apply, LinearMap.id_apply, LinearMap.compr₂_apply, map_nsmul, LinearMap.zero_apply, LinearMap.flip_apply]`. Rewrite using `[← map_nsmul, hz])`. Use `⟨{ toFun := fun x => { toFun := fun y => (B'' x.toAdd y.toAdd).toMul map_one' := by simp map_mul' := by simp } map_one' := by ext; simp map_mul' := by intros; ext; simp }, fun a b => ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(z (B a b)).toMul = _`. Rewrite using `[LinearMap.toSpanSingleton_apply, ← ofMul_zpow]`. Both sides reduce to the same expression.
-/
theorem exists_bichar {O : Type} [CommRing O] (p n : ℕ) (B : La →ₗ[ℤ] La →ₗ[ℤ] ℤ) (ζ : Oˣ) (hζ : ζ ^ p ^ n = 1) :
    ∃ β : LevGrp La p n →* LevGrp La p n →* Oˣ, ∀ a b, β (lev p n a) (lev p n b) = ζ ^ B a b := by
  let N := LinearMap.range ((p ^ n) • (LinearMap.id : La →ₗ[ℤ] La))
  let z : ℤ →ₗ[ℤ] Additive Oˣ := LinearMap.toSpanSingleton ℤ _ (Additive.ofMul ζ)
  have hz : ∀ k : ℤ, z ((p ^ n) • k) = 0 := by
    intro k
    rw [map_nsmul, LinearMap.toSpanSingleton_apply, smul_comm, ← ofMul_pow, hζ]
    simp
  let B' : La →ₗ[ℤ] La →ₗ[ℤ] Additive Oˣ := B.compr₂ z
  let B'' : (La ⧸ N) →ₗ[ℤ] (La ⧸ N) →ₗ[ℤ] Additive Oˣ := B'.liftQ₂ N N
    (by
      rintro _ ⟨a, rfl⟩
      rw [LinearMap.mem_ker]
      ext b
      simp only [B', LinearMap.smul_apply, LinearMap.id_apply, LinearMap.compr₂_apply, map_nsmul,
        LinearMap.zero_apply]
      rw [← map_nsmul, hz])
    (by
      rintro _ ⟨a, rfl⟩
      rw [LinearMap.mem_ker]
      ext b
      simp only [B', LinearMap.smul_apply, LinearMap.id_apply, LinearMap.compr₂_apply, map_nsmul,
        LinearMap.zero_apply, LinearMap.flip_apply]
      rw [← map_nsmul, hz])
  refine ⟨{ toFun := fun x => { toFun := fun y => (B'' x.toAdd y.toAdd).toMul
                                map_one' := by simp
                                map_mul' := by simp }
            map_one' := by ext; simp
            map_mul' := by intros; ext; simp }, fun a b => ?_⟩
  change (z (B a b)).toMul = _
  rw [LinearMap.toSpanSingleton_apply, ← ofMul_zpow]
  rfl

end Lev

end PositivityTheory.HtPt.Twpair
