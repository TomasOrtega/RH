import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LocalLengthAdditivityTorsionFree

namespace ReciprocityTheory.ChartRestriction.G.AI

universe u

/- English proof (translation)
The claim follows from `((f.quotKerEquivOfSurjective hf).symm.trans ((Submodule.quotEquivOfEq _ _ h).trans (g.quotKerEquivOfSurjective hg))).length_eq`.
-/
theorem length_eq_of_surj_of_ker_eq {A C M N : Type*} [CommRing A] [AddCommGroup C] [Module A C]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] (f : C →ₗ[A] M) (g : C →ₗ[A] N)
    (hf : Function.Surjective f) (hg : Function.Surjective g)
    (h : LinearMap.ker f = LinearMap.ker g) : Module.length A M = Module.length A N := ((f.quotKerEquivOfSurjective hf).symm.trans ((Submodule.quotEquivOfEq _ _ h).trans
      (g.quotKerEquivOfSurjective hg))).length_eq

/- English proof (translation)
Rewrite using `[LinearMap.mem_ker, LinearMap.lsmul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]`. Both sides reduce to the same expression.
-/
theorem mem_ker_lsmul_mk {A : Type u} [CommRing A] (a b x : A) :
    Ideal.Quotient.mk (Ideal.span {a}) x ∈
        LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) ↔ ∃ y, b * x = a * y := by
  rw [LinearMap.mem_ker, LinearMap.lsmul_apply, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
    ← map_mul, Ideal.Quotient.eq_zero_iff_mem, Ideal.mem_span_singleton]
  rfl

/- English proof (translation)
Use `set S : Submodule A (A × A) := LinearMap.ker (b • LinearMap.fst A A A - a • LinearMap.snd A A A) with hSdef`. Establish `hS : ∀ p : A × A, p ∈ S ↔ b * p.1 = a * p.2`. Introduce `p`. Rewrite using `[hSdef, LinearMap.mem_ker]`. Simplify using `[sub_eq_zero]`.

Establish `hf0 : ∀ p : S, (Ideal.span {a}).mkQ (p : A × A).1 ∈ LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)`. Introduce `p`. Conclude with `(mem_ker_lsmul_mk a b _).mpr ⟨_, (hS _).mp p.2⟩`. Establish `hg0 : ∀ p : S, (Ideal.span {b}).mkQ (p : A × A).2 ∈ LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)`. Introduce `p`.

Conclude with `(mem_ker_lsmul_mk b a _).mpr ⟨(p : A × A).1, ((hS _).mp p.2).symm⟩`. Set `f` to `LinearMap.codRestrict _ ((Ideal.span {a}).mkQ ∘ₗ LinearMap.fst A A A ∘ₗ S.subtype) hf0`. Set `g` to `LinearMap.codRestrict _ ((Ideal.span {b}).mkQ ∘ₗ LinearMap.snd A A A ∘ₗ S.subtype) hg0`. Apply `length_eq_of_surj_of_ker_eq f g` to reduce the goal to its premises. Introduce and unpack `⟨k, hk⟩`.

Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective k`. Take `⟨y, hy⟩` from `(mem_ker_lsmul_mk a b x).mp hk`. Conclude with `⟨⟨(x, y), (hS _).mpr hy⟩, rfl⟩`. Introduce and unpack `⟨k, hk⟩`. Take `⟨y, rfl⟩` from `Ideal.Quotient.mk_surjective k`.

Take `⟨x, hx⟩` from `(mem_ker_lsmul_mk b a y).mp hk`. Conclude with `⟨⟨(x, y), (hS _).mpr hx.symm⟩, rfl⟩`. Use extensionality with `⟨⟨x, y⟩, hp⟩`. Establish `hp'` using `(hS _).mp hp`. Rewrite using `[LinearMap.mem_ker, LinearMap.mem_ker, ← Submodule.coe_eq_zero, ← Submodule.coe_eq_zero]`.

Use `show (Ideal.span {a}).mkQ x = 0 ↔ (Ideal.span {b}).mkQ y = 0`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton, Ideal.mem_span_singleton]`. Simplify using `only at hp'`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, rfl⟩`.

Use `⟨z, ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ ha` to reduce the goal to its premises. Rewrite using `[← hp']`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨w, rfl⟩`.

Use `⟨w, ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hb` to reduce the goal to its premises. Rewrite using `[hp']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem length_ker_swap {A : Type u} [CommRing A] [IsDomain A] (a b : A) (ha : a ≠ 0) (hb : b ≠ 0) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) =
      Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a)) := by
  set S : Submodule A (A × A) :=
    LinearMap.ker (b • LinearMap.fst A A A - a • LinearMap.snd A A A) with hSdef
  have hS : ∀ p : A × A, p ∈ S ↔ b * p.1 = a * p.2 := by
    intro p
    rw [hSdef, LinearMap.mem_ker]
    simp [sub_eq_zero]
  have hf0 : ∀ p : S, (Ideal.span {a}).mkQ (p : A × A).1 ∈
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b) := by
    intro p
    exact (mem_ker_lsmul_mk a b _).mpr ⟨_, (hS _).mp p.2⟩
  have hg0 : ∀ p : S, (Ideal.span {b}).mkQ (p : A × A).2 ∈
      LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {b}) a) := by
    intro p
    exact (mem_ker_lsmul_mk b a _).mpr ⟨(p : A × A).1, ((hS _).mp p.2).symm⟩
  let f := LinearMap.codRestrict _
    ((Ideal.span {a}).mkQ ∘ₗ LinearMap.fst A A A ∘ₗ S.subtype) hf0
  let g := LinearMap.codRestrict _
    ((Ideal.span {b}).mkQ ∘ₗ LinearMap.snd A A A ∘ₗ S.subtype) hg0
  apply length_eq_of_surj_of_ker_eq f g
  · rintro ⟨k, hk⟩
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective k
    obtain ⟨y, hy⟩ := (mem_ker_lsmul_mk a b x).mp hk
    exact ⟨⟨(x, y), (hS _).mpr hy⟩, rfl⟩
  · rintro ⟨k, hk⟩
    obtain ⟨y, rfl⟩ := Ideal.Quotient.mk_surjective k
    obtain ⟨x, hx⟩ := (mem_ker_lsmul_mk b a y).mp hk
    exact ⟨⟨(x, y), (hS _).mpr hx.symm⟩, rfl⟩
  · ext ⟨⟨x, y⟩, hp⟩
    have hp' := (hS _).mp hp
    rw [LinearMap.mem_ker, LinearMap.mem_ker, ← Submodule.coe_eq_zero, ← Submodule.coe_eq_zero]
    show (Ideal.span {a}).mkQ x = 0 ↔ (Ideal.span {b}).mkQ y = 0
    rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero,
      Submodule.Quotient.mk_eq_zero, Ideal.mem_span_singleton, Ideal.mem_span_singleton]
    simp only at hp'
    constructor
    · rintro ⟨z, rfl⟩
      refine ⟨z, ?_⟩
      apply mul_left_cancel₀ ha
      rw [← hp']
      ring
    · rintro ⟨w, rfl⟩
      refine ⟨w, ?_⟩
      apply mul_left_cancel₀ hb
      rw [hp']
      ring

/- English proof (translation)
Rewrite `hfin`, the goal using `[Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian]`. Take `⟨hN, hA⟩` from `hfin`. Take `⟨n, s, hs⟩` from `Module.Finite.exists_fin (R := A) (M := N)`. Set `φ : Fin n → (A ⧸ I) →ₗ[A] N` to `fun i => Submodule.liftQ I (LinearMap.toSpanSingleton A N (s i)) (by`. Introduce `r hr`.

Rewrite using `[LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]`. Conclude with `hI r hr (s i))`. Set `Φ : (Fin n → A ⧸ I) →ₗ[A] N` to `∑ i, (φ i).comp (LinearMap.proj i)`. Establish `hΦ : Function.Surjective Φ`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Use `⟨Pi.single i (Submodule.Quotient.mk 1), ?_⟩` and prove the remaining obligations. Simplify using `only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]`. Rewrite using `[Finset.sum_eq_single i]`. Rewrite using `[Pi.single_eq_same]`.

Simplify using `only [φ, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]`. Introduce `j _ hj`. Simplify using `[Pi.single_eq_of_ne hj]`. Simplify using the standard rewrite rules. Conclude with `⟨isNoetherian_of_surjective Φ (LinearMap.range_eq_top.mpr hΦ), isArtinian_of_surjective _ Φ hΦ⟩`.
-/
theorem length_ne_top_of_killed {A N : Type*} [CommRing A] [AddCommGroup N] [Module A N]
    [Module.Finite A N] (I : Ideal A) (hI : ∀ r ∈ I, ∀ x : N, r • x = 0)
    (hfin : Module.length A (A ⧸ I) ≠ ⊤) : Module.length A N ≠ ⊤ := by
  rw [Module.length_ne_top_iff, isFiniteLength_iff_isNoetherian_isArtinian] at hfin ⊢
  obtain ⟨hN, hA⟩ := hfin
  obtain ⟨n, s, hs⟩ := Module.Finite.exists_fin (R := A) (M := N)
  let φ : Fin n → (A ⧸ I) →ₗ[A] N := fun i =>
    Submodule.liftQ I (LinearMap.toSpanSingleton A N (s i)) (by
      intro r hr
      rw [LinearMap.mem_ker, LinearMap.toSpanSingleton_apply]
      exact hI r hr (s i))
  let Φ : (Fin n → A ⧸ I) →ₗ[A] N := ∑ i, (φ i).comp (LinearMap.proj i)
  have hΦ : Function.Surjective Φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hs, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    refine ⟨Pi.single i (Submodule.Quotient.mk 1), ?_⟩
    simp only [Φ, LinearMap.sum_apply, LinearMap.comp_apply, LinearMap.proj_apply]
    rw [Finset.sum_eq_single i]
    · rw [Pi.single_eq_same]
      simp only [φ, Submodule.liftQ_apply, LinearMap.toSpanSingleton_apply, one_smul]
    · intro j _ hj
      simp [Pi.single_eq_of_ne hj]
    · simp
  exact ⟨isNoetherian_of_surjective Φ (LinearMap.range_eq_top.mpr hΦ),
    isArtinian_of_surjective _ Φ hΦ⟩

/- English proof (translation)
Apply `length_ne_top_of_killed (Ideal.span {a, b}) _ hfin` to reduce the goal to its premises. Introduce and unpack `r hr ⟨k, hk⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Submodule.coe_smul, Submodule.coe_zero]`. Take `⟨u, v, rfl⟩` from `Ideal.mem_span_pair.mp hr`.

Establish `hbk : b • k = 0` using `by simpa using hk`. Establish `hak : a • k = 0`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective k`. Rewrite using `[Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)`.

Rewrite using `[add_smul, mul_smul, mul_smul, hak, hbk, smul_zero, smul_zero, add_zero]`.
-/
theorem length_ker_ne_top {A : Type u} [CommRing A] [IsDomain A] [IsNoetherianRing A] (a b : A)
    (ha : a ≠ 0) (hb : b ≠ 0) (hfin : Module.length A (A ⧸ Ideal.span {a, b}) ≠ ⊤) :
    Module.length A (LinearMap.ker (LinearMap.lsmul A (A ⧸ Ideal.span {a}) b)) ≠ ⊤ := by
  apply length_ne_top_of_killed (Ideal.span {a, b}) _ hfin
  rintro r hr ⟨k, hk⟩
  apply Subtype.ext
  simp only [Submodule.coe_smul, Submodule.coe_zero]
  obtain ⟨u, v, rfl⟩ := Ideal.mem_span_pair.mp hr
  have hbk : b • k = 0 := by simpa using hk
  have hak : a • k = 0 := by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective k
    rw [Algebra.smul_def, Ideal.Quotient.algebraMap_eq, ← map_mul, Ideal.Quotient.eq_zero_iff_mem]
    exact Ideal.mul_mem_right _ _ (Ideal.mem_span_singleton_self a)
  rw [add_smul, mul_smul, mul_smul, hak, hbk, smul_zero, smul_zero, add_zero]

end ReciprocityTheory.ChartRestriction.G.AI
