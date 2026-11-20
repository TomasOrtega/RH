import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.LengthCommensurableMapIffOfInjective
universe u_1 u_2

namespace GlobalTheory.LengthCokernelInjective

variable {R : Type*} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj, IsDiscreteValuationRing.addVal_mul, ih]`.
-/
theorem addVal_finset_prod {ι : Type*} (s : Finset ι) (a : ι → R) :
    IsDiscreteValuationRing.addVal R (∏ i ∈ s, a i) =
      ∑ i ∈ s, IsDiscreteValuationRing.addVal R (a i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj, IsDiscreteValuationRing.addVal_mul, ih]

/- English proof (translation)
Establish `h : Ring.ord R (0 : R) = ⊤` using `by rw [Ring.ord_eq_addVal]; simp`. Establish `h2 : Ring.ord R (0 : R) ≤ Module.length R R` using `Module.length_le_of_surjective (Ideal.span {(0 : R)}).mkQ (Submodule.mkQ_surjective _)`. Rewrite `h2` using `[h]`. Conclude with `top_le_iff.mp h2`.
-/
theorem length_self_eq_top : Module.length R R = ⊤ := by
  have h : Ring.ord R (0 : R) = ⊤ := by rw [Ring.ord_eq_addVal]; simp
  have h2 : Ring.ord R (0 : R) ≤ Module.length R R :=
    Module.length_le_of_surjective (Ideal.span {(0 : R)}).mkQ (Submodule.mkQ_surjective _)
  rw [h] at h2
  exact top_le_iff.mp h2

variable {M : Type*} [AddCommGroup M] [Module R M] [Module.Free R M] [Module.Finite R M]

/- English proof (translation)
Set `b` to `Module.Free.chooseBasis R M`. Establish `h : Module.finrank R (LinearMap.range f) = Module.finrank R M` using `LinearMap.finrank_range_of_inj hf`. Set `a` to `Submodule.smithNormalFormCoeffs b h`. Set `t` to `Submodule.smithNormalFormTopBasis b h`. Set `s` to `Submodule.smithNormalFormBotBasis b h`.

Establish `hs : ∀ i, (s i : M) = a i • t i` using `Submodule.smithNormalFormBotBasis_def b h`. Establish `h1 : Associated (LinearMap.det ((LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap)) (LinearMap.det ((LinearMap.range f).subtype ∘ₗ (t.equiv s (Equiv.refl _)).toLinearMap))` using `LinearMap.associated_det_comp_equiv _ _ _`. Establish `h2 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap = f`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Establish `h3 : (LinearMap.range f).subtype ∘ₗ (t.equiv s (Equiv.refl _)).toLinearMap = Matrix.toLin t t (Matrix.diagonal a)`. Use `t.ext fun i => ?_` and prove the remaining obligations. Simplify using `[hs, Matrix.diagonal_apply, Finset.sum_ite_eq']`. Rewrite `h1` using `[h2, h3, LinearMap.det_toLin, Matrix.det_diagonal]`. Rewrite using `[(IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr h1, addVal_finset_prod, (Submodule.quotientEquivPiSpan (LinearMap.range f) b h).length_eq, Module.length_pi_of_fintype]`.

Conclude with `Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (a i)`.
-/
theorem length_coker_of_injective (f : M →ₗ[R] M) (hf : Function.Injective f) :
    Module.length R (M ⧸ LinearMap.range f) =
      IsDiscreteValuationRing.addVal R (LinearMap.det f) := by
  classical
  let b := Module.Free.chooseBasis R M
  have h : Module.finrank R (LinearMap.range f) = Module.finrank R M :=
    LinearMap.finrank_range_of_inj hf
  let a := Submodule.smithNormalFormCoeffs b h
  let t := Submodule.smithNormalFormTopBasis b h
  let s := Submodule.smithNormalFormBotBasis b h
  have hs : ∀ i, (s i : M) = a i • t i := Submodule.smithNormalFormBotBasis_def b h
  have h1 : Associated
      (LinearMap.det ((LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap))
      (LinearMap.det ((LinearMap.range f).subtype ∘ₗ (t.equiv s (Equiv.refl _)).toLinearMap)) :=
    LinearMap.associated_det_comp_equiv _ _ _
  have h2 : (LinearMap.range f).subtype ∘ₗ (LinearEquiv.ofInjective f hf).toLinearMap = f := by
    ext x
    simp
  have h3 : (LinearMap.range f).subtype ∘ₗ (t.equiv s (Equiv.refl _)).toLinearMap =
      Matrix.toLin t t (Matrix.diagonal a) := by
    refine t.ext fun i => ?_
    simp [hs, Matrix.diagonal_apply, Finset.sum_ite_eq']
  rw [h2, h3, LinearMap.det_toLin, Matrix.det_diagonal] at h1
  rw [(IsDiscreteValuationRing.addVal_eq_iff_associated _ _).mpr h1, addVal_finset_prod,
    (Submodule.quotientEquivPiSpan (LinearMap.range f) b h).length_eq,
    Module.length_pi_of_fintype]
  exact Finset.sum_congr rfl fun i _ => Ring.ord_eq_addVal (a i)

/- English proof (translation)
Establish `h1 : Module.finrank R (LinearMap.ker f) ≠ 0`. Rewrite using `[ne_eq, Submodule.finrank_eq_zero]` and apply the resulting hypothesis. Establish `h2` using `Submodule.finrank_quotient_add_finrank (LinearMap.ker f)`. Establish `h3` using `Submodule.finrank_quotient_add_finrank (LinearMap.range f)`. Rewrite `h2` using `[f.quotKerEquivRange.finrank_eq]`.

Establish `h4 : Module.finrank R (M ⧸ LinearMap.range f) ≠ 0` using `by omega`. Rewrite `h4` using `[ne_eq, Module.finrank_eq_zero_iff]`. Use `push Not at h4`. Take `⟨x, hx⟩` from `h4`. Establish `h5 : Function.Injective (LinearMap.toSpanSingleton R _ x)`.

Rewrite using `[injective_iff_map_eq_zero]`. Introduce `r hr`. Assume the negation of the conclusion as `h0`. Conclude with `hx r h0 hr`. Establish `h6` using `Module.length_le_of_injective _ h5`.

Rewrite `h6` using `[length_self_eq_top]`. Conclude with `top_le_iff.mp h6`.
-/
theorem length_coker_of_not_injective (f : M →ₗ[R] M) (hf : LinearMap.ker f ≠ ⊥) :
    Module.length R (M ⧸ LinearMap.range f) = ⊤ := by
  have h1 : Module.finrank R (LinearMap.ker f) ≠ 0 := by
    rwa [ne_eq, Submodule.finrank_eq_zero]
  have h2 := Submodule.finrank_quotient_add_finrank (LinearMap.ker f)
  have h3 := Submodule.finrank_quotient_add_finrank (LinearMap.range f)
  rw [f.quotKerEquivRange.finrank_eq] at h2
  have h4 : Module.finrank R (M ⧸ LinearMap.range f) ≠ 0 := by omega
  rw [ne_eq, Module.finrank_eq_zero_iff] at h4
  push Not at h4
  obtain ⟨x, hx⟩ := h4
  have h5 : Function.Injective (LinearMap.toSpanSingleton R _ x) := by
    rw [injective_iff_map_eq_zero]
    intro r hr
    by_contra h0
    exact hx r h0 hr
  have h6 := Module.length_le_of_injective _ h5
  rw [length_self_eq_top] at h6
  exact top_le_iff.mp h6

/- English proof (translation)
Distinguish the cases in `hf : LinearMap.ker f = ⊥`. Conclude with `length_coker_of_injective f (LinearMap.ker_eq_bot.mp hf)`. Rewrite using `[length_coker_of_not_injective f hf, LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hf]`. Simplify using the standard rewrite rules.
-/
theorem length_coker (f : M →ₗ[R] M) :
    Module.length R (M ⧸ LinearMap.range f) =
      IsDiscreteValuationRing.addVal R (LinearMap.det f) := by
  by_cases hf : LinearMap.ker f = ⊥
  · exact length_coker_of_injective f (LinearMap.ker_eq_bot.mp hf)
  · rw [length_coker_of_not_injective f hf, LinearMap.det_eq_zero_iff_ker_ne_bot.mpr hf]
    simp

/- English proof (translation)
Establish `h : (Submodule.map g A).submoduleOf A = LinearMap.range (LinearMap.restrict g hg)`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, hxy⟩`. Conclude with `⟨⟨y, hy⟩, Subtype.ext hxy⟩`.

Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨y, y.2, rfl⟩`. Rewrite using `[GlobalTheory.relLength_def, h, length_coker]`.
-/
theorem relLength_map_eq_addVal_det {R : Type u_1} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {V : Type u_2} [AddCommGroup V] [Module R V] {A : Submodule R V}
    [Module.Free R A] [Module.Finite R A] (g : V →ₗ[R] V) (hg : ∀ x ∈ A, g x ∈ A) :
    GlobalTheory.relLength A (Submodule.map g A) =
      IsDiscreteValuationRing.addVal R (LinearMap.det (LinearMap.restrict g hg)) := by
  have h : (Submodule.map g A).submoduleOf A = LinearMap.range (LinearMap.restrict g hg) := by
    ext x
    constructor
    · rintro ⟨y, hy, hxy⟩
      exact ⟨⟨y, hy⟩, Subtype.ext hxy⟩
    · rintro ⟨y, rfl⟩
      exact ⟨y, y.2, rfl⟩
  rw [GlobalTheory.relLength_def, h, length_coker]

end GlobalTheory.LengthCokernelInjective
