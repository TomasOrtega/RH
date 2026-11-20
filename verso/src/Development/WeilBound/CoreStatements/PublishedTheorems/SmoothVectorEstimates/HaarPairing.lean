import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.MirabolicColumnBlock

noncomputable section

open MeasureTheory Matrix GlobalTheory.CuspGeneric Topology
open scoped ContDiff

namespace PositivityTheory.jumpWindows

namespace HaarPairing

open scoped FourierTransform RealInnerProductSpace Real SchwartzMap

/- English proof (translation)
Establish `hI : Integrable (𝓕 g)`. Set `G : 𝓢(EuclideanSpace ℝ (Fin d), ℂ)` to `𝓕 (hc.toSchwartzMap hg)`. Establish `e : (𝓕 g) = ⇑G`. Simplify using `only [G, SchwartzMap.fourier_coe]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `G.integrable`. Establish `h` using `congrFun (hg.continuous.fourierInv_fourier_eq (hg.continuous.integrable_of_hasCompactSupport hc) hI) v`. Rewrite `h` using `[Real.fourierInv_eq]`. Simplify `h` using `only [Real.fourier_eq]`.
-/
theorem inv_E {d : ℕ} (g : EuclideanSpace ℝ (Fin d) → ℂ) (hg : ContDiff ℝ ∞ g) (hc : HasCompactSupport g)
    (v : EuclideanSpace ℝ (Fin d)) :
    ∫ w, 𝐞 ⟪w, v⟫ • (∫ z, 𝐞 (-⟪z, w⟫) • g z) = g v := by
  have hI : Integrable (𝓕 g) := by
    let G : 𝓢(EuclideanSpace ℝ (Fin d), ℂ) := 𝓕 (hc.toSchwartzMap hg)
    have e : (𝓕 g) = ⇑G := by
      simp only [G, SchwartzMap.fourier_coe]; rfl
    rw [e]; exact G.integrable
  have h := congrFun (hg.continuous.fourierInv_fourier_eq
    (hg.continuous.integrable_of_hasCompactSupport hc) hI) v
  rw [Real.fourierInv_eq] at h
  simpa only [Real.fourier_eq] using h

/- English proof (translation)
Establish `: (μ.map e).IsAddHaarMeasure` using `e.isAddHaarMeasure_map μ`. Use `set c := Measure.addHaarScalarFactor (μ.map e) volume with hc`. Establish `hm : μ.map e = c • volume` using `Measure.isAddLeftInvariant_eq_smul _ _`. Use `⟨c, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', fun h => ?_⟩` and prove the remaining obligations. Establish `key : ∫ x, h (e x) ∂μ = ∫ z, h z ∂(μ.map e)` using `(e.toHomeomorph.measurableEmbedding.integral_map h).symm`.

Rewrite using `[key, hm, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]`.
-/
theorem haar_E {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    [MeasurableSpace V] [BorelSpace V] (μ : Measure V) [μ.IsAddHaarMeasure] {d : ℕ}
    (e : V ≃L[ℝ] EuclideanSpace ℝ (Fin d)) :
    ∃ c : NNReal, c ≠ 0 ∧ ∀ h : EuclideanSpace ℝ (Fin d) → ℂ,
      ∫ x, h (e x) ∂μ = ((c : ℝ) : ℂ) * ∫ z, h z := by
  have : (μ.map e).IsAddHaarMeasure := e.isAddHaarMeasure_map μ
  set c := Measure.addHaarScalarFactor (μ.map e) volume with hc
  have hm : μ.map e = c • volume := Measure.isAddLeftInvariant_eq_smul _ _
  refine ⟨c, (Measure.addHaarScalarFactor_pos_of_isAddHaarMeasure _ _).ne', fun h => ?_⟩
  have key : ∫ x, h (e x) ∂μ = ∫ z, h z ∂(μ.map e) :=
    (e.toHomeomorph.measurableEmbedding.integral_map h).symm
  rw [key, hm, integral_smul_nnreal_measure, NNReal.smul_def, Complex.real_smul]

/- English proof (translation)
Set `T : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V))` to `toEuclidean`. Set `φ : V → StrongDual ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ V)))` to `fun y => (2 * π)⁻¹ • (β.flip y).comp (T.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)`. Establish `φadd : ∀ y y', φ (y + y') = φ y + φ y'`. Introduce `y y'`. Simplify using `only [φ, map_add, ContinuousLinearMap.add_comp, smul_add]`.

Establish `φsmul : ∀ (r : ℝ) y, φ (r • y) = r • φ y`. Introduce `r y`. Simplify using `only [φ, map_smul, ContinuousLinearMap.smul_comp, smul_comm r]`. Set `L : V →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V))` to `{ toFun := fun y => (InnerProductSpace.toDual ℝ _).symm (φ y) map_add' := fun y y' => by simp only [φadd, map_add] map_smul' := fun r y => by`. Simplify using `only [φsmul, LinearIsometryEquiv.map_smulₛₗ, RingHom.id_apply, RCLike.conj_to_real] }`.

Establish `hL : ∀ x y, ⟪T x, L y⟫ = (2 * π)⁻¹ * β x y`. Introduce `x y`. Rewrite using `[real_inner_comm]`. Express the relevant statement in the definitionally equal form `⟪(InnerProductSpace.toDual ℝ _).symm (φ y), T x⟫ = _`. Rewrite using `[InnerProductSpace.toDual_symm_apply]`.

Simplify using `[φ]`. Establish `hinj : Function.Injective L`. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `y hy`. Apply `hβ` to reduce the goal to its premises.

Introduce `x`. Establish `h1` using `hL x y`. Rewrite `h1` using `[hy, inner_zero_right]`. Establish `hp : (2 * π)⁻¹ ≠ 0` using `by positivity`. Conclude with `(mul_eq_zero.mp h1.symm).resolve_left hp`.

Set `A` to `(L.linearEquivOfInjective hinj finrank_euclideanSpace_fin.symm).toContinuousLinearEquiv`. Use `⟨T, A, fun x y => ?_⟩` and prove the remaining obligations. Establish `hA : A y = L y` using `rfl`. Rewrite using `[hA, hL]`. Clear the denominators using the available nonvanishing facts.
-/
theorem pair {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [FiniteDimensional ℝ V]
    (β : V →L[ℝ] V →L[ℝ] ℝ) (hβ : ∀ y, (∀ x, β x y = 0) → y = 0) :
    ∃ T A : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)),
      ∀ x y, β x y = 2 * π * ⟪T x, A y⟫ := by
  let T : V ≃L[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) := toEuclidean
  let φ : V → StrongDual ℝ (EuclideanSpace ℝ (Fin (Module.finrank ℝ V))) := fun y =>
    (2 * π)⁻¹ • (β.flip y).comp (T.symm : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) →L[ℝ] V)
  have φadd : ∀ y y', φ (y + y') = φ y + φ y' := by
    intro y y'; simp only [φ, map_add, ContinuousLinearMap.add_comp, smul_add]
  have φsmul : ∀ (r : ℝ) y, φ (r • y) = r • φ y := by
    intro r y; simp only [φ, map_smul, ContinuousLinearMap.smul_comp, smul_comm r]
  let L : V →ₗ[ℝ] EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) :=
    { toFun := fun y => (InnerProductSpace.toDual ℝ _).symm (φ y)
      map_add' := fun y y' => by simp only [φadd, map_add]
      map_smul' := fun r y => by
        simp only [φsmul, LinearIsometryEquiv.map_smulₛₗ, RingHom.id_apply, RCLike.conj_to_real] }
  have hL : ∀ x y, ⟪T x, L y⟫ = (2 * π)⁻¹ * β x y := by
    intro x y
    rw [real_inner_comm]
    change ⟪(InnerProductSpace.toDual ℝ _).symm (φ y), T x⟫ = _
    rw [InnerProductSpace.toDual_symm_apply]
    simp [φ]
  have hinj : Function.Injective L := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro y hy
    apply hβ
    intro x
    have h1 := hL x y
    rw [hy, inner_zero_right] at h1
    have hp : (2 * π)⁻¹ ≠ 0 := by positivity
    exact (mul_eq_zero.mp h1.symm).resolve_left hp
  let A := (L.linearEquivOfInjective hinj finrank_euclideanSpace_fin.symm).toContinuousLinearEquiv
  refine ⟨T, A, fun x y => ?_⟩
  have hA : A y = L y := rfl
  rw [hA, hL]
  field_simp

end HaarPairing

/- English proof (translation)
Introduce `V _ _ _ _ _ μ _ β hβ`. Take `⟨T, A, hTA⟩` from `HaarPairing.pair β hβ`. Take `⟨c1, hc1, h1⟩` from `HaarPairing.haar_E μ T`. Take `⟨c2, hc2, h2⟩` from `HaarPairing.haar_E μ A`. Use `⟨((c1 : ℝ) : ℂ) * ((c2 : ℝ) : ℂ), mul_ne_zero (by exact_mod_cast hc1) (by exact_mod_cast hc2), fun f hf hc ξ => ?_⟩` and prove the remaining obligations.

Use `set g : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ := f ∘ T.symm with hg_def`. Establish `hgs : ContDiff ℝ ∞ g` using `hf.comp T.symm.contDiff`. Establish `hgc : HasCompactSupport g` using `hc.comp_homeomorph T.symm.toHomeomorph`. Establish `hFT : ∀ y, FT μ β f y = ((c1 : ℝ) : ℂ) * ∫ z, Real.fourierChar (-inner ℝ z (A y)) • g z`. Introduce `y`.

Rewrite using `[FT, ← h1 (fun z => Real.fourierChar (-inner ℝ z (A y)) • g z)]`. Use `congr 1 with x`. Simplify using `only [g, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hTA]`. Use `push_cast`. Put the polynomial expressions in normal form.

Establish `step : ∫ y, Complex.exp ((β ξ y : ℝ) * Complex.I) * FT μ β f y ∂μ = ((c1 : ℝ) : ℂ) * ∫ y, Real.fourierChar (inner ℝ (A y) (T ξ)) • (∫ z, Real.fourierChar (-inner ℝ z (A y)) • g z) ∂μ`. Rewrite using `[← integral_const_mul]`. Use `congr 1 with y`. Simplify using `only [hFT, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hTA, real_inner_comm (A y)]`. Use `push_cast`.

Put the polynomial expressions in normal form. Establish `h2'` using `h2 (fun w => Real.fourierChar (inner ℝ w (T ξ)) • ∫ z, Real.fourierChar (-inner ℝ z w) • g z)`. Rewrite using `[step, h2', HaarPairing.inv_E g hgs hgc]`. Simplify using `only [g, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem haar_measure_pairing : S5 := by
  intro V _ _ _ _ _ μ _ β hβ
  obtain ⟨T, A, hTA⟩ := HaarPairing.pair β hβ
  obtain ⟨c1, hc1, h1⟩ := HaarPairing.haar_E μ T
  obtain ⟨c2, hc2, h2⟩ := HaarPairing.haar_E μ A
  refine ⟨((c1 : ℝ) : ℂ) * ((c2 : ℝ) : ℂ), mul_ne_zero (by exact_mod_cast hc1) (by exact_mod_cast hc2),
    fun f hf hc ξ => ?_⟩
  set g : EuclideanSpace ℝ (Fin (Module.finrank ℝ V)) → ℂ := f ∘ T.symm with hg_def
  have hgs : ContDiff ℝ ∞ g := hf.comp T.symm.contDiff
  have hgc : HasCompactSupport g := hc.comp_homeomorph T.symm.toHomeomorph
  have hFT : ∀ y, FT μ β f y = ((c1 : ℝ) : ℂ) *
      ∫ z, Real.fourierChar (-inner ℝ z (A y)) • g z := by
    intro y
    rw [FT, ← h1 (fun z => Real.fourierChar (-inner ℝ z (A y)) • g z)]
    congr 1 with x
    simp only [g, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply, Circle.smul_def,
      Real.fourierChar_apply, smul_eq_mul, hTA]
    push_cast
    ring_nf
  have step : ∫ y, Complex.exp ((β ξ y : ℝ) * Complex.I) * FT μ β f y ∂μ =
      ((c1 : ℝ) : ℂ) * ∫ y, Real.fourierChar (inner ℝ (A y) (T ξ)) •
        (∫ z, Real.fourierChar (-inner ℝ z (A y)) • g z) ∂μ := by
    rw [← integral_const_mul]
    congr 1 with y
    simp only [hFT, Circle.smul_def, Real.fourierChar_apply, smul_eq_mul, hTA, real_inner_comm (A y)]
    push_cast
    ring_nf
  have h2' := h2 (fun w => Real.fourierChar (inner ℝ w (T ξ)) •
    ∫ z, Real.fourierChar (-inner ℝ z w) • g z)
  rw [step, h2', HaarPairing.inv_E g hgs hgc]
  simp only [g, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]
  ring

end PositivityTheory.jumpWindows

end
