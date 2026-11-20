import Mathlib
import Development.AutomorphicArithmetic.LocalEmbeddings.ConeBDefs
open MeasureTheory FreeSingleHomotopyEquivDiscreteChains.UpperTheory.Dv.ConeB

/- English proof (translation)
Use `⟨fun w => (l (Pi.single w 1) : ℂ) - (l (Pi.single w Complex.I) : ℂ) * Complex.I, fun s => ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← Finset.univ_sum_single s]`. Rewrite using `[map_sum, Complex.re_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Establish `h : (Pi.single w (s w) : ι → ℂ) = (s w).re • (Pi.single w 1 : ι → ℂ) + (s w).im • (Pi.single w Complex.I : ι → ℂ)`.

Rewrite using `[← Pi.single_smul, ← Pi.single_smul, ← Pi.single_add]`. Use `congr 1`. Simplify using the standard rewrite rules. Rewrite using `[h, map_add, map_smul, map_smul]`. Simplify using the standard rewrite rules.
-/
private theorem exists_rep {ι : Type} [Fintype ι] (l : (ι → ℂ) →ₗ[ℝ] ℝ) :
    ∃ y : ι → ℂ, ∀ s : ι → ℂ, l s = (∑ w, (s * y) w).re := by
  classical
  refine ⟨fun w => (l (Pi.single w 1) : ℂ) - (l (Pi.single w Complex.I) : ℂ) * Complex.I, fun s => ?_⟩
  conv_lhs => rw [← Finset.univ_sum_single s]
  rw [map_sum, Complex.re_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  have h : (Pi.single w (s w) : ι → ℂ) =
      (s w).re • (Pi.single w 1 : ι → ℂ) + (s w).im • (Pi.single w Complex.I : ι → ℂ) := by
    rw [← Pi.single_smul, ← Pi.single_smul, ← Pi.single_add]
    congr 1
    simp
  rw [h, map_add, map_smul, map_smul]
  simp

/- English proof (translation)
Unfold `FT`. Use `continuous_of_dominated (bound := fun s => ‖φ s‖) (fun y => ?_) (fun y => ?_) hi.norm ?_` and prove the remaining obligations. Conclude with `(hc.mul (continuous_ec.comp (continuous_id.mul continuous_const))).aestronglyMeasurable`. Conclude with `Filter.Eventually.of_forall fun s => by rw [norm_mul, norm_ec, mul_one]`. Conclude with `Filter.Eventually.of_forall fun s => continuous_const.mul (continuous_ec.comp (continuous_const.mul continuous_id))`.
-/
private theorem continuous_FT {ι : Type} [Fintype ι] (φ : (ι → ℂ) → ℂ) (hc : Continuous φ)
    (hi : Integrable φ) : Continuous (FT φ) := by
  unfold FT
  refine continuous_of_dominated (bound := fun s => ‖φ s‖) (fun y => ?_) (fun y => ?_) hi.norm ?_
  · exact (hc.mul (continuous_ec.comp (continuous_id.mul continuous_const))).aestronglyMeasurable
  · exact Filter.Eventually.of_forall fun s => by rw [norm_mul, norm_ec, mul_one]
  · exact Filter.Eventually.of_forall fun s =>
      continuous_const.mul (continuous_ec.comp (continuous_const.mul continuous_id))

open FourierTransform in
/- English proof (translation)
Introduce `ι _ φ hc hi hne`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Establish `h0 : FT φ = fun _ => 0` using `Continuous.ext_on dense_ne_zero (continuous_FT φ hc hi) continuous_const fun y hy => hcon y hy`. Set `T : EuclideanSpace ℝ (Fin (Module.finrank ℝ (ι → ℂ))) ≃L[ℝ] (ι → ℂ)` to `toEuclidean.symm`.

Use `haveI : (Measure.map T volume).IsAddHaarMeasure := T.isAddHaarMeasure_map _`. Establish `hm` using `Measure.isAddLeftInvariant_eq_smul (Measure.map T volume) (volume : Measure (ι → ℂ))`. Use `set c := Measure.addHaarScalarFactor (Measure.map T volume) (volume : Measure (ι → ℂ))`. Establish `hme : MeasurableEmbedding T` using `T.toHomeomorph.measurableEmbedding`. Establish `hfi : Integrable (φ ∘ T)`.

Rewrite using `[← hme.integrable_map_iff, hm]`. Conclude with `hi.smul_measure_nnreal`. Establish `hF : 𝓕 (φ ∘ T) = fun _ => 0`. Use function extensionality and compare the values at `w`. Take `⟨y, hy⟩` from `exists_rep (((innerₗ _).flip w) ∘ₗ (T.symm : (ι → ℂ) →ₗ[ℝ] _))`.

Establish `h1 : ∫ s, φ s * ec (s * y) ∂(Measure.map T volume) = 0`. Rewrite using `[hm, integral_smul_nnreal_measure]`. Use `congrFun h0 y` as an intermediate fact. Unfold `FT at this`. Rewrite using `[this, smul_zero]`.

Rewrite `h1` using `[hme.integral_map]`. Rewrite using `[Real.fourier_eq', ← h1]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Establish `h2` using `hy (T v)`. Simplify using `only [ec, ← h2]`.

Simplify using `[mul_comm]`. Use `left`. Rewrite using `[real_inner_comm]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Establish `hinv` using `(hc.comp T.continuous).fourierInv_fourier_eq hfi (by rw [hF]; exact integrable_zero _ _ _)`. Apply `hne` to reduce the goal to its premises. Use function extensionality and compare the values at `s`. Use `congrFun hinv (T.symm s)` as an intermediate fact. Rewrite `this` using `[hF, Real.fourierInv_eq]`.

Simplify using `using this.symm`.
-/
theorem UpperTheory.fourier_nonvanishing_unit_point :
    ∀ {ι : Type} [Fintype ι] (φ : (ι → ℂ) → ℂ), Continuous φ → Integrable φ → φ ≠ 0 →
        ∃ y : ι → ℂ, (∀ w, y w ≠ 0) ∧ FT φ y ≠ 0 := by
  intro ι _ φ hc hi hne
  by_contra hcon
  push Not at hcon
  have h0 : FT φ = fun _ => 0 :=
    Continuous.ext_on dense_ne_zero (continuous_FT φ hc hi) continuous_const fun y hy => hcon y hy
  let T : EuclideanSpace ℝ (Fin (Module.finrank ℝ (ι → ℂ))) ≃L[ℝ] (ι → ℂ) := toEuclidean.symm
  haveI : (Measure.map T volume).IsAddHaarMeasure := T.isAddHaarMeasure_map _
  have hm := Measure.isAddLeftInvariant_eq_smul (Measure.map T volume) (volume : Measure (ι → ℂ))
  set c := Measure.addHaarScalarFactor (Measure.map T volume) (volume : Measure (ι → ℂ))
  have hme : MeasurableEmbedding T := T.toHomeomorph.measurableEmbedding
  have hfi : Integrable (φ ∘ T) := by
    rw [← hme.integrable_map_iff, hm]
    exact hi.smul_measure_nnreal
  have hF : 𝓕 (φ ∘ T) = fun _ => 0 := by
    funext w
    obtain ⟨y, hy⟩ := exists_rep (((innerₗ _).flip w) ∘ₗ (T.symm : (ι → ℂ) →ₗ[ℝ] _))
    have h1 : ∫ s, φ s * ec (s * y) ∂(Measure.map T volume) = 0 := by
      rw [hm, integral_smul_nnreal_measure]
      have := congrFun h0 y
      unfold FT at this
      rw [this, smul_zero]
    rw [hme.integral_map] at h1
    rw [Real.fourier_eq', ← h1]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    have h2 := hy (T v)
    simp only [ec, ← h2]
    simp [mul_comm]
    left
    rw [real_inner_comm]
    congr 1
    ring
  have hinv := (hc.comp T.continuous).fourierInv_fourier_eq hfi (by rw [hF]; exact integrable_zero _ _ _)
  apply hne
  funext s
  have := congrFun hinv (T.symm s)
  rw [hF, Real.fourierInv_eq] at this
  simpa using this.symm
