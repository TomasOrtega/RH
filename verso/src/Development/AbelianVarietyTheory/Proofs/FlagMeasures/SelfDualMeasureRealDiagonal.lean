import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.GaugeUnfold
import Formalism.LocalToGlobal.GlobalTheory.GL5.Statement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.FourierInversionHaarSymmForm

open MeasureTheory FourierTransform Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace GlobalTheory.SelfDualDiagReal

/- English proof (translation)
Use `⟨hμ, ?_⟩` and prove the remaining obligations. Introduce `Φ hΦc hΦs hint z`. Establish `ha : a ≠ 0` using `left_ne_zero_of_mul_eq_one hab`. Use `set ψ : E → ℂ := fun w => Φ (T.symm w) with hψdef`. Use `set φ : E → ℂ := fun w => ψ (-w) with hφdef`.

Establish `hφc : Continuous φ` using `hΦc.comp (T.symm.continuous.comp continuous_neg)`. Establish `hφs : HasCompactSupport φ` using `(hΦs.comp_homeomorph T.symm.toHomeomorph).comp_homeomorph (Homeomorph.neg E)`. Establish `hφi : Integrable φ` using `hφc.integrable_of_hasCompactSupport hφs`. Establish `hψφ : 𝓕⁻ ψ = 𝓕 φ` using `Real.fourierInv_eq_fourier_comp_neg ψ`. Establish `hhat : ∀ y, ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ = a * 𝓕⁻ ψ (R y)`.

Introduce `y`. Establish `h` using `haI (fun w => ψ w * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ w (R y) : ℝ) : ℂ)))`. Simplify using `only [hψdef, ContinuousLinearEquiv.symm_apply_apply] at h`. Repeatedly rewrite using `[hR]`. Rewrite using `[h, Real.fourierInv_eq']`.

Use `congr 1`. Use `integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations. Simplify using `only [smul_eq_mul]`. Rewrite using `[mul_comm]`. Use `congr 2`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hint' : Integrable (fun y => 𝓕⁻ ψ (R y)) μ`. Establish `h2 : (fun y => 𝓕⁻ ψ (R y)) = fun y => a⁻¹ * ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ`. Use function extensionality and compare the values at `y`.

Rewrite using `[hhat y, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]`. Rewrite using `[h2]`. Conclude with `hint.const_mul _`. Take `⟨c, -, -, hiff⟩` from `GlobalTheory.exists_pos_integral_comp_equiv_haar R μ`. Establish `hFi : Integrable (𝓕 φ)`.

Rewrite using `[← hψφ]`. Conclude with `(hiff _).1 hint'`. Establish `hinv : 𝓕⁻ (𝓕⁻ ψ) = φ`. Rewrite using `[hψφ]`. Conclude with `hφc.fourierInv_fourier_eq hφi hFi`.

Establish `hsym : ∀ y, B y z = inner ℝ (R y) (T z)` using `fun y => by`. Rewrite using `[hs, hR, real_inner_comm]`. Establish `hlast : ∫ u, 𝓕⁻ ψ u * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ)) = 𝓕⁻ (𝓕⁻ ψ) (T z)`. Rewrite using `[Real.fourierInv_eq']`. Use `integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)` and prove the remaining obligations.

Simplify using `only [smul_eq_mul]`. Rewrite using `[mul_comm]`. Use `congr 2`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Combine the equalities or inequalities in the displayed calculation. Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[hhat y, hsym y, mul_assoc]`. Use `_ = b * ∫ u, a * (𝓕⁻ ψ u * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ))) := hbI (fun u => a * (𝓕⁻ ψ u * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ))))`.

Use `_ = (a * b) * φ (T z) := by`. Rewrite using `[integral_const_mul, hlast, hinv]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = Φ (-z) := by`. Rewrite using `[hab, one_mul, hφdef, hψdef]`.

Simplify using `only [map_neg, ContinuousLinearEquiv.symm_apply_apply]`.
-/
theorem selfDual_of_transport {V E : Type} [NormedAddCommGroup V] [NormedSpace ℝ V]
    [FiniteDimensional ℝ V] [MeasurableSpace V] [BorelSpace V]
    [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [FiniteDimensional ℝ E] [MeasurableSpace E] [BorelSpace E]
    (B : V → V → ℝ) (hs : ∀ x y, B x y = B y x) (T R : V ≃L[ℝ] E)
    (hR : ∀ x y, B x y = inner ℝ (T x) (R y)) (μ : Measure V) [hμ : μ.IsAddHaarMeasure]
    (a b : ℂ) (hab : a * b = 1) (haI : ∀ g : E → ℂ, ∫ x, g (T x) ∂μ = a * ∫ w, g w)
    (hbI : ∀ g : E → ℂ, ∫ x, g (R x) ∂μ = b * ∫ w, g w) :
    SelfDual μ (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ))) := by
  refine ⟨hμ, ?_⟩
  intro Φ hΦc hΦs hint z
  have ha : a ≠ 0 := left_ne_zero_of_mul_eq_one hab

  set ψ : E → ℂ := fun w => Φ (T.symm w) with hψdef
  set φ : E → ℂ := fun w => ψ (-w) with hφdef
  have hφc : Continuous φ := hΦc.comp (T.symm.continuous.comp continuous_neg)
  have hφs : HasCompactSupport φ :=
    (hΦs.comp_homeomorph T.symm.toHomeomorph).comp_homeomorph (Homeomorph.neg E)
  have hφi : Integrable φ := hφc.integrable_of_hasCompactSupport hφs
  have hψφ : 𝓕⁻ ψ = 𝓕 φ := Real.fourierInv_eq_fourier_comp_neg ψ

  have hhat : ∀ y, ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ
      = a * 𝓕⁻ ψ (R y) := by
    intro y
    have h := haI (fun w => ψ w * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ w (R y) : ℝ) : ℂ)))
    simp only [hψdef, ContinuousLinearEquiv.symm_apply_apply] at h
    simp_rw [hR]
    rw [h, Real.fourierInv_eq']
    congr 1
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  have hint' : Integrable (fun y => 𝓕⁻ ψ (R y)) μ := by
    have h2 : (fun y => 𝓕⁻ ψ (R y)) = fun y => a⁻¹ *
        ∫ x, Φ x * Complex.exp (2 * Real.pi * Complex.I * ((B x y : ℝ) : ℂ)) ∂μ := by
      funext y
      rw [hhat y, ← mul_assoc, inv_mul_cancel₀ ha, one_mul]
    rw [h2]
    exact hint.const_mul _
  obtain ⟨c, -, -, hiff⟩ := GlobalTheory.exists_pos_integral_comp_equiv_haar R μ
  have hFi : Integrable (𝓕 φ) := by
    rw [← hψφ]
    exact (hiff _).1 hint'
  have hinv : 𝓕⁻ (𝓕⁻ ψ) = φ := by
    rw [hψφ]
    exact hφc.fourierInv_fourier_eq hφi hFi
  have hsym : ∀ y, B y z = inner ℝ (R y) (T z) := fun y => by
    rw [hs, hR, real_inner_comm]
  have hlast : ∫ u, 𝓕⁻ ψ u * Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ))
      = 𝓕⁻ (𝓕⁻ ψ) (T z) := by
    rw [Real.fourierInv_eq']
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    simp only [smul_eq_mul]
    rw [mul_comm]
    congr 2
    push_cast
    ring
  calc _ = ∫ y, (fun u => a * (𝓕⁻ ψ u *
          Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ)))) (R y) ∂μ := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        rw [hhat y, hsym y, mul_assoc]
    _ = b * ∫ u, a * (𝓕⁻ ψ u *
          Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ))) :=
          hbI (fun u => a * (𝓕⁻ ψ u *
            Complex.exp (2 * Real.pi * Complex.I * ((inner ℝ u (T z) : ℝ) : ℂ))))
    _ = (a * b) * φ (T z) := by
        rw [integral_const_mul, hlast, hinv]
        ring
    _ = Φ (-z) := by
        rw [hab, one_mul, hφdef, hψdef]
        simp only [map_neg, ContinuousLinearEquiv.symm_apply_apply]

/- English proof (translation)
Use `set f : (κ → ℝ) →ₗ[ℝ] (κ → ℝ) := Matrix.toLin' (Matrix.diagonal d) with hf`. Establish `hdet : LinearMap.det f = ∏ k, d k`. Rewrite using `[hf, LinearMap.det_toLin', Matrix.det_diagonal]`. Establish `hne : LinearMap.det f ≠ 0`. Rewrite using `[hdet]`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun k _ => hd k`. Use `set D : (κ → ℝ) ≃L[ℝ] (κ → ℝ) := (LinearMap.equivOfDetNeZero f hne).toContinuousLinearEquiv with hDdef`. Establish `hDf : ∀ x, D x = f x` using `fun x => rfl`. Use `⟨D, ?_, ?_⟩` and prove the remaining obligations. Introduce `y k`.

Rewrite using `[hDf, hf, Matrix.toLin'_apply, Matrix.mulVec_diagonal]`. Introduce `g`. Establish `hmap` using `MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar (volume : Measure (κ → ℝ)) hne`. Establish `hcoe : (⇑D.toHomeomorph : (κ → ℝ) → (κ → ℝ)) = ⇑f` using `rfl`. Establish `h` using `D.toHomeomorph.measurableEmbedding.integral_map (μ := (volume : Measure (κ → ℝ))) g`.

Rewrite `h` using `[hcoe, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), hdet, abs_inv]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_diag_equiv (κ : Type) [Fintype κ] (d : κ → ℝ) (hd : ∀ k, d k ≠ 0) :
    ∃ D : (κ → ℝ) ≃L[ℝ] (κ → ℝ), (∀ y k, D y k = d k * y k) ∧
      ∀ g : (κ → ℝ) → ℂ, ∫ x, g (D x) = ((|∏ k, d k|⁻¹ : ℝ) : ℂ) * ∫ w, g w := by
  classical
  set f : (κ → ℝ) →ₗ[ℝ] (κ → ℝ) := Matrix.toLin' (Matrix.diagonal d) with hf
  have hdet : LinearMap.det f = ∏ k, d k := by
    rw [hf, LinearMap.det_toLin', Matrix.det_diagonal]
  have hne : LinearMap.det f ≠ 0 := by
    rw [hdet]
    exact Finset.prod_ne_zero_iff.mpr fun k _ => hd k
  set D : (κ → ℝ) ≃L[ℝ] (κ → ℝ) := (LinearMap.equivOfDetNeZero f hne).toContinuousLinearEquiv
    with hDdef
  have hDf : ∀ x, D x = f x := fun x => rfl
  refine ⟨D, ?_, ?_⟩
  · intro y k
    rw [hDf, hf, Matrix.toLin'_apply, Matrix.mulVec_diagonal]
  · intro g
    have hmap := MeasureTheory.Measure.map_linearMap_addHaar_eq_smul_addHaar
      (volume : Measure (κ → ℝ)) hne
    have hcoe : (⇑D.toHomeomorph : (κ → ℝ) → (κ → ℝ)) = ⇑f := rfl
    have h := D.toHomeomorph.measurableEmbedding.integral_map (μ := (volume : Measure (κ → ℝ))) g
    rw [hcoe, hmap, integral_smul_measure, ENNReal.toReal_ofReal (abs_nonneg _), hdet,
      abs_inv] at h
    calc ∫ x, g (D x) = ∫ x, g (f x) := rfl
      _ = _ := by rw [← h, Complex.real_smul]

/- English proof (translation)
Use `⟨(EuclideanSpace.equiv κ ℝ).symm, ?_, ?_⟩` and prove the remaining obligations. Introduce `x y`. Simplify using `[PiLp.inner_apply, mul_comm]`. Introduce `g`. Conclude with `(PiLp.volume_preserving_toLp κ).integral_comp (MeasurableEquiv.toLp 2 (κ → ℝ)).measurableEmbedding g`.
-/
theorem exists_euclid_equiv (κ : Type) [Fintype κ] :
    ∃ T : (κ → ℝ) ≃L[ℝ] EuclideanSpace ℝ κ, (∀ x y, inner ℝ (T x) (T y) = ∑ k, x k * y k) ∧
      ∀ g : EuclideanSpace ℝ κ → ℂ, ∫ x, g (T x) = ∫ w, g w := by
  refine ⟨(EuclideanSpace.equiv κ ℝ).symm, ?_, ?_⟩
  · intro x y
    simp [PiLp.inner_apply, mul_comm]
  · intro g
    exact (PiLp.volume_preserving_toLp κ).integral_comp
      (MeasurableEquiv.toLp 2 (κ → ℝ)).measurableEmbedding g

/- English proof (translation)
Take `⟨D, hD, hDI⟩` from `exists_diag_equiv κ d hd`. Take `⟨T, hT, hTI⟩` from `exists_euclid_equiv κ`. Use `set s : ℝ := ∏ k, √|d k| with hsdef`. Establish `hs0 : 0 < s` using `Finset.prod_pos fun k _ => Real.sqrt_pos.2 (abs_pos.2 (hd k))`. Establish `hsq : s * s = |∏ k, d k|`.

Rewrite using `[Finset.abs_prod, hsdef, ← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => Real.mul_self_sqrt (abs_nonneg _)`. Establish `hr : |∏ k, d k| ≠ 0` using `abs_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun k _ => hd k)`. Establish `: (ENNReal.ofReal s • (volume : Measure (κ → ℝ))).IsAddHaarMeasure` using `Measure.IsAddHaarMeasure.smul _ (by simpa using hs0) ENNReal.ofReal_ne_top`. Establish `hint : ∀ g : (κ → ℝ) → ℂ, ∫ x, g x ∂(ENNReal.ofReal s • (volume : Measure (κ → ℝ))) = (s : ℂ) * ∫ x, g x`.

Introduce `g`. Rewrite using `[integral_smul_measure, ENNReal.toReal_ofReal hs0.le, Complex.real_smul]`. Establish `hsym : ∀ x y : κ → ℝ, ∑ k, d k * (x k * y k) = ∑ k, d k * (y k * x k)`. Introduce `x y`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Establish `hR : ∀ x y : κ → ℝ, ∑ k, d k * (x k * y k) = inner ℝ (T x) ((D.trans T) y)`. Introduce `x y`. Rewrite using `[ContinuousLinearEquiv.trans_apply, hT]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[hD]`. Expand and normalize the polynomial expressions, which then agree. Establish `hab : (s : ℂ) * ((s : ℂ) * ((|∏ k, d k|⁻¹ : ℝ) : ℂ)) = 1`. Rewrite using `[← mul_assoc, ← Complex.ofReal_mul, hsq, ← Complex.ofReal_mul, mul_inv_cancel₀ hr, Complex.ofReal_one]`. Establish `haI : ∀ g : EuclideanSpace ℝ κ → ℂ, ∫ x, g (T x) ∂(ENNReal.ofReal s • (volume : Measure (κ → ℝ))) = (s : ℂ) * ∫ w, g w`.

Introduce `g`. Rewrite using `[hint, hTI]`. Establish `hbI : ∀ g : EuclideanSpace ℝ κ → ℂ, ∫ x, g ((D.trans T) x) ∂(ENNReal.ofReal s • (volume : Measure (κ → ℝ))) = ((s : ℂ) * ((|∏ k, d k|⁻¹ : ℝ) : ℂ)) * ∫ w, g w`. Introduce `g`. Rewrite using `[hint]`.

Simplify using `only [ContinuousLinearEquiv.trans_apply]`. Rewrite using `[hDI (fun x => g (T x)), hTI]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `selfDual_of_transport (V := κ → ℝ) (E := EuclideanSpace ℝ κ) (fun x y => ∑ k, d k * (x k * y k)) hsym T (D.trans T) hR _ _ _ hab haI hbI`.
-/
theorem selfDual_diag (κ : Type) [Fintype κ] (d : κ → ℝ) (hd : ∀ k, d k ≠ 0) :
    SelfDual (ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ)))
      (fun x y => Complex.exp (2 * Real.pi * Complex.I * ((∑ k, d k * (x k * y k) : ℝ) : ℂ))) := by
  obtain ⟨D, hD, hDI⟩ := exists_diag_equiv κ d hd
  obtain ⟨T, hT, hTI⟩ := exists_euclid_equiv κ
  set s : ℝ := ∏ k, √|d k| with hsdef
  have hs0 : 0 < s := Finset.prod_pos fun k _ => Real.sqrt_pos.2 (abs_pos.2 (hd k))
  have hsq : s * s = |∏ k, d k| := by
    rw [Finset.abs_prod, hsdef, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl fun k _ => Real.mul_self_sqrt (abs_nonneg _)
  have hr : |∏ k, d k| ≠ 0 := abs_ne_zero.2 (Finset.prod_ne_zero_iff.2 fun k _ => hd k)
  have : (ENNReal.ofReal s • (volume : Measure (κ → ℝ))).IsAddHaarMeasure :=
    Measure.IsAddHaarMeasure.smul _ (by simpa using hs0) ENNReal.ofReal_ne_top
  have hint : ∀ g : (κ → ℝ) → ℂ,
      ∫ x, g x ∂(ENNReal.ofReal s • (volume : Measure (κ → ℝ))) = (s : ℂ) * ∫ x, g x := by
    intro g
    rw [integral_smul_measure, ENNReal.toReal_ofReal hs0.le, Complex.real_smul]
  have hsym : ∀ x y : κ → ℝ, ∑ k, d k * (x k * y k) = ∑ k, d k * (y k * x k) := by
    intro x y
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  have hR : ∀ x y : κ → ℝ, ∑ k, d k * (x k * y k) = inner ℝ (T x) ((D.trans T) y) := by
    intro x y
    rw [ContinuousLinearEquiv.trans_apply, hT]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hD]
    ring
  have hab : (s : ℂ) * ((s : ℂ) * ((|∏ k, d k|⁻¹ : ℝ) : ℂ)) = 1 := by
    rw [← mul_assoc, ← Complex.ofReal_mul, hsq, ← Complex.ofReal_mul, mul_inv_cancel₀ hr,
      Complex.ofReal_one]
  have haI : ∀ g : EuclideanSpace ℝ κ → ℂ,
      ∫ x, g (T x) ∂(ENNReal.ofReal s • (volume : Measure (κ → ℝ))) = (s : ℂ) * ∫ w, g w := by
    intro g
    rw [hint, hTI]
  have hbI : ∀ g : EuclideanSpace ℝ κ → ℂ,
      ∫ x, g ((D.trans T) x) ∂(ENNReal.ofReal s • (volume : Measure (κ → ℝ))) =
        ((s : ℂ) * ((|∏ k, d k|⁻¹ : ℝ) : ℂ)) * ∫ w, g w := by
    intro g
    rw [hint]
    simp only [ContinuousLinearEquiv.trans_apply]
    rw [hDI (fun x => g (T x)), hTI]
    ring
  exact selfDual_of_transport (V := κ → ℝ) (E := EuclideanSpace ℝ κ)
    (fun x y => ∑ k, d k * (x k * y k)) hsym T (D.trans T) hR _ _ _ hab haI hbI

/- English proof (translation)
Introduce `κ _ d hd μ hμ`. Establish `hν` using `selfDual_diag κ d hd`. Establish `: (ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ))).IsAddHaarMeasure` using `hν.1`. Set `Bl : (κ → ℝ) →ₗ[ℝ] (κ → ℝ) →ₗ[ℝ] ℝ` to `LinearMap.mk₂ ℝ (fun x y => ∑ k, d k * (x k * y k)) (fun x x' y => by`. Simplify using `only [Pi.add_apply, ← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun k _ => by ring)`. Use the proof step `(fun c x y => by`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring)`. Use the proof step `(fun x y y' => by`.

Simplify using `only [Pi.add_apply, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring)`. Use the proof step `(fun c x y => by`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring)`.

Establish `hBl : ∀ x y, Bl x y = ∑ k, d k * (x k * y k)` using `fun x y => rfl`. Establish `hsymm : ∀ x y, Bl x y = Bl y x` using `fun x y => by`. Rewrite using `[hBl, hBl]`. Conclude with `Finset.sum_congr rfl fun k _ => by ring`. Establish `hnd : ∀ x, (∀ y, Bl x y = 0) → x = 0`.

Introduce `x hx`. Use function extensionality and compare the values at `k`. Establish `h` using `hx (Pi.single k 1)`. Rewrite `h` using `[hBl]`. Simplify using `only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true] at h`.

Conclude with `(mul_eq_zero.1 h).resolve_left (hd k)`. Take `⟨-, hsch⟩` from `GlobalTheory.fourier_inversion_haar_symm_form Bl hsymm hnd (ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ))) inferInstance`. Take `⟨u, -, hu_cs, hu_sm, -, hu0⟩` from `exists_contDiff_tsupport_subset (n := ⊤) (x := (0 : κ → ℝ)) (s := Set.univ) Filter.univ_mem`. Establish `hΦcs : HasCompactSupport (⇑Complex.ofRealCLM ∘ u)` using `hu_cs.comp_left (map_zero _)`. Establish `hΦsm` using `Complex.ofRealCLM.contDiff.comp hu_sm`.

Establish `hI` using `(hsch (hΦcs.toSchwartzMap hΦsm)).2`. Conclude with `SelfDual.eq_of_test hν hμ (⇑Complex.ofRealCLM ∘ u) hΦsm.continuous hΦcs hI 0 (by simp [hu0])`.
-/
theorem eq_of_selfDual_diag : ∀ (κ : Type) [Fintype κ] (d : κ → ℝ), (∀ k, d k ≠ 0) →
    ∀ μ : Measure (κ → ℝ), SelfDual μ (fun x y => Complex.exp
      (2 * Real.pi * Complex.I * ((∑ k, d k * (x k * y k) : ℝ) : ℂ))) →
      μ = ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ)) := by
  intro κ _ d hd μ hμ
  classical
  have hν := selfDual_diag κ d hd
  have : (ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ))).IsAddHaarMeasure := hν.1
  let Bl : (κ → ℝ) →ₗ[ℝ] (κ → ℝ) →ₗ[ℝ] ℝ := LinearMap.mk₂ ℝ (fun x y => ∑ k, d k * (x k * y k))
    (fun x x' y => by
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring)
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring)
    (fun x y y' => by
      simp only [Pi.add_apply, ← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun k _ => by ring)
    (fun c x y => by
      simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring)
  have hBl : ∀ x y, Bl x y = ∑ k, d k * (x k * y k) := fun x y => rfl
  have hsymm : ∀ x y, Bl x y = Bl y x := fun x y => by
    rw [hBl, hBl]
    exact Finset.sum_congr rfl fun k _ => by ring
  have hnd : ∀ x, (∀ y, Bl x y = 0) → x = 0 := by
    intro x hx
    funext k
    have h := hx (Pi.single k 1)
    rw [hBl] at h
    simp only [Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq',
      Finset.mem_univ, if_true] at h
    exact (mul_eq_zero.1 h).resolve_left (hd k)
  obtain ⟨-, hsch⟩ := GlobalTheory.fourier_inversion_haar_symm_form Bl hsymm hnd
    (ENNReal.ofReal (∏ k, √|d k|) • (volume : Measure (κ → ℝ))) inferInstance
  obtain ⟨u, -, hu_cs, hu_sm, -, hu0⟩ := exists_contDiff_tsupport_subset (n := ⊤)
    (x := (0 : κ → ℝ)) (s := Set.univ) Filter.univ_mem
  have hΦcs : HasCompactSupport (⇑Complex.ofRealCLM ∘ u) := hu_cs.comp_left (map_zero _)
  have hΦsm := Complex.ofRealCLM.contDiff.comp hu_sm
  have hI := (hsch (hΦcs.toSchwartzMap hΦsm)).2
  exact SelfDual.eq_of_test hν hμ (⇑Complex.ofRealCLM ∘ u) hΦsm.continuous hΦcs hI 0
    (by simp [hu0])

end GlobalTheory.SelfDualDiagReal
