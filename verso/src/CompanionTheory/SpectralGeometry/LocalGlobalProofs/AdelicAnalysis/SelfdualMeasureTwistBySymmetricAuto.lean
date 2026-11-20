import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.SdChange

/- English proof (translation)
Introduce `V _ _ _ _ _ _ _ _ μ χ hsd B hsym c hc`. Take `⟨hHaar, hinv⟩` from `hsd`. Establish `hemb : MeasurableEmbedding B` using `(B.toHomeomorph).measurableEmbedding`. Establish `hc0 : c ≠ 0`. Introduce and unpack `rfl`.

Establish `h0 : μ.map B = 0` using `by simpa using hc`. Rewrite `h0` using `[Measure.map_eq_zero_iff hemb.measurable.aemeasurable]`. Conclude with `(NeZero.ne μ) h0`. Establish `hs0 : NNReal.sqrt c ≠ 0` using `by simpa using hc0`. Establish `hss : NNReal.sqrt c * NNReal.sqrt c = c` using `NNReal.mul_self_sqrt c`.

Generalize the expression as in `NNReal.sqrt c = s at hs0 hss ⊢`. Use `⟨Measure.IsAddHaarMeasure.nnreal_smul μ (inv_ne_zero hs0), ?_⟩` and prove the remaining obligations. Introduce `Φ _ _ hint z`. Set `H : V → ℂ` to `fun y => ∫ x, Φ x * χ x y ∂μ`. Establish `h1 : ∀ y, ∫ x, Φ x * χ x (B y) ∂(s⁻¹ • μ) = s⁻¹ • H (B y)` using `fun y => integral_smul_nnreal_measure _ _`.

Simplify using `only [h1] at hint ⊢`. Establish `hsE : ((s⁻¹ : ℝ≥0) : ℝ≥0∞) ≠ 0` using `by simpa using hs0`. Establish `hint2 : Integrable (fun y => H (B y)) μ`. Establish `h2 : Integrable (fun y => s⁻¹ • H (B y)) μ`. Establish `h3 : s⁻¹ • μ = ((s⁻¹ : ℝ≥0) : ℝ≥0∞) • μ` using `rfl`.

Rewrite `hint` using `[h3]`. Conclude with `(integrable_smul_measure hsE ENNReal.coe_ne_top).1 hint`. Establish `h4` using `h2.smul (s : ℝ)`. Use `h4.congr (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Establish `hsR : (s : ℝ) ≠ 0` using `by exact_mod_cast hs0`.

Establish `hsC : ((s : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast hsR`. Simplify using `[NNReal.smul_def, smul_smul]`. Rewrite using `[← mul_assoc, mul_inv_cancel₀ hsC, one_mul]`. Establish `hintH : Integrable H μ`. Establish `h5 : Integrable H (μ.map B)` using `(hemb.integrable_map_iff).2 hint2`.

Rewrite `h5` using `[hc]`. Establish `h6 : c • μ = (c : ℝ≥0∞) • μ` using `rfl`. Rewrite `h5` using `[h6]`. Conclude with `(integrable_smul_measure (by simpa using hc0) ENNReal.coe_ne_top).1 h5`. Establish `hI` using `hinv Φ ‹_› ‹_› hintH z`.

Establish `h7 : ∫ w, H w * χ w z ∂(μ.map B) = c • ∫ w, H w * χ w z ∂μ`. Rewrite using `[hc]`. Conclude with `integral_smul_nnreal_measure _ _`. Establish `h8 : ∫ w, H w * χ w z ∂(μ.map B) = ∫ y, H (B y) * χ (B y) z ∂μ` using `hemb.integral_map _`. Rewrite using `[integral_smul_nnreal_measure]`.

Establish `h9 : ∀ y, (s⁻¹ • H (B y)) * χ y (B z) = s⁻¹ • (H (B y) * χ (B y) z)`. Introduce `y`. Rewrite using `[hsym, smul_mul_assoc]`. Simplify using `only [h9]`. Establish `h10 : ∫ y, H (B y) * χ (B y) z ∂μ = c • Φ (-z)`.

Rewrite using `[← h8, h7]`. Conclude with `congrArg (c • ·) hI`. Establish `hsR : (s : ℝ) ≠ 0` using `by exact_mod_cast hs0`. Establish `hcR : (c : ℝ) = (s : ℝ) * s` using `by exact_mod_cast hss.symm`. Simplify using `only [NNReal.smul_def] at h10 ⊢`.

Rewrite using `[integral_smul, h10, smul_smul, smul_smul, hcR]`. Establish `h11 : (((s⁻¹ : ℝ≥0) : ℝ)) = (s : ℝ)⁻¹` using `by simp`. Rewrite using `[h11]`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules.
-/
theorem selfDual_twist : ∀ (V : Type) [AddCommGroup V] [TopologicalSpace V] [IsTopologicalAddGroup V]
    [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V]
    (μ : Measure V) (χ : V → V → ℂ), SelfDual μ χ → ∀ (B : V ≃ₜ+ V),
    (∀ x y, χ x (B y) = χ (B x) y) → ∀ c : ℝ≥0, μ.map B = c • μ →
    SelfDual ((NNReal.sqrt c)⁻¹ • μ) (fun x y => χ x (B y)) := by
  intro V _ _ _ _ _ _ _ _ μ χ hsd B hsym c hc
  obtain ⟨hHaar, hinv⟩ := hsd
  have hemb : MeasurableEmbedding B := (B.toHomeomorph).measurableEmbedding
  have hc0 : c ≠ 0 := by
    rintro rfl
    have h0 : μ.map B = 0 := by simpa using hc
    rw [Measure.map_eq_zero_iff hemb.measurable.aemeasurable] at h0
    exact (NeZero.ne μ) h0
  have hs0 : NNReal.sqrt c ≠ 0 := by simpa using hc0
  have hss : NNReal.sqrt c * NNReal.sqrt c = c := NNReal.mul_self_sqrt c
  generalize NNReal.sqrt c = s at hs0 hss ⊢
  refine ⟨Measure.IsAddHaarMeasure.nnreal_smul μ (inv_ne_zero hs0), ?_⟩
  intro Φ _ _ hint z
  let H : V → ℂ := fun y => ∫ x, Φ x * χ x y ∂μ
  have h1 : ∀ y, ∫ x, Φ x * χ x (B y) ∂(s⁻¹ • μ) = s⁻¹ • H (B y) :=
    fun y => integral_smul_nnreal_measure _ _
  simp only [h1] at hint ⊢
  have hsE : ((s⁻¹ : ℝ≥0) : ℝ≥0∞) ≠ 0 := by simpa using hs0
  have hint2 : Integrable (fun y => H (B y)) μ := by
    have h2 : Integrable (fun y => s⁻¹ • H (B y)) μ := by
      have h3 : s⁻¹ • μ = ((s⁻¹ : ℝ≥0) : ℝ≥0∞) • μ := rfl
      rw [h3] at hint
      exact (integrable_smul_measure hsE ENNReal.coe_ne_top).1 hint
    have h4 := h2.smul (s : ℝ)
    refine h4.congr (Filter.Eventually.of_forall fun y => ?_)
    have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs0
    have hsC : ((s : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hsR
    simp [NNReal.smul_def, smul_smul]
    rw [← mul_assoc, mul_inv_cancel₀ hsC, one_mul]
  have hintH : Integrable H μ := by
    have h5 : Integrable H (μ.map B) := (hemb.integrable_map_iff).2 hint2
    rw [hc] at h5
    have h6 : c • μ = (c : ℝ≥0∞) • μ := rfl
    rw [h6] at h5
    exact (integrable_smul_measure (by simpa using hc0) ENNReal.coe_ne_top).1 h5
  have hI := hinv Φ ‹_› ‹_› hintH z
  have h7 : ∫ w, H w * χ w z ∂(μ.map B) = c • ∫ w, H w * χ w z ∂μ := by
    rw [hc]; exact integral_smul_nnreal_measure _ _
  have h8 : ∫ w, H w * χ w z ∂(μ.map B) = ∫ y, H (B y) * χ (B y) z ∂μ :=
    hemb.integral_map _
  rw [integral_smul_nnreal_measure]
  have h9 : ∀ y, (s⁻¹ • H (B y)) * χ y (B z) = s⁻¹ • (H (B y) * χ (B y) z) := by
    intro y; rw [hsym, smul_mul_assoc]
  simp only [h9]
  have h10 : ∫ y, H (B y) * χ (B y) z ∂μ = c • Φ (-z) := by
    rw [← h8, h7]
    exact congrArg (c • ·) hI
  have hsR : (s : ℝ) ≠ 0 := by exact_mod_cast hs0
  have hcR : (c : ℝ) = (s : ℝ) * s := by exact_mod_cast hss.symm
  simp only [NNReal.smul_def] at h10 ⊢
  rw [integral_smul, h10, smul_smul, smul_smul, hcR]
  have h11 : (((s⁻¹ : ℝ≥0) : ℝ)) = (s : ℝ)⁻¹ := by simp
  rw [h11]
  field_simp
  simp

end GlobalTheory.CompanionTheory.SW.SdChange
