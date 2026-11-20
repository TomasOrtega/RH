import Mathlib
import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.KFiniteVectors.LocalWhittakerDuality.WSteps
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WeilModulusHypothesis
open MeasureTheory Matrix GroundTheory.LocalField GroundTheory.Automorphic Ad3 Ad3.K.GL2LocalData
open scoped ValuativeRel

noncomputable section

namespace GlobalTheory.CompanionTheory.WeilTorus

/- English proof (translation)
Establish `he : MeasurableEmbedding (fun x : K => (t : K) * x)` using `(Homeomorph.mulLeft₀ (t : K) t.ne_zero).measurableEmbedding`. Rewrite using `[← he.integral_map, map_mul_left_eq_smul μ t.ne_zero, integral_smul_nnreal_measure]`. Simplify using `[NNReal.smul_def]`.
-/
theorem integral_comp_unit_mul {K : Type} [Field K] [ValuativeRel K] [TopologicalSpace K]
    [IsNonarchimedeanLocalField K] [MeasurableSpace K] [BorelSpace K]
    (μ : Measure K) [μ.IsAddHaarMeasure] (t : Kˣ) (f : K → ℂ) :
    ∫ u, f ((t : K) * u) ∂μ = ((modulus (t : K) : ℝ) : ℂ)⁻¹ * ∫ x, f x ∂μ := by
  have he : MeasurableEmbedding (fun x : K => (t : K) * x) :=
    (Homeomorph.mulLeft₀ (t : K) t.ne_zero).measurableEmbedding
  rw [← he.integral_map, map_mul_left_eq_smul μ t.ne_zero, integral_smul_nnreal_measure]
  simp [NNReal.smul_def]

/- English proof (translation)
Introduce `F _ _ _ _ _ _ _ χ hχc hχ E _ _ _ _ _ _ _ hd hc σ hσ η hη g hg s Φ _`. Establish `hmul : ∀ a b : F, a ≠ 0 → b ≠ 0 → nsg E (a * b) = nsg E a * nsg E b`. Introduce `a b ha hb`. Establish `h1` using `hη (Units.mk0 a ha * Units.mk0 b hb)`. Rewrite `h1` using `[map_mul, Units.val_mul, hη, hη]`.

Simplify using `using h1.symm`. Establish `hs : (s : F) ≠ 0` using `s.ne_zero`. Establish `hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1`. Rewrite using `[← hg, Matrix.det_fin_two]`. Establish `hmod : ((modulus (algebraMap F E (s : F)) : ℝ)) = (modulus (s : F) : ℝ) ^ 2`.

Establish `h` using `GlobalTheory.CompanionTheory.NormModulus.wMod F χ hχc hχ E hd hc σ hσ η hη (algebraMap F E (s : F))`. Rewrite using `[h, Algebra.norm_algebraMap, hd, GlobalTheory.CompanionTheory.NormModulus.modulus_pow_nat]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hN : ∀ u : E, Algebra.norm F (algebraMap F E (s : F) * u) = (s : F) ^ 2 * Algebra.norm F u`.

Introduce `u`. Rewrite using `[map_mul, Algebra.norm_algebraMap, hd]`. Use function extensionality and compare the values at `z`. Establish `e00 : (g * !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)]) 0 0 = g 0 0 * s`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`.

Establish `e01 : (g * !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)]) 0 1 = g 0 1 * (s : F)⁻¹`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e10 : (g * !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)]) 1 0 = g 1 0 * s`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`. Establish `e11 : (g * !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)]) 1 1 = g 1 1 * (s : F)⁻¹`.

Simplify using `[Matrix.mul_apply, Fin.sum_univ_two]`. Establish `hm : rWE E χ σ η !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)] Φ = fun u => nsg E (s : F) * ((modulus (s : F) : ℝ) : ℂ) * Φ (algebraMap F E (s : F) * u)`. Use function extensionality and compare the values at `u`. Simplify using `[rWm, rW]`. Rewrite using `[hm]`.

Simplify using `only [rWm]`. Rewrite using `[e00, e01, e10, e11]`. Distinguish the cases in `hc0 : g 1 0 = 0`. Establish `ha : g 0 0 ≠ 0`. Introduce `h`.

Rewrite `hdet` using `[h, hc0]`. Simplify using `at hdet`. Rewrite using `[rW, rW, if_pos (by rw [hc0, zero_mul]), if_pos hc0, hmul _ _ ha hs, modulus_mul]`. Establish `e1 : g 0 0 * (s : F) * (g 0 1 * (s : F)⁻¹) = g 0 0 * g 0 1`. Clear the denominators using the available nonvanishing facts.

Establish `e2 : algebraMap F E (g 0 0 * (s : F)) * z = algebraMap F E (s : F) * (algebraMap F E (g 0 0) * z)`. Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e1, e2]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hcs : g 1 0 * (s : F) ≠ 0` using `mul_ne_zero hc0 hs`. Rewrite using `[rW, rW, if_neg hcs, if_neg hc0]`. Establish `hneg : -(g 1 0 * (s : F)) = -g 1 0 * s` using `by ring`. Rewrite using `[hneg, hmul _ _ (neg_ne_zero.2 hc0) hs, modulus_mul]`.

Use `set tE : Eˣ := Units.map (algebraMap F E).toMonoidHom s with htE`. Establish `htv : (tE : E) = algebraMap F E (s : F)` using `rfl`. Use `set f : E → ℂ := fun u => (χ ((g 0 0 * (s : F) * Algebra.norm F z + g 1 1 * (s : F)⁻¹ * Algebra.norm F u - Algebra.trace F E (σ z * u)) / (g 1 0 * (s : F))) : ℂ) * Φ u with hf`. Establish `hint` using `integral_comp_unit_mul (muE E χ) tE f`. Establish `hfe : ∀ u, f ((tE : E) * u) = (χ ((g 0 0 * Algebra.norm F z + g 1 1 * Algebra.norm F u - Algebra.trace F E (σ z * u)) / g 1 0) : ℂ) * Φ (algebraMap F E (s : F) * u)`.

Introduce `u`. Establish `htr : Algebra.trace F E (σ z * (algebraMap F E (s : F) * u)) = (s : F) * Algebra.trace F E (σ z * u)`. Rewrite using `[show σ z * (algebraMap F E (s : F) * u) = (s : F) • (σ z * u) by`. Rewrite using `[Algebra.smul_def]`. Use the proof step `ring, map_smul, smul_eq_mul]`.

Simplify using `only [hf, htv]`. Rewrite using `[hN, htr]`. Use `congr 3`. Clear the denominators using the available nonvanishing facts. Simplify using `only [hfe] at hint`.

Establish `hmodE : ((modulus (tE : E) : ℝ) : ℂ) = ((modulus (s : F) : ℝ) : ℂ) ^ 2`. Rewrite using `[htv, hmod]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hs0 : ((modulus (s : F) : ℝ) : ℂ) ≠ 0`.

Conclude with `modulus_ne_zero hs` after adjusting the coercions. Establish `hI : ∫ x, f x ∂muE E χ = ((modulus (s : F) : ℝ) : ℂ) ^ 2 * ∫ u, (χ ((g 0 0 * Algebra.norm F z + g 1 1 * Algebra.norm F u - Algebra.trace F E (σ z * u)) / g 1 0) : ℂ) * Φ (algebraMap F E (s : F) * u) ∂muE E χ`. Rewrite using `[hint, hmodE]`. Clear the denominators using the available nonvanishing facts. Establish `hR : ∫ u, (χ ((g 0 0 * Algebra.norm F z + g 1 1 * Algebra.norm F u - Algebra.trace F E (σ z * u)) / g 1 0) : ℂ) * (nsg E (s : F) * ((modulus (s : F) : ℝ) : ℂ) * Φ (algebraMap F E (s : F) * u)) ∂muE E χ = nsg E (s : F) * ((modulus (s : F) : ℝ) : ℂ) * ∫ u, (χ ((g 0 0 * Algebra.norm …`.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `u`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hR, show (∫ u, (χ ((g 0 0 * (s : F) * Algebra.norm F z + g 1 1 * (s : F)⁻¹ * Algebra.norm F u - Algebra.trace F E (σ z * u)) / (g 1 0 * (s : F))) : ℂ) * Φ u ∂muE E χ) = ∫ x, f x ∂muE E χ from rfl, hI]`.

Establish `hc1 : ((modulus (g 1 0) : ℝ) : ℂ) ≠ 0`. Conclude with `modulus_ne_zero hc0` after adjusting the coercions. Generalize the expression as in `(∫ u, (χ ((g 0 0 * Algebra.norm F z + g 1 1 * Algebra.norm F u - Algebra.trace F E (σ z * u)) / g 1 0) : ℂ) * Φ (algebraMap F E (s : F) * u) ∂muE E χ) = J`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem wRepM : Ad3.K.GL2LocalData.WRepM := by
  intro F _ _ _ _ _ _ _ χ hχc hχ E _ _ _ _ _ _ _ hd hc σ hσ η hη g hg s Φ _
  have hmul : ∀ a b : F, a ≠ 0 → b ≠ 0 → nsg E (a * b) = nsg E a * nsg E b := by
    intro a b ha hb
    have h1 := hη (Units.mk0 a ha * Units.mk0 b hb)
    rw [map_mul, Units.val_mul, hη, hη] at h1
    simpa using h1.symm
  have hs : (s : F) ≠ 0 := s.ne_zero
  have hdet : g 0 0 * g 1 1 - g 0 1 * g 1 0 = 1 := by
    rw [← hg, Matrix.det_fin_two]
  have hmod : ((modulus (algebraMap F E (s : F)) : ℝ)) = (modulus (s : F) : ℝ) ^ 2 := by
    have h := GlobalTheory.CompanionTheory.NormModulus.wMod F χ hχc hχ E hd hc σ hσ η hη (algebraMap F E (s : F))
    rw [h, Algebra.norm_algebraMap, hd, GlobalTheory.CompanionTheory.NormModulus.modulus_pow_nat]
    push_cast
    rfl
  have hN : ∀ u : E, Algebra.norm F (algebraMap F E (s : F) * u) = (s : F) ^ 2 * Algebra.norm F u := by
    intro u
    rw [map_mul, Algebra.norm_algebraMap, hd]
  funext z
  have e00 : (g * !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)]) 0 0 = g 0 0 * s := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e01 : (g * !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)]) 0 1 = g 0 1 * (s : F)⁻¹ := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e10 : (g * !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)]) 1 0 = g 1 0 * s := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have e11 : (g * !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)]) 1 1 = g 1 1 * (s : F)⁻¹ := by
    simp [Matrix.mul_apply, Fin.sum_univ_two]
  have hm : rWE E χ σ η !![(s : F), 0; 0, ((s⁻¹ : Fˣ) : F)] Φ =
      fun u => nsg E (s : F) * ((modulus (s : F) : ℝ) : ℂ) * Φ (algebraMap F E (s : F) * u) := by
    funext u
    simp [rWm, rW]
  rw [hm]
  simp only [rWm]
  rw [e00, e01, e10, e11]
  by_cases hc0 : g 1 0 = 0
  · have ha : g 0 0 ≠ 0 := by
      intro h
      rw [h, hc0] at hdet
      simp at hdet
    rw [rW, rW, if_pos (by rw [hc0, zero_mul]), if_pos hc0, hmul _ _ ha hs, modulus_mul]
    have e1 : g 0 0 * (s : F) * (g 0 1 * (s : F)⁻¹) = g 0 0 * g 0 1 := by
      field_simp
    have e2 : algebraMap F E (g 0 0 * (s : F)) * z = algebraMap F E (s : F) * (algebraMap F E (g 0 0) * z) := by
      rw [map_mul]; ring
    rw [e1, e2]
    push_cast
    ring
  · have hcs : g 1 0 * (s : F) ≠ 0 := mul_ne_zero hc0 hs
    rw [rW, rW, if_neg hcs, if_neg hc0]
    have hneg : -(g 1 0 * (s : F)) = -g 1 0 * s := by ring
    rw [hneg, hmul _ _ (neg_ne_zero.2 hc0) hs, modulus_mul]
    set tE : Eˣ := Units.map (algebraMap F E).toMonoidHom s with htE
    have htv : (tE : E) = algebraMap F E (s : F) := rfl
    set f : E → ℂ := fun u => (χ ((g 0 0 * (s : F) * Algebra.norm F z + g 1 1 * (s : F)⁻¹ * Algebra.norm F u -
      Algebra.trace F E (σ z * u)) / (g 1 0 * (s : F))) : ℂ) * Φ u with hf
    have hint := integral_comp_unit_mul (muE E χ) tE f
    have hfe : ∀ u, f ((tE : E) * u) =
        (χ ((g 0 0 * Algebra.norm F z + g 1 1 * Algebra.norm F u -
          Algebra.trace F E (σ z * u)) / g 1 0) : ℂ) * Φ (algebraMap F E (s : F) * u) := by
      intro u
      have htr : Algebra.trace F E (σ z * (algebraMap F E (s : F) * u)) =
          (s : F) * Algebra.trace F E (σ z * u) := by
        rw [show σ z * (algebraMap F E (s : F) * u) = (s : F) • (σ z * u) by
          rw [Algebra.smul_def]; ring, map_smul, smul_eq_mul]
      simp only [hf, htv]
      rw [hN, htr]
      congr 3
      field_simp
    simp only [hfe] at hint
    have hmodE : ((modulus (tE : E) : ℝ) : ℂ) = ((modulus (s : F) : ℝ) : ℂ) ^ 2 := by
      rw [htv, hmod]
      push_cast
      rfl
    have hs0 : ((modulus (s : F) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast modulus_ne_zero hs
    have hI : ∫ x, f x ∂muE E χ = ((modulus (s : F) : ℝ) : ℂ) ^ 2 * ∫ u,
        (χ ((g 0 0 * Algebra.norm F z + g 1 1 * Algebra.norm F u -
          Algebra.trace F E (σ z * u)) / g 1 0) : ℂ) * Φ (algebraMap F E (s : F) * u) ∂muE E χ := by
      rw [hint, hmodE]
      field_simp
    have hR : ∫ u, (χ ((g 0 0 * Algebra.norm F z + g 1 1 * Algebra.norm F u -
          Algebra.trace F E (σ z * u)) / g 1 0) : ℂ) *
          (nsg E (s : F) * ((modulus (s : F) : ℝ) : ℂ) * Φ (algebraMap F E (s : F) * u)) ∂muE E χ =
        nsg E (s : F) * ((modulus (s : F) : ℝ) : ℂ) * ∫ u,
        (χ ((g 0 0 * Algebra.norm F z + g 1 1 * Algebra.norm F u -
          Algebra.trace F E (σ z * u)) / g 1 0) : ℂ) * Φ (algebraMap F E (s : F) * u) ∂muE E χ := by
      rw [← integral_const_mul]
      congr 1
      funext u
      ring
    rw [hR, show (∫ u, (χ ((g 0 0 * (s : F) * Algebra.norm F z + g 1 1 * (s : F)⁻¹ * Algebra.norm F u -
      Algebra.trace F E (σ z * u)) / (g 1 0 * (s : F))) : ℂ) * Φ u ∂muE E χ) = ∫ x, f x ∂muE E χ from rfl, hI]
    have hc1 : ((modulus (g 1 0) : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast modulus_ne_zero hc0
    generalize (∫ u, (χ ((g 0 0 * Algebra.norm F z + g 1 1 * Algebra.norm F u -
      Algebra.trace F E (σ z * u)) / g 1 0) : ℂ) * Φ (algebraMap F E (s : F) * u) ∂muE E χ) = J
    push_cast
    field_simp

end GlobalTheory.CompanionTheory.WeilTorus
