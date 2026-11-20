import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.WeilFormulaBesselUnitaryIntegrableStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupsClosedUnitaryWCompactStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnimodularBesselSubgroupsUWNStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFunctionalEquivariantUnipotentCharacterStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InnerBesselFunctionalEqIntegralSubgroupStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableMatrixCoefficientQuotientMeasureStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MatrixCoeffMulInnerBesselFunctionalEqIntegralStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IntegrableBesselFubiniIntegrandProdStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSchurTranslatedMatrixCoefficientStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselSubgroupIntegralEqInnerBesselFormStatement

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace

namespace GlobalTheory.SgInf

/- English proof (translation)
Introduce `k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ`. Establish `hHaarG : IsHaarOn (GG k r) μG` using `hStd.2.2.2.2.1`. Establish `hHaarS : IsHaarOn (Sset k r z) μS` using `hSide.2.2.2.1`. Use `haveI : SigmaFinite μG := hHaarG.1`. Use `haveI : SigmaFinite μS := hHaarS.1`.

Establish `hcl` using `GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1`. Establish `hF` using `GlobalTheory.T.integrable_bessel_fubini_integrand_prod k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ`. Establish `haeG : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r` using `ae_iff.2 hHaarG.2.2.1`. Establish `haeS : ∀ᵐ t ∂μS, Matrix.of t ∈ Sset k r z` using `ae_iff.2 hHaarS.2.2.1`. Establish `hae : ∀ᵐ y ∂μG, coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ = ∫ t, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS` using `haeG.mono fun y hy => GlobalTheory.T.matrixCoeff_mul_inner_besselFunctional_eq_integral k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ y hy`.

Use `⟨hF.integral_prod_left.congr (hae.mono fun y hy => hy.symm), ?_⟩` and prove the remaining obligations. Rewrite using `[integral_congr_ae hae, integral_integral_swap hF]`. Establish `hin : ∀ᵐ t ∂μS, (∫ y, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μG) = (⟪u₁, u⟫_ℂ / (d : ℂ)) * (⟪v, σ (Matrix.of t)⁻¹ v⟫_ℂ * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ)` using `by filter_upwards [haeS] with t ht`. Rewrite using `[integral_mul_const, GlobalTheory.T.besselSchur_translated_matrixCoefficient k r σ w a μG d hStd u u₁ v _ (hcl.2.2.2.1.1 ht)]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[integral_congr_ae hin, integral_const_mul, GlobalTheory.T.besselSubgroupIntegral_eq_inner_besselForm k r σ w a μG d z c π μS hStd hSide v hv ξ]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem phiIntegral_besselCoef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp,
    Integrable (fun y : Mt k r => coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ) μG ∧
    ∫ y, coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ ∂μG =
      ⟪u₁, u⟫_ℂ * ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ / (d : ℂ) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  have hHaarG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hHaarS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  haveI : SigmaFinite μG := hHaarG.1
  haveI : SigmaFinite μS := hHaarS.1
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hF := GlobalTheory.T.integrable_bessel_fubini_integrand_prod k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  have haeG : ∀ᵐ y ∂μG, Matrix.of y ∈ GG k r := ae_iff.2 hHaarG.2.2.1
  have haeS : ∀ᵐ t ∂μS, Matrix.of t ∈ Sset k r z := ae_iff.2 hHaarS.2.2.1
  have hae : ∀ᵐ y ∂μG, coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ =
      ∫ t, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) *
        ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μS :=
    haeG.mono fun y hy => GlobalTheory.T.matrixCoeff_mul_inner_besselFunctional_eq_integral k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ y hy
  refine ⟨hF.integral_prod_left.congr (hae.mono fun y hy => hy.symm), ?_⟩
  rw [integral_congr_ae hae, integral_integral_swap hF]
  have hin : ∀ᵐ t ∂μS, (∫ y, coef σ u v (Matrix.of y) * star (coef σ u₁ v (Matrix.of t * Matrix.of y)) *
        ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ ∂μG) =
      (⟪u₁, u⟫_ℂ / (d : ℂ)) * (⟪v, σ (Matrix.of t)⁻¹ v⟫_ℂ * ⟪PiS (psiGen k r z c) π (Matrix.of t)⁻¹ ξ, ξ⟫_ℂ) := by
    filter_upwards [haeS] with t ht
    rw [integral_mul_const, GlobalTheory.T.besselSchur_translated_matrixCoefficient k r σ w a μG d hStd u u₁ v _ (hcl.2.2.2.1.1 ht)]
    ring
  rw [integral_congr_ae hin, integral_const_mul, GlobalTheory.T.besselSubgroupIntegral_eq_inner_besselForm k r σ w a μG d z c π μS hStd hSide v hv ξ]
  ring

/- English proof (translation)
Introduce `k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν u hu u₁ hu₁ v hv ξ`. Establish `hHaarG : IsHaarOn (GG k r) μG` using `hStd.2.2.2.2.1`. Establish `hHaarS : IsHaarOn (Sset k r z) μS` using `hSide.2.2.2.1`. Establish `hcl` using `GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1`. Establish `hUnS` using `(GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hSide.1 hSide.2.1 μS).1 hHaarS`.

Take `⟨-, hνG, -, hWeil, -⟩` from `GlobalTheory.T.weil_formula_besselUnitary_integrable k r (Sset k r z) μG μS ν hcl.2.2.2.1 hHaarG hHaarS hUnS hν`. Take `⟨hφ, hφint⟩` from `phiIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ`. Take `⟨hWi, hWe⟩` from `hWeil ℂ _ hφ`. Establish `haeν : ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r` using `ae_iff.2 hνG`. Establish `hae : ∀ᵐ x ∂ν, (∫ s, (fun y : Mt k r => coef σ u v (Matrix.of y) * ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ) (lmulM (Matrix.of s) x) ∂μS) = ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ` using `haeν.mono fun x hx => (GlobalTheory.T.inner_besselFunctional_eq_integral_subgroup k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ x hx).symm`.

Use `⟨hWi.congr hae, ?_⟩` and prove the remaining obligations. Rewrite using `[← integral_congr_ae hae, ← hWe, hφint]`.
-/
theorem innerIntegral_besselCoef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)), Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν →
    ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp,
    Integrable (fun x : Mt k r => ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x),
      Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ) ν ∧
    ∫ x, ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ ∂ν =
      ⟪u₁, u⟫_ℂ * ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ / (d : ℂ) := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν u hu u₁ hu₁ v hv ξ
  have hHaarG : IsHaarOn (GG k r) μG := hStd.2.2.2.2.1
  have hHaarS : IsHaarOn (Sset k r z) μS := hSide.2.2.2.1
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hUnS := (GlobalTheory.T.unimodular_besselSubgroups_UW_N k r z hSide.1 hSide.2.1 μS).1 hHaarS
  obtain ⟨-, hνG, -, hWeil, -⟩ := GlobalTheory.T.weil_formula_besselUnitary_integrable k r (Sset k r z) μG μS ν hcl.2.2.2.1 hHaarG hHaarS hUnS hν
  obtain ⟨hφ, hφint⟩ := phiIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ
  obtain ⟨hWi, hWe⟩ := hWeil ℂ _ hφ
  have haeν : ∀ᵐ x ∂ν, Matrix.of x ∈ GG k r := ae_iff.2 hνG
  have hae : ∀ᵐ x ∂ν, (∫ s, (fun y : Mt k r => coef σ u v (Matrix.of y) *
        ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of y), ξ⟫_ℂ) (lmulM (Matrix.of s) x) ∂μS) =
      ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ :=
    haeν.mono fun x hx => (GlobalTheory.T.inner_besselFunctional_eq_integral_subgroup k r σ w a μG d z c π μS hStd hSide u hu u₁ hu₁ v hv ξ x hx).symm
  refine ⟨hWi.congr hae, ?_⟩
  rw [← integral_congr_ae hae, ← hWe, hφint]

/- English proof (translation)
Introduce `k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν u hu u₁ hu₁ v hv ξ`. Establish `hw1 : ‖w‖ = 1` using `hStd.2.2.2.1`. Establish `hd : 0 < d` using `hStd.2.2.2.2.2.1.1`. Establish `hcl` using `GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1`. Establish `hwD : w ∈ DD σ w`.

Establish `h1` using `mem_DD σ w hcl.1.2.2.1`. Rewrite `h1` using `[hStd.2.1.1.1, ContinuousLinearMap.one_apply]`. Then use the resulting hypothesis. Establish `hAi` using `GlobalTheory.T.integrable_matrixCoefficient_quotientMeasure k r σ w a μG d z c π μS hStd hSide ν hν u hu v hv ξ`. Take `⟨hIi, -⟩` from `innerIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν u hu u hu v hv ξ`. Establish `hIe` using `(innerIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν u hu u₁ hu₁ v hv ξ).2`.

Establish `hsq : Integrable (fun x : Mt k r => ‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖ ^ 2) ν`. Use `hIi.re.congr (Filter.Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Conclude with `inner_self_eq_norm_sq _`. Take `⟨-, hwe⟩` from `innerIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν w hwD w hwD v hv ξ`. Establish `hww : ⟪w, w⟫_ℂ = 1` using `by rw [inner_self_eq_norm_sq_to_K, hw1]; simp`.

Establish `hL : (∫ x, ⟪Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x)⟫_ℂ ∂ν) = ((∫ x, ‖Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x)‖ ^ 2 ∂ν : ℝ) : ℂ)`. Rewrite using `[← integral_complex_ofReal]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[inner_self_eq_norm_sq_to_K]`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite `hwe` using `[hL, hww, one_mul]`. Establish `hX : ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ = ((d * ∫ x, ‖Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x)‖ ^ 2 ∂ν : ℝ) : ℂ)`. Establish `hd' : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`.

Rewrite `hwe` using `[eq_div_iff hd']`. Rewrite using `[← hwe]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨GlobalTheory.T.besselFunctional_equivariant_unipotent_character k r σ w a μG d z c π μS hStd hSide u hu v hv ξ, hAi, (memLp_two_iff_integrable_sq_norm hAi.aestronglyMeasurable).2 hsq, hIe, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hX, Complex.ofReal_re]`. Conclude with `mul_nonneg hd.le (integral_nonneg fun x => by positivity)`. Rewrite using `[hX, Complex.ofReal_im]`.
-/
theorem normIdentity_besselCoef : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp] [CompleteSpace Wp] (σ : Mat k r → (H →L[ℂ] H)) (w : H) (a : ℝ) (μG : Measure (Mt k r)) (d : ℝ) (z : Fin (2 * r + k + 1) → ℂ) (c : Fin r → ℂ) (π : Mat k r → (Wp →L[ℂ] Wp)) (μS : Measure (Mt k r)) , Std σ w a μG d → Side z π μS → ∀ ν : Measure (Mt k r), IsQuotMeas μG μS ν → ∀ u ∈ DD σ w, ∀ u₁ ∈ DD σ w, ∀ v ∈ DD σ w, ∀ ξ : Wp, IsSPsiEquiv z (psiGen k r z c) π (Afun (psiGen k r z c) π μS σ u v ξ) ∧ Integrable (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) ν ∧ MemLp (fun x : Mt k r => Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)) 2 ν ∧ ∫ x, ⟪Afun (psiGen k r z c) π μS σ u₁ v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)⟫_ℂ ∂ν = ⟪u₁, u⟫_ℂ * ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ / (d : ℂ) ∧ 0 ≤ (⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ).re ∧ (⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ).im = 0 := by
  intro k r H _ _ _ Wp _ _ _ _ σ w a μG d z c π μS hStd hSide ν hν u hu u₁ hu₁ v hv ξ
  have hw1 : ‖w‖ = 1 := hStd.2.2.2.1
  have hd : 0 < d := hStd.2.2.2.2.2.1.1
  have hcl := GlobalTheory.T.bessel_subgroups_closed_unitaryW_compact k r z hSide.1 hSide.2.1
  have hwD : w ∈ DD σ w := by
    have h1 := mem_DD σ w hcl.1.2.2.1
    rwa [hStd.2.1.1.1, ContinuousLinearMap.one_apply] at h1
  have hAi := GlobalTheory.T.integrable_matrixCoefficient_quotientMeasure k r σ w a μG d z c π μS hStd hSide ν hν u hu v hv ξ
  obtain ⟨hIi, -⟩ := innerIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν u hu u hu v hv ξ
  have hIe := (innerIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν u hu u₁ hu₁ v hv ξ).2
  have hsq : Integrable (fun x : Mt k r => ‖Afun (psiGen k r z c) π μS σ u v ξ (Matrix.of x)‖ ^ 2) ν := by
    refine hIi.re.congr (Filter.Eventually.of_forall fun x => ?_)
    exact inner_self_eq_norm_sq _
  obtain ⟨-, hwe⟩ := innerIntegral_besselCoef k r σ w a μG d z c π μS hStd hSide ν hν w hwD w hwD v hv ξ
  have hww : ⟪w, w⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K, hw1]; simp
  have hL : (∫ x, ⟪Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x), Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x)⟫_ℂ ∂ν)
      = ((∫ x, ‖Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x)‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    congr 1; funext x
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  rw [hL, hww, one_mul] at hwe
  have hX : ⟪ξ, be (psiGen k r z c) π μS σ v v ξ⟫_ℂ =
      ((d * ∫ x, ‖Afun (psiGen k r z c) π μS σ w v ξ (Matrix.of x)‖ ^ 2 ∂ν : ℝ) : ℂ) := by
    have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
    rw [eq_div_iff hd'] at hwe
    rw [← hwe]; push_cast; ring
  refine ⟨GlobalTheory.T.besselFunctional_equivariant_unipotent_character k r σ w a μG d z c π μS hStd hSide u hu v hv ξ, hAi,
    (memLp_two_iff_integrable_sq_norm hAi.aestronglyMeasurable).2 hsq, hIe, ?_, ?_⟩
  · rw [hX, Complex.ofReal_re]
    exact mul_nonneg hd.le (integral_nonneg fun x => by positivity)
  · rw [hX, Complex.ofReal_im]

end GlobalTheory.SgInf
