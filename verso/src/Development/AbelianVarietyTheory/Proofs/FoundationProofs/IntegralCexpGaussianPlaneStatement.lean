import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralCexpGaussianPlane
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsPosHermFormV
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IntMIffInt
open Complex MeasureTheory GlobalTheory.UnitaryTheta
open scoped BigOperators ComplexConjugate Real Classical
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.UnitaryTheta.integral_cexp_gaussian_plane` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FIntegralCexpGaussianPlane.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.integral_cexp_complex_gaussian_linear : ∀ l u v : ℂ, 0 < l.re → Integrable (fun z : ℂ => cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v))) ∧ ∫ z : ℂ, cexp (-(π : ℂ) * l * (z * conj z) + π * (u * conj z) + π * (z * conj v)) = l⁻¹ * cexp (π * (u * conj v) / l) := by
  first | exact @GlobalTheory.UnitaryTheta.integral_cexp_gaussian_plane | exact GlobalTheory.UnitaryTheta.integral_cexp_gaussian_plane | (intros; apply GlobalTheory.UnitaryTheta.integral_cexp_gaussian_plane <;> assumption)
