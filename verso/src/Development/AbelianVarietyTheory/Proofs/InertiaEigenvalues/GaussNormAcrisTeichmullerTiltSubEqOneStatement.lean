import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.GaussNormAcrisTeichmullerTiltSubEqOne
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FGaussNormAcrisTeichmullerTiltSubEqOne.lean&line=23#L23)
-/
theorem _root_.GlobalTheory.T.gaussNormAcris_teichmuller_tilt_sub_eq_one : ∀ (l : ℕ) [Fact l.Prime] (ζ ζ' : Formalism.Per.Fl l), ‖(((ζ - ζ').untilt : Formalism.Per.OC l) : ℂ_[l])‖ = 1 → ∀ ρ : ℝ, (l : ℝ)⁻¹ ≤ ρ → ρ < 1 → gC l ρ (tc l ζ - tc l ζ') = 1 := by
  first | exact @GlobalTheory.PMon.Gauss.gC_teich_sub_eq_one | exact GlobalTheory.PMon.Gauss.gC_teich_sub_eq_one | (intros; apply GlobalTheory.PMon.Gauss.gC_teich_sub_eq_one <;> assumption)
