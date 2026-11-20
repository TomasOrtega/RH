import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsTiltRootOfUnityApproxRatio
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsGauss
open GlobalTheory.PMon.Gauss
open scoped Formalism.Per
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FExistsTiltRootOfUnityApproxRatio.lean&line=67#L67)
-/
theorem _root_.GlobalTheory.T.exists_tilt_root_of_unity_approx_ratio : ∀ (l : ℕ) [Fact l.Prime] (y y' : Formalism.Per.Fl l), y' ≠ 0 → ‖(((y).untilt : Formalism.Per.OC l) : ℂ_[l])‖ = ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ → ∃ (ζ : Formalism.Per.Fl l) (o : ℕ), 0 < o ∧ ζ ^ (l ^ o) = ζ ∧ ζ ≠ 0 ∧ ‖(((y - ζ * y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ < ‖(((y').untilt : Formalism.Per.OC l) : ℂ_[l])‖ := by
  first | exact @GlobalTheory.TiltRootApprox.exists_root_approx | exact GlobalTheory.TiltRootApprox.exists_root_approx | (intros; apply GlobalTheory.TiltRootApprox.exists_root_approx <;> assumption)
