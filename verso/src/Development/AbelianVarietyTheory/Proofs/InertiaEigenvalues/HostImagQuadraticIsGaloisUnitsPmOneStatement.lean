import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HostImagQuadraticIsGaloisUnitsPmOne
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
open NumberField
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FHostImagQuadraticIsGaloisUnitsPmOne.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.host_imagQuadratic_isGalois_units_pm_one : ∀ D : Formalism.BasicNotions.D7, IsGalois ℚ D.host.K ∧ ∀ u : (𝓞 D.host.K)ˣ, u = 1 ∨ u = -1 := by
  first | exact @GlobalTheory.HostQuadUnits.main | exact GlobalTheory.HostQuadUnits.main | (intros; apply GlobalTheory.HostQuadUnits.main <;> assumption)
