import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BhattScholzeCoefficientsOfPadicIntLattices
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.bhattScholze_coeff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FBhattScholzeCoefficientsOfPadicIntLattices.lean&line=98#L98)
-/
theorem _root_.GlobalTheory.T.bhattScholze_coefficients_of_padicInt_lattices : GlobalTheory.Published.BhattScholzeIntegral → GlobalTheory.Published.BhattScholzeCrystallineLattices := by
  first | exact @GlobalTheory.bhattScholze_coeff | exact GlobalTheory.bhattScholze_coeff | (intros; apply GlobalTheory.bhattScholze_coeff <;> assumption)
