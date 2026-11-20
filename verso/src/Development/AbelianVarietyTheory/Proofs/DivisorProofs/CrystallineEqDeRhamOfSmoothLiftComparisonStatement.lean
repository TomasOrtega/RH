import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CrystallineEqDeRhamOfSmoothLiftComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.BijectiveCechDeRhamComparisonDegreeOne
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCrystallineEqDeRhamOfSmoothLiftComparison.lean&line=72#L72)
-/
theorem _root_.GlobalTheory.T.crystalline_eq_deRham_of_smoothLift_comparison : GlobalTheory.Published.CrystallineSmoothLift → GlobalTheory.Published.CrystallineDeRham := by
  first | exact @GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift | exact GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift | (intros; apply GlobalTheory.CrysLift.crystallineDeRham_of_smoothLift <;> assumption)
