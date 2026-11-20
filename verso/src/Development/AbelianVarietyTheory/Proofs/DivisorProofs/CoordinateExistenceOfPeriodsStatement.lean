import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoordinateExistenceOfPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatJet.An.coordEx` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoordinateExistenceOfPeriods.lean&line=78#L78)
-/
theorem _root_.GlobalTheory.T.coordinate_existence_of_periods : GlobalTheory.Published.GaussManinPeriods → JetCalc → DiagFrame → CoordEx := by
  first | exact @GlobalTheory.LatJet.An.coordEx | exact GlobalTheory.LatJet.An.coordEx | (intros; apply GlobalTheory.LatJet.An.coordEx <;> assumption)
