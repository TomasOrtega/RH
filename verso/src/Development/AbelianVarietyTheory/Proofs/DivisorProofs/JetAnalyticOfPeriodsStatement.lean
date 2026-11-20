import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.JetAnalyticOfPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.LatJet.An.jetAnalytic_of_periods` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FJetAnalyticOfPeriods.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.jet_analytic_of_periods : GlobalTheory.Published.GaussManinPeriods → GlobalTheory.Published.PeriodComparison → GlobalTheory.Published.HilbertBlumenthal → GlobalTheory.Published.GrothendieckDeformation → GlobalTheory.Published.AbelianDeRham → GlobalTheory.Published.AbelianDualCrystal → GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates.Statement → JetAnalytic := by
  first | exact @GlobalTheory.LatJet.An.jetAnalytic_of_periods | exact GlobalTheory.LatJet.An.jetAnalytic_of_periods | (intros; apply GlobalTheory.LatJet.An.jetAnalytic_of_periods <;> assumption)
