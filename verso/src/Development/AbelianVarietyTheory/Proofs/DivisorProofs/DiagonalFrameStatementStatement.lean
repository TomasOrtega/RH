import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiagonalFrameStatement
import Development.AbelianVarietyTheory.Definitions.Divisors.StepsNonvacuous
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PeriodComparison
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GrothendieckDeformation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
open GlobalTheory.LatVal GlobalTheory.LatJet GlobalTheory.LatJet.An
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.DiagAH.diagFrame` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDiagonalFrameStatement.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.diagonal_frame_statement : DiagFrame := by
  first | exact @GlobalTheory.DiagAH.diagFrame | exact GlobalTheory.DiagAH.diagFrame | (intros; apply GlobalTheory.DiagAH.diagFrame <;> assumption)
