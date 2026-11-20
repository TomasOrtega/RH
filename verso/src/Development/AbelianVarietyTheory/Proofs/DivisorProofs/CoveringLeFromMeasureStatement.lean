import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoveringLeFromMeasure
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
open GlobalTheory.CovTop GlobalTheory.BigTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FCoveringLeFromMeasure.lean&line=87#L87)
-/
theorem _root_.GlobalTheory.T.covering_le_from_measure : Gram → Meas → GlobalTheory.CovTop.Rat → CoreLe := by
  first | exact @GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat | exact GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat | (intros; apply GlobalTheory.CoreSlope.coreLe_of_gram_meas_rat <;> assumption)
