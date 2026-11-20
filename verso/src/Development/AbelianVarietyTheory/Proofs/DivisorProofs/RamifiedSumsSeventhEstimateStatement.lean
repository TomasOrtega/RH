import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RamifiedSumsSeventhEstimate
import Development.AbelianVarietyTheory.Definitions.Divisors.TwistedPlaceChoiceLiesOverPair
open Formalism.BasicNotions Formalism.MainNotions NumberField Formalism.L2.Indef Formalism.L2.Indef.Tree GlobalTheory.BigTop GlobalTheory.BigTop.Fun
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FRamifiedSumsSeventhEstimate.lean&line=131#L131)
-/
theorem _root_.GlobalTheory.T.ramified_sum_bound : RamifiedSumBound := by
  first | exact @GlobalTheory.BigTop.Fun.ramified_sums_seventh_bound | exact GlobalTheory.BigTop.Fun.ramified_sums_seventh_bound | (intros; apply GlobalTheory.BigTop.Fun.ramified_sums_seventh_bound <;> assumption)
