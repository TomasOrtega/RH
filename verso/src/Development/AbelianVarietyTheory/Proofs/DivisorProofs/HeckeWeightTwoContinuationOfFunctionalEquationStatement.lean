import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeWeightTwoContinuationOfFunctionalEquation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OmegaFactorization
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.PartialZetaFunctionalEquation
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FHeckeWeightTwoContinuationOfFunctionalEquation.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.heckeWeightTwoContinuation_of_functionalEquation : GlobalTheory.Published.PartialZetaFunctionalEquation → GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.HeckeWeightTwo := by
  first | exact @GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe | exact GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe | (intros; apply GlobalTheory.HeckeTwo.heckeWeightTwo_of_fe <;> assumption)
