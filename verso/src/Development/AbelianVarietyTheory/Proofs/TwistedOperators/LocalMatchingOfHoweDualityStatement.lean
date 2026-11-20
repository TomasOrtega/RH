import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LocalMatchingOfHoweDuality
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FTwistedOperators%2FLocalMatchingOfHoweDuality.lean&line=25#L25)
-/
theorem _root_.GlobalTheory.T.local_matching_of_howe_duality : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → GlobalTheory.SquareSt.LocalMatching := by
  first | exact @GlobalTheory.SquareLM.localMatching | exact GlobalTheory.SquareLM.localMatching | (intros; apply GlobalTheory.SquareLM.localMatching <;> assumption)
