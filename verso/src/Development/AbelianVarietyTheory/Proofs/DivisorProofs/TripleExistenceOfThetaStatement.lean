import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleExistenceOfTheta
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.HoweDualityReal
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SqTop.triEx_holds` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTripleExistenceOfTheta.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.triple_existence_of_theta : GlobalTheory.Published.HoweDualityReal → GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → TriEx := by
  first | exact @GlobalTheory.SqTop.triEx_holds | exact GlobalTheory.SqTop.triEx_holds | (intros; apply GlobalTheory.SqTop.triEx_holds <;> assumption)
