import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BottomConstantOfTheta
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBottomConstantOfTheta.lean&line=61#L61)
-/
theorem _root_.GlobalTheory.T.bottom_constant_of_theta : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → (∀ D, GlobalTheory.NormSum.Inp D) → BotSmall → LNe → BotConst := by
  first | exact @GlobalTheory.SqTop.botConst_of_inputs | exact GlobalTheory.SqTop.botConst_of_inputs | (intros; apply GlobalTheory.SqTop.botConst_of_inputs <;> assumption)
