import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TowerOfThetaMatching
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
open GlobalTheory.SqTop
/- English proof (citation)
Apply `GlobalTheory.SqTower.tower` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FTowerOfThetaMatching.lean&line=174#L174)
-/
theorem _root_.GlobalTheory.T.tower_of_theta_matching : GlobalTheory.FunPr.Hypotheses₂ → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.ThetaIntegralsAgree → GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.LocalMatching → LNe → Tower := by
  first | exact @GlobalTheory.SqTower.tower | exact GlobalTheory.SqTower.tower | (intros; apply GlobalTheory.SqTower.tower <;> assumption)
