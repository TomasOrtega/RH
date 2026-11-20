import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BetaConjugateMeanLogAbsBoundOfTransport
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LatticeNormTransport
open GlobalTheory.SqTop
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBetaConjugateMeanLogAbsBoundOfTransport.lean&line=43#L43)
-/
theorem _root_.GlobalTheory.T.betaConjugate_mean_logAbs_bound_of_transport : GlobalTheory.IndefiniteRowSideFullHecke.LatticeNormTransport.Transport → FieldDat → LBound → TorEx → BetaArch := by
  first | exact @GlobalTheory.SqTop.betaArch_of_transport | exact GlobalTheory.SqTop.betaArch_of_transport | (intros; apply GlobalTheory.SqTop.betaArch_of_transport <;> assumption)
