import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FourierJacobiCoefficientOfBound
import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.HeckeEta
open PositivityTheory.Rg.Rsw
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FFourierJacobiCoefficientOfBound.lean&line=50#L50)
-/
theorem _root_.GlobalTheory.T.fourier_jacobi_coefficient_of_bound : PcBound → CfFJ := by
  first | exact @GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound | exact GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound | (intros; apply GlobalTheory.CompanionTheory.CfFJ.cfFJ_of_pcBound <;> assumption)
