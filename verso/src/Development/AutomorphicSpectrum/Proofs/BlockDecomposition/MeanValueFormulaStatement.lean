import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MeanValueFormula
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.BinaryMassMeans.MeanVal
open PositivityTheory.Rg.Mass
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMeanValueFormula.lean&line=362#L362)
-/
theorem _root_.GlobalTheory.T.mean_value_formula : Equi → CountBd → MeanVal := by
  first | exact @GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd | exact GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd | (intros; apply GlobalTheory.CompanionTheory.Mass.MeanV.meanVal_of_equi_countBd <;> assumption)
