import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityLevelFormula
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SiegLoc.NuIndex.nuLev` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMultiplicityLevelFormula.lean&line=298#L298)
-/
theorem _root_.GlobalTheory.T.multiplicity_level_formula : PositivityTheory.SiegelWeilFormula.Gunr.NuLev := by
  first | exact @GlobalTheory.CompanionTheory.SiegLoc.NuIndex.nuLev | exact GlobalTheory.CompanionTheory.SiegLoc.NuIndex.nuLev | (intros; apply GlobalTheory.CompanionTheory.SiegLoc.NuIndex.nuLev <;> assumption)
