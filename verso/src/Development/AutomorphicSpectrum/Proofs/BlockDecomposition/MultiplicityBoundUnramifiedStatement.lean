import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityBoundUnramified
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMultiplicityBoundUnramified.lean&line=215#L215)
-/
theorem _root_.GlobalTheory.T.multiplicity_bound_unramified : PositivityTheory.SiegelWeilFormula.Gunr.NuBound := by
  first | exact @GlobalTheory.CompanionTheory.GunrNuBound.nuBound | exact GlobalTheory.CompanionTheory.GunrNuBound.nuBound | (intros; apply GlobalTheory.CompanionTheory.GunrNuBound.nuBound <;> assumption)
