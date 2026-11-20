import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityPowerFormula
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FMultiplicityPowerFormula.lean&line=28#L28)
-/
theorem _root_.GlobalTheory.T.multiplicity_power_formula : PositivityTheory.SiegelWeilFormula.Gunr.NuPow := by
  first | exact @GlobalTheory.CompanionTheory.GunrNu.nuPow | exact GlobalTheory.CompanionTheory.GunrNu.nuPow | (intros; apply GlobalTheory.CompanionTheory.GunrNu.nuPow <;> assumption)
