import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.MultiplicityPowerFormula
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.CProps
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @GlobalTheory.CompanionTheory.GunrNu.nuPow | exact GlobalTheory.CompanionTheory.GunrNu.nuPow | (intros; apply GlobalTheory.CompanionTheory.GunrNu.nuPow <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.multiplicity_power_formula : PositivityTheory.SiegelWeilFormula.Gunr.NuPow := by
  first | exact @GlobalTheory.CompanionTheory.GunrNu.nuPow | exact GlobalTheory.CompanionTheory.GunrNu.nuPow | (intros; apply GlobalTheory.CompanionTheory.GunrNu.nuPow <;> assumption)
