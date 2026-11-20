import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.WeilThetaConvergence.WeilThetaConvergenceOfSiegelSet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary

namespace PositivityTheory.Rg.Sw.Glob

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.WTC.weilThetaConvergence_of_core GlobalTheory.CompanionTheory.SiegelRed.siegelCore`.
-/
theorem wtc : GlobalTheory.Published.WeilThetaConvergence := GlobalTheory.CompanionTheory.WTC.weilThetaConvergence_of_core GlobalTheory.CompanionTheory.SiegelRed.siegelCore

end PositivityTheory.Rg.Sw.Glob
