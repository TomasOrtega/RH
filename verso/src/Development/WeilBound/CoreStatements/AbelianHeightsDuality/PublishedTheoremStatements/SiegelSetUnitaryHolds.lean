import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore

namespace PositivityTheory.Prw

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.SiegelRed.siegelCore`.
-/
theorem siegelCore_holds : PositivityTheory.ThKR.SiegelCore :=
  GlobalTheory.CompanionTheory.SiegelRed.siegelCore

end PositivityTheory.Prw
