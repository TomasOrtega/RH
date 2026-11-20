import Mathlib
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.SiegelSetUnitary
import Development.WeilBound.ThetaLifts.Reductions.SiegelOfCore

namespace PositivityTheory.Prw

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem siegelCore_holds : PositivityTheory.ThKR.SiegelCore :=
  GlobalTheory.CompanionTheory.SiegelRed.siegelCore

end PositivityTheory.Prw
