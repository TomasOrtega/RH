import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsPrimeMemAsIdeal
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.DualityForAbsGal
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardH1EqCardH0MulCardH2
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ContinuousCompOfIsOpenKer

namespace GlobalTheory.CompanionTheory.Hypotheses₂

/- English proof (translation)
The claim follows from `UnrOrth.unramifiedOrthogonality_of localFiniteness localTateDuality LocalEuler.localEulerChar_holds`.
-/
theorem unramifiedOrthogonality : ReciprocityTheory.Gal.UnramifiedOrthogonality :=
  UnrOrth.unramifiedOrthogonality_of localFiniteness localTateDuality
    LocalEuler.localEulerChar_holds

end GlobalTheory.CompanionTheory.Hypotheses₂
