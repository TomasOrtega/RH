import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CardH1EqCardH0MulCardH2

namespace GlobalTheory.Laid

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler.localEulerChar_holds`.
-/
theorem loceuler_holds : ReciprocityTheory.Gal.LocalEulerChar := GlobalTheory.CompanionTheory.Hypotheses₂.LocalEuler.localEulerChar_holds

end GlobalTheory.Laid
