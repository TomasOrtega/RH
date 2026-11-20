import Mathlib
import ReciprocityTheory.Hypotheses.GalCoh
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohFin
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohField
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.ExistsPrimeMemAsIdeal

namespace GlobalTheory.Laid

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.Hypotheses₂.localFiniteness`.
-/
theorem locfin_holds : ReciprocityTheory.Gal.LocalFiniteness := GlobalTheory.CompanionTheory.Hypotheses₂.localFiniteness

end GlobalTheory.Laid
