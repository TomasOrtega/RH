import Mathlib
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTopEuler
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.UnramifiedOrthogonality

namespace GlobalTheory

/- English proof (translation)
The claim follows from `GlobalTheory.CompanionTheory.Hypotheses₂.unramifiedOrthogonality`.
-/
theorem unramifiedOrthogonality_holds : ReciprocityTheory.Gal.UnramifiedOrthogonality :=
  GlobalTheory.CompanionTheory.Hypotheses₂.unramifiedOrthogonality

end GlobalTheory
