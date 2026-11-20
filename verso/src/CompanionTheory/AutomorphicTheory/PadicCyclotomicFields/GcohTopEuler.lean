import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohTop
import CompanionTheory.AutomorphicTheory.PadicCyclotomicFields.GcohEuler

namespace CompanionTheory.LocalTateOrthogonality.Gcoh

/- English proof (translation)
The claim follows from `euler_of gcRep gc0 gc1 gc2 gcField`.
-/
theorem top_euler : Formalism.GaloisCohomology.LocalEulerCharK := euler_of gcRep gc0 gc1 gc2 gcField

end CompanionTheory.LocalTateOrthogonality.Gcoh
