import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTop
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohEuler

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

/- English proof (translation)
The claim follows from `euler_of gcRep gc0 gc1 gc2 gcField`.
-/
theorem top_euler : Formalism.GaloisCohomology.LocalEulerCharK := euler_of gcRep gc0 gc1 gc2 gcField

end PositivityTheory.LocalTateOrthogonality.Gcoh
