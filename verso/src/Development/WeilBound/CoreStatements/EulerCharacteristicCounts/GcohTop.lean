import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohField
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohMu
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohTate
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohFin

open CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal ValuativeRel

namespace PositivityTheory.LocalTateOrthogonality.Gcoh

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem top_tate : Formalism.GaloisCohomology.LocalTateDualityK := tate_of gcRep gc0 gc1 gc2 gcField gcMu

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem top_locfin : Formalism.GaloisCohomology.LocalFinitenessK := locfin_of gcField

end PositivityTheory.LocalTateOrthogonality.Gcoh
