import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ClozelCohomologicalOfThree
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.ArchimedeanWhittakerDerivatives.HasDerivAtDpsi
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.CochainExpansions.CochainHolds
import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.KugaCoordinates.KugaGluing.KugaGlueHolds

namespace PositivityTheory.Rg.Cz

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem clozelCohomological : GlobalTheory.Published.ClozelCohomological :=
  clozelCohomological_of_three whitLie_holds kugaGlue_holds Coch.cochain_holds

end PositivityTheory.Rg.Cz
