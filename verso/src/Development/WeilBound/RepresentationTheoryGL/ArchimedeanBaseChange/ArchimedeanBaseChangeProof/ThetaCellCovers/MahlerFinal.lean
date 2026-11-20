import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ThetaCellCovers.Mahler
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic

namespace PositivityTheory.Rg.BcB.E1

open D1

/- English proof (translation)
The claim follows from `mahlerC_of_deg degBasis degAdelic degBdd degRat`.
-/
theorem mahlerC_holds : MahlerC := mahlerC_of_deg degBasis degAdelic degBdd degRat

/- English proof (translation)
The claim follows from `mahler_of_c mahlerC_holds`.
-/
theorem mahler_holds : Mahler := mahler_of_c mahlerC_holds

end PositivityTheory.Rg.BcB.E1
