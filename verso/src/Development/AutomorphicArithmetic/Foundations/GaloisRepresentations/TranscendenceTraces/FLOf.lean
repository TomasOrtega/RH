import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PhiAsm
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PPhiQis
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PExtRes
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.TranscendenceTraces.PFamHom

namespace UpperTheory.Gal.TranscendenceTraces

/- English proof (translation)
The claim follows from `fL_of_parts phiQis_of extRes_of famHom_of`.
-/
theorem fL_of : PhiEx → FL := fL_of_parts phiQis_of extRes_of famHom_of

end UpperTheory.Gal.TranscendenceTraces
