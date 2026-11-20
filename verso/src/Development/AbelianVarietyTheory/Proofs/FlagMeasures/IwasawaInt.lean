import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LintegralEquivariantLeftInvariant
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IwasawaDecompComplexifiedMaxCompactStatement

namespace GlobalTheory.IwaInt

/- English proof (translation)
The claim follows from `iwasawaInt_of GlobalTheory.T.iwasawa_decomp_complexifiedMaxCompact`.
-/
theorem iwasawaInt : GlobalTheory.Dec.IwasawaInt := iwasawaInt_of GlobalTheory.T.iwasawa_decomp_complexifiedMaxCompact

end GlobalTheory.IwaInt
