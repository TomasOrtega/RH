import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.SmoothOfHolds
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.HeckeFubiniCompatibility.GelOf
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.OnlyIsotropic

open PositivityTheory.RgBcC

namespace PositivityTheory.Rg.BcB.CG

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem gelOf_of (hW : WaveEx) : GelOf := gelOf hW compatFub tensTest

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem pack_of_C (hW : WaveEx) (hB : Bridge.BridgeSt) : Pack :=
  pack_of_gel PositivityTheory.Rg.BcB.D1.sizeBasic hB (gelOf_of hW)

end PositivityTheory.Rg.BcB.CG
