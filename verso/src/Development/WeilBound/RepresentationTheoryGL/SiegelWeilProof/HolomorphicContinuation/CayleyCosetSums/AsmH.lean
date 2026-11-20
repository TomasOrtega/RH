import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.AsmCore
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.TopHolPf
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.FarId
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SmoothTop

namespace PositivityTheory.Rg.Sw.HSt

/- English proof (translation)
The claim follows from `asmH_of farId Conv.smoothX topHol rcCongr (fun _ x Z t hx => expLie x Z t hx)`.
-/
theorem asmH : AsmH :=
  asmH_of farId Conv.smoothX topHol rcCongr (fun _ x Z t hx => expLie x Z t hx)

end PositivityTheory.Rg.Sw.HSt
