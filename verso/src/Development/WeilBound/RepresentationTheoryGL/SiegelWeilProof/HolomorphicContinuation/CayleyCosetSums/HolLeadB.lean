import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.SphericalSectionConjugationSwap
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.InverseFirstBlockEqAdjoint
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.CrLem
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.LocTau
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.CayleyCosetSums.AsmH

namespace PositivityTheory.Rg.Sw.HSt

/- English proof (translation)
The claim follows from `conj (asmH locTau secFz crLem)`.
-/
theorem holLeadB : PositivityTheory.SiegelWeilFormula.HolLead := conj (asmH locTau secFz crLem)

end PositivityTheory.Rg.Sw.HSt
