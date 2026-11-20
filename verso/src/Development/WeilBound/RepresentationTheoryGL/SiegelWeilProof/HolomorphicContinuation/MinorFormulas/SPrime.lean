import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.SPrimeOfMinor
import Development.WeilBound.RepresentationTheoryGL.SiegelWeilProof.HolomorphicContinuation.MinorFormulas.MinorFormula

namespace PositivityTheory.Rg.Sw.SP

/- English proof (translation)
The claim follows from `wrOrd_of_minor minorFormula`.
-/
theorem wrOrd : PositivityTheory.SiegelWeilFormula.Gen.WROrd := wrOrd_of_minor minorFormula

end PositivityTheory.Rg.Sw.SP
