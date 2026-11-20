import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.ElemPairJHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.PowerMatchingTraces.VarTraceHolds

namespace UpperTheory.Gal.InertialTypesAlt.L

/- English proof (translation)
The claim follows from `finTrace_holds h G.varEx_holds G.varTrace_holds G.normInt_holds`.
-/
theorem finTrace_of_matching (h : GlobalTheory.DZA.InflMatching) : FinTrace :=
  finTrace_holds h G.varEx_holds G.varTrace_holds G.normInt_holds

end UpperTheory.Gal.InertialTypesAlt.L
