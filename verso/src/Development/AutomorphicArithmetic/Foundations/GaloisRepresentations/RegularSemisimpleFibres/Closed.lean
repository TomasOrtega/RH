import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.TypeOfLblHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.InflMatch

namespace UpperTheory.Gal.InertialTypesAlt

/- English proof (translation)
The claim follows from `suppBC_holds L.inflMatch`.
-/
theorem suppBC_outright : SuppBC := suppBC_holds L.inflMatch

end UpperTheory.Gal.InertialTypesAlt
