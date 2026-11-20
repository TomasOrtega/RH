import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.ExistsUnitaryGroupDatumOfVectorExponentSpectral
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CharConjHolds
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.SpecTopG

namespace UpperTheory.Gal.Int.Geo.Pl

/- English proof (translation)
The claim follows from `UpperTheory.Gal.Spc.specTopG wtOf_holds`.
-/
theorem specTop_holds : SpecTop := UpperTheory.Gal.Spc.specTopG wtOf_holds

/- English proof (translation)
The claim follows from `exists_unitaryGroupDatum_of_vector_exponent_spectral vecEx_holds expOf_holds specTop_holds`.
-/
theorem planEx_holds : PlanEx := exists_unitaryGroupDatum_of_vector_exponent_spectral vecEx_holds expOf_holds specTop_holds

end UpperTheory.Gal.Int.Geo.Pl
