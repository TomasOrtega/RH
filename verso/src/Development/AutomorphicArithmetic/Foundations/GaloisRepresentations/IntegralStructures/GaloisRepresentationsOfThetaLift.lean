import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.Development
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.WeightOneGeometricRealization

namespace UpperTheory.Gal.Int

/- English proof (translation)
The claim follows from `galoisLocalGlobalStrong_of_geometry_lift UpperTheory.Gal.Int.Geo.geoOne_holds up`.
-/
theorem galoisRepresentations_of_thetaLift (up : UpperTheory.TP.TLiftK) : UpperTheory.GalStar.Row0b recT := galoisLocalGlobalStrong_of_geometry_lift UpperTheory.Gal.Int.Geo.geoOne_holds up

end UpperTheory.Gal.Int
