import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.MapInvMul
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PackExOf

namespace UpperTheory.Gal.Int.Geo

/- English proof (translation)
The claim follows from `geoOne_of h₁ (packEx_of h₂ h₃)`.
-/
theorem geoOne_of_parts (h₁ : Steps) (h₂ : KSAll) (h₃ : PlanEx) : GeoOne := geoOne_of h₁ (packEx_of h₂ h₃)

end UpperTheory.Gal.Int.Geo
