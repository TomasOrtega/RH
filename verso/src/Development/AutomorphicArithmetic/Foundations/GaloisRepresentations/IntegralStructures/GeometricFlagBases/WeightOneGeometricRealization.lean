import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.GeometricRealizationOfWeightOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LefschetzFixedPointFiniteEtaleCorrespondence

namespace UpperTheory.Gal.Int.Geo

/- English proof (translation)
Unfold `LocalSmoothExtension.HolomorphicLefschetzFormula`. Conclude with `GlobalTheory.T.lefschetz_fixedPoint_finite_etale_correspondence`.
-/
theorem weight_one_geometric_realization : LocalSmoothExtension.HolomorphicLefschetzFormula := by
  unfold LocalSmoothExtension.HolomorphicLefschetzFormula
  exact GlobalTheory.T.lefschetz_fixedPoint_finite_etale_correspondence

/- English proof (translation)
The claim follows from `geometric_realization_of_weight_one weight_one_geometric_realization`.
-/
theorem geoOne_holds : GeoOne := geometric_realization_of_weight_one weight_one_geometric_realization

end UpperTheory.Gal.Int.Geo
