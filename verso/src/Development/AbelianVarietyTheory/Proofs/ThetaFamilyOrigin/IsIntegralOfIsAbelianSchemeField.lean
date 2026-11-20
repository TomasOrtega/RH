import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.IsIntegralOfSmoothFieldOfConnectedSpace

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

/- English proof (translation)
Use `hA.smooth` as an intermediate fact. Use `hA.geomConnected` as an intermediate fact. Use `geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres A.hom` as an intermediate fact. Conclude with `GeometricallyIntegral.isIntegral_of_subsingleton A.hom`.
-/
theorem isIntegral_of_isAbelianScheme_field (K : Type) [Field K] (A : Over (Sp K)) [GrpObj A]
    (hA : IsAbelianScheme A) : IsIntegral A.left := by
  have := hA.smooth
  have := hA.geomConnected
  have := geometricallyIntegral_of_smooth_of_geometricallyConnected_fibres A.hom
  exact GeometricallyIntegral.isIntegral_of_subsingleton A.hom

/- English proof (translation)
Introduce `K _ _ P` and use `isIntegral_of_isAbelianScheme_field K P.A P.isAb`.
-/
theorem polAV_isIntegral_of_isAlgClosed :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)), IsIntegral P.A.left :=
  fun K _ _ P => isIntegral_of_isAbelianScheme_field K P.A P.isAb

end GlobalTheory
