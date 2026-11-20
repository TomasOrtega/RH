import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.GeometricallyReducedOfPerfectField
import ReciprocityTheory.ThetaQuasiPeriods.ThetaQuasiPeriodStatement
import ReciprocityTheory.ThetaQuasiPeriods.Transl
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaUnifAV
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.GlobalSectionsRankAlgClosed

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj Complex Matrix Filter Topology
open ReciprocityTheory.PTheta ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped BigOperators Real

namespace GlobalTheory

/- English proof (translation)
Introduce `X Y hX hY hfX hfY`. Establish `: GeometricallyReduced X.hom` using `ReducedSubgroup.geometricallyReduced_of_perfectField (k := ℂ) X.hom`. Establish `: Flat X.hom` using `inferInstance`. Establish `: IsLocallyNoetherian Y.left` using `LocallyOfFiniteType.isLocallyNoetherian Y.hom`. Express the relevant statement in the definitionally equal form `IsReduced (Limits.pullback X.hom Y.hom)`.

Use `infer_instance`.
-/
theorem isReduced_tensorObj_complex :
    (∀ (X Y : Over (Sp ℂ)), IsReduced X.left → IsReduced Y.left → LocallyOfFiniteType X.hom → LocallyOfFiniteType Y.hom → IsReduced (X ⊗ Y).left) := by
  intro X Y hX hY hfX hfY

  have : GeometricallyReduced X.hom :=
    ReducedSubgroup.geometricallyReduced_of_perfectField (k := ℂ) X.hom
  have : Flat X.hom := inferInstance
  have : IsLocallyNoetherian Y.left := LocallyOfFiniteType.isLocallyNoetherian Y.hom
  change IsReduced (Limits.pullback X.hom Y.hom)
  infer_instance

end GlobalTheory
