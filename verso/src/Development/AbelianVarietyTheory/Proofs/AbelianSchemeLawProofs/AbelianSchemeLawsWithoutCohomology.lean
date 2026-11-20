import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.SecBaseChangeAnySt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ForallGeometricallyIntegralOfSmoothOfGeometrical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.RelAmpleOfLocallyOnBaseStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.ExistsUniqueGeneratorExtendDiscreteValuationRingStatement
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.CubicalExtendsAndExtendGen
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Semi
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory

/- English proof (translation)
The claim follows from `polBaseChange_of_relAmple_local T.relAmple_of_locally_on_base`.
-/
theorem polBaseChange_holds : PolBaseChangeSt :=
  polBaseChange_of_relAmple_local T.relAmple_of_locally_on_base

/- English proof (translation)
The claim follows from `(cubical_extends_and_extendGen forall_geometricallyIntegral_of_smooth_of_geometricallyConnected T.existsUnique_generator_extend_discreteValuationRing).1`.
-/
theorem cubical_extends_holds : Semi.cubical_extendsSt.{0} :=
  (cubical_extends_and_extendGen
    forall_geometricallyIntegral_of_smooth_of_geometricallyConnected T.existsUnique_generator_extend_discreteValuationRing).1

/- English proof (translation)
Assemble the required witnesses or components as `⟨globalFns_holds, rigidity_holds, polBaseChange_holds, lemmaB_holds, cubical_extends_holds⟩`.
-/
theorem laws_without_cohomology :
    GlobalFnsSt ∧ RigiditySt ∧ PolBaseChangeSt ∧ Semi.lemmaBSt.{0} ∧ Semi.cubical_extendsSt.{0} :=
  ⟨globalFns_holds, rigidity_holds, polBaseChange_holds, lemmaB_holds, cubical_extends_holds⟩

end GlobalTheory
