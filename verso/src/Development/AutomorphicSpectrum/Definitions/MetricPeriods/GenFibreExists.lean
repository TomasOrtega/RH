import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDerived
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterDivSupp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.MultihomogeneousIdeals.MultiIsProjVarFOfRatDiv
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ExistsUnique
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ImageArithClosed
import GroundTheory.HeightsAndTheta.Heights.OrbitLimits.ChangeOfModel
import GroundTheory.HeightsAndTheta.Heights.Intersections.PConsequences

namespace GlobalTheory.CompanionTheory.Ar.PB.Known

open ReciprocityTheory.ChartRestriction.G

/- English proof (translation)
The claim follows from `Geo.metricChange`.
-/
theorem metricChange : AI.I2.MetricChangeStatement := Geo.metricChange

/- English proof (translation)
The claim follows from `Geo.divSuppArith`.
-/
theorem divSuppArith : Geo.DivSuppArithStatement := Geo.divSuppArith

/- English proof (translation)
The claim follows from `GroundTheory.Heights₂.Heights.Targets.genFibreExists`.
-/
theorem genFibreExists : AI.I4.GenFibreExistsStatement := GroundTheory.Heights₂.Heights.Targets.genFibreExists

/- English proof (translation)
Assemble the required witnesses or components as `⟨GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full F ι, AI.I1.symm_thm F ι, AI.I1.multilin_thm F ι⟩`.
-/
theorem fieldNumbers (F : Type) [Field F] (K : Type) [Fintype K] (ι : K → Type) [∀ k, Fintype (ι k)] :
    AI.I1.ExistsUniqueStatement F ι ∧ AI.I1.SymmStatement F ι ∧ AI.I1.MultilinStatement F ι :=
  ⟨GroundTheory.Heights₂.Heights.Targets.ExistsUnique.full F ι, AI.I1.symm_thm F ι, AI.I1.multilin_thm F ι⟩

end GlobalTheory.CompanionTheory.Ar.PB.Known
