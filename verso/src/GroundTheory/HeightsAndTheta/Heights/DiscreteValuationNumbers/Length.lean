import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.Statements
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthCokerEqKerAddDimOneOrderSum
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArithmeticIntersection.LengthTwoGeneratorQuotient
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.NumbersDVR

universe u v

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lengthFormulaDimOne : LengthFormulaDimOne.Statement.{u, v} :=
  ReciprocityTheory.ChartRestriction.G.AI.dimOneFormula

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lengthFormulaDimTwo : LengthFormulaDimTwo.Statement.{u} :=
  ReciprocityTheory.ChartRestriction.G.AI.length_two_generator_quotient

end GroundTheory.Heights₂.Heights.NumbersDVR
