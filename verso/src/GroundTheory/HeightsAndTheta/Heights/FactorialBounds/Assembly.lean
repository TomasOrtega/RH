import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.Statements
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PTorsionEquidistribution
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PThirdDifferenceConstant
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PBoundedHomogeneousZero
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PSupOfOrthonormalSum
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PSlopeParameterChoice
import GroundTheory.HeightsAndTheta.Heights.FactorialBounds.PMonomialNormLowerBound
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

universe u v

/- English proof (translation)
The claim follows from `TorsionEquidistribution.proof`.
-/
theorem TorsionEquidistribution.full : TorsionEquidistribution.Statement :=
  TorsionEquidistribution.proof

/- English proof (translation)
The claim follows from `ThirdDifferenceConstant.proof`.
-/
theorem ThirdDifferenceConstant.full : ThirdDifferenceConstant.Statement.{u} :=
  ThirdDifferenceConstant.proof

/- English proof (translation)
The claim follows from `BoundedHomogeneousZero.proof`.
-/
theorem BoundedHomogeneousZero.full : BoundedHomogeneousZero.Statement.{u} :=
  BoundedHomogeneousZero.proof

/- English proof (translation)
The claim follows from `SupOfOrthonormalSum.proof`.
-/
theorem SupOfOrthonormalSum.full : SupOfOrthonormalSum.Statement.{u, v} :=
  SupOfOrthonormalSum.proof

/- English proof (translation)
The claim follows from `SlopeParameterChoice.proof`.
-/
theorem SlopeParameterChoice.full : SlopeParameterChoice.Statement :=
  SlopeParameterChoice.proof

/- English proof (translation)
The claim follows from `MonomialNormLowerBound.proof`.
-/
theorem MonomialNormLowerBound.full : MonomialNormLowerBound.Statement :=
  MonomialNormLowerBound.proof

end GroundTheory.Heights₂.Heights
