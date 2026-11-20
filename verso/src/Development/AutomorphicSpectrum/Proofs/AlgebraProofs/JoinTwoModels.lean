import Mathlib
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.ImportsTerSide
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinJoinTwoModels
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PConeTrdegFnField

namespace GlobalTheory.CompanionTheory.CommAlg

/- English proof (translation)
The claim follows from `GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels.proof GroundTheory.Heights₂.Heights.NumbersDVR.ConeTrdegFnField.proof`.
-/
theorem joinTwoModels : GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels.Statement :=
  GroundTheory.Heights₂.Heights.NumbersDVR.JoinTwoModels.proof
    GroundTheory.Heights₂.Heights.NumbersDVR.ConeTrdegFnField.proof

end GlobalTheory.CompanionTheory.CommAlg
