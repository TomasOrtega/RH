import Mathlib
import Development.AutomorphicSpectrum.Proofs.AlgebraProofs.FlagIndependenceStatement
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPlainValueIndep
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinFlagPairIff
import GroundTheory.HeightsAndTheta.Heights.DiscreteValuationNumbers.PTwinVertDivSupportFibre

namespace GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue

open GroundTheory.Heights₂.Heights.NumbersDVR in

/- English proof (translation)
The claim follows from `FlagPlainValueIndependence.proof GlobalTheory.T.flag_independence FlagPairCharacterisation.proof VerticalDivisorSupportFibre.proof`.
-/
theorem main : GroundTheory.Heights₂.Heights.NumbersDVR.FlagPlainValueIndependence.Statement :=
  FlagPlainValueIndependence.proof GlobalTheory.T.flag_independence FlagPairCharacterisation.proof VerticalDivisorSupportFibre.proof

end GlobalTheory.CompanionTheory.CommAlg.FlagPlainValue
