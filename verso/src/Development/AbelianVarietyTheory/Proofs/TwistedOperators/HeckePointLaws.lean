import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.HeckePrimeDetection
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckePointLawsOfTransport
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeckeIsogenyThetaGeneratorTransportStatement

set_option autoImplicit false

namespace GlobalTheory.HeckePointLaw

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem heckePointLaws : GlobalTheory.IndefiniteRowSideFullHecke.HeckePrimeDetection.HeckePointLaws :=
  heckePointLaws_of_transport GlobalTheory.T.heckeIsogeny_thetaGenerator_transport

end GlobalTheory.HeckePointLaw
