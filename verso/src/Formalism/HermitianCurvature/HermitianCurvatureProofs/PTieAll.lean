import Formalism.HermitianCurvature.HermitianCurvatureProofs.PtieLevTransportHerOf
import Formalism.HermitianCurvature.HermitianCurvatureProofs.SfiniteOfHaar

namespace Formalism.FourierDecayAlt.P

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem ptie_levTransportHer_of_sliceStep (hS : Formalism.FourierDecayAlt.P.PTie.SliceStepHer) : Formalism.FourierDecayAlt.P.PTie.LevTransportHer :=
  ptie_levTransportHer_of jacquet_scaling hS

end Formalism.FourierDecayAlt.P
