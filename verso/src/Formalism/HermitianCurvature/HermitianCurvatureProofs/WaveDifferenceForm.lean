import Formalism.HermitianCurvature.HermitianCurvatureProofs.BoundOnEarlierRegion
import Formalism.HermitianCurvature.HermitianCurvatureProofs.WaveDiffFormOf

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.StandardPairingDecay.waveDiffForm_of Formalism.FourierDecayAlt.P.StandardPairingDecay.bound_on_earlier_region`.
-/
theorem Formalism.FourierDecayAlt.P.wave_difference_form : Formalism.FourierDecayAlt.P.PBO.WaveDiffForm :=
  Formalism.FourierDecayAlt.P.StandardPairingDecay.waveDiffForm_of Formalism.FourierDecayAlt.P.StandardPairingDecay.bound_on_earlier_region
