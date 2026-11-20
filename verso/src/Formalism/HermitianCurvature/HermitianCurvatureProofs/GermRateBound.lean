import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateTopBound
import Formalism.HermitianCurvature.HermitianCurvatureProofs.GermRateLowerBound

/- English proof (translation)
The claim follows from `Formalism.FourierDecayAlt.P.germ_rate_bound_of_split Formalism.FourierDecayAlt.P.germ_rate_lower_bound Formalism.FourierDecayAlt.P.germ_rate_top_bound`.
-/
theorem Formalism.FourierDecayAlt.P.germ_rate_bound : Formalism.FourierDecayAlt.P.GermFibreKernels.GermRateB :=
  Formalism.FourierDecayAlt.P.germ_rate_bound_of_split Formalism.FourierDecayAlt.P.germ_rate_lower_bound Formalism.FourierDecayAlt.P.germ_rate_top_bound
