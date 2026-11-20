import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.RadialDecompositionOfParts

/- English proof (translation)
The claim follows from `radial_decomposition_of_parts`.
-/
theorem Formalism.FourierDecayAlt.P.q_radial_decomposition_of_pieces : Formalism.FourierDecayAlt.Q.RadialDecompositionOfParts :=
  radial_decomposition_of_parts
