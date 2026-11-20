import Formalism.HermitianCurvature.StatementU
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UsCompose
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CutoffPlainAndSmoothed
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UsCost

/- English proof (translation)
The claim follows from `differential_operator_compose`.
-/
theorem Formalism.FourierDecayAlt.P.compose_discrete_series : Formalism.FourierDecayAlt.U.ComposeDD :=
  differential_operator_compose

/- English proof (translation)
The claim follows from `cutoff_plain_and_smoothed.1`.
-/
theorem Formalism.FourierDecayAlt.P.corollary_u1_plain : Formalism.FourierDecayAlt.U.StarBoundOfCutoffOperator :=
  cutoff_plain_and_smoothed.1

/- English proof (translation)
The claim follows from `cutoff_plain_and_smoothed.2`.
-/
theorem Formalism.FourierDecayAlt.P.corollary_u1_truncated_alt : Formalism.FourierDecayAlt.U.StarBoundOfTwoCutoffOperator :=
  cutoff_plain_and_smoothed.2

/- English proof (translation)
The claim follows from `operator_word_cost`.
-/
theorem Formalism.FourierDecayAlt.P.derivative_cost_of_parts : Formalism.FourierDecayAlt.U.DerivativeCostFromComponents :=
  operator_word_cost
