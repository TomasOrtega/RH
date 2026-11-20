import Formalism.PeriodIntegrals.HasseJidPow
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HasseJacobsonPowers.SfrMulMemJHfr
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.HassePresH

/- English proof (translation)
The claim follows from `PI.HJP.hasseJidPow_of hasse_presentation`.
-/
theorem hasse_jid_power : PI.HasseJidPow := PI.HJP.hasseJidPow_of hasse_presentation
