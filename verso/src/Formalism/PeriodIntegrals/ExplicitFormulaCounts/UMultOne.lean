import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnitarySecondCountable.Assembly
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CompactGelfandAverage.GelfCptOf
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GelfSpan
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.GelfConv
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UConjT
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.CommMult

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.GelfCpt.gelfCpt_of gelfand_integral_span gelfand_convolution_comm`.
-/
theorem gelfCpt_closed : PI.UMultOne.GelfandCompact :=
  PI.UnitaryGroupMassFormula.GelfCpt.gelfCpt_of gelfand_integral_span gelfand_convolution_comm

/- English proof (translation)
The claim follows from `PI.UMultOne.UnitaryGroupMassFormula.uMultOne_of unitary_conj_transpose gelfCpt_closed commutant_multiplicity_one`.
-/
theorem uMultOne_closed : PI.UMultOne.MultOne :=
  PI.UMultOne.UnitaryGroupMassFormula.uMultOne_of unitary_conj_transpose gelfCpt_closed commutant_multiplicity_one
