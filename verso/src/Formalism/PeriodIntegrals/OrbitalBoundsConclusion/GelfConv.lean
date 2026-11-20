import Mathlib
import Formalism.PeriodIntegrals.UMultOne
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandPairConvolution.ConvComm

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.GelfConv.convComm`.
-/
theorem gelfand_convolution_comm : PI.UMultOne.ConvComm := PI.UnitaryGroupMassFormula.GelfConv.convComm
