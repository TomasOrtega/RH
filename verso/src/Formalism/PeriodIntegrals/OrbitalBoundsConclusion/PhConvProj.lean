import Mathlib
import Formalism.PeriodIntegrals.PhConvProj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.ConvProjOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.SelfAdj
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ConvolutionProjection.UrepMulApply

/- English proof (translation)
The claim follows from `PI.UnitaryGroupMassFormula.PhConvProj.Defs.convProj_of PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.selfAdj PI.UnitaryGroupMassFormula.PhConvProj.Sand.sand`.
-/
theorem convolution_projection : PI.PhConvProj.ConvProj :=
  PI.UnitaryGroupMassFormula.PhConvProj.Defs.convProj_of PI.UnitaryGroupMassFormula.PhConvProj.SelfAdj.selfAdj PI.UnitaryGroupMassFormula.PhConvProj.Sand.sand
