import Formalism.PeriodIntegrals.ScPiExists
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.TensorFrameConstruction.InnerOfNorm

/- English proof (translation)
The claim follows from `PI.ScPiBuildW.Asm.build`.
-/
theorem sc_pi_construction : PI.ScPiExists.Build :=
  PI.ScPiBuildW.Asm.build
