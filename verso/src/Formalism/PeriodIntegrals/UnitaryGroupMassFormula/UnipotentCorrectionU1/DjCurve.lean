import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.CoreStar
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnipotentCorrectionU1.DjCurveB

open Matrix
open scoped ComplexConjugate

noncomputable section

namespace PI.UnitaryCorollaryDerivatives

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.U

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Introduce `_ _ _ Y hY` and use `DjC.djCurve_general Y hY`.
-/
theorem determinant_curve_derivative : DjCurve := fun _ _ _ Y hY => DjC.djCurve_general Y hY

end PI.UnitaryCorollaryDerivatives
