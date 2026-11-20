import Mathlib
import Formalism.HermitianCurvature.StatementQ
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LevelImageArithmetic.GlevImageOf

/- English proof (translation)
The claim follows from `QnGlevImageW.glevImage_of`.
-/
theorem gl_level_image : Formalism.QuantumDeterminants.LevHom → Formalism.QuantumDeterminants.LevUH → Formalism.FourierDecayAlt.Q.GlevImage :=
  QnGlevImageW.glevImage_of
