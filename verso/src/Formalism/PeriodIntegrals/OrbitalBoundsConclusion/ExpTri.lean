import Mathlib
import Formalism.PeriodIntegrals.ExpTri
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ExpTriOfHorn
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.NormDetConjExp
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ExponentialTriangular.ProdLeOfInjective

/- English proof (translation)
The claim follows from `PI.ET.expTri_of_horn (PI.ET.horn_of PI.ET.kyFanDet)`.
-/
theorem exp_triangle_inequality : PI.ExpTri := PI.ET.expTri_of_horn (PI.ET.horn_of PI.ET.kyFanDet)
