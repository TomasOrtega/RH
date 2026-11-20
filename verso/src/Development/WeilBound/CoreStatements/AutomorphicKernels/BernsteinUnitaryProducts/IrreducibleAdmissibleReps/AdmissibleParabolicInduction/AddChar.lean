import Mathlib
import GroundTheory.LocalFields.LocalFourierExistence
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.Assembly

namespace PositivityTheory.PfBern.Props1

open PositivityTheory.PfBern.Assembly

/- English proof (translation)
Introduce `k _ _ _ _` and use `GroundTheory.LocalField.exists_addChar_continuous_ne_one (K := k)`.
-/
theorem existsAddChar_holds : ExistsAddChar := fun k _ _ _ _ =>
  GroundTheory.LocalField.exists_addChar_continuous_ne_one (K := k)

end PositivityTheory.PfBern.Props1
