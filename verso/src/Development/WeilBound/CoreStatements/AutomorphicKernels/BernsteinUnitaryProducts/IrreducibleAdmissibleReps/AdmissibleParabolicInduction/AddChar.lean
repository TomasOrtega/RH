import Mathlib
import GroundTheory.LocalFields.LocalFourierExistence
import Development.WeilBound.CoreStatements.AutomorphicKernels.BernsteinUnitaryProducts.IrreducibleAdmissibleReps.Assembly

namespace PositivityTheory.PfBern.Props1

open PositivityTheory.PfBern.Assembly

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem existsAddChar_holds : ExistsAddChar := fun k _ _ _ _ =>
  GroundTheory.LocalField.exists_addChar_continuous_ne_one (K := k)

end PositivityTheory.PfBern.Props1
