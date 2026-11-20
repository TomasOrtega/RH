import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.FormalDegreeSquareIntegrable.FormalDegreeOrthogonality

noncomputable section

namespace PIW.HCFdeg

open PI.UpqRep

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem formal_degree_of_schur_unimodular (hSchur : StSchur) (hBdd : StBdd) (hOrthOf : StOrthOf) (hUni : StUnimod) : StableSubspaceMobius :=
  formal_degree_orthogonality (hOrthOf hSchur hBdd) hUni

end PIW.HCFdeg
