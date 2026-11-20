import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.ProdAbsNormDifferentIdealPowers
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.NMPseudoOf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.CountCoeEqMultiplicity
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.CountingFormula.DeterminantLocal

namespace PI.UnitaryGroupMassFormula.CntFormula.R6

/- English proof (translation)
The claim follows from `normMM_of_NM (nMPseudo_of hE hD count_extension norm_mass_assembly)`.
-/
theorem normMM_of_JD (hE : JordanExists) (hD : DetLocal) : Formalism.L2.SG.Pf.Cnt.NormMM :=
  normMM_of_NM (nMPseudo_of hE hD count_extension norm_mass_assembly)

/- English proof (translation)
The claim follows from `normMM_of_JD hE determinant_local`.
-/
theorem normMM_of_J (hE : JordanExists) : Formalism.L2.SG.Pf.Cnt.NormMM :=
  normMM_of_JD hE determinant_local

end PI.UnitaryGroupMassFormula.CntFormula.R6
