import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResInjOfDetermined
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ResidueInjectivityChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypesStatement

noncomputable section

namespace GlobalTheory.LowTypeRestriction

/- English proof (translation)
The claim follows from `GlobalTheory.T.multiplicitySpace_eq_zero_of_lowestKTypes`.
-/
theorem determinedByLowTypes : DeterminedByLowTypes := GlobalTheory.T.multiplicitySpace_eq_zero_of_lowestKTypes

/- English proof (translation)
The claim follows from `resInj_of_determined determinedByLowTypes`.
-/
theorem resInj : GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInj := resInj_of_determined determinedByLowTypes

end GlobalTheory.LowTypeRestriction

end
