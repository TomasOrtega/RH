import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ResInjOfDetermined
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ResidueInjectivityChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MultiplicitySpaceEqZeroOfLowestKTypesStatement

noncomputable section

namespace GlobalTheory.LowTypeRestriction

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem determinedByLowTypes : DeterminedByLowTypes := GlobalTheory.T.multiplicitySpace_eq_zero_of_lowestKTypes

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem resInj : GlobalTheory.IndefiniteRowSideFullHecke.ResidueInjectivityAt.ResInj := resInj_of_determined determinedByLowTypes

end GlobalTheory.LowTypeRestriction

end
