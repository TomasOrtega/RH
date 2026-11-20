import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GenericMultOneDimOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalIdempotentCharacters
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WhittakerSpaceDimParabolicInductionCuspidalEqOneStatement

namespace GlobalTheory.GenericProduct

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneGenericVector : OneGenericVector := GlobalTheory.T.whittakerSpaceDim_parabolicInduction_cuspidal_eq_one

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem genericMultOne_holds : GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne.GenericMultOne := genericMultOne oneGenericVector

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem oneWhittakerVector_holds : GlobalTheory.IndefiniteRowSideFullHecke.CuspidalInducedCharacter.OneWhittakerVector :=
  GlobalTheory.CuspidalIdempotentCharacters.genericMultOne_iff.1 genericMultOne_holds

end GlobalTheory.GenericProduct
