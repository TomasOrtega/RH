import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.SinvOfSwt
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PlacePermOperatorBicommutantSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.PlacePermOperatorCommutantSpan
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.BlkConjTranspose
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.FFTAsm
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.SmoothCompositionIdentity.MatOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.Weights
import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.Transport

namespace PositivityTheory.KB.BlockInvariants

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem aGood : AGood := TwAG.aGood

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem swt_all (hE : SEv) (hS : SStokes) : SWt :=
  swt hE hS (fft_of cplx sw1 sw2) aGood wPad weylTwoBlockMatrix wInv wOne wCyc tStab tBlk pStab blockSum_preserves_cone

end PositivityTheory.KB.BlockInvariants
