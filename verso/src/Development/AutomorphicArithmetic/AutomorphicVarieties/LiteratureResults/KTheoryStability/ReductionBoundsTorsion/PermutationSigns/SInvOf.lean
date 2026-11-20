import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.KTheoryStability.ReductionBoundsTorsion.PermutationSigns.SwtAll

namespace PositivityTheory.KB

/- English proof (translation)
Introduce `hC hE hP hS` and use `BlockInvariants.sinv_of_swt hC hP hS BlockInvariants.aGood (BlockInvariants.swt_all hE hS)`.
-/
theorem sInv_of : SChain → SEv → SPsi → SStokes → SInv := fun hC hE hP hS =>
  BlockInvariants.sinv_of_swt hC hP hS BlockInvariants.aGood (BlockInvariants.swt_all hE hS)

end PositivityTheory.KB
