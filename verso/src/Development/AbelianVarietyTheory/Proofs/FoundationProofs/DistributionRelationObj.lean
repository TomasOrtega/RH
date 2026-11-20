import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsHeckeLOfHasInf
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.OddWindowBounds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToricSumEqHeckeLValueMulAuxiliaryFactors

noncomputable section

open NumberField IsDedekindDomain ReciprocityTheory.Gal Formalism.ConjugateSelfDual Formalism.BasicNotions Formalism.MainNotions GlobalTheory.CMVal GlobalTheory.ToricDenom GlobalTheory.ToricDistribution

namespace GlobalTheory.ToricDistributionObj

/- English proof (translation)
The claim follows from `GlobalTheory.ToricSumValue.toricSum_eq exists_isHeckeL_of_hasInf`.
-/
theorem toricSumFormula_holds : ToricSumFormula :=
  GlobalTheory.ToricSumValue.toricSum_eq exists_isHeckeL_of_hasInf

end GlobalTheory.ToricDistributionObj
