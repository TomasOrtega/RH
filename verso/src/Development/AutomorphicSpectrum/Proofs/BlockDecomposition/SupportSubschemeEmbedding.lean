import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInjectiveOfSubsingleton
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ProductIrreducibleAppendEquivStatement
open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult GlobalTheory.SmGL.Exponents

namespace GlobalTheory.CompanionTheory.SubEmb

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem subEmbedding : Ysupp.SubEmbedding :=
  subEmbedding_of_stage GlobalTheory.T.product_irreducible_append_equiv

end GlobalTheory.CompanionTheory.SubEmb
