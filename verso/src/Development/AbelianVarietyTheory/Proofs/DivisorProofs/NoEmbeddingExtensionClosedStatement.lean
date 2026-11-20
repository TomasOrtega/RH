import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NoEmbeddingExtensionClosed
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GlobalHeightBoundIffAtGoodPrimes
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsZeroPresZeroMod
open CategoryTheory Limits AlgebraicGeometry IsLocalRing
open GlobalTheory GlobalTheory.Vert GlobalTheory.MixedLocalChains GlobalTheory.FrobFilt
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FNoEmbeddingExtensionClosed.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.no_embedding_extension_closed : ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] (B : GlobalTheory.Vert.Model O) (S : ShortComplex B.X.Modules), S.ShortExact → NoEmb B S.X₁ → NoEmb B S.X₃ → NoEmb B S.X₂ := by
  first | exact @GlobalTheory.FrobFilt.noEmb_of_shortExact | exact GlobalTheory.FrobFilt.noEmb_of_shortExact | (intros; apply GlobalTheory.FrobFilt.noEmb_of_shortExact <;> assumption)
