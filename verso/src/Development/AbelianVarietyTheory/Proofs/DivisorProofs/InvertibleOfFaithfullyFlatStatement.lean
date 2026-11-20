import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InvertibleOfFaithfullyFlat
import Mathlib
open TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.FFDescent.invertible_of_invertible_baseChange` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FInvertibleOfFaithfullyFlat.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.invertible_of_faithfully_flat : ∀ (B B' : Type) [CommRing B] [CommRing B'] [Algebra B B'] [IsNoetherianRing B] [Module.FaithfullyFlat B B']
    (M : Type) [AddCommGroup M] [Module B M], Module.Invertible B' (B' ⊗[B] M) → Module.Invertible B M := by
  first | exact @GlobalTheory.FFDescent.invertible_of_invertible_baseChange | exact GlobalTheory.FFDescent.invertible_of_invertible_baseChange | (intros; apply GlobalTheory.FFDescent.invertible_of_invertible_baseChange <;> assumption)
