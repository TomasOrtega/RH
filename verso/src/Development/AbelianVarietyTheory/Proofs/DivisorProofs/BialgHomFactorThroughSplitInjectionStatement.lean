import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BialgHomFactorThroughSplitInjection
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.bialgHom_factor_through_split` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FBialgHomFactorThroughSplitInjection.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.bialgHom_factor_through_split_injection : ∀ (O : Type) [CommRing O] (A B D : Type) [CommRing A] [CommRing B] [CommRing D] [Bialgebra O A] [Bialgebra O B] [Bialgebra O D] (j : B →ₐc[O] A) (ρ : A →ₗ[O] B) (f : D →ₐc[O] A), (∀ b, ρ (j b) = b) → (∀ d, f d ∈ Set.range j) → ∃ g : D →ₐc[O] B, ∀ d, j (g d) = f d := by
  first | exact @GlobalTheory.bialgHom_factor_through_split | exact GlobalTheory.bialgHom_factor_through_split | (intros; apply GlobalTheory.bialgHom_factor_through_split <;> assumption)
