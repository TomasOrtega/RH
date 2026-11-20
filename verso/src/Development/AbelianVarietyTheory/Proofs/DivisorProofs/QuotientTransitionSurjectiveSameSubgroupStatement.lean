import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QuotientTransitionSurjectiveSameSubgroup
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRetractionMulP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvEqOneOfForallPairing
open CategoryTheory Coalgebra GlobalTheory GlobalTheory.PDiv GlobalTheory.PDivGroup GlobalTheory.HTPair
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FQuotientTransitionSurjectiveSameSubgroup.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.quotientTransition_surjective_same_subgroup : ∀ (O : Type) [CommRing O] (A₁ : Type) [CommRing A₁] [HopfAlgebra O A₁] [IsCocomm O A₁] [Module.Finite O A₁] [Module.Projective O A₁] (A₂ : Type) [CommRing A₂] [HopfAlgebra O A₂] [IsCocomm O A₂] [Module.Finite O A₂] [Module.Projective O A₂] (B₁ : Type) [CommRing B₁] [HopfAlgebra O B₁] [IsCocomm O B₁] [Module.Finite O B₁] [Module.Projective O B₁] (B₂ : Type) [CommRing B₂] [HopfAlgebra O B₂] [IsCocomm O B₂] [Module.Finite O B₂] [Module.Projective O B₂] (π : A₂ →ₐc[O] A₁) (j₁ : B₁ →ₐc[O] A₁) (j₂ : B₂ →ₐc[O] A₂) (r : B₂ →ₐc[O] B₁) (ρ : A₁ →ₗ[O] B₁), (∀ b, ρ (j₁ b) = b) → (∀ b, j₁ (r b) = π (j₂ b)) → kerIdeal j₁ = Ideal.map (π : A₂ →ₐ[O] A₁) (kerIdeal j₂) → Function.Surjective r := by
  first | exact @GlobalTheory.QuotTransition.transition_surjective | exact GlobalTheory.QuotTransition.transition_surjective | (intros; apply GlobalTheory.QuotTransition.transition_surjective <;> assumption)
