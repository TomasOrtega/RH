import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantDerivationsQuotientBialgebra
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInvariantDerivationOfCounitalComul
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsInvariantDerivationsQuotientBialgebra.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_invariant_derivations_quotient_bialgebra : ∀ (O A : Type) [CommRing O] [CommRing A] [Bialgebra O A] (I : Ideal O) (d : ℕ) (l : Fin d → (A →ₗ[O] O ⧸ I)), (∀ i a b, l i (a * b) = Coalgebra.counit (R := O) a • l i b + Coalgebra.counit (R := O) b • l i a) → ∃ D : Fin d → Derivation (O ⧸ I) ((O ⧸ I) ⊗[O] A) ((O ⧸ I) ⊗[O] A), ∀ i a, Bialgebra.counitAlgHom (O ⧸ I) ((O ⧸ I) ⊗[O] A) (D i (1 ⊗ₜ a)) = l i a := by
  first | exact @GlobalTheory.quotient_base_change_invariant_derivations | exact GlobalTheory.quotient_base_change_invariant_derivations | (intros; apply GlobalTheory.quotient_base_change_invariant_derivations <;> assumption)
