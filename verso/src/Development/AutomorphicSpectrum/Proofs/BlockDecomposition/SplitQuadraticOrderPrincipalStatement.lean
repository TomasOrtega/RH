import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitQuadraticOrderPrincipal
import Mathlib
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAutomorphicSpectrum%2FProofs%2FBlockDecomposition%2FSplitQuadraticOrderPrincipal.lean&line=5#L5)
-/
theorem _root_.GlobalTheory.T.split_quadratic_order_principal : ∀ (R O : Type) [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] [CommRing O] (ι : R →+* O) (δ : O) (e : R), δ * δ = ι (e * e) → (∀ y : O, ∃ p q : R, y = ι p + ι q * δ) → (∀ p q : R, ι p + ι q * δ = 0 → p = 0 ∧ q = 0) → IsUnit e → IsUnit (2 : R) → IsPrincipalIdealRing O := by
  first | exact @GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq | exact GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq | (intros; apply GlobalTheory.CompanionTheory.SplitQuadratic.isPrincipalIdealRing_of_sq_eq_sq <;> assumption)
