import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsDerivationExtendingCotangentForm
import Mathlib
open IsLocalRing
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsDerivationExtendingCotangentForm.lean&line=92#L92)
-/
theorem _root_.GlobalTheory.T.exists_derivation_extending_cotangent_form : ∀ (R B : Type) [CommRing R] [IsDomain R] [Algebra ℚ R] [CommRing B] [IsLocalRing B] [Algebra R B], (∀ r : R, r ≠ 0 → IsUnit (algebraMap R B r)) → ∀ (lam : CotangentSpace B →ₗ[ResidueField B] ResidueField B), ∃ δ : Derivation R B (ResidueField B), ∀ y (hy : y ∈ maximalIdeal B), δ y = lam ((maximalIdeal B).toCotangent ⟨y, hy⟩) := by
  first | exact @GlobalTheory.ConormalDer.exists_derivation_extending | exact GlobalTheory.ConormalDer.exists_derivation_extending | (intros; apply GlobalTheory.ConormalDer.exists_derivation_extending <;> assumption)
