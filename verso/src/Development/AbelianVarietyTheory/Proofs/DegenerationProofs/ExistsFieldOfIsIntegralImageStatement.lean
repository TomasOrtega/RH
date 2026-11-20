import Mathlib
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFieldOfIsIntegralImage
open scoped BigOperators
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDegenerationProofs%2FExistsFieldOfIsIntegralImage.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.exists_field_of_isIntegral_image' : ∀ (R : Type) [CommRing R] (φ : R →+* ℂ), (∀ r, IsIntegral ℤ (φ r)) → ∃ (F : Type) (_ : Field F) (_ : CharZero F) (φ' : R →+* F), (∀ x : F, ∃ (r : R) (n : ℕ), 0 < n ∧ φ' r = n * x) ∧ ∀ (A : Type) [CommRing A] [Algebra ℚ A] (χ : R →+* A), (∀ r, φ r = 0 → χ r = 0) → ∃ χ' : F →+* A, χ'.comp φ' = χ := by
  first | exact @GlobalTheory.exists_field_of_isIntegral_image | exact GlobalTheory.exists_field_of_isIntegral_image | (intros; apply GlobalTheory.exists_field_of_isIntegral_image <;> assumption)
