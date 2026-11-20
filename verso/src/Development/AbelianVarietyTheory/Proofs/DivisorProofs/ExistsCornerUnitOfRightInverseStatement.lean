import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCornerUnitOfRightInverse
import Mathlib
open scoped Matrix
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.exists_corner_unit_of_right_inverse` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FExistsCornerUnitOfRightInverse.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_corner_unit_of_right_inverse' : ∀ {F R : Type} [Field F] [CommRing R] [Algebra F R] (e : R), e * e = e → (∀ ψ : Polynomial R, (∀ (Ω : Type) [Field Ω] (φ : R →+* Ω), φ e = 1 → ψ.map φ ≠ 0) → ∃ t : F, IsUnit (e * ψ.eval (algebraMap F R t) + (1 - e))) → ∀ {n : ℕ} (D C P Q : Matrix (Fin n) (Fin n) R), D * P + C * Q = 1 → ∃ x : Matrix (Fin n) (Fin n) R, IsUnit (e * (D + C * x).det + (1 - e)) := by
  first | exact @GlobalTheory.exists_corner_unit_of_right_inverse | exact GlobalTheory.exists_corner_unit_of_right_inverse | (intros; apply GlobalTheory.exists_corner_unit_of_right_inverse <;> assumption)
