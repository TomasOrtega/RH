import Mathlib
import Development.AbelianVarietyTheory.Proofs.HeightProofs.QuadraticExtNormFormOverAlgebra
import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.QuadNormBase.norm_form` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FHeightProofs%2FQuadraticExtNormFormOverAlgebra.lean&line=66#L66)
-/
theorem _root_.GlobalTheory.T.quadraticExt_norm_form_over_algebra : ∀ (F E : Type) [Field F] [CharZero F] [Field E] [Algebra F E] (σ : E →ₐ[F] E), Module.finrank F E = 2 → (∀ x, σ (σ x) = x) → (∃ x, σ x ≠ x) → ∃ δ : F, ¬ IsSquare δ ∧ ∀ (R : Type) [CommRing R] [Algebra F R], (∀ z : R ⊗[F] E, ∃ x y : R, Algebra.norm R z = x ^ 2 - algebraMap F R δ * y ^ 2 ∧ z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2)) ∧ ∀ x y : R, ∃ z : R ⊗[F] E, z * sigR R σ z = algebraMap R (R ⊗[F] E) (x ^ 2 - algebraMap F R δ * y ^ 2) := by
  first | exact @GlobalTheory.QuadNormBase.norm_form | exact GlobalTheory.QuadNormBase.norm_form | (intros; apply GlobalTheory.QuadNormBase.norm_form <;> assumption)
