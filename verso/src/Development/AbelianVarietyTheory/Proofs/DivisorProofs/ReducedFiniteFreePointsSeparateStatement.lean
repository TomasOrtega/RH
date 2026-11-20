import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ReducedFiniteFreePointsSeparate
import Mathlib
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FReducedFiniteFreePointsSeparate.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.reduced_finite_free_points_separate : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [IsAlgClosed K] [Algebra R K] [IsFractionRing R K] (r : R), r ≠ 0 →
    ∀ (C : Type) [CommRing C] [Algebra R C] [Algebra (Localization.Away r) C] [IsScalarTower R (Localization.Away r) C]
      [Module.Finite (Localization.Away r) C] [Module.Free (Localization.Away r) C], IsReduced C →
      Finite (C →ₐ[R] K) ∧ ∀ a : C, (∀ ψ : C →ₐ[R] K, ψ a = 0) → a = 0 := by
  first | exact @GlobalTheory.finite_free_reduced_points_finite_and_separate | exact GlobalTheory.finite_free_reduced_points_finite_and_separate | (intros; apply GlobalTheory.finite_free_reduced_points_finite_and_separate <;> assumption)
