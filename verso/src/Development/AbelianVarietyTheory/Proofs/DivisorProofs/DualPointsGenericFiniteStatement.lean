import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DualPointsGenericFinite
import Mathlib
set_option autoImplicit false
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.isReduced_of_dualNumber_points_trivial` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDivisorProofs%2FDualPointsGenericFinite.lean&line=22#L22)
-/
theorem _root_.GlobalTheory.T.dual_points_generic_finite : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [CharZero K] [Algebra R K] [IsFractionRing R K] (r : R), r ≠ 0 →
    ∀ (C : Type) [CommRing C] [Algebra R C] [Algebra (Localization.Away r) C] [IsScalarTower R (Localization.Away r) C]
      [Module.Finite (Localization.Away r) C] [Module.Free (Localization.Away r) C],
      (∀ (k : Type) [Field k] [Algebra R k] [Algebra K k] [IsScalarTower R K k] (ψ : C →ₐ[R] DualNumber k),
        ψ = ((TrivSqZeroExt.inlAlgHom R k k).comp (TrivSqZeroExt.fstHom R k k)).comp ψ) → IsReduced C := by
  first | exact @GlobalTheory.isReduced_of_dualNumber_points_trivial | exact GlobalTheory.isReduced_of_dualNumber_points_trivial | (intros; apply GlobalTheory.isReduced_of_dualNumber_points_trivial <;> assumption)
