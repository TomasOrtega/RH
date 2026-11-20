import Mathlib
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.DetOneReductionOfDetOne
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FUnitaryExistence%2FDetOneReductionOfDetOne.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.det_one_reduction_of_det_one : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (L : Type) [AddCommGroup L] [Module R L] [Module.Finite R L] [Module.Projective R L] (I : Ideal R) [Finite (R ⧸ I)] (γ : L →ₗ[R] L), LinearMap.det (LinearMap.baseChange K γ) = 1 → LinearMap.det (LinearMap.baseChange (R ⧸ I) γ) = 1 := by
  first | exact @GlobalTheory.DetMod.det_baseChange_quot_eq_one | exact GlobalTheory.DetMod.det_baseChange_quot_eq_one | (intros; apply GlobalTheory.DetMod.det_baseChange_quot_eq_one <;> assumption)
