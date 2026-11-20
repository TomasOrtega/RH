import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SpecialLinearGroupIntMapZmodSurjective
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSpecialLinearGroupIntMapZmodSurjective.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.specialLinearGroup_int_map_zmod_surjective : ∀ (M : ℕ), Function.Surjective (Matrix.SpecialLinearGroup.map (Int.castRingHom (ZMod M)) : SL(2, ℤ) →* Matrix.SpecialLinearGroup (Fin 2) (ZMod M)) := by
  first | exact @GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective | exact GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective | (intros; apply GlobalTheory.specialLinearGroup_map_intCast_zmod_surjective <;> assumption)
