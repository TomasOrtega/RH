import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TowerJInvariantTranscendental
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.KZ.Tower.jK_transcendental` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FTowerJInvariantTranscendental.lean&line=37#L37)
-/
theorem _root_.GlobalTheory.T.towerJInvariant_transcendental : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε), Transcendental Ω X.jK := by
  first | exact @GlobalTheory.KZ.Tower.jK_transcendental | exact GlobalTheory.KZ.Tower.jK_transcendental | (intros; apply GlobalTheory.KZ.Tower.jK_transcendental <;> assumption)
