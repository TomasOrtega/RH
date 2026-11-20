import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiamondMatrixGamma1Gamma0OfCoprime
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.EigenOfTwoStep
open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FExistsIsDiamondMatrixGamma1Gamma0OfCoprime.lean&line=8#L8)
-/
theorem _root_.GlobalTheory.T.exists_isDiamondMatrixGamma1Gamma0_of_coprime : ∀ (N l d : ℕ), 0 < N → Nat.Coprime N l → Nat.Coprime d N → ∃ γ : SL(2, ℤ), IsDiam N l d γ := by
  first | exact @GlobalTheory.diam_exists | exact GlobalTheory.diam_exists | (intros; apply GlobalTheory.diam_exists <;> assumption)
