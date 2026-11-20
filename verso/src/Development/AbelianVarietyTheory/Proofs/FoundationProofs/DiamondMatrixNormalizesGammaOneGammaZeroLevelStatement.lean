import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondMatrixNormalizesGammaOneGammaZeroLevel
import Development.AbelianVarietyTheory.Definitions.Foundations.IsDCReps
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FDiamondMatrixNormalizesGammaOneGammaZeroLevel.lean&line=46#L46)
-/
theorem _root_.GlobalTheory.T.diamondMatrix_normalizes_gammaOneGammaZeroLevel : ∀ (N l : ℕ) (d : ZMod N) (σ : SL(2, ℤ)), IsDiam N l d σ → ∀ γ : Lev N l, ∃ γ' : Lev N l, mat σ * mat γ = mat γ' * mat σ := by
  first | exact @GlobalTheory.HeckeFamilyMatrices.diam_normalises_lev | exact GlobalTheory.HeckeFamilyMatrices.diam_normalises_lev | (intros; apply GlobalTheory.HeckeFamilyMatrices.diam_normalises_lev <;> assumption)
