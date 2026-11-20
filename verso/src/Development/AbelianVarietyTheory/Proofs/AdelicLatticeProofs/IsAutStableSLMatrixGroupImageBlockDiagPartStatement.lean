import Mathlib
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.IsAutStableSLMatrixGroupImageBlockDiagPart
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.AdelicPair
open Matrix GlobalTheory.ClassFin
open scoped Kronecker ComplexOrder TensorProduct
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FAdelicLatticeProofs%2FIsAutStableSLMatrixGroupImageBlockDiagPart.lean&line=56#L56)
-/
theorem _root_.GlobalTheory.T.isAutStableSLMatrixGroup_image_blockDiagPart : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (Γ : Set (Matrix ι ι ℂ)) (e : Matrix ι ι ℚ), IsPre Γ → e * e = e → (∀ g ∈ Γ, (1 - e.map (algebraMap ℚ ℂ)) * g * e.map (algebraMap ℚ ℂ) = 0) → IsPre (blk e '' Γ) := by
  first | exact @GlobalTheory.ClassFin.isPre_blk_image | exact GlobalTheory.ClassFin.isPre_blk_image | (intros; apply GlobalTheory.ClassFin.isPre_blk_image <;> assumption)
