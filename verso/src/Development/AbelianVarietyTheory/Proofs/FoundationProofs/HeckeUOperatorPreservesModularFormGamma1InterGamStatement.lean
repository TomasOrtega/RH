import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeUOperatorPreservesModularFormGamma1InterGamma0
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Hk.uOp_modularForm` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FHeckeUOperatorPreservesModularFormGamma1InterGamma0.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.heckeUOperator_preserves_modularForm_gamma1InterGamma0 : ∀ (N l q : ℕ) (k : ℤ), 0 < N → 0 < l → q.Prime → q ∣ N * l → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∃ g : ModularForm (GlobalTheory.Hk.lev N l) k, ⇑g = GlobalTheory.Hk.uOp q ⇑f := by
  first | exact @GlobalTheory.Hk.uOp_modularForm | exact GlobalTheory.Hk.uOp_modularForm | (intros; apply GlobalTheory.Hk.uOp_modularForm <;> assumption)
