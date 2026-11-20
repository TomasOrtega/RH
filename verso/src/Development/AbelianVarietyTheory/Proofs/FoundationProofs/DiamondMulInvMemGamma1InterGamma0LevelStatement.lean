import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondMulInvMemGamma1InterGamma0Level
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FDiamondMulInvMemGamma1InterGamma0Level.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.diamond_mul_inv_mem_gamma1InterGamma0Level : ∀ (N l : ℕ) (d : ℤ) (σ τ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ → GlobalTheory.Hk.IsDia N l d τ → τ * σ⁻¹ ∈ GlobalTheory.Hk.lev N l := by
  first | exact @GlobalTheory.Hk.dia_mul_inv_mem_lev | exact GlobalTheory.Hk.dia_mul_inv_mem_lev | (intros; apply GlobalTheory.Hk.dia_mul_inv_mem_lev <;> assumption)
