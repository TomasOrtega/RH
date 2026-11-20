import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DiamondOperatorOfMatrixCompMul
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.Hk.dia_mul` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FDiamondOperatorOfMatrixCompMul.lean&line=24#L24)
-/
theorem _root_.GlobalTheory.T.diamondOperatorOfMatrix_comp_mul : ∀ (N l : ℕ) (k d e : ℤ) (σ τ ρ : SL(2, ℤ)), 0 < N → GlobalTheory.Hk.IsDia N l d σ → GlobalTheory.Hk.IsDia N l e τ → GlobalTheory.Hk.IsDia N l (d * e) ρ → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.dia k τ (GlobalTheory.Hk.dia k σ ⇑f) = GlobalTheory.Hk.dia k ρ ⇑f := by
  first | exact @GlobalTheory.Hk.dia_mul | exact GlobalTheory.Hk.dia_mul | (intros; apply GlobalTheory.Hk.dia_mul <;> assumption)
