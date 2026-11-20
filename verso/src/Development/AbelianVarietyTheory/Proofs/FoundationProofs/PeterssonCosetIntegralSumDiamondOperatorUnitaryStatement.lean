import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PeterssonCosetIntegralSumDiamondOperatorUnitary
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FPeterssonCosetIntegralSumDiamondOperatorUnitary.lean&line=33#L33)
-/
theorem _root_.GlobalTheory.T.peterssonCosetIntegralSum_diamondOperator_unitary : ∀ (N l : ℕ) (k d : ℤ) (σ : SL(2, ℤ)), 0 < N → 0 < l → GlobalTheory.Hk.IsDia N l d σ → ∀ f g : CuspForm (GlobalTheory.Hk.lev N l) k, GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k (GlobalTheory.Hk.dia k σ ⇑f) (GlobalTheory.Hk.dia k σ ⇑g) = GlobalTheory.Hk.pet (GlobalTheory.Hk.lev N l) k ⇑f ⇑g := by
  first | exact @GlobalTheory.Hk.pet_dia_dia | exact GlobalTheory.Hk.pet_dia_dia | (intros; apply GlobalTheory.Hk.pet_dia_dia <;> assumption)
