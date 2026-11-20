import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.CuspFormGamma1InterGamma0SlashRatIsZeroAt
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FCuspFormGamma1InterGamma0SlashRatIsZeroAt.lean&line=21#L21)
-/
theorem _root_.GlobalTheory.T.cuspForm_gamma1InterGamma0_slash_rat_isZeroAt : ∀ (N l : ℕ) (k : ℤ) (g : GL (Fin 2) ℚ), 0 < N → 0 < l → 0 < (g.det : ℚ) → ∀ f : CuspForm (GlobalTheory.Hk.lev N l) k, ∀ c : OnePoint ℝ, IsCusp c (GlobalTheory.Hk.lev N l) → c.IsZeroAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k := by
  first | exact @GlobalTheory.Hk.cuspForm_slash_rat_isZeroAt | exact GlobalTheory.Hk.cuspForm_slash_rat_isZeroAt | (intros; apply GlobalTheory.Hk.cuspForm_slash_rat_isZeroAt <;> assumption)
