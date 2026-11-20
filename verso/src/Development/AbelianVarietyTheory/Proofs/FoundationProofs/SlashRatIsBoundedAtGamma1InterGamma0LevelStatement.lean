import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SlashRatIsBoundedAtGamma1InterGamma0Level
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
open UpperHalfPlane ModularForm CongruenceSubgroup MeasureTheory
open scoped MatrixGroups ModularForm Manifold
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSlashRatIsBoundedAtGamma1InterGamma0Level.lean&line=20#L20)
-/
theorem _root_.GlobalTheory.T.slash_rat_isBoundedAt_gamma1InterGamma0Level : ∀ (N l : ℕ) (k : ℤ) (g : GL (Fin 2) ℚ), 0 < N → 0 < l → 0 < (g.det : ℚ) → ∀ f : ModularForm (GlobalTheory.Hk.lev N l) k, ∀ c : OnePoint ℝ, IsCusp c (GlobalTheory.Hk.lev N l) → c.IsBoundedAt (⇑f ∣[k] (Matrix.GeneralLinearGroup.map (Rat.castHom ℝ) g)) k := by
  first | exact @GlobalTheory.Hk.slash_rat_isBoundedAt | exact GlobalTheory.Hk.slash_rat_isBoundedAt | (intros; apply GlobalTheory.Hk.slash_rat_isBoundedAt <;> assumption)
