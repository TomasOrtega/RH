import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SiegelInvarianceImpliesCongruence
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SiegSep.fix_siegel_pm_one` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFoundationProofs%2FSiegelInvarianceImpliesCongruence.lean&line=327#L327)
-/
theorem _root_.GlobalTheory.T.siegel_invariance_implies_congruence : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), ∀ (M c : ℕ) (γ : SL(2, ℤ)), 0 < M → 1 < c → Nat.Coprime c 6 → c ≡ 1 [MOD M] → (∀ a b : ℤ, ¬ ((M : ℤ) ∣ a ∧ (M : ℤ) ∣ b) → X.sl (ofSL γ) (siegel X c ![(a : ℚ) / M, (b : ℚ) / M]) = siegel X c ![(a : ℚ) / M, (b : ℚ) / M]) → γ ∈ CongruenceSubgroup.Gamma M ∨ -γ ∈ CongruenceSubgroup.Gamma M := by
  first | exact @GlobalTheory.SiegSep.fix_siegel_pm_one | exact GlobalTheory.SiegSep.fix_siegel_pm_one | (intros; apply GlobalTheory.SiegSep.fix_siegel_pm_one <;> assumption)
