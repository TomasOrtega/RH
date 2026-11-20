import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicNormZpowSubOnePadicValInt
import Formalism.SharpRestriction.LevelLetterCocycles.DataNLoc
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
open Formalism.BasicNotions Formalism.BasicNotions.Loc GlobalTheory.Cyc
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FInertiaEigenvalues%2FPadicNormZpowSubOnePadicValInt.lean&line=109#L109)
-/
theorem _root_.GlobalTheory.T.padic_norm_zpow_sub_one_padicValInt : ∀ (l : ℕ) [Fact l.Prime] (j : ℕ), Lev l j → ∀ u : ℚ_[l], ‖u - 1‖ = (l : ℝ) ^ (-(j : ℤ)) → ∀ k : ℤ, k ≠ 0 → ‖u ^ k - 1‖ = (l : ℝ) ^ (-((j : ℤ) + (padicValInt l k : ℤ))) := by
  first | exact @GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one | exact GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one | (intros; apply GlobalTheory.Cyc.LiftExp.norm_zpow_sub_one <;> assumption)
