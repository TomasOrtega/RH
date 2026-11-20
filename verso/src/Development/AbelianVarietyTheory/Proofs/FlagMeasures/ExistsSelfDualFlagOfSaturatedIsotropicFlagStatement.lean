import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsSelfDualFlagOfSaturatedIsotropicFlag
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.RadCov.FullFlag.main` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsSelfDualFlagOfSaturatedIsotropicFlag.lean&line=13#L13)
-/
theorem _root_.GlobalTheory.T.exists_selfDual_flag_of_saturated_isotropic_flag : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ (F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (r : ℕ → ℕ), IsDualFlag I.J F (2 * a + 1) ∧ F (2 * a + 1) = lamX I (1, xf) ∧ (∀ i : Fin (a + 1), F i = S i) ∧ (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) ∧ (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) ∧ r a = I.n - 2 * ∑ i, j i ∧ ∀ b, 2 * a + 1 ≤ b → r b = 0 := by
  first | exact @GlobalTheory.RadCov.FullFlag.main | exact GlobalTheory.RadCov.FullFlag.main | (intros; apply GlobalTheory.RadCov.FullFlag.main <;> assumption)
