import Mathlib
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.OmegaKSqSubSelfAddEqZero
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.EndOmega
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.TranslateProduct
import Formalism.LocalToGlobal.TorsionIntegrality.TorsionTranslationPowers.StatementC
import Formalism.LocalToGlobal.TorsionIntegrality.GaussSumParity.StatementK
open PowerSeries GlobalTheory.Honda Formalism.L2.Th1.CM
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FDecoratedLatticeProofs%2FOmegaKSqSubSelfAddEqZero.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.omegaK_sq_sub_self_add_eq_zero : ∀ d : ℕ, d % 4 = 3 → omegaK d ^ 2 - omegaK d + (((d + 1) / 4 : ℕ) : ℂ) = 0 := by
  first | exact @GlobalTheory.omegaK_quadratic | exact GlobalTheory.omegaK_quadratic | (intros; apply GlobalTheory.omegaK_quadratic <;> assumption)
