import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCommonDenominatorIsIntegral
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsCommonDenominatorIsIntegral.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_common_denominator_isIntegral : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) (f : Fin n → E), ∃ d : ℕ, 0 < d ∧ ∀ j, IsIntegral ℤ ((d : E) * f j) := by
  first | exact @GlobalTheory.exists_common_denominator | exact GlobalTheory.exists_common_denominator | (intros; apply GlobalTheory.exists_common_denominator <;> assumption)
