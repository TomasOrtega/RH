import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntMultipleOfInteger
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.algInt_dvd_nonzero_intCast` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FExistsIntMultipleOfInteger.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.exists_int_multiple_of_integer : ∀ (E : Type) [Field E] [NumberField E] (u : 𝓞 E), u ≠ 0 → ∃ c : ℤ, c ≠ 0 ∧ u ∣ (c : 𝓞 E) := by
  first | exact @GlobalTheory.algInt_dvd_nonzero_intCast | exact GlobalTheory.algInt_dvd_nonzero_intCast | (intros; apply GlobalTheory.algInt_dvd_nonzero_intCast <;> assumption)
