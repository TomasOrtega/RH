import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DvdUnitPowSubOne
import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.OneAddSmulVecMulVecMulVec
open ReciprocityTheory.ChartRestriction.G.FD NumberField GlobalTheory.UnipKill
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FIwasawaDecomposition%2FDvdUnitPowSubOne.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.dvd_unit_pow_sub_one : ∀ (E : Type) [Field E] [NumberField E] (u : (𝓞 E)ˣ) (M : 𝓞 E), M ≠ 0 → ∃ k : ℕ, 0 < k ∧ M ∣ ((u ^ k : (𝓞 E)ˣ) : 𝓞 E) - 1 := by
  first | exact @GlobalTheory.UnipKill.unit_pow_congr_one | exact GlobalTheory.UnipKill.unit_pow_congr_one | (intros; apply GlobalTheory.UnipKill.unit_pow_congr_one <;> assumption)
