import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NcardRealGeneratedIdealsLe
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.SameKindIsometric
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FNcardRealGeneratedIdealsLe.lean&line=64#L64)
-/
theorem _root_.GlobalTheory.T.ncard_realGenerated_ideals_le : ∀ (E : Type) [Field E] [NumberField E] [StarRing E], Formalism.HermitianLatticesTheory.IsCMUnram E → ∀ Y : ℝ, 1 ≤ Y → {𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}.Finite ∧ (({𝔫 : Ideal (𝓞 E) | 𝔫 ≠ ⊥ ∧ 𝔫 = Ideal.span {t | t ∈ 𝔫 ∧ star (t : E) = t} ∧ (Ideal.absNorm 𝔫 : ℝ) ≤ Y ^ 2}.ncard : ℕ) : ℝ) ≤ Y * (1 + Real.log Y) ^ Formalism.HermitianLatticesTheory.fDeg E := by
  first | exact @GlobalTheory.RealIdealCount.ncard_real_ideals_le | exact GlobalTheory.RealIdealCount.ncard_real_ideals_le | (intros; apply GlobalTheory.RealIdealCount.ncard_real_ideals_le <;> assumption)
