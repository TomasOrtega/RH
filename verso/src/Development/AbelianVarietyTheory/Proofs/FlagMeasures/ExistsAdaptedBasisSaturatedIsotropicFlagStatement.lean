import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdaptedBasisSaturatedIsotropicFlag
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FExistsAdaptedBasisSaturatedIsotropicFlag.lean&line=68#L68)
-/
theorem _root_.GlobalTheory.T.exists_adaptedBasis_saturatedIsotropicFlag : ∀ (I I₀ : AutInst) (e : I₀.E ≃+* I.E) (p q a : ℕ) (j : Fin a → ℕ), (∀ y, e (star y) = star (e y)) → HasSig I p q → ∑ i, j i ≤ p → ∑ i, j i ≤ q → HasSig I₀ (p - ∑ i, j i) (q - ∑ i, j i) → ∀ (xf : I.Gf) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ Λ x₀ T T' T₀, IsAdapted I I₀ e xf j S Λ x₀ T T' T₀ := by
  first | exact @GlobalTheory.AdaptedExists.exists_isAdapted | exact GlobalTheory.AdaptedExists.exists_isAdapted | (intros; apply GlobalTheory.AdaptedExists.exists_isAdapted <;> assumption)
