import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagGradedPieceSizesStabiliserMul
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsLatMeasurableConst
open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FFlagGradedPieceSizesStabiliserMul.lean&line=102#L102)
-/
theorem _root_.GlobalTheory.T.flagGradedPieceSizes_stabiliser_mul : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∀ γ ∈ flagGroup I xf S, ∀ g : I.Ginf, sizesAt I xf S (γ * g) = sizesAt I xf S g := by
  first | exact @GlobalTheory.FlagSizeInv.sizesAt_mul | exact GlobalTheory.FlagSizeInv.sizesAt_mul | (intros; apply GlobalTheory.FlagSizeInv.sizesAt_mul <;> assumption)
