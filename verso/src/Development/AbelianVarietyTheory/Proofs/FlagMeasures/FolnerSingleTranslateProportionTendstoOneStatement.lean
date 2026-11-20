import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FolnerSingleTranslateProportionTendstoOne
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SgInf.folner_single_translate` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FFolnerSingleTranslateProportionTendstoOne.lean&line=9#L9)
-/
theorem _root_.GlobalTheory.T.folner_single_translate_proportion_tendsto_one : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ : Measure (Mt k r)) (Om : ℕ → Set (Mt k r)), IsFolner S μ Om → ∀ p ∈ S, Filter.Tendsto (fun j => μ {s | s ∈ Om j ∧ lmulM p s ∈ Om j} / μ (Om j)) Filter.atTop (nhds 1) := by
  first | exact @GlobalTheory.SgInf.folner_single_translate | exact GlobalTheory.SgInf.folner_single_translate | (intros; apply GlobalTheory.SgInf.folner_single_translate <;> assumption)
