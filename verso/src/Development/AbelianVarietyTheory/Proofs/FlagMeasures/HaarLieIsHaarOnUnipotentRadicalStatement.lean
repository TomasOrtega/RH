import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HaarLieIsHaarOnUnipotentRadical
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHaarLieIsHaarOnUnipotentRadical.lean&line=10#L10)
-/
theorem _root_.GlobalTheory.T.haarLie_isHaarOn_unipotentRadical : ∀ (k r : ℕ) (κ : ENNReal), 0 < κ → κ < ⊤ → IsHaarOn (Nset k r) (haarLie (Nset k r) κ) := by
  first | exact @GlobalTheory.haarLie_isHaarOn_Nset | exact GlobalTheory.haarLie_isHaarOn_Nset | (intros; apply GlobalTheory.haarLie_isHaarOn_Nset <;> assumption)
