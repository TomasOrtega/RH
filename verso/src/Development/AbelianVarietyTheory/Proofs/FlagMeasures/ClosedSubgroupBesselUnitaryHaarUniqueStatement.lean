import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ClosedSubgroupBesselUnitaryHaarUnique
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FClosedSubgroupBesselUnitaryHaarUnique.lean&line=29#L29)
-/
theorem _root_.GlobalTheory.T.closedSubgroupBesselUnitary_haar_unique : ∀ (k r : ℕ) (S : Set (Mat k r)) (μ μ' : Measure (Mt k r)), IsClosedSub k r S → IsHaarOn S μ → IsHaarOn S μ' → ∃ c : ENNReal, 0 < c ∧ c < ⊤ ∧ μ' = c • μ := by
  first | exact @GlobalTheory.SgInf.haarOn_unique | exact GlobalTheory.SgInf.haarOn_unique | (intros; apply GlobalTheory.SgInf.haarOn_unique <;> assumption)
