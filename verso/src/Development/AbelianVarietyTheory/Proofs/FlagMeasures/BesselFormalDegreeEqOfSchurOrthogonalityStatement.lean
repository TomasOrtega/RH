import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselFormalDegreeEqOfSchurOrthogonality
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SgInf.fdegH_eq_of_schurH` to the given parameters and hypotheses. The parameters and hypotheses occur in the same order in both statements, and the conclusions agree.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FBesselFormalDegreeEqOfSchurOrthogonality.lean&line=7#L7)
-/
theorem _root_.GlobalTheory.T.besselFormalDegree_eq_of_schurOrthogonality : ∀ (k r : ℕ) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H] (σ : Mat k r → (H →L[ℂ] H)) (μG : Measure (Mt k r)) (d : ℝ) (w : H), SchurH μG σ d → w ≠ 0 → fdegH μG σ w = d := by
  first | exact @GlobalTheory.SgInf.fdegH_eq_of_schurH | exact GlobalTheory.SgInf.fdegH_eq_of_schurH | (intros; apply GlobalTheory.SgInf.fdegH_eq_of_schurH <;> assumption)
