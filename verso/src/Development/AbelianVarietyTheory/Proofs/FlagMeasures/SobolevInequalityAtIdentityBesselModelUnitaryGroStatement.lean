import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SobolevInequalityAtIdentityBesselModelUnitaryGro
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FSobolevInequalityAtIdentityBesselModelUnitaryGro.lean&line=26#L26)
-/
theorem _root_.GlobalTheory.T.sobolev_inequality_at_identity_besselModelUnitaryGroup : ∀ (k r : ℕ) (μG : Measure (Mt k r)), IsHaarOn (GG k r) μG → ∃ (C : ℝ) (Ws : List (List (Mat k r))) (K₀ : Set (Mt k r)), IsCompact K₀ ∧ (∀ ws ∈ Ws, ∀ X ∈ ws, InLieHpk k r X) ∧ ∀ (B : Type) [NormedAddCommGroup B] [NormedSpace ℂ B] [CompleteSpace B] (f : Mat k r → B), SmoothOnH (Hpk k r) f → ‖f 1‖ ^ 2 ≤ C * (Ws.map fun ws => ∫ x in K₀, ‖rdWord ws f (Matrix.of x)‖ ^ 2 ∂μG).sum := by
  first | exact @GlobalTheory.SobAtOne.sobolev_at_one_G | exact GlobalTheory.SobAtOne.sobolev_at_one_G | (intros; apply GlobalTheory.SobAtOne.sobolev_at_one_G <;> assumption)
