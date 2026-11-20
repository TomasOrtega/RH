import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.BesselUnitaryHaarTransportDiagonal
import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.MatrixOfBesselTwoSidedAction
open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S GlobalTheory.SgInf
open scoped ENNReal
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FBesselUnitaryHaarTransportDiagonal.lean&line=34#L34)
-/
theorem _root_.GlobalTheory.T.besselUnitary_haar_transport_diagonal : ∀ (k r : ℕ) (μG : Measure (Mt k r)) (ε : Fin (2 * r + k + 1) → Bool) (P : Mat k r), IsHaarOn (GG k r) μG → IsUnit P.det → Pᴴ * Formalism.REAL.Jm ε * P = Hpk k r → ∃ c : ℝ≥0∞, c ≠ ⊤ ∧ ∀ φ : Mt k r → ℝ≥0∞, Measurable φ → ∫⁻ y, φ (Matrix.of.symm (P⁻¹ * umat y * P)) ∂(Formalism.REAL.muG ε) = c * ∫⁻ x, φ x ∂μG := by
  first | exact @GlobalTheory.HaarTransport.haar_transport | exact GlobalTheory.HaarTransport.haar_transport | (intros; apply GlobalTheory.HaarTransport.haar_transport <;> assumption)
