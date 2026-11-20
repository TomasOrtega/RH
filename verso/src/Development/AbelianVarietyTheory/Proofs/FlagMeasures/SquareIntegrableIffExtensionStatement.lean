import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SquareIntegrableIffExtension
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SqIntSU.sqInt_iff` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FSquareIntegrableIffExtension.lean&line=207#L207)
-/
theorem _root_.GlobalTheory.T.square_integrable_iff_extension : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (m : ℤ) (π' π : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), Ext ε m π' π → IsURepOn (UJset ε) π → (IsSqIntOn ε π ↔ IsSqIntS ε π') := by
  first | exact @GlobalTheory.SqIntSU.sqInt_iff | exact GlobalTheory.SqIntSU.sqInt_iff | (intros; apply GlobalTheory.SqIntSU.sqInt_iff <;> assumption)
