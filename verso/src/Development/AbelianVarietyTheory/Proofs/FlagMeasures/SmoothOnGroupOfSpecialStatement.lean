import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SmoothOnGroupOfSpecial
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply `GlobalTheory.SmoothCentral.smooth_of_central` to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FSmoothOnGroupOfSpecial.lean&line=52#L52)
-/
theorem _root_.GlobalTheory.T.smooth_on_group_of_special : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (m : ℤ) (f f' : Matrix (Fin n) (Fin n) ℂ → ℂ), (∀ z : ℂ, ‖z‖ = 1 → ∀ g ∈ SUset ε, f (z • g) = z ^ m * f' g) → SmoothS ε f' → SmoothOnG ε f := by
  first | exact @GlobalTheory.SmoothCentral.smooth_of_central | exact GlobalTheory.SmoothCentral.smooth_of_central | (intros; apply GlobalTheory.SmoothCentral.smooth_of_central <;> assumption)
