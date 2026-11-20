import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HarishChandraCentralAction
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ExistsIsHaarMeasureSUJ
open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId GlobalTheory.DSSU
open scoped InnerProductSpace
set_option maxHeartbeats 1000000 in
/- English proof (citation)
Apply the cited theorem to the given parameters and hypotheses. The imported theorem has the same written statement and gives the conclusion directly.

[Source theorem](?module=Development%2FAbelianVarietyTheory%2FProofs%2FFlagMeasures%2FHarishChandraCentralAction.lean&line=85#L85)
-/
theorem _root_.GlobalTheory.T.harish_chandra_central_action : ∀ (n : ℕ), 1 ≤ n → ∀ (ε : Fin n → Bool) (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H] (π' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)) (lam : Fin n → ℝ) (m : ℤ), IsParU lam → ∑ a, lam a = (m : ℝ) → IsHCS ε (fun a => lam a - (m : ℝ) / n) π' → ∀ z : ℂ, z ^ n = 1 → ∀ v, π' (z • (1 : Matrix (Fin n) (Fin n) ℂ)) v = z ^ m • v := by
  first | exact @GlobalTheory.SUCentre.centre_acts | exact GlobalTheory.SUCentre.centre_acts | (intros; apply GlobalTheory.SUCentre.centre_acts <;> assumption)
